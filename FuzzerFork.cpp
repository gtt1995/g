//===- FuzzerFork.cpp - run fuzzing in separate subprocesses --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
// Spawn and orchestrate separate fuzzing processes.
//===----------------------------------------------------------------------===//

#include "FuzzerCommand.h"
#include "FuzzerFork.h"
#include "FuzzerIO.h"
#include "FuzzerInternal.h"
#include "FuzzerMerge.h"
#include "FuzzerSHA1.h"
#include "FuzzerTracePC.h"
#include "FuzzerUtil.h"

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <fstream>
#include <memory>
#include <mutex>
#include <queue>
#include <sstream>
#include <thread>
#include <random>

namespace fuzzer {

struct Stats {
  size_t number_of_executed_units = 0;
  size_t peak_rss_mb = 0;
  size_t average_exec_per_sec = 0;
};
//定义子语料库结构体
struct SubCorpus {
  size_t Id;
  double Energy;
  double Reward;
  //Set<uint32_t> AddFeatures = 0;
  double AddFeatures = 0;
  //Set<uint32_t> AddCov = 0;
  double AddCov = 0;
  double Execs = 0;
  double AddFiles = 0;
  double AddFunctions = 0;
  double EnergyTotal = 0;
};
struct Current_MAX_MIN{
  double CurrentExecs[120] = {0};//保存当前执行速度
  double CurrentAddFeatures[120] = {0};//保存当前执行速度
  double CurrentAddCov[120] = {0};//保存当前执行速度
  double CurrentAddFiles[120] = {0};//保存当前执行速度
  double maxExecs = 0;
  double maxAddFeatures = 0;
  double maxAddCov = 0;
  double maxAddFiles = 0;
  double minExecs = 0;
  double minAddFeatures = 0;
  double minAddCov = 0;
  double minAddFiles = 0;

};
//arr[]存储Energy，用来根据概率选择目标子语料库
double arr[120] = {0};

void Normalization(struct Current_MAX_MIN *CR,struct SubCorpus *SC, int NumJobs){
	int j = 0;
	CR->maxExecs = CR->CurrentExecs[1];
	CR->minExecs = CR->CurrentExecs[1];
	CR->maxAddFeatures = CR->CurrentAddFeatures[1];
	CR->minAddFeatures = CR->CurrentAddFeatures[1];
	CR->maxAddCov = CR->CurrentAddCov[1];
	CR->minAddCov = CR->CurrentAddCov[1];
        CR->maxAddFiles = CR->CurrentAddFiles[1];
        CR->minAddFiles = CR->CurrentAddFiles[1];
	for (int i = 0; i < NumJobs ; i++){
		if (CR->CurrentExecs[j] > CR->maxExecs) CR->maxExecs = CR->CurrentExecs[j];
		if (CR->CurrentExecs[j] < CR->minExecs) CR->minExecs = CR->CurrentExecs[j];
		if (CR->CurrentAddFeatures[j] > CR->maxAddFeatures) CR->maxAddFeatures = CR->CurrentAddFeatures[j];
                if (CR->CurrentAddFeatures[j] < CR->minAddFeatures) CR->minAddFeatures = CR->CurrentAddFeatures[j];
		if (CR->CurrentAddCov[j] > CR->maxAddCov) CR->maxAddCov = CR->CurrentAddCov[j];
                if (CR->CurrentAddCov[j] < CR->minAddCov) CR->minAddCov = CR->CurrentAddCov[j];
		if (CR->CurrentAddFiles[j] > CR->maxAddFiles) CR->maxAddFiles = CR->CurrentAddFiles[j];
                if (CR->CurrentAddFiles[j] < CR->minAddFiles) CR->minAddFiles = CR->CurrentAddFiles[j];
		j++;
    }
	SC->Execs = (SC->Execs - CR->minExecs)/(CR->maxExecs - CR->minExecs);
	SC->AddFeatures = (SC->AddFeatures - CR->minAddFeatures)/(CR->maxAddFeatures - CR->minAddFeatures);
	SC->AddCov = (SC->AddCov - CR->minAddCov)/(CR->maxAddCov - CR->minAddCov);
	SC->AddFiles = (SC->AddFiles - CR->minAddFiles)/(CR->maxAddFiles - CR->minAddFiles);

}
//根据当前语料库的Energy，更新权重
void UpdateWeight(double * arr,struct SubCorpus * SC,int NumCorpus){
	double sum = 0;
	for (int i = 0; i<NumCorpus;i++){
		sum += SC[i].Energy;
		arr[i] = sum;
	}
}
//根据权重选择目标语料库
int PickWithWeight(double * arr,size_t NumCorpus){
	std::mt19937 Rng;
	Rng.seed(std::random_device()());
	std::uniform_real_distribution<double> RAnd(0,arr[NumCorpus-1]);
	double randomNum = RAnd(Rng);
	int left = 0,right = NumCorpus - 1;
	while (left<right){
		int mid = left + ((right - left) >> 1);
		if (arr[mid] == randomNum){
			return mid;
		}else if (arr[mid] > randomNum){
			right = mid;
		}else{
			left = mid + 1;
		}
	}
	return left;
}

static Stats ParseFinalStatsFromLog(const std::string &LogPath) {
  std::ifstream In(LogPath);
  std::string Line;
  Stats Res;
  struct {
    const char *Name;
    size_t *Var;
  } NameVarPairs[] = {
      {"stat::number_of_executed_units:", &Res.number_of_executed_units},
      {"stat::peak_rss_mb:", &Res.peak_rss_mb},
      {"stat::average_exec_per_sec:", &Res.average_exec_per_sec},
      {nullptr, nullptr},
  };
  while (std::getline(In, Line, '\n')) {
    if (Line.find("stat::") != 0) continue;
    std::istringstream ISS(Line);
    std::string Name;
    size_t Val;
    ISS >> Name >> Val;
    for (size_t i = 0; NameVarPairs[i].Name; i++)
      if (Name == NameVarPairs[i].Name)
        *NameVarPairs[i].Var = Val;
  }
  return Res;
}

struct FuzzJob {
  // Inputs.
  Command Cmd;
  std::string CorpusDir;
  std::string FeaturesDir;
  std::string LogPath;
  std::string SeedListPath;
  std::string CFPath;
  size_t      JobId;

  int         DftTimeInSeconds = 0;

  // Fuzzing Outputs.
  int ExitCode;

  ~FuzzJob() {
    RemoveFile(CFPath);
    RemoveFile(LogPath);
    RemoveFile(SeedListPath);
    RmDirRecursive(CorpusDir);
    RmDirRecursive(FeaturesDir);
  }
};

struct GlobalEnv {
  Vector<std::string> Args;
  Vector<std::string> CorpusDirs;
  std::string MainCorpusDir;
  std::string TempDir;
  std::string DFTDir;
  std::string DataFlowBinary;
  Set<uint32_t> Features, Cov;
  Set<std::string> FilesWithDFT;
  Vector<std::string> Files;
  Random *Rand;
  std::chrono::system_clock::time_point ProcessStartTime;
  int Verbosity = 0;

  size_t NumTimeouts = 0;
  size_t NumOOMs = 0;
  size_t NumCrashes = 0;
  
  

  size_t NumRuns = 0;

  std::string StopFile() { return DirPlusFile(TempDir, "STOP"); }

  size_t secondsSinceProcessStartUp() const {
    return std::chrono::duration_cast<std::chrono::seconds>(
               std::chrono::system_clock::now() - ProcessStartTime)
        .count();
  }



  FuzzJob *CreateNewJob(size_t JobId,int Total, size_t CorpusId) {
    Command Cmd(Args);
    Cmd.removeFlag("fork");
    Cmd.removeFlag("runs");
    Cmd.removeFlag("collect_data_flow");
    for (auto &C : CorpusDirs) // Remove all corpora from the args.
      Cmd.removeArgument(C);
    Cmd.addFlag("reload", "0");  // working in an isolated dir, no reload.
    Cmd.addFlag("print_final_stats", "1");
    Cmd.addFlag("print_funcs", "0");  // no need to spend time symbolizing.
    Cmd.addFlag("max_total_time", std::to_string(std::min((size_t)300, JobId)));
    Cmd.addFlag("stop_file", StopFile());
    if (!DataFlowBinary.empty()) {
      Cmd.addFlag("data_flow_trace", DFTDir);
      if (!Cmd.hasFlag("focus_function"))
        Cmd.addFlag("focus_function", "auto");
    }
    auto Job = new FuzzJob;
    std::string Seeds;
    if (size_t CorpusSubsetSize =
            std::min(Files.size(), (size_t)sqrt(Files.size() + 2))) {
      size_t AverageSize = Files.size()/Total +1;
      auto Time1 = std::chrono::system_clock::now();
      size_t StartIndex = CorpusId *  AverageSize;
      for (size_t i = 0; i < CorpusSubsetSize; i++) {
	size_t j = Rand->SkewTowardsLast(AverageSize);
	size_t m = j + StartIndex;
        if (m < Files.size()) {
		auto &SF = Files[m];
        	Seeds += (Seeds.empty() ? "" : ",") + SF;
        	CollectDFT(SF);
	}
	else  {
		auto &SF = Files[Files.size()/2];
        	Seeds += (Seeds.empty() ? "" : ",") + SF;
        	CollectDFT(SF);
	} 
      }
      auto Time2 = std::chrono::system_clock::now();
      Job->DftTimeInSeconds = duration_cast<seconds>(Time2 - Time1).count();
    }
    if (!Seeds.empty()) {
      Job->SeedListPath =
          DirPlusFile(TempDir, std::to_string(JobId) + ".seeds");
      WriteToFile(Seeds, Job->SeedListPath);
      Cmd.addFlag("seed_inputs", "@" + Job->SeedListPath);
    }
    Job->LogPath = DirPlusFile(TempDir, std::to_string(JobId) + ".log");
    Job->CorpusDir = DirPlusFile(TempDir, "C" + std::to_string(JobId));
    Job->FeaturesDir = DirPlusFile(TempDir, "F" + std::to_string(JobId));
    Job->CFPath = DirPlusFile(TempDir, std::to_string(JobId) + ".merge");
    Job->JobId = JobId;


    Cmd.addArgument(Job->CorpusDir);
    Cmd.addFlag("features_dir", Job->FeaturesDir);

    for (auto &D : {Job->CorpusDir, Job->FeaturesDir}) {
      RmDirRecursive(D);
      MkDir(D);
    }

    Cmd.setOutputFile(Job->LogPath);
    Cmd.combineOutAndErr();

    Job->Cmd = Cmd;

    if (Verbosity >= 2)
      Printf("Job %zd/%p Created: %s\n", JobId, Job,
             Job->Cmd.toString().c_str());
    // Start from very short runs and gradually increase them.
    return Job;
  }

  void RunOneMergeJob(FuzzJob *Job, struct SubCorpus * SC, struct Current_MAX_MIN *CR, int NumJobs) {
    auto Stats = ParseFinalStatsFromLog(Job->LogPath);
    NumRuns += Stats.number_of_executed_units;

    Vector<SizedFile> TempFiles, MergeCandidates;
    // Read all newly created inputs and their feature sets.
    // Choose only those inputs that have new features.
    GetSizedFilesFromDir(Job->CorpusDir, &TempFiles);
    std::sort(TempFiles.begin(), TempFiles.end());
    for (auto &F : TempFiles) {
      auto FeatureFile = F.File;
      FeatureFile.replace(0, Job->CorpusDir.size(), Job->FeaturesDir);
      auto FeatureBytes = FileToVector(FeatureFile, 0, false);
      assert((FeatureBytes.size() % sizeof(uint32_t)) == 0);
      Vector<uint32_t> NewFeatures(FeatureBytes.size() / sizeof(uint32_t));
      memcpy(NewFeatures.data(), FeatureBytes.data(), FeatureBytes.size());
      for (auto Ft : NewFeatures) {
        if (!Features.count(Ft)) {
          MergeCandidates.push_back(F);
          break;
        }
      }
    }
    // if (!FilesToAdd.empty() || Job->ExitCode != 0)
    Printf("#%zd: cov: %zd ft: %zd corp: %zd exec/s %zd "
           "oom/timeout/crash: %zd/%zd/%zd time: %zds job: %zd dft_time: %d\n",
           NumRuns, Cov.size(), Features.size(), Files.size(),
           Stats.average_exec_per_sec, NumOOMs, NumTimeouts, NumCrashes,
           secondsSinceProcessStartUp(), Job->JobId, Job->DftTimeInSeconds);

    if (MergeCandidates.empty()) return;

    Vector<std::string> FilesToAdd;
    Set<uint32_t> NewFeatures, NewCov;
    CrashResistantMerge(Args, {}, MergeCandidates, &FilesToAdd, Features,
                        &NewFeatures, Cov, &NewCov, Job->CFPath, false);
    for (auto &Path : FilesToAdd) {
      auto U = FileToVector(Path);
      auto NewPath = DirPlusFile(MainCorpusDir, Hash(U));
      WriteToFile(U, NewPath);
      Files.push_back(NewPath);
    }
    Features.insert(NewFeatures.begin(), NewFeatures.end());
    Cov.insert(NewCov.begin(), NewCov.end());
    SC->Execs = (double)Stats.average_exec_per_sec;
    SC->AddFeatures = (double)NewFeatures.size();
    SC->AddCov = (double)NewCov.size();
    SC->AddFiles = (double)FilesToAdd.size();
    CR->CurrentExecs[((Job->JobId-1)%NumJobs)] = SC->Execs;//记录最新NumJobs个Jobs的执行速度，用来归一化执行速度特征
    CR->CurrentAddFeatures[((Job->JobId-1)%NumJobs)] = SC->AddFeatures;//记录最新NumJobs个Jobs的执行速度，用来归一化执行速度特征
    CR->CurrentAddCov[((Job->JobId-1)%NumJobs)] = SC->AddCov;//记录最新NumJobs个Jobs的执行速度，用来归一化执行速度特征
    CR->CurrentAddFiles[((Job->JobId-1)%NumJobs)] = SC->AddFiles;//记录最新NumJobs个Jobs的执行速度，用来归一化执行速度特征
    CR->maxExecs = SC->Execs;
    CR->minExecs = SC->Execs;
    CR->maxAddFeatures = SC->AddFeatures;
    CR->minAddFeatures = SC->AddFeatures;
    CR->maxAddCov = SC->AddCov;
    CR->minAddCov = SC->AddCov;
    CR->maxAddFiles = SC->AddFiles;
    CR->minAddFiles = SC->AddFiles;
    for (auto Idx : NewCov)
      if (auto *TE = TPC.PCTableEntryByIdx(Idx))
        if (TPC.PcIsFuncEntry(TE)){
          PrintPC("  NEW_FUNC: %p %F %L\n", "",
                  TPC.GetNextInstructionPc(TE->PC));
	  SC->AddFunctions++;
	}
    
    Normalization(CR,SC,NumJobs);
    //把Fuzz过程分几个阶段，计算Energy，前n个job变化剧烈，不计算能量，此段fuzz特征增长较明显
    if (Job->JobId >  2 && Job->JobId < 10000){
	    SC->Reward = (SC->Execs + (SC->AddFeatures*20 + SC->AddCov*20 + SC->AddFiles*10));
	    if (SC->AddFunctions) SC->Reward = SC->Reward * 3 ;
	    SC->Energy = 0.5*SC->Reward + (1 - 0.5)*SC->Energy;
	    SC->EnergyTotal+=SC->Energy;

    }
    /*if (Job->JobId >= 100 && Job->JobId < 300){
	    SC->Reward = (SC->Execs + (SC->AddFeatures + SC->AddCov + SC->AddFiles));
            if (SC->AddFunctions) SC->Reward = SC->Reward * 5 ;
            SC->Energy = 0.5*SC->Reward + (1 - 0.5)*SC->Energy;
	    SC->EnergyTotal+=SC->Energy;
    }

    if(Job->JobId >= 300 && Job->JobId < 700){
	    SC->Reward = (SC->Execs  + (SC->AddFeatures + SC->AddCov*10 + SC->AddFiles)*10);
            if (SC->AddFunctions) SC->Reward = SC->Reward * 10 ;
            SC->Energy = 0.5*SC->Reward + (1 - 0.5)*SC->Energy;
	    SC->EnergyTotal+=SC->Energy;
    }
    if(Job->JobId >= 700 && Job->JobId < 1000){
	    SC->Reward = (SC->Execs + (SC->AddFeatures + SC->AddCov*10 + SC->AddFiles)*10);
            if (SC->AddFunctions) SC->Reward = SC->Reward * 50 ;
            SC->Energy = 0.5*SC->Reward + (1 - 0.5)*SC->Energy;
	    SC->EnergyTotal+=SC->Energy;
    }
    if(Job->JobId >= 1000 && Job->JobId < 4000){
	    SC->Reward = (SC->Execs + (SC->AddFeatures + SC->AddCov*10 + SC->AddFiles)*10);
            if (SC->AddFunctions) SC->Reward = SC->Reward * 100 ;
            SC->Energy = 0.5*SC->Reward + (1 - 0.5)*SC->Energy;
	    SC->EnergyTotal+=SC->Energy;
    }
    if(Job->JobId >= 4000){
	    SC->Reward = (SC->Execs + (SC->AddFeatures + SC->AddCov*10 + SC->AddFiles)*10);
            if (SC->AddFunctions) SC->Reward = SC->Reward * 300 ;
            SC->Energy = 0.5*SC->Reward + (1 - 0.5)*SC->Energy;
	    SC->EnergyTotal+=SC->Energy;
    }*/
    
    printf("Current Corpus Id: %d   SC->Execs :%f   SC->Reward :%f  S->Energy :%f	SC->AddFeatures:%f  SC->AddCov:%f  SC->AddFiles:%f  SC->AddFunctions:%f \n",SC->Id,SC->Execs,SC->Reward,SC->Energy,SC->AddFeatures,SC->AddCov,SC->AddFiles,SC->AddFunctions); 
    //清0
    //printf("Total Energy : %f\n",SC->EnergyTotal);
    SC->Execs = 0 ;
    SC->AddFeatures = 0 ;
    SC->AddCov =  0;
    SC->AddFiles =  0;
    SC->AddFunctions = 0;

    //根据当前corpus的reward，计算其最新的能量（全局变量）并赋值给当前Corpus;
    //E(B)=a*R+(1-a)*E(B);E=E1/(E1+E2+E3....)；
    //然后清空当前Id的Corpus.RewardFeatures，Corpus.RewardCov，Corpus.RewardExecs

  }


  void CollectDFT(const std::string &InputPath) {
    if (DataFlowBinary.empty()) return;
    if (!FilesWithDFT.insert(InputPath).second) return;
    Command Cmd(Args);
    Cmd.removeFlag("fork");
    Cmd.removeFlag("runs");
    Cmd.addFlag("data_flow_trace", DFTDir);
    Cmd.addArgument(InputPath);
    for (auto &C : CorpusDirs) // Remove all corpora from the args.
      Cmd.removeArgument(C);
    Cmd.setOutputFile(DirPlusFile(TempDir, "dft.log"));
    Cmd.combineOutAndErr();
    // Printf("CollectDFT: %s\n", Cmd.toString().c_str());
    ExecuteCommand(Cmd);
  }

};

struct JobQueue {
  std::queue<FuzzJob *> Qu;
  std::mutex Mu;
  std::condition_variable Cv;

  void Push(FuzzJob *Job) {
    {
      std::lock_guard<std::mutex> Lock(Mu);
      Qu.push(Job);
    }
    Cv.notify_one();
  }
  FuzzJob *Pop() {
    std::unique_lock<std::mutex> Lk(Mu);
    // std::lock_guard<std::mutex> Lock(Mu);
    Cv.wait(Lk, [&]{return !Qu.empty();});
    assert(!Qu.empty());
    auto Job = Qu.front();
    Qu.pop();
    return Job;
  }
};

void WorkerThread(JobQueue *FuzzQ, JobQueue *MergeQ) {
  while (auto Job = FuzzQ->Pop()) {
    // Printf("WorkerThread: job %p\n", Job);
    Job->ExitCode = ExecuteCommand(Job->Cmd);
    MergeQ->Push(Job);
  }
}

// This is just a skeleton of an experimental -fork=1 feature.
void FuzzWithFork(Random &Rand, const FuzzingOptions &Options,
                  const Vector<std::string> &Args,
                  const Vector<std::string> &CorpusDirs, int NumJobs) {
  Printf("INFO: -fork=%d: fuzzing in separate process(s)\n", NumJobs);
  
  struct SubCorpus SC[NumJobs];//定义子语料库结构体
  struct Current_MAX_MIN CR;
  //struct SubCorpus * sc[NumJobs];
  int Instance[NumJobs] ;//保存当前JobId取模后对应选取的子语料库Id
  for (size_t j = 0; j < NumJobs; j++){
	  SC[j].Id = j;
	  SC[j].Energy = 1;
	  Instance[j] = j;
	  //sc[j] = &SC[j];
  }
  int CorpusId = 0;
  int CorpusCount[120] = {0};
  double InitialEnergy = 0;
  int JobExecuted = 0;//记录执行的Jobs，当达到某一数值时，清空当前的子语料库能量，重新计算，避免Fuzz各阶段的不均衡
  int UpdateCtr = NumJobs;
  GlobalEnv Env;
  Env.Args = Args;
  Env.CorpusDirs = CorpusDirs;
  Env.Rand = &Rand;
  Env.Verbosity = Options.Verbosity;
  Env.ProcessStartTime = std::chrono::system_clock::now();
  Env.DataFlowBinary = Options.CollectDataFlow;

  Vector<SizedFile> SeedFiles;
  for (auto &Dir : CorpusDirs)
    GetSizedFilesFromDir(Dir, &SeedFiles);
  std::sort(SeedFiles.begin(), SeedFiles.end());
  Env.TempDir = TempPath(".dir");
  Env.DFTDir = DirPlusFile(Env.TempDir, "DFT");
  RmDirRecursive(Env.TempDir);  // in case there is a leftover from old runs.
  MkDir(Env.TempDir);
  MkDir(Env.DFTDir);


  if (CorpusDirs.empty())
    MkDir(Env.MainCorpusDir = DirPlusFile(Env.TempDir, "C"));
  else
    Env.MainCorpusDir = CorpusDirs[0];

  auto CFPath = DirPlusFile(Env.TempDir, "merge.txt");
  CrashResistantMerge(Env.Args, {}, SeedFiles, &Env.Files, {}, &Env.Features,
                      {}, &Env.Cov,
                      CFPath, false);
  RemoveFile(CFPath);
  Printf("INFO: -fork=%d: %zd seed inputs, starting to fuzz in %s\n", NumJobs,
         Env.Files.size(), Env.TempDir.c_str());

  int ExitCode = 0;

  JobQueue FuzzQ, MergeQ;

  auto StopJobs = [&]() {
    for (int i = 0; i < NumJobs; i++)
      FuzzQ.Push(nullptr);
    MergeQ.Push(nullptr);
    WriteToFile(Unit({1}), Env.StopFile());
  };

  size_t JobId = 0;
  Vector<std::thread> Threads;
  for (int t = 0; t < NumJobs; t++) {
    Threads.push_back(std::thread(WorkerThread, &FuzzQ, &MergeQ));
    JobId++;
    FuzzQ.Push(Env.CreateNewJob(JobId,NumJobs,Instance[t]));
  }

  while (true) {
    std::unique_ptr<FuzzJob> Job(MergeQ.Pop());
    if (!Job)
      break;
    ExitCode = Job->ExitCode;
    if (ExitCode == Options.InterruptExitCode) {
      Printf("==%lu== libFuzzer: a child was interrupted; exiting\n", GetPid());
      StopJobs();
      break;
    }
    Fuzzer::MaybeExitGracefully();
    
    Env.RunOneMergeJob(Job.get(),&SC[Instance[(Job->JobId-1)%NumJobs]], &CR, NumJobs); 
    // Continue if our crash is one of the ignorred ones.
    if (Options.IgnoreTimeouts && ExitCode == Options.TimeoutExitCode)
      Env.NumTimeouts++;
    else if (Options.IgnoreOOMs && ExitCode == Options.OOMExitCode)
      Env.NumOOMs++;
    else if (ExitCode != 0) {
      Env.NumCrashes++;
      if (Options.IgnoreCrashes) {
        std::ifstream In(Job->LogPath);
        std::string Line;
        while (std::getline(In, Line, '\n'))
          if (Line.find("ERROR:") != Line.npos ||
              Line.find("runtime error:") != Line.npos)
            Printf("%s\n", Line.c_str());
      } else {
        // And exit if we don't ignore this crash.
        Printf("INFO: log from the inner process:\n%s",
               FileToString(Job->LogPath).c_str());
        StopJobs();
        break;
      }
    }

    // Stop if we are over the time budget.
    // This is not precise, since other threads are still running
    // and we will wait while joining them.
    // We also don't stop instantly: other jobs need to finish.
    if (Options.MaxTotalTimeSec > 0 &&
        Env.secondsSinceProcessStartUp() >= (size_t)Options.MaxTotalTimeSec) {
      Printf("INFO: fuzzed for %zd seconds, wrapping up soon\n",
             Env.secondsSinceProcessStartUp());
      StopJobs();
      for (int i=0;i<NumJobs;i++)
	      printf("Corpus %d is chosen %d.\n",i,CorpusCount[i]);
      break;
    }
    if (Env.NumRuns >= Options.MaxNumberOfRuns) {
      Printf("INFO: fuzzed for %zd iterations, wrapping up soon\n",
             Env.NumRuns);
      StopJobs();
      break;
    }
    JobExecuted++;
    if (JobExecuted >= NumJobs * 50 || JobExecuted <2){
	    for (int i=0; i<NumJobs ; i++){
		    InitialEnergy += SC[i].Energy;
	    }
	    InitialEnergy = InitialEnergy/NumJobs;
	    for (int i=0; i<NumJobs ; i++){
		    SC[i].Energy = InitialEnergy;
	    }
	    printf("\n\n		重置能量		\n\n");
	    JobExecuted = 0;
    }
    UpdateCtr++;
    /*if (UpdateCtr >= NumJobs){
	    UpdateWeight(arr, SC, NumJobs);
	    UpdateCtr = 0;

    }*/
    UpdateWeight(arr, SC, NumJobs);
    int CorpusId = PickWithWeight(arr,NumJobs);
    Instance[(((JobId++)-1)%NumJobs)] = CorpusId;
    FuzzQ.Push(Env.CreateNewJob(JobId,NumJobs,CorpusId));
    //printf("	JobId :%d	(JobId-1)%NumJobs :%d	   CorpusId : %d \n",JobId,(((JobId)-1)%NumJobs),CorpusId);
    CorpusCount[CorpusId]++;
    
  }

  for (auto &T : Threads)
    T.join();

  // The workers have terminated. Don't try to remove the directory before they
  // terminate to avoid a race condition preventing cleanup on Windows.
  RmDirRecursive(Env.TempDir);

  // Use the exit code from the last child process.
  Printf("INFO: exiting: %d time: %zds\n", ExitCode,
         Env.secondsSinceProcessStartUp());
  exit(ExitCode);
}

} // namespace fuzzer
