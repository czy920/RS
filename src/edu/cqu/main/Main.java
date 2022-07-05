package edu.cqu.main;


import edu.cqu.core.FinishedListener;
import edu.cqu.core.ProgressChangedListener;
import edu.cqu.core.Solver;
import edu.cqu.result.Result;
import edu.cqu.result.ResultWithPrivacy;
import edu.cqu.utils.FileUtils;

import java.time.chrono.IsoChronology;
import java.util.concurrent.atomic.AtomicBoolean;



public class Main {
    static AtomicBoolean isSolving = new AtomicBoolean(false);

    static StringBuilder msg_ret = new StringBuilder();
    static StringBuilder nccc_ret = new StringBuilder();
    static StringBuilder ub_ret = new StringBuilder();
    static StringBuilder privacy_ret = new StringBuilder();
    static StringBuilder time = new StringBuilder();
    static StringBuilder induceWidth = new StringBuilder();
    static StringBuilder messageSizeCount = new StringBuilder();
    static StringBuilder maxLen = new StringBuilder();
    static StringBuffer cycle = new StringBuffer();
    static String problemDir = "problem\\DCOP\\16";//
    static String outDir = problemDir.replace("problem","result");

    static String amPath = "problem/am.xml";
    static String[] agents = new String[]{
            "TreeBB",
            "TreeBBRetentionPlusOCS",
            "TreeBBRetentionPlus",
            "TreeBBRetentionPlusFIFO",
            "TreeBBRetentionPlusFILO" ,
            "TreeBBRetentionPlusLFU" ,
            "TreeBBRetentionPlusLRU" ,
            "TreeBBRetentionPlusUB" ,
            "TreeBBRetentionPlusOri" ,
            "TreeBBRetentionPlusSYS",
            "PTFB",
            "PTFBRS",
            "PTISBB",
            "PTISBBRS",
            "HSCAI",
            "HSCAIRS",
    };
    static int agentIndex = -1;
    static Solver solver = new Solver();
    static int validateTime = 1;
    static FinishedListenerImpl finishedListener = new FinishedListenerImpl();
    static OnProgressChangedListenerImpl progressChangedListener = new OnProgressChangedListenerImpl();

    private static class FinishedListenerImpl implements FinishedListener{
        @Override
        public void onFinished(Result result) {
            //output
            String algo = agents[agentIndex];
            System.out.println(algo + " have been done!");

            ResultWithPrivacy resultCycle = (ResultWithPrivacy) result;
            maxLen.append(resultCycle.getMaxLen() + "\n");
            ub_ret.append(resultCycle.getUb() + "\n");
            nccc_ret.append(resultCycle.getNcccs() + "\n");
            msg_ret.append(resultCycle.getMessageQuantity() + "  \n");
            privacy_ret.append(resultCycle.getLossRate() + " \n");
            time.append(resultCycle.getTotalTime() + " \n");
            messageSizeCount.append(resultCycle.getMessageSizeCount() + " \n");
            induceWidth.append(resultCycle.getMaxInduceWidth() + " \n");
            cycle.append(resultCycle.costInCycle.length);

            FileUtils.writeStringToFile(nccc_ret.toString(),outDir + "/" + algo +"/nccc.txt");//-treebb-
            FileUtils.writeStringToFile(msg_ret.toString(),outDir + "/" + algo +"/msg.txt");
            FileUtils.writeStringToFile(ub_ret.toString(),outDir + "/" + algo +"/ub.txt");
            FileUtils.writeStringToFile(privacy_ret.toString(),outDir + "/" + algo +"/privacy_ret.txt");
            FileUtils.writeStringToFile(time.toString(),outDir + "/" + algo +"/time.txt");
            FileUtils.writeStringToFile(messageSizeCount.toString(),outDir + "/" + algo +"/messageSizeCount.txt");
            FileUtils.writeStringToFile(cycle.toString(),outDir + "/" + algo +"/cycle.txt");
            FileUtils.writeStringToFile(maxLen.toString(),outDir + "/" + algo +"/maxLen.txt");

            maxLen = new StringBuilder();
            ub_ret= new StringBuilder();
            nccc_ret= new StringBuilder();

            msg_ret= new StringBuilder();

            privacy_ret = new StringBuilder();

            time= new StringBuilder();
            messageSizeCount= new StringBuilder();

            induceWidth= new StringBuilder();
            cycle = new StringBuffer();

            //start next cycle
            synchronized (isSolving) {
                isSolving.set(false);
                isSolving.notify();
            }
        }
    }

    public static void main(String[] args) {
        new Thread(new Monitor()).start();
    }

    private static class OnProgressChangedListenerImpl implements ProgressChangedListener{
        @Override
        public void onProgressChanged(double percentage, Result result) {
            // add content to rets
            System.out.println(percentage);
            ResultWithPrivacy resultCycle = (ResultWithPrivacy) result;
            maxLen.append(resultCycle.getMaxLen() + "\n");
            ub_ret.append(resultCycle.getUb() + "\n");
            nccc_ret.append(resultCycle.getNcccs() + "\n");
            msg_ret.append(resultCycle.getMessageQuantity() + "  \n");
            privacy_ret.append(resultCycle.getLossRate() + " \n");
            time.append(resultCycle.getTotalTime() + " \n");
            messageSizeCount.append(resultCycle.getMessageSizeCount() + " \n");
            induceWidth.append(resultCycle.getMaxInduceWidth() + " \n");
            cycle.append(resultCycle.costInCycle.length+ " \n");
        }

        @Override
        public void interrupted(String reason) {

        }
    }

    private static class Monitor implements Runnable{
        @Override
        public void run() {
            while (true) {
                synchronized (isSolving) {
                    while (isSolving.get()) {
                        try {
                            isSolving.wait();
                        } catch (InterruptedException e) {
                            e.printStackTrace();
                        }
                    }
                    agentIndex++;
                    if (agentIndex == agents.length){
                        break;
                    }
                    isSolving.set(true);
                    solver.batchSolve(amPath, agents[agentIndex], problemDir, validateTime, finishedListener, progressChangedListener);
                }
            }
        }
    }
}
