package edu.cqu.algorithms.Treebb.OCS;


import edu.cqu.core.SyncMailer;

import java.util.*;

public abstract class RetentionPlusFrameOCS extends RetentionFrameOCS {

    private ArrayList<OptHistory> optHistories;
//    private Map<Integer,Integer> proportion;
    private int proportion;

    public RetentionPlusFrameOCS(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        optHistories = new ArrayList<>();
//        proportion = new HashMap<>();
    }

    protected void acllocateK(int K){
        proportion = K;
    }

    //todo
    protected void fillOptHistory(){
        boolean skip = false;
        for (OptHistory history : optHistories) {
            if (history.conmpatible(cpa)) {
                history.rowOpt.sendUb = preUB;
                history.rowOpt.costStar = localBound();
                skip = true;
            }

            break;
        }
        if (skip)   return;
        if (proportion > 0) {
            OptElement tmpOpt = new OptElement(localBound(), preUB);
            optHistories.add(new OptHistory(tmpOpt,projection()));
            proportion--;
        }
    }

    //todo
    private void showOptHistory() {
        System.out.println("---------------");
        System.out.println("id : " + id);
        for (OptHistory optHistory : optHistories) {
                System.out.println(" optHistory.ppsAssignment : " + optHistory.ppsAssignment + "value : " + " ( " + optHistory.rowOpt.sendUb + ", " + optHistory.rowOpt.costStar + " )");
        }
        System.out.println("---------------");

    }


    protected int writeOpt(){

        for (OptHistory history : optHistories){
            if (history.conmpatible(cpa)){
                return history.rowOpt.costStar;
            }
        }
        return -1;
    }

    private Map<Integer,Integer> projection(){
        Map<Integer,Integer> result = new HashMap<>();
        for (int child : children)
            for (int id : branchPseudoParents.get(child)){
                result.put(id,cpa.get(id));
            }
        for (int pp : pseudoParents)
            result.put(pp,cpa.get(pp));
        result.put(parent,cpa.get(parent));
        return result;
    }

    private class OptHistory{
        OptElement rowOpt;
        Map<Integer,Integer> ppsAssignment;

        public OptHistory(OptElement rowOpt, Map<Integer, Integer> ppsAssignment) {
            this.rowOpt = rowOpt;
            this.ppsAssignment = ppsAssignment;
        }

        public boolean conmpatible(Map<Integer,Integer> cpa){
            for (int id : ppsAssignment.keySet()){
                if (ppsAssignment.get(id).intValue() != cpa.get(id)){
                    return false;
                }
            }
            return true;
        }
    }
}
