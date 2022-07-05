package edu.cqu.algorithms.Treebb.FILO;


import edu.cqu.core.SyncMailer;

import java.util.*;

public abstract class RetentionPlusFrameFILO extends RetentionFrameFILO {

    private ArrayList<OptHistory> optHistories;
    private Map<Integer,Integer> proportion;

    public RetentionPlusFrameFILO(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        optHistories = new ArrayList<>();
        proportion = new HashMap<>();
    }

    protected void acllocateK(int K){
        int totalPPs = 0;   //  所有孩子伪父的总数
        for (int child : branchPseudoParents.keySet()){
            totalPPs += branchPseudoParents.get(child).size();
        }
        int id = -1;
        int remainer = K;
        for (int child : branchPseudoParents.keySet()){
            int pps = branchPseudoParents.get(child).size();
            if (pps == 0){
                continue;
            }
            id = child;
            int tmpProportion = (int)(((totalPPs - pps) * 1.0 * K) / ((children.size() - 1) * totalPPs));
            int totalSpaceSize = (int) Math.pow(domain.length,pps);
            int allocated = Integer.min(tmpProportion,totalSpaceSize);
            remainer -= allocated;
            proportion.put(child, allocated);
        }
        if (proportion.size() == 1){
            int pps = branchPseudoParents.get(id).size();
            int totalSpaceSize = (int) Math.pow(domain.length,pps);
            proportion.put(id, Integer.min(K,totalSpaceSize));
        }
        else if (proportion.size() != 0){
            int old = proportion.get(id);
            proportion.put(id,old + remainer);
        }
        System.out.println("proportion ：" + proportion);
    }


    protected void fillOptHistory(){
        for (int child : proportion.keySet()){
            boolean skip = false;
            //update Opt
            for (OptHistory history : optHistories){
                if (history.childId == child && history.conmpatible(cpa)){
                    for (int i = 0; i < domain.length; i++){
                        if (opt.get(child)[i].sendUb > 0){
                            history.rowOpt[i].costStar = opt.get(child)[i].costStar;
                            history.rowOpt[i].sendUb = opt.get(child)[i].sendUb;
                        }
                    }
                    skip = true;
                    break;
                }
            }
            int tmpProportion = proportion.get(child);
            if (skip){
                continue;
            }
            if (tmpProportion <= 0) {
                int removeID = -1;
                for (int i = optHistories.size() - 1; i >= 0; i--) {
                    if (optHistories.get(i).childId == child) {
                        removeID = i;
                        break;
                    }
                }
                optHistories.remove(removeID);
                OptElement[] tmpOpt = new OptElement[domain.length];
                for (int i = 0; i < domain.length; i++){
                    tmpOpt[i] = new OptElement(opt.get(child)[i].costStar, opt.get(child)[i].sendUb);
                }
                optHistories.add(new OptHistory(tmpOpt,projection(child),child));
//                System.out.println("----------");
            }
            //fill Opt
            else {
                OptElement[] tmpOpt = new OptElement[domain.length];
                for (int i = 0; i < domain.length; i++){
                    tmpOpt[i] = new OptElement(opt.get(child)[i].costStar, opt.get(child)[i].sendUb);
                }
                optHistories.add(new OptHistory(tmpOpt,projection(child),child));
                proportion.put(child,tmpProportion - 1);
            }
        }
    }


    protected Set<Integer> writeOpt(){
        Set<Integer> hitChild = new HashSet<>();
        for (int child : children)
            for (OptHistory history : optHistories){
                if (history.childId == child && history.conmpatible(cpa)){
                    OptElement[] tmpOpt = new OptElement[domain.length];
                    for (int i = 0; i < domain.length; ++i){
//                        if (history.rowOpt[i].sendUb > 0)
                        tmpOpt[i] = new OptElement(history.rowOpt[i].costStar, history.rowOpt[i].sendUb);
                    }
                    opt.put(child, tmpOpt);
                    hitChild.add(child);
                }
            }
            return hitChild;
    }

    private Map<Integer,Integer> projection(int childId){
        Map<Integer,Integer> result = new HashMap<>();
        for (int id : branchPseudoParents.get(childId)){
            result.put(id,cpa.get(id));
        }
        return result;
    }

    private class OptHistory{
        OptElement[] rowOpt;
        Map<Integer,Integer> ppsAssignment;
        int childId;

        public OptHistory(OptElement[] rowOpt, Map<Integer, Integer> ppsAssignment, int childId) {
            this.rowOpt = rowOpt;
            this.ppsAssignment = ppsAssignment;
            this.childId = childId;
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
