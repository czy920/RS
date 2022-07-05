package edu.cqu.algorithms.Treebb.LRU;


import edu.cqu.core.SyncMailer;

import java.util.*;

public abstract class RetentionPlusFrameLRU extends RetentionFrameLRU {

    private ArrayList<OptHistory> optHistories;
    private Map<Integer,Integer> proportion;

    public RetentionPlusFrameLRU(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
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
//        System.out.println("proportion ：" + proportion);
    }


    protected void fillOptHistory() {
        for (int child : proportion.keySet()){
            boolean skip = false;
            int removeFlag = -1;
            //update Opt
            for (int ii = 0; ii < optHistories.size(); ii++) {
                if (optHistories.get(ii).childId == child && optHistories.get(ii).conmpatible(cpa)){
                    for (int i = 0; i < domain.length; i++){
                        if (opt.get(child)[i].sendUb > 0){
                            optHistories.get(ii).rowOpt[i].costStar = opt.get(child)[i].costStar;
                            optHistories.get(ii).rowOpt[i].sendUb = opt.get(child)[i].sendUb;
                        }
                    }
                    skip = true;
                    removeFlag = ii;
                    break;
                }
            }
            if (removeFlag != -1) {
                OptHistory temp = null;
                try {
                    temp = (OptHistory)optHistories.get(removeFlag).clone();
                } catch (CloneNotSupportedException e) {
                    e.printStackTrace();
                }
                optHistories.remove(removeFlag);
                optHistories.add(temp);
            }
            int tmpProportion = proportion.get(child);
            if (skip){
                continue;
            }
            if (tmpProportion <= 0) {
                int removeID = -1;
                for (int i = 0; i < optHistories.size(); i++) {
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

    private class OptHistory implements Cloneable{
        OptElement[] rowOpt;
        Map<Integer,Integer> ppsAssignment;
        int childId;

        public OptHistory(OptElement[] rowOpt, Map<Integer, Integer> ppsAssignment, int childId) {
            this.rowOpt = rowOpt;
            this.ppsAssignment = ppsAssignment;
            this.childId = childId;
        }

        @Override
        protected Object clone() throws CloneNotSupportedException {
            OptHistory opt = (OptHistory)super.clone();
            return opt;
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
