package edu.cqu.algorithms.Treebb.SYS;


import edu.cqu.core.SyncMailer;

import java.util.*;

public abstract class RetentionPlusFrameSYS extends RetentionFrameSYS {

    private ArrayList<OptHistory> optHistories;
    private Map<Integer,Integer> proportion;
    private Map<Integer,Integer> proportionR;
    private Map<Integer, Integer> hitCountSum;
    private double memSize;
    private List<Integer> removeNum;

    public RetentionPlusFrameSYS(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        optHistories = new ArrayList<>();
        proportion = new HashMap<>();
        hitCountSum = new HashMap<>();
        removeNum = new ArrayList<>();
        proportionR = new HashMap<>();
    }

    protected void acllocateK(int K){
        int totalPPs = 0;   //  所有孩子伪父的总数
        memSize = Math.log(K) / Math.log(domain.length) + 1;
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
            proportionR.put(child, allocated);
        }
        if (proportion.size() == 1){
            int pps = branchPseudoParents.get(id).size();
            int totalSpaceSize = (int) Math.pow(domain.length,pps);
            proportion.put(id, Integer.min(K,totalSpaceSize));
            proportionR.put(id, Integer.min(K,totalSpaceSize));
        }
        else if (proportion.size() != 0){
            int old = proportion.get(id);
            proportion.put(id,old + remainer);
            proportionR.put(id,old + remainer);
        }
//        initHitCountSum();
        System.out.println("proportion ：" + proportion);
    }

    private void initHitCountSum() {
        int maxHeight = -1;
        for (int i : ancHeight.keySet()) {
            if (maxHeight < ancHeight.get(i))
                maxHeight = ancHeight.get(i);
        }
        int sumCount = maxHeight - height;
        for (int child : branchPseudoParents.keySet()) {
            int childCount = sumCount - branchPseudoParents.get(child).size();
            if (childCount != 0)
                hitCountSum.put(child, (int) Math.pow(domain.length, childCount));
            else
                hitCountSum.put(child, 0);
        }
        System.out.println("----" + hitCountSum);
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
            if (tmpProportion <= 0 ) {
                int stayNum = 0;
                for (int v = 0; v < domain.length; v++) {
                    if (opt.get(child)[v].sendUb <= 0) {
                        stayNum++;
                    }
                }
                if (stayNum > 2)    continue;
                int remove = removePage(child);
                if (remove != -1) {
                    optHistories.remove(remove);
                    OptElement[] tmpOpt = new OptElement[domain.length];
                    for (int i = 0; i < domain.length; i++){
                        tmpOpt[i] = new OptElement(opt.get(child)[i].costStar, opt.get(child)[i].sendUb);
                    }
                    optHistories.add(new OptHistory(tmpOpt,projection(child),child));
                }

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
//            showOptHistory();
        }
    }

    private void showOptHistory() {
        System.out.println("---------------");
        System.out.println("id : " + id);
        for (OptHistory optHistory : optHistories) {
            for (int i = 0; i < optHistory.rowOpt.length; i++) {
                System.out.println("optHistory.childId : " + optHistory.childId + " optHistory.ppsAssignment : " + optHistory.ppsAssignment + " ( " + optHistory.rowOpt[i].sendUb + ", " + optHistory.rowOpt[i].costStar + " )");
            }
        }
        System.out.println("---------------");

    }

    private int removePage(int child) {
//  todo 根据cpa和存储的cache对比，估算未来调用最少的cache块移除
        int removeOutID = -1;
        /*double iii = proportionR.get(child) == 0 ? 0 : Math.floor(Math.log(proportionR.get(child)) / Math.log(domain.length) - 1) ;
        int ii = (int) iii;
        System.out.println("id : " + id + "anc: " + ancHeight);
        Map<Integer, Integer> sepH = new HashMap<>();
        sepH.put(id, height);
        for (int pp : branchPseudoParents.get(child)) {
            sepH.put(pp, ancHeight.get(pp));
        }
        List<Map.Entry<Integer, Integer>> list = new ArrayList<Map.Entry<Integer, Integer>>(sepH.entrySet());
        Collections.sort(list, new Comparator<Map.Entry<Integer, Integer>>() {
            @Override
            public int compare(Map.Entry<Integer, Integer> mapping1, Map.Entry<Integer, Integer> mapping2) {
                return mapping1.getValue() - mapping2.getValue();
            }
        });
//        for (Map.Entry<Integer, Integer> key : list) {
//            System.out.println(key.getKey() + " ：" + key.getValue());
//        }
        int T;
//        System.out.println(ii);
        if (list.get(ii + 1) == null) {
            T = 1;
        }
        else {
            T = list.get(ii + 1).getValue() - list.get(ii).getValue();
        }
        System.out.println("id: " + id + " child : " + child + " pop : " + proportionR.get(child) + " T : " + T);
        if (T > 1) {//FIFO
            int removeID = -1;
            for (int i = 0; i < optHistories.size(); i++) {
                if (optHistories.get(i).childId == child) {
                    removeID = i;
                    break;
                }
            }
            optHistories.remove(removeID);
        }
        else {//SendUB
            Collections.sort(optHistories, new Comparator<OptHistory>() {
                @Override
                public int compare(OptHistory optHistory, OptHistory t1) {
                    long sendUB1 = 0;
                    for (int i = 0; i < domain.length; i++) {
                        if (optHistory.rowOpt[i].sendUb == Integer.MAX_VALUE)
                            sendUB1 += 1e6;
                        else
                            sendUB1 += optHistory.rowOpt[i].sendUb;
                    }
                    long sendUB2 = 0;
                    for (int i = 0; i < domain.length; i++) {
                        if (optHistory.rowOpt[i].sendUb == Integer.MAX_VALUE)
                            sendUB2 += 1e6;
                        else
                            sendUB2 += optHistory.rowOpt[i].sendUb;
                    }
                    return (int) (sendUB1 - sendUB2);
                }
            });
            int removeID = -1;
            for (int i = 0; i < optHistories.size(); i++) {
                if (optHistories.get(i).childId == child) {
                    removeID = i;
                    break;
                }
            }
            optHistories.remove(removeID);
        }*/
        for (int i = 0; i < optHistories.size(); i++) {
            if (optHistories.get(i).childId == child) {
                int isRemove = 0;
                for (int v = 0; v < domain.length; v++) {
                    if (optHistories.get(i).rowOpt[v].sendUb <= 0)
                        isRemove++;
                }
                if (isRemove == domain.length) {
                    removeOutID = i;
                    break;
                }
            }
        }
        if (removeOutID != -1) {
            return removeOutID;
        }


        for (int i = 0; i < optHistories.size(); i++) {
            if (optHistories.get(i).childId == child) {
                int isRemove = 0;
                for (int v = 0; v < domain.length; v++) {
                    if (optHistories.get(i).rowOpt[v].sendUb <= 0)
                        isRemove++;
                }
                if (isRemove == domain.length - 1) {
                    removeOutID = i;
                    break;
                }
            }
        }


        if (removeOutID != -1) {
            return removeOutID;
        }

//        for (int i = 0; i < optHistories.size(); i++) {
//            if (optHistories.get(i).childId == child) {
//                int isRemove = 0;
//                for (int v = 0; v < domain.length; v++) {
//                    if (optHistories.get(i).rowOpt[v].sendUb <= 0)
//                        isRemove++;
//                }
//                if (isRemove == domain.length - 2) {
//                    removeOutID = i;
//                    break;
//                }
//            }
//        }
//
//
//        if (removeOutID != -1) {
//            return removeOutID;
//        }

        double iii = proportionR.get(child) == 0 ? 0 : Math.floor(Math.log(proportionR.get(child)) / Math.log(domain.length) - 1) ;
        int ii = (int) iii;
//        System.out.println("id : " + id + "anc: " + ancHeight);
        Map<Integer, Integer> sepH = new HashMap<>();
        sepH.put(id, level);
        for (int pp : branchPseudoParents.get(child)) {
            sepH.put(pp, ancHeight.get(pp));
        }
        List<Map.Entry<Integer, Integer>> list = new ArrayList<Map.Entry<Integer, Integer>>(sepH.entrySet());
        Collections.sort(list, new Comparator<Map.Entry<Integer, Integer>>() {
            @Override
            public int compare(Map.Entry<Integer, Integer> mapping1, Map.Entry<Integer, Integer> mapping2) {
                return mapping2.getValue() - mapping1.getValue();
            }
        });
//        System.out.println("----------");
//        for (Map.Entry<Integer, Integer> key : list) {
//            System.out.println("id : " + id + key.getKey() + " ：" + key.getValue());
//        }
        int dis = 0;
        for (int t = list.size() - 2; t >= 0; t--) {
            if (list.get(t).getValue() - list.get(t + 1).getValue() == 1) {
                dis = list.get(t).getValue();
                continue;
            }
            else
                break;
        }

        if (list.get(ii).getValue() >= dis) {
            int removeID = -1;
            for (int i = 0; i < optHistories.size(); i++) {
                if (optHistories.get(i).childId == child) {
                    removeID = i;
                    break;
                }
            }
            return removeID;
        }

        int T;
//        System.out.println(ii);
        if (list.get(ii + 1) == null) {
            T = 1;
        }
        else {
            T = list.get(ii).getValue() - list.get(ii + 1).getValue();
        }

//        System.out.println("id: " + id + " child : " + child + " pop : " + proportionR.get(child) + " T : " + T);
        if (T == 1) {//FIFO
            int change = -1;
            for (int v = ii; v < list.size() - 1; v++) {
                if (list.get(v).getValue() - list.get(v + 1).getValue() == 1) {
                    continue;
                }
                else {
                    change = list.get(v + 1).getKey();
                    break;
                }
            }

            int removeID = -1;
            for (int i = 0; i < optHistories.size(); i++) {
                if (optHistories.get(i).childId == child && (cpa.get(change)!=optHistories.get(i).ppsAssignment.get(change))) {
                    removeID = i;
                    break;
                }
            }
            return removeID;


        }
        else {//SendUB
            int removeID = -1;
            for (int i = 0; i < optHistories.size(); i++) {
                if (optHistories.get(i).childId == child) {
                    removeID = i;
                    break;
                }
            }
            return removeID;
        }

//


        /*int maxHeight = 0;
        for (int i : ancHeight.keySet()) {
            if (ancHeight.get(i) > maxHeight)
                maxHeight = ancHeight.get(i);
        }
        int comHeight = (maxHeight + height) / 2;
        int first = 0, second = 0;
        for (int agent : branchPseudoParents.get(child)) {
            if (ancHeight.get(agent) >= comHeight) {
                first += (ancHeight.get(agent) - comHeight) * memSize;
            }
            else
                second += (comHeight - ancHeight.get(agent)) * memSize;
        }
        if (first >= second-100000) {
            int removeID = -1;
            for (int i = 0; i < optHistories.size(); i++) {
                if (optHistories.get(i).childId == child) {
                    removeID = i;
                    break;
                }
            }
            optHistories.remove(removeID);
        }
        else {
            int removeID = -1;
            for (int i = optHistories.size() - 1; i >= 0; i--) {
                if (optHistories.get(i).childId == child) {
                    removeID = i;
                    break;
                }
            }
            optHistories.remove(removeID);
        }*/
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
        int hitCount;
        int childId;

        public OptHistory(OptElement[] rowOpt, Map<Integer, Integer> ppsAssignment, int childId) {
            this.rowOpt = rowOpt;
            this.ppsAssignment = ppsAssignment;
            this.childId = childId;
            this.hitCount = 0;
        }

        public OptHistory(OptElement[] rowOpt, Map<Integer, Integer> ppsAssignment, int childId, int hitCount) {
            this.rowOpt = rowOpt;
            this.ppsAssignment = ppsAssignment;
            this.childId = childId;
            this.hitCount = hitCount;
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
