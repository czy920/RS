package edu.cqu.algorithms.PTISBB;



import edu.cqu.algorithms.dcop.incomplete.ADPOP.NDData;
import edu.cqu.core.Message;
import edu.cqu.core.SyncMailer;
import edu.cqu.ordering.DFSSyncAgent;
import edu.cqu.result.ResultWithPrivacy;
import edu.cqu.result.annotations.NotRecordCostInCycle;

import java.util.*;
import java.util.concurrent.ConcurrentSkipListSet;

@NotRecordCostInCycle
public class PTISBBRS extends DFSSyncAgent {

    private static final int MSG_BRANCH_PSEUDO_PARENTS = 10086;

    private static final int MSG_LEVEL = 0;
    private static final int MSG_UTIL = 1;
    private static final int MSG_CPA = 2;
    //   private static final int MSG_REQUEST_COST = 3;
//    private static final int MSG_COST_RESPONSE = 4;
    private static final int MSG_BACKTRACK = 5;
    private static final int MSG_TERMINATE = 6;
    private static final int INFINTY = 1000000;
    private static final int NULL = -1;

    private static final int K = 7;
    private static final int M = 110000;

    private TreeMap<Integer,Integer> levelView;
    private Map<Integer, NDData> localUtil;
    private NDData sendUtil;
    private Map<Integer, NDData> childrenNDData;
    private int[] subtreeLB;
    private Map<Integer,int[]> lb;
    private Map<Integer,Integer> srchVal;
    private CPA curCpa;
    private int ub;
    private int preub;
    private int[] highCost;
    //    private int[] highCostReceived;
//    private boolean[] highCostRequested;
//    private boolean[] feasible;
    private int[] backtrackCount;
    //    private Map<Integer, boolean[][]> privacyMat;
    private long messageSizeCount;
    //table to record high cost
    private Map<Integer, CostList> costTable;
    int cpa_count;

    //   private Set<Integer> pseudoChildren;
    //   private int SumOfMinPCUtil[];
    //   private boolean OneTime;

    private ArrayList<OptHistory> optHistories;
    private Map<Integer,Integer> proportion;
    private Map<Integer, Integer> cpa;
    private Map<Integer, OptElement[]> opt;
    protected Map<Integer,Set<Integer>> branchPseudoParents;
    protected Set<Integer> pseudoChildren;
    protected Map<Integer, LinkedList<Integer>> exploreValue;


    public PTISBBRS(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        childrenNDData = new HashMap<>();
        subtreeLB = new int[domain.length];
        srchVal = new HashMap<>();
        cpa_count = 0;
        messageSizeCount=0;
    /*    privacyMat = new HashMap<>();
        for (int nId : neighbours) {
            boolean[][] tmp = new boolean[domain.length][neighbourDomains.get(nId).length];
            privacyMat.put(nId, tmp);
        }*/
        costTable = new HashMap<>();
        highCost = new int[domain.length];
        optHistories = new ArrayList<>();
        proportion = new HashMap<>();
        cpa = new HashMap<>();
        opt = new HashMap<>();
        branchPseudoParents = new HashMap<>();
        pseudoChildren = new HashSet<>();
        exploreValue = new HashMap<>();
        lb = new HashMap<>();
        //     OneTime=false;
        //     SumOfMinPCUtil=new int[domain.length];
    }

    @Override
    protected void pseudoTreeCreated() {
        /*
        pseudoChildren = new HashSet<>();
        for (int neighbor : neighbours){
            if (neighbor != parent && !pseudoParents.contains(neighbor) && !children.contains(neighbor)){
                pseudoChildren.add(neighbor);
            }
        }*/
        for (int neighbourId : neighbours)
            if (!children.contains(neighbourId) && parent != neighbourId && !pseudoParents.contains(neighbourId))
                pseudoChildren.add(neighbourId);
        if (isLeafAgent()) {
            sendMessage(new Message(id,parent,MSG_BRANCH_PSEUDO_PARENTS,new HashSet<>(pseudoParents)));
        }
        for (int child : children) {
            OptElement[] optRow = new OptElement[domain.length];
            for (int i = 0; i < domain.length; ++i){
                optRow[i] = new OptElement();
            }
            opt.put(child,optRow);
        }
        for (int child : children) {
            lb.put(child, new int[domain.length]);
        }

        if (isRootAgent()){
            Map<Integer,Integer> map = new HashMap<>();
            map.put(level,id);
            for (int c : children){
                sendMessage(new Message(id,c,MSG_LEVEL,map));
            }
        }
        else {
            localUtil = new HashMap<>();
            localUtil.put(parent,new NDData(constraintCosts.get(parent),id,parent));
            ncccs++;
            for (int pp : pseudoParents){
                localUtil.put(pp,new NDData(constraintCosts.get(pp),id,pp));
                ncccs++;
            }
        }
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
//        System.out.println(super.id + "proportion ：" + proportion);
//        System.out.println("proportion ：" + proportion);
    }

    @Override
    public void disposeMessage(Message message) {
        super.disposeMessage(message);
        switch (message.getType()){
            case MSG_BRANCH_PSEUDO_PARENTS: {
                Set<Integer> receivedPesudoParents = (Set) message.getValue();
                if (receivedPesudoParents.contains(id)) {
                    receivedPesudoParents.remove(id);
                }
                branchPseudoParents.put(message.getIdSender(), receivedPesudoParents);
                if (branchPseudoParents.size() == children.size()) {
//                    System.out.println("id : " + id + " branchPseudoParents : " + branchPseudoParents);
                    if (!isRootAgent()) {
                        Set<Integer> pp = new HashSet<>(pseudoParents);
                        for (Set<Integer> subPP : branchPseudoParents.values()) {
                            pp.addAll(subPP);
                        }
                        sendMessage(new Message(id, parent, MSG_BRANCH_PSEUDO_PARENTS, pp));
                    }
                    acllocateK(M);
                }
                break;
            }


            case MSG_LEVEL:
                messageSizeCount += 1;
                levelView = new TreeMap<>((Map<Integer,Integer>) message.getValue());
                if (!isLeafAgent()) {
                    Map<Integer, Integer> map = new HashMap<>(levelView);
                    map.put(level, id);
                    for (int c : children){
                        sendMessage(new Message(id,c,MSG_LEVEL,map));
                    }
                }
                else {
                    sendUtilMessage();
                }
                break;
            case MSG_UTIL:
                NDData receivedUtil = (NDData) message.getValue();
                ncccs++;
                messageSizeCount += receivedUtil.data.length;
/*////////////////////////下面是我加滴///////////////////////////
                if(!OneTime) {
                    int[][] matrixc = constraintCosts.get(message.getIdSender());
                    int[][] matrix = new int[matrixc.length][matrixc[0].length];
                    Calculate_SumOfMinPCUtil();
                    for (int i = 0; i < matrix.length; i++) {
                        for (int j = 0; j < matrix[0].length; j++) {
                            matrix[i][j] += SumOfMinPCUtil[i];//取最小 值
                        }
                    }
                    OneTime=true;
                    receivedUtil.merge(new NDData(matrix,id,message.getIdSender()));
                }
                else
*////////////////////////上面是我加滴///////////////////////////
                //  receivedUtil.merge(new NDData(constraintCosts.get(message.getIdSender()),id,message.getIdSender()));
                childrenNDData.put(message.getIdSender(),receivedUtil);
                if (childrenNDData.size() == children.size()){
                    if (!isRootAgent()) {
                        sendUtilMessage();
                    }
                    else {
                        // start search phase
                        curCpa = new CPA(new HashMap<>(),Integer.MAX_VALUE);
                        initVariables();
                        for (int child : children){
                            CPA cpa = new CPA(new HashMap<>(),Integer.MAX_VALUE);
                            cpa.assign.put(id,0);
                            ub = Integer.MAX_VALUE;
                            srchVal.put(child,0);
                            sendMessage(new Message(id,child,MSG_CPA,cpa.copy()));
                        }
                    }
                }
                break;
            case MSG_CPA: {
                cpa_count ++;
                CPA cpaMsg = (CPA) message.getValue();
                curCpa = (CPA) message.getValue();
                messageSizeCount += curCpa.assign.size()*2+2;
//                System.out.println(id + " received cpa " + map2String(curCpa.assign));


                ub = cpaMsg.ub;
                preub = cpaMsg.ub;
                cpa = cpaMsg.assign;
                System.out.println("id:" + id + "  receive cpa from " + message.getIdSender() + " cpa: " + cpa + " ub : " + ub);
                if(isLeafAgent()) {
                    initHighCost();
                    sendMessage(new Message(id,parent,MSG_BACKTRACK, new BacktrackMsg(INFINTY, optimalRet())));
                }
                else {
                    initVariables();
                    if (isOptFull())
                        backtrack();
                    else {
                        for (int child : children) {
                            if (exploreValue.containsKey(child) && !exploreValue.get(child).isEmpty())
                                goNext(child);
                        }
                    }

/*
                    int feasibleVal = -1;
                    for (int i = 0; i < domain.length; i++) {
                        if (lowerBound(i) < ub) {
                            feasibleVal = i;
                            break;
                        } else {
                            feasible[i] = false;
                        }
                    }
                    if (feasibleVal != -1) {
                        //   sendCostRequest(feasibleVal);
                        int sendUb = ub - lowerBound(feasibleVal);
                        for (int child : children){
                            //  if (srchVal.get(child) == feasibleVal){
                            CPA cpa = curCpa.copy();
                            cpa.assign.put(id,feasibleVal);
                            cpa.ub = sendUb + childrenNDData.get(child).getValue(cpa.assign);
                            sendMessage(new Message(id,child,MSG_CPA,cpa));
                            srchVal.put(child, feasibleVal);
                            //   }
                        }
                        //  for (int child : children) {

                        //  }
                    } else {
                        //backtrack
                        backtrack();
//                        sendMessage(new Message(id, parent, MSG_BACKTRACK, Integer.MAX_VALUE));
                    }*/
                }
            }
            break;
/*            case MSG_REQUEST_COST:{
                int sender = message.getIdSender();
                CostRequest costRequest = (CostRequest) message.getValue();
                int cost = constraintCosts.get(sender)[costRequest.higherValue][costRequest.lowerValue];
                privacyMat.get(sender)[costRequest.higherValue][costRequest.lowerValue] = true;
                ncccs++;
                sendMessage(new Message(id,sender,MSG_COST_RESPONSE,new CostResponse(costRequest.lowerValue,cost)));
                break;
            }
            case MSG_COST_RESPONSE:{
                CostResponse costResponse = (CostResponse) message.getValue();
                int value = costResponse.value;
                int cost = costResponse.cost;
                highCostReceived[value]++;
                highCost[value] += cost;
                if (highCostReceived[value] == pseudoParents.size() + 1){
                    if (isLeafAgent()){
                        int feasibleVal = -1;
                        ub = Integer.min(ub,lowerBound(value));
                        for (int i = value + 1; i < domain.length; i++){
                            if (lowerBound(i) < ub){
                                feasibleVal = i;
                                break;
                            }
                        }
                        if (feasibleVal != -1){
                            sendCostRequest(feasibleVal);
                        }
                        else {
                            sendMessage(new Message(id,parent,MSG_BACKTRACK,optimalRet()));
                        }
                    }
                    else {
                        if (lowerBound(value) < ub) {
                            int sendUb = ub - lowerBound(value);
                            for (int child : children){
                                if (srchVal.get(child) == value){
                                    CPA cpa = curCpa.copy();
                                    cpa.assign.put(id,value);
                                    cpa.ub = sendUb + childrenNDData.get(child).getValue(cpa.assign);
                                    sendMessage(new Message(id,child,MSG_CPA,cpa));
                                }
                            }
                        } else {
                            int feasibleVal = -1;
                            for (int i = value; i < domain.length; i++){
                                if (lowerBound(i) < ub){
                                    feasibleVal = i;
                                    break;
                                }
                                else {
                                    feasible[i] = false;
                                }
                            }
                            if (feasibleVal != -1){
                                if (!highCostRequested[feasibleVal])
                                    sendCostRequest(feasibleVal);
                                for (int child : children){
                                    if (srchVal.get(child) == value){
                                        srchVal.put(child,feasibleVal);
                                    }
                                }
                            }
                            else {
                                for (int child : children){
                                    if (srchVal.get(child) == value){
                                        srchVal.put(child,domain.length);
                                    }
                                }
                                if (canBacktrack())
                                    sendMessage(new Message(id,parent,MSG_BACKTRACK,optimalRet()));
                            }
                        }
                    }
                }
                break;
            }*/
            case MSG_BACKTRACK:
                messageSizeCount += 1;
                int sender = message.getIdSender();
                int val = srchVal.get(sender);
                BacktrackMsg backtrackMsg = (BacktrackMsg)message.getValue();
                opt.get(sender)[val].costStar = backtrackMsg.costStar;
                opt.get(sender)[val].sendUb = backtrackMsg.receiveUb;
                subtreeLB[val] += backtrackMsg.costStar - lb.get(sender)[val];
                System.out.println("id:" + id + " receive backtrack from " + sender + " srchVal:" + val + " cost : " + backtrackMsg.costStar);

                if (isOptFull(val)) {
                    System.out.println("id : " + id + " ub : " + ub);
                    ub = Integer.min(ub,subtreeLB[val]);
                }
                exploreValue.get(sender).remove(exploreValue.get(sender).indexOf(val));
                goNext(sender);
               /* while (++val < domain.length){
                    if (!feasible[val]){
                        continue;
                    }
                    if (lowerBound(val) < ub){
                        srchVal.put(sender,val);
                        int base = isRootAgent() ? 0 : 1;
                        // if (!highCostRequested[val]){
                        //     sendCostRequest(val);
                        //  }
                        // else if (highCostReceived[val] == pseudoParents.size() + base){
                        CPA cpa = curCpa.copy();
                        cpa.assign.put(id,val);
                        cpa.ub = ub - lowerBound(val) + subtreeLB.get(sender)[val];
                        srchVal.put(sender,val);
                        sendMessage(new Message(id,sender,MSG_CPA,cpa));
                        //  }
                        break;
                    }
                    else {
                        feasible[val] = false;
                    }
                }
                if (val == domain.length){
                    srchVal.put(sender,val);
                    if (canBacktrack()) {
                        if (isRootAgent()) {
                            for (int child : children) {
                                sendMessage(new Message(id, child, MSG_TERMINATE, null));
                            }
                            stopProcess();
                        } else {
                            backtrack();
//                            sendMessage(new Message(id, parent, MSG_BACKTRACK, optimalRet()));
                        }
                    }
                }*/
                break;
            case MSG_TERMINATE:
                messageSizeCount += 1;
                for (int child : children){
                    sendMessage(new Message(id,child,MSG_TERMINATE,null));
                }
                stopProcess();
        }
    }

    private boolean isOptFull(int i) {
        /*for (int child : exploreValue.keySet()){
            if (exploreValue.get(child).contains(i))
                return false;
        }
        return true;*/
        for (int child : children) {
            if (opt.get(child)[i].costStar == NULL)
                return false;
        }
        return true;
    }

    private void goNext(int childId) {
        int value = firstFeasibleAssignment(childId);
        if (isOptFull()){
            if (isRootAgent()){
                System.out.println("ub : " + ub);
                for (int child : children)
                    sendMessage(new Message(id,child,MSG_TERMINATE,null));
                stopProcess();
            }
            else{
                backtrack();
            }
        }
        else if (value != -1){
            int sendUb = (ub - subtreeLB[value] + lb.get(childId)[value]);
//            System.out.println("id : " + id + "sendUb : " + sendUb);
            if (sendUb > opt.get(childId)[value].sendUb){
                srchVal.put(childId, value);
                Map<Integer,Integer> newCpa = new HashMap<>(cpa);
                newCpa.put(id, value);
                sendMessage(new Message(id, childId, MSG_CPA, new CPA(newCpa, sendUb)));
            }
            else {
//                System.out.println("=======");
                exploreValue.get(childId).removeFirst();
                goNext(childId);
            }
        }
    }

    private int firstFeasibleAssignment(int childId) {
        int value = NULL;
        while(!exploreValue.get(childId).isEmpty()){
            value = exploreValue.get(childId).getFirst();
            if (ub > subtreeLB[value]) {
                return value;
            }
            opt.get(childId)[value].costStar = INFINTY;
            opt.get(childId)[value].sendUb = ub - subtreeLB[value];
            subtreeLB[value] = INFINTY;
            exploreValue.get(childId).remove(exploreValue.get(childId).indexOf(value));
        }
        if (exploreValue.get(childId).isEmpty())
            return NULL;
        return value;
    }

    private boolean isOptFull() {
        for (int child : exploreValue.keySet()){
            if (!exploreValue.get(child).isEmpty())
                return false;
        }
        return true;
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
            showOptHistory();
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

    private Map<Integer,Integer> projection(int childId){
        Map<Integer,Integer> result = new HashMap<>();
        for (int id : branchPseudoParents.get(childId)){
            result.put(id,cpa.get(id));
        }
        return result;
    }

    private void backtrack() {
        fillOptHistory();
        int costStar = optimalRet();
        int receiveUb = INFINTY;
        if ( costStar >= preub && optContainsInfinity())
            receiveUb = preub;
        sendMessage(new Message(id,parent,MSG_BACKTRACK,new BacktrackMsg(receiveUb, costStar)));
    }

    protected boolean optContainsInfinity(){
        for (int i = 0; i < domain.length; i++){
            for (int child : children){
                if (opt.get(child)[i].costStar == INFINTY){
                    return true;
                }
            }
        }
        return false;
    }

    private boolean canBacktrack(){
        boolean canBacktrack = true;
        if (srchVal.size() < children.size()){
            canBacktrack = false;
        }
        else {
            for (int child : children){
                int val = srchVal.get(child);
                if (val != domain.length){
                    canBacktrack = false;
                    break;
                }
            }
        }
        return canBacktrack;
    }
    /*
    private void Calculate_SumOfMinPCUtil() {

        for (int pcId : pseudoChildren) {

            int[][] matrix= constraintCosts.get(pcId);
            for (int i = 0; i < matrix.length; i++) {
                int minUtil = Integer.MAX_VALUE;
                for (int j = 0; j < matrix[0].length; j++) {
                if(matrix[i][j]<minUtil) minUtil=matrix[i][j];//取最小 值
                }
                SumOfMinPCUtil[i]+=minUtil;
            }
        }
        System.out.println("id"+id+"  pseudochildren.size()="+pseudoChildren.size()+"  SumOfMinPCUtil="+SumOfMinPCUtil);
    }
    private void sendCostRequest(int feasibleVal) {
        for (int pp : pseudoParents){
            sendMessage(new Message(id,pp,MSG_REQUEST_COST,new CostRequest(feasibleVal,curCpa.assign.get(pp))));
        }
        sendMessage(new Message(id,parent,MSG_REQUEST_COST,new CostRequest(feasibleVal,curCpa.assign.get(parent))));
        highCostRequested[feasibleVal] = true;
    }*/

    private int optimalRet(){
        int optRet = Integer.MAX_VALUE;
        for (int i = 0; i < domain.length; ++i) {
            optRet = Integer.min(optRet, optRep(i));
        }
        return optRet;
    }

    private int optRep(int valueIndex) {
//        System.out.println("========" + highCost[valueIndex]);
        int tmp = highCost[valueIndex];
        for (int child : children) {
            if (opt.get(child)[valueIndex].costStar == INFINTY) {
                return INFINTY;
            }
            else {
                tmp += opt.get(child)[valueIndex].costStar;
            }
        }
        return tmp;
    }

//    private int lowerBound(int i){
//        long cost = highCost[i];
//        for (int child : children){
//            cost += subtreeLB.get(child)[i];
//        }
//        return cost > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) cost;
//    }

    private void initHighCost() {
        Set<Integer> tmpP = new HashSet<>(pseudoParents);
        if (!isRootAgent()) {
            tmpP.add(parent);
        }
        for (int i = 0; i < domain.length; i++) {
            int cost = 0;
            for (int pp : tmpP){
                if (!costTable.containsKey(pp)) {
                    costTable.put(pp, new CostList());
                }
                if (costTable.get(pp).value != curCpa.assign.get(pp)) {
                    costTable.get(pp).cost[i] = constraintCosts.get(pp)[i][curCpa.assign.get(pp)];
                    ncccs++;
                }
                cost += costTable.get(pp).cost[i];
            }
            highCost[i] = cost;
        }

        for (int pp : tmpP) {
            costTable.get(pp).value = curCpa.assign.get(pp);
        }
    }

    private void initHighCost1() {
        for (int i = 0; i < domain.length; i++){
            int cost = 0;
            for (int pp : pseudoParents){
                cost += constraintCosts.get(pp)[i][curCpa.assign.get(pp)];
                ncccs++;
            }
            if (!isRootAgent()){
                cost += constraintCosts.get(parent)[i][curCpa.assign.get(parent)];
                ncccs++;
            }
            highCost[i] = cost;
        }
    }

    private void initVariables(){
//        feasible = new boolean[domain.length];
//        Arrays.fill(feasible,true);
//        backtrackCount = new int[domain.length];
//        highCost = new int[domain.length];
        initHighCost();
        //   highCostReceived = new int[domain.length];
        //    highCostRequested = new boolean[domain.length];
        //   if (isRootAgent()){
        //       Arrays.fill(highCostRequested,true);
        //   }
        Map<Integer, Integer> assign = new HashMap<>(curCpa.assign);
        for (int child : children){
//            int[] lb = new int[domain.length];
            for (int i = 0; i < domain.length; i++){
                assign.put(id,i);
                lb.get(child)[i] = childrenNDData.get(child).getValue(assign);
            }
        }


        for (int i = 0; i < domain.length; ++i) {
            subtreeLB[i] = highCost[i];
            for (int child : children) {
                subtreeLB[i] += lb.get(child)[i];
            }
        }
//        for (int child : children){
//            int[] tlb = new int[domain.length];
//            for (int i = 0; i < tlb.length; i++){
//                assign.put(id,i);
//                tlb[i] = childrenNDData.get(child).getValue(assign);
//            }
//            subtreeLB.put(child,tlb);
//        }
        readHistory();
    }

    private void readHistory() {
        Set<Integer> hitChild = new HashSet<>();
        for (int child : children) {
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
        }
        Set<Integer> noHitChild = new ConcurrentSkipListSet<>(children);
        for (int child : noHitChild) {
            if (hitChild.contains(child))
                noHitChild.remove(child);
        }
        for (int child : noHitChild){
            LinkedList<Integer> tmp = new LinkedList<>();
            for (int i = 0; i < domain.length; ++i) {
                tmp.add(i);
                opt.get(child)[i].sendUb = -1;
                opt.get(child)[i].costStar = NULL;
            }
            exploreValue.put(child, tmp);
        }
        for (int child : children) {
            if (hitChild.contains(child)) {
                LinkedList<Integer> tmp = new LinkedList<>();
                for (int i = 0; i < domain.length; i++) {
                    if (opt.get(child)[i].sendUb != INFINTY) {
                        tmp.add(i);
                    }
                }
                if (!tmp.isEmpty())
                    exploreValue.put(child, tmp);
            }
        }

    }

    private void sendUtilMessage(){
        Set<Integer> removedDim = new HashSet<>();
        Set<Integer> allDim = new HashSet<>(pseudoParents);
        allDim.add(parent);
        Set<Integer> childrenDim = new HashSet<>();
        for (NDData nDData : childrenNDData.values()){
            childrenDim.addAll(nDData.orderedId);
        }
        allDim.addAll(childrenDim);
        allDim.remove(id);
        int dimCount = allDim.size() - K;
        for (int le : levelView.navigableKeySet()){
            int sep = levelView.get(le);
            if (allDim.contains(sep)){
                if (dimCount-- <= 0){
                    break;
                }
                removedDim.add(sep);
            }
        }
        Set<Integer> localDim = new HashSet<>();
        Set<Integer> joinDim = new HashSet<>();
        Set<Integer> bothDim = new HashSet<>();
        for (int id : removedDim){
            if (localUtil.containsKey(id)){
                if (childrenDim.contains(id)){
                    bothDim.add(id);
                }
                else {
                    localDim.add(id);
                }
            }
            else {
                joinDim.add(id);
            }
        }
        Set<NDData> mergedData = new HashSet<>();
        for (int dim : joinDim){
            for (NDData data : childrenNDData.values()){
                if (!mergedData.contains(data)) {
                    if (data.containsDim(dim)) {
                        if (sendUtil == null) {
                            sendUtil = data.copy();
                        } else {
                            sendUtil.merge(data);
                        }
                        mergedData.add(data);
                    }
                }
            }
            sendUtil = sendUtil.min(dim);
            ncccs += sendUtil.operationCount;
        }
        for (int dim : localDim){
            NDData min = localUtil.get(dim).min(dim);
            ncccs += min.operationCount;
            if (sendUtil == null){
                sendUtil = min;
            }
            else {
                sendUtil.merge(min);
            }
        }
        for (int dim : bothDim){
            if (sendUtil == null){
                sendUtil = localUtil.get(dim).copy();
            }
            else {
                sendUtil.merge(localUtil.get(dim));
            }
            for (NDData data : childrenNDData.values()){
                if (!mergedData.contains(data) && data.containsDim(dim)){
                    sendUtil.merge(data);
                    mergedData.add(data);
                }
            }
            sendUtil = sendUtil.min(dim);
            ncccs += sendUtil.operationCount;
        }
        for (NDData data : childrenNDData.values()){
            if (!mergedData.contains(data)){
                if (sendUtil == null){
                    sendUtil = data.copy();
                }
                else {
                    sendUtil.merge(data);
                }
                mergedData.add(data);
            }
        }
        if (mergedData.size() != childrenNDData.size()){
            throw new IllegalStateException();
        }
        for (int dim : localUtil.keySet()){
            if (!removedDim.contains(dim)){
                if (sendUtil == null){
                    sendUtil = localUtil.get(dim).copy();
                }
                else {
                    sendUtil.merge(localUtil.get(dim));
                }
            }
        }

        NDData cntPrivacy = sendUtil.copy();
        for (int ind : sendUtil.orderedId) {
            if (ind != id && ind != parent)
                cntPrivacy = cntPrivacy.min(ind);
        }

        sendUtil = sendUtil.min(id);
        ncccs += sendUtil.operationCount;
        sendMessage(new Message(id,parent,MSG_UTIL, sendUtil.copy()));
    }

    private class CPA{
        Map<Integer,Integer> assign;
        int ub;

        public CPA(Map<Integer, Integer> assign, int ub) {
            this.assign = assign;
            this.ub = ub;
        }

        public CPA copy(){
            return new CPA(new HashMap<>(assign),ub);
        }
    }

    private class CostResponse{
        int value;
        int cost;

        public CostResponse(int value, int cost) {
            this.value = value;
            this.cost = cost;
        }
    }

    private class CostRequest{
        int lowerValue;
        int higherValue;

        public CostRequest(int lowerValue, int higherValue) {
            this.lowerValue = lowerValue;
            this.higherValue = higherValue;
        }
    }

    @Override
    public void runFinished() {
        super.runFinished();

        ResultWithPrivacy res = new ResultWithPrivacy();
        res.setNcccs(ncccs);
        res.setMessageSizeCount(messageSizeCount);
        res.setAgentValues(id, valueIndex);
        if (isRootAgent())
            res.setUb(ub);
        res.setMsgSearchPart(cpa_count);
        mailer.setResultCycle(id,res);
    }

    private class CostList{
        int value;
        int[] cost;

        public CostList() {
            this.value = -1;
            this.cost = new int[domain.length];
        }

    }

    private class BacktrackMsg{
        public int receiveUb;
        public int costStar;

        public BacktrackMsg(int receiveUb, int costStar) {
            this.receiveUb = receiveUb;
            this.costStar = costStar;
        }
    }

    protected class OptElement{
        public int costStar;
        public int sendUb;
        public OptElement(int costStar, int sendUb) {
            this.costStar = costStar;
            this.sendUb = sendUb;
        }
        public OptElement() {
            this.costStar = INFINTY;
            this.sendUb = -1;
        }

        @Override
        public String toString() {
            return "cost:" + costStar + " ub:" + sendUb;
        }
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
