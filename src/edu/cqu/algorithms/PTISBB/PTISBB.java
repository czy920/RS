package edu.cqu.algorithms.PTISBB;



import edu.cqu.algorithms.dcop.incomplete.ADPOP.NDData;
import edu.cqu.core.Message;
import edu.cqu.core.SyncMailer;
import edu.cqu.ordering.DFSSyncAgent;
import edu.cqu.result.ResultWithPrivacy;
import edu.cqu.result.annotations.NotRecordCostInCycle;

import java.util.*;

@NotRecordCostInCycle
public class PTISBB extends DFSSyncAgent {

    private static final int MSG_LEVEL = 0;
    private static final int MSG_UTIL = 1;
    private static final int MSG_CPA = 2;
 //   private static final int MSG_REQUEST_COST = 3;
//    private static final int MSG_COST_RESPONSE = 4;
    private static final int MSG_BACKTRACK = 5;
    private static final int MSG_TERMINATE = 6;

    private static final int K = 7;

    private TreeMap<Integer,Integer> levelView;
    private Map<Integer, NDData> localUtil;
    private NDData sendUtil;
    private Map<Integer, NDData> childrenNDData;
    private Map<Integer,int[]> subtreeLB;
    private Map<Integer,Integer> srchVal;
    private CPA curCpa;
    private int ub;
    private int[] highCost;
//    private int[] highCostReceived;
//    private boolean[] highCostRequested;
    private boolean[] feasible;
    private int[] backtrackCount;
//    private Map<Integer, boolean[][]> privacyMat;
private long messageSizeCount;
    //table to record high cost
    private Map<Integer, CostList> costTable;
    int cpa_count;

 //   private Set<Integer> pseudoChildren;
 //   private int SumOfMinPCUtil[];
 //   private boolean OneTime;
    public PTISBB(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        childrenNDData = new HashMap<>();
        subtreeLB = new HashMap<>();
        srchVal = new HashMap<>();
        cpa_count = 0;
        messageSizeCount=0;
    /*    privacyMat = new HashMap<>();
        for (int nId : neighbours) {
            boolean[][] tmp = new boolean[domain.length][neighbourDomains.get(nId).length];
            privacyMat.put(nId, tmp);
        }*/
        costTable = new HashMap<>();

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

    @Override
    public void disposeMessage(Message message) {
        super.disposeMessage(message);
        switch (message.getType()){
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
/*////////////////////////??????????????????///////////////////////////
                if(!OneTime) {
                    int[][] matrixc = constraintCosts.get(message.getIdSender());
                    int[][] matrix = new int[matrixc.length][matrixc[0].length];
                    Calculate_SumOfMinPCUtil();
                    for (int i = 0; i < matrix.length; i++) {
                        for (int j = 0; j < matrix[0].length; j++) {
                            matrix[i][j] += SumOfMinPCUtil[i];//????????? ???
                        }
                    }
                    OneTime=true;
                    receivedUtil.merge(new NDData(matrix,id,message.getIdSender()));
                }
                else
*////////////////////////??????????????????///////////////////////////
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
                            srchVal.put(child,0);
                            sendMessage(new Message(id,child,MSG_CPA,cpa.copy()));
                        }
                    }
                }
                break;
            case MSG_CPA: {
                cpa_count ++;
                curCpa = (CPA) message.getValue();
                messageSizeCount += curCpa.assign.size()*2+2;
//                System.out.println(id + " received cpa " + map2String(curCpa.assign));
                initVariables();
                if(isLeafAgent()) sendMessage(new Message(id,parent,MSG_BACKTRACK,optimalRet()));
                else {
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

                        sendMessage(new Message(id, parent, MSG_BACKTRACK, Integer.MAX_VALUE));
                    }
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
                int opt = (int) message.getValue();
                int val = srchVal.get(sender);
                backtrackCount[val]++;
                subtreeLB.get(sender)[val] = opt;
                if (backtrackCount[val] == children.size()){
                    ub = Integer.min(ub,lowerBound(val));
                }
                while (++val < domain.length){
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
                            sendMessage(new Message(id, parent, MSG_BACKTRACK, optimalRet()));
                        }
                    }
                }
                break;
            case MSG_TERMINATE:
                messageSizeCount += 1;
                for (int child : children){
                    sendMessage(new Message(id,child,MSG_TERMINATE,null));
                }
                stopProcess();
        }
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
                if(matrix[i][j]<minUtil) minUtil=matrix[i][j];//????????? ???
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
        long bestCost = Integer.MAX_VALUE;
        for (int i = 0; i < domain.length; i++){
            long cost = highCost[i];
            if (backtrackCount[i] != children.size()){
                continue;
            }
            for (int child : children){
                cost += subtreeLB.get(child)[i];
            }
            bestCost = Long.min(bestCost,cost);
          //  if(isLeafAgent())
                ncccs++;
        }
        return bestCost > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) bestCost;
    }

    private int lowerBound(int i){
        long cost = highCost[i];
        for (int child : children){
            cost += subtreeLB.get(child)[i];
        }
        return cost > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) cost;
    }

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
        ub = curCpa.ub;
        srchVal.clear();
        feasible = new boolean[domain.length];
        Arrays.fill(feasible,true);
        backtrackCount = new int[domain.length];
        highCost = new int[domain.length];
        initHighCost();
     //   highCostReceived = new int[domain.length];
    //    highCostRequested = new boolean[domain.length];
     //   if (isRootAgent()){
     //       Arrays.fill(highCostRequested,true);
     //   }
        Map<Integer,Integer> assign = new HashMap<>(curCpa.assign);
        for (int child : children){
            int[] lb = new int[domain.length];
            for (int i = 0; i < lb.length; i++){
                assign.put(id,i);
                lb[i] = childrenNDData.get(child).getValue(assign);
            }
            subtreeLB.put(child,lb);
        }
    }

    private void sendUtilMessage(){
        //??????0??????ID??????
        Set<Integer> removedDim = new HashSet<>();
        Set<Integer> allDim = new HashSet<>(pseudoParents);
        allDim.add(parent);
        Set<Integer> childrenDim = new HashSet<>();//??????????????????????????????????????????????????????????????????????????????????????????????????????
        for (NDData nDData : childrenNDData.values()){
            childrenDim.addAll(nDData.orderedId);
        }
        allDim.addAll(childrenDim);//?????????????????????????????????????????????????????????????????????????????????????????????
        allDim.remove(id);
        int dimCount = allDim.size() - K;//??????K????????????????????????????????????
        for (int le : levelView.navigableKeySet()){
            int sep = levelView.get(le);
            if (allDim.contains(sep)){
                if (dimCount-- <= 0){
                    break;
                }
                removedDim.add(sep);
            }
        }
        //?????????  ??????ID??????
        Set<Integer> localDim = new HashSet<>();
        Set<Integer> joinDim = new HashSet<>();//from children
        Set<Integer> bothDim = new HashSet<>();
        for (int id : removedDim){
            if (localUtil.containsKey(id)){
                if (childrenDim.contains(id)){
                    bothDim.add(id);//??????????????????id???localUtil???children?????????????????????
                }
                else {
                    localDim.add(id);//??????????????????id??????localUtil??????????????????
                }
            }
            else {
                joinDim.add(id);//???????????????id ????????????localUtil????????????children????????????
            }
        }
        //????????? ??????????????????ID??????children????????????????????????????????????????????????ID???????????????????????????
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
        //?????????  ??????????????????ID??????localUtil??????????????????????????????????????????????????????ID???????????????????????????
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
        //????????? ??????????????????ID??????localUtil?????????????????????hildren?????????????????????????????????????????????????????????ID???????????????????????????
       // bothDim.add(id);
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
        //????????? ??????children????????????????????????ID?????????????????????
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
       // ????????? ???????????? ??????????????????????????????????????????????????????????????????
        if (mergedData.size() != childrenNDData.size()){
            throw new IllegalStateException();
        }
        //????????? ??????localUtil????????????????????????ID?????????????????????
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

        //????????? ????????????????????????
        NDData cntPrivacy = sendUtil.copy();
        for (int ind : sendUtil.orderedId) {
            if (ind != id && ind != parent)
                cntPrivacy = cntPrivacy.min(ind);
        }
        //?????????  ????????????????????????
        /*
        Map<Integer,Integer> assign = new HashMap<>();
        for (int i = 0; i < domain.length; ++i) {
            assign.put(id, i);
            for (int j = 0; j < neighbourDomains.get(parent).length; ++j) {
                assign.put(parent, j);
                if (cntPrivacy.getValue(assign)==0) {
                    privacyMat.get(parent)[i][j] = true;
                }
            }
        }*/
        sendUtil = sendUtil.min(id);
        ncccs += sendUtil.operationCount;
        //????????????
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
      //  int total = 0;
     //   int leaked = 0;
        /*
        for (int neighbor : neighbours){
            for (int i = 0; i < domain.length; i++){
                for (int j = 0; j < neighbourDomains.get(neighbor).length; j++){
                    total++;
                    if (privacyMat.get(neighbor)[i][j]){
                        leaked++;
                    }
                }
            }
        }*/
        res.setMsgSearchPart(cpa_count);

     //   res.setTotalEntropy(total);
     //   res.setLeakedEntropy(leaked);
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
}
