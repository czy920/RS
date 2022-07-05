package edu.cqu.algorithms.ptfb;

import edu.cqu.core.Message;
import edu.cqu.core.SyncMailer;
import edu.cqu.result.ResultWithPrivacy;
import edu.cqu.test.xiagao.retentionFinal.ptfb.RetentionPlusFrame;

import java.util.*;

public class PTFB_RS extends RetentionPlusFrame {

    private static final int MSG_PCB = 0;
    private static final int MSG_ECA = 1;
    private static final int MSG_LATEST_DIVIDER = 2;
    private static final int MSG_LATEST_DIVIDER_ACK = 3;
    private static final int MSG_CPA = 4;
    private static final int MSG_REQUEST = 5;
    private static final int MSG_REPORT = 6;
    private static final int MSG_UB = 7;
    private static final int MSG_BACKTRACK = 8;
    private static final int MSG_REDUCE_UB = 9;
    private static final int MSG_TERMINATE = 10;

    private static final int NULL = -1;
    private static final int K = 243;
    private static final int INF = 100000;
    private final int EMPTY = (int)(domain.length);
    private long cpaMsgCount;

    //TODO: to be sorted: from big to small
    private List<NeighborLevel> pseudoParentLevels;
    private Set<Integer> latestDividers;
    private Map<Integer,Set<Integer>> pcb;
    private Map<Integer,Set<Integer>> pcbCache;
    private boolean started;
    private Set<Integer> pseudoChildren;
    private int latestDividerAckCount;

    private int receiveCost;
    private int ub;
    private int sendUb;
    private int receiveUb;
    private Map<Integer,Integer> parentLbReports;
    private Map<Integer,Integer> subtreeLb;
    private int[] domainLb;
    private Map<Integer,Set<Integer>> desc;
    private CPA cpaPTFB;
    private Map<Integer,int[]> localCosts;
    private Map<Integer,Integer> srchVal;
    private Map<Integer,Integer> lbAdjust;
    private int lastSentUb;
    private Map<Integer,int[]> subtreeLB;
    private Map<Integer,int[]> subtreeUB;
    private Map<Integer,Integer> lbReport;
    private long messageSizeCount;
    private boolean frameDone;
    private boolean ackDone;
    private Map<Integer,Integer> childAssignment;

    public PTFB_RS(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        pcbCache = new HashMap<>();
        localCosts = new HashMap<>();
        srchVal = new HashMap<>();
        lbReport = new HashMap<>();
        lbAdjust = new HashMap<>();
        subtreeUB = new HashMap<>();
        pcbCache = new HashMap<>();
        subtreeLB = new HashMap<>();
        childAssignment = new HashMap<>();

    }

    @Override
    protected void pseudoTreeCreated() {
        super.pseudoTreeCreated();
        pseudoParentLevels = new LinkedList<>();
        latestDividers = new HashSet<>();
        pcb = new HashMap<>();
        pseudoChildren = new HashSet<>();
        for (int neighbor : neighbours){
            if (neighbor != parent && !pseudoParents.contains(neighbor) && !children.contains(neighbor)){
                pseudoChildren.add(neighbor);
            }
        }
        if (isLeafAgent()){
            Set<Integer> pcbSet = new HashSet<>();
            pcbSet.add(id);
            sendMessage(new Message(id,parent,MSG_PCB,pcbSet));
        }
        started = true;
        if (!isLeafAgent() && pcbCache != null && pcbCache.size() == children.size()){
            calculatePCB();
        }
        if (isRootAgent()){
            localCosts.put(-1,new int[domain.length]);
            cpaPTFB = new CPA(new HashMap<>(),(int) 1e8,0,new HashMap<>());
        }
    }

    @Override
    protected void start() {
        frameDone = true;
        acllocateK(K);
        startPTFB();
    }

    private void startPTFB() {
        if (ackDone && frameDone)
            disposeCpaMessage();
    }

    private void calculatePCB(){
        Set<Integer> pcbSet = new HashSet<>();
        for (int c : pcbCache.keySet()){
            pcbSet.addAll(pcbCache.get(c));
            Set<Integer> set = pcb.get(c);
            if (set == null){
                set = new HashSet<>();
                pcb.put(c,set);

            }
            for (int desc : pcbCache.get(c)){
                if (pseudoChildren.contains(desc)){
                    pcb.get(c).add(desc);
                }
            }
            pcb.get(c).add(c);
        }
        pcbSet.add(id);
        if (!isRootAgent())
            sendMessage(new Message(id,parent,MSG_PCB,pcbSet));
        else {
            sendECA(new HashMap<>());
            sendLatestDivider();
        }
        desc = pcbCache;
        pcbCache = null;
    }

    private void sendECA(Map<Integer,Integer> levels){
        levels.put(id,level);
        for (int pc : children){
            sendMessage(new Message(id,pc,MSG_ECA,levels));
        }
    }

    private void sendLatestDivider(){
        if (isLeafAgent()){
            sendMessage(new Message(id,parent,MSG_LATEST_DIVIDER_ACK,null));
            return;
        }
        Set<Integer> sendinglatestDividers = new HashSet<>(latestDividers);
        if (children.size() > 1){
            sendinglatestDividers.clear();
        }
        sendinglatestDividers.add(id);
        for (int c : children){
            sendMessage(new Message(id,c, MSG_LATEST_DIVIDER,sendinglatestDividers));
        }
    }



    @Override
    public void disposeMessage(Message message) {
        super.disposeMessage(message);
        switch (message.getType()){
            case MSG_PCB: {
                Set<Integer> msg = (Set<Integer>) message.getValue();
                messageSizeCount += msg.size();
                pcbCache.put(message.getIdSender(), msg);
                if (started && pcbCache.size() == children.size()) {
                    calculatePCB();
                }
                break;
            }
            case MSG_ECA: {
                Map<Integer, Integer> levels = (Map<Integer, Integer>) message.getValue();
                messageSizeCount += levels.size() * 2;
                for (int highId : pseudoParents) {
                    pseudoParentLevels.add(new NeighborLevel(highId, levels.get(highId)));
                }
                Collections.sort(pseudoParentLevels, new Comparator<NeighborLevel>() {
                    @Override
                    public int compare(NeighborLevel o1, NeighborLevel o2) {
                        return o2.level - o1.level;
                    }
                });
                sendECA(new HashMap<>(levels));
                break;
            }
            case MSG_LATEST_DIVIDER: {
                latestDividers = new HashSet<>((Set) message.getValue());
                messageSizeCount += latestDividers.size();
                sendLatestDivider();
                break;
            }
            case MSG_LATEST_DIVIDER_ACK: {
                messageSizeCount++;
                if (++latestDividerAckCount == children.size()) {
                    if (!isRootAgent()) {
                        sendMessage(new Message(id, parent, MSG_LATEST_DIVIDER_ACK, null));
                    } else {
                        ackDone = true;
                        startPTFB();
                    }
                }
                break;
            }
            case MSG_REQUEST: {
                messageSizeCount ++;
                int val = (int) message.getValue();

                int sender = message.getIdSender();
                int[] costs = updateLocalCost(sender, val);
                int minCost = Integer.MAX_VALUE;
                for (int c : costs) {
                    if (minCost > c) {
                        minCost = c;
                    }
                }
                sendMessage(new Message(id, sender, MSG_REPORT, new LBResponse(val, minCost)));
                break;
            }
            case MSG_REPORT:{
                LBResponse response = (LBResponse) message.getValue();
                messageSizeCount = messageSizeCount + 2;
                int sender = message.getIdSender();
                lbReport.put(sender,response.estimate);
                int branch = -1;
                for (int c : pcb.keySet()){
                    if (pcb.get(c).contains(sender)){
                        branch = c;
                        break;
                    }
                }
                for (int pc : pcb.get(branch)){
                    if (!lbReport.containsKey(pc)){
                        return;
                    }
                }
                int subtreeAdjust = 0;
                for (int pc : pcb.get(branch)){
                    int shift = parentLbReports.containsKey(pc) ? parentLbReports.get(pc) : 0;
                    subtreeAdjust += lbReport.get(pc) - shift;
                    lbAdjust.put(pc,lbReport.get(pc) - shift);
                }
                srchVal.put(branch,response.value);
                domainLb[response.value] += subtreeAdjust;
                if (!subtreeLB.containsKey(branch)) {
                    subtreeLB.put(branch,new int[domain.length]);
                }
                subtreeLB.get(branch)[response.value] = subtreeLb.get(branch) + subtreeAdjust;
                for (int c : children) {
                    if (c == branch || !srchVal.containsKey(c) || srchVal.get(c) != response.value){
                        continue;
                    }
                    sendMessage(new Message(id,c,MSG_REDUCE_UB,subtreeAdjust));
                }
                if (domainLb[response.value] < ub) {
                    continueAssignment(response.value,branch);
                }
                else {
                    assignNextVal(response.value,branch);
                }
                break;
            }
            case MSG_UB:{
                UB Ub = (UB) message.getValue();
                messageSizeCount ++;
                messageSizeCount += Ub.assignment.size() * 2;
                if (id == 1)
                    System.out.println("UB:"+ub);
                int sender = message.getIdSender();
                childAssignment.putAll(Ub.assignment);
                if (children.size() == 1){
                    ub = Ub.ub;
                }
                else {
                    int branch = -1;
                    for (int c : desc.keySet()){
                        if (desc.get(c).contains(sender)){
                            branch = c;
                            break;
                        }
                    }
                    int val = srchVal.get(branch);
                    subtreeUB.get(branch)[val] = Ub.ub;
                    int sum = 0;

                    for (int c : children){
                        if (subtreeUB.containsKey(c)){
                            sum += subtreeUB.get(c)[val];
                        }
                    }
                    int totalUb = receiveCost + localCosts.get(parent)[val] + sum;
                    totalUb = subtreeUB.size() < children.size() ? Integer.MAX_VALUE : totalUb;
                    if (totalUb < ub){
                        ub = totalUb;
                        for (int ancestor : latestDividers){
                            sendMessage(new Message(id,ancestor,MSG_UB,new UB(ub,new HashMap<>(childAssignment))));
                        }
                    }
                }
            }
            break;
            case MSG_BACKTRACK:{
                messageSizeCount ++;
                int sender = message.getIdSender();
                int val = srchVal.get(sender);
                BacktrackMsg backtrackMsg = (BacktrackMsg)message.getValue();
                opt.get(sender)[val].costStar =  backtrackMsg.costStar;
                opt.get(sender)[val].sendUb = backtrackMsg.costStar >= INF ? -1 : backtrackMsg.receiveUb;
                exploreValue.get(sender).remove(exploreValue.get(sender).indexOf(val));
                if (children.size() > 1){
                    int diff = subtreeUB.get(sender)[val] - subtreeLB.get(sender)[val];
                    subtreeLB.get(sender)[val] = subtreeUB.get(sender)[val];
                    for (int c : children){
                        if (c == sender || !srchVal.containsKey(c) || srchVal.get(c) != val){
                            continue;
                        }
                        sendMessage(new Message(id,c,MSG_REDUCE_UB,diff));
                    }
                }
                assignNextVal(val,sender);
            }
                break;
            case MSG_REDUCE_UB:{
                messageSizeCount ++;
                receiveUb -= (int) message.getValue();
                if (receiveUb < ub){
                    int newDiff;
                    if (children.size() > 1){
                        newDiff = ub - receiveUb;
                    }
                    else {
                        newDiff = lastSentUb - receiveUb;
                        lastSentUb = receiveUb;
                    }
                    ub = receiveUb;
                    for (int c : children){
                        sendMessage(new Message(id,c,MSG_REDUCE_UB,newDiff));
                    }
                }
            }
                break;
            case MSG_TERMINATE:
                messageSizeCount ++;
                for (int c : children){
                    sendMessage(new Message(id,c,MSG_TERMINATE,null));
                }
                stopProcess();
                break;
            case MSG_CPA:
                cpaMsgCount++;
                cpaPTFB = (CPA) message.getValue();
                messageSizeCount = messageSizeCount + 2 + cpaPTFB.assignment.size()*2 + cpaPTFB.lbReports.size()*2;
                for (int c : children) {
                    for (int i = 0; i < domain.length; i++) {
                        opt.get(c)[i].sendUb = NULL;
                        opt.get(c)[i].costStar = INF;
                    }

                }
                disposeCpaMessage();
        }
    }




    public void setPreviousCpa(Map<Integer, Integer> previousCpa) {
        this.previousCpa = previousCpa;
    }

    private Set<Integer> resetChildren;
    private Set<Integer> partialResetChildren;

    private void disposeCpaMessage(){
        lbReport.clear();
        receiveCost = cpaPTFB == null ? 0 : cpaPTFB.cpaCost;
        parentLbReports = cpaPTFB == null ? new HashMap<>() : new HashMap<>(cpaPTFB.lbReports);
        lastSentUb = ub = receiveUb = cpaPTFB == null ? (int) 1e8 : cpaPTFB.ub;
        subtreeLb = new HashMap<>();
        subtreeUB.clear();
        if (!cpaPTFB.assignment.isEmpty())
            cpa = cpaPTFB.assignment;
        initLocalCost();
        partialResetChildren = new HashSet<>();
        resetChildren = getResetChildren();
        Set<Integer> noSearchChildren = new HashSet<>(children);
        noSearchChildren.removeAll(resetChildren);
        int lbSum = 0;
        for (int c : resetChildren) {
            LinkedList<Integer> tmp = new LinkedList<>();
            for (int i = 0; i < domain.length; ++i)
                tmp.add(i);
            exploreValue.put(c, tmp);
        }
        for (int c : noSearchChildren) {
            if (exploreValue.containsKey(c))
                exploreValue.get(c).clear();
            int tmp = Integer.MAX_VALUE;
            LinkedList<Integer> tmp1 = new LinkedList<>();
            for (int i = 0; i < domain.length; ++i) {
                if (opt.get(c)[i].sendUb < INF) {
                    if (exploreValue.containsKey(c))
                        exploreValue.get(c).add(i);
                    else {//修改过
                        tmp1.add(i);
                        exploreValue.put(c, tmp1);
                    }
                    partialResetChildren.add(c);
                }
                else {
                    subtreeLB.get(c)[i] = opt.get(c)[i].costStar;
                    if (!subtreeUB.containsKey(c)) {
                        subtreeUB.put(c, new int[domain.length]);
                    }
                    subtreeUB.get(c)[i] = subtreeLB.get(c)[i];
                    tmp = Integer.min(tmp, subtreeUB.get(c)[i]);
                }
            }
        }
        resetChildren.addAll(partialResetChildren);
        for (int c : resetChildren){
            srchVal.put(c,NULL);
            int sum = 0;

            for (int pc : desc.get(c)) {
                if (parentLbReports.containsKey(pc)) {
                    sum += parentLbReports.get(pc);
                }
            }

            lbSum += sum;
            subtreeLb.put(c,sum);
            if (!partialResetChildren.contains(c)) {
                int[] tmpArrays = new int[domain.length];
                Arrays.fill(tmpArrays, sum);
                subtreeLB.put(c, tmpArrays);
            }
            else {
                for (int i = 0; i < domain.length; ++i){
                    if(!exploreValue.get(c).contains(i))
                        subtreeLB.get(c)[i] = sum;
                }
            }
        }

        domainLb = new int[domain.length];
        int tmpLb = Integer.MAX_VALUE;
        for (int i = 0; i < domain.length; i ++){
            domainLb[i] = receiveCost + localCosts.get(parent)[i] + lbSum;
            tmpLb = Integer.min(tmpLb, domainLb[i]);
        }
        if (!isLeafAgent() && resetChildren.isEmpty()) {
            int minCost = Integer.MAX_VALUE;
            for (int i = 0; i < domain.length; i++) {
                int tempCost = localCosts.get(parent)[i];
                for (int c : children) {
                    if (ub < opt.get(c)[i].sendUb)
                        tempCost += opt.get(c)[i].costStar;
                    else
                        tempCost += INF;
                }
                minCost = Math.min(minCost, tempCost);
            }
            minCost += receiveCost;
            ub = Math.min(ub, minCost);
            for (int ancestor : latestDividers){
                sendMessage(new Message(id,ancestor,MSG_UB,new UB(ub,new HashMap<>())));
            }
            backTrack();
        }
        for (int c : resetChildren){
            assignNextVal(NULL,c);

        }
        if (isLeafAgent()){
            assignNextVal(NULL,NULL);
        }
    }

    private void backTrack1() {
        int costStar = localBound();
        int receiveUb = INFINITE;
        if ( costStar > sendUb && optContainsInfinity())
            receiveUb = sendUb;
        sendMessage(new Message(id,parent,MSG_BACKTRACK,new BacktrackMsg(receiveUb, costStar)));
    }

    @Override
    protected Set<Integer> getResetChildren() {
        Set<Integer> resetChildren = super.getResetChildren();
        Set<Integer> hitChild = writeOpt();
        Set<Integer> ret = new HashSet<>(resetChildren);
        for (int child : resetChildren) {
            if (hitChild.contains(child))
                ret.remove(child);
        }
        return ret;
    }

    private void assignNextVal(int val,int child){

        if (child != NULL) {
            for (int pc : pcb.get(child)) {
                lbReport.remove(pc);
            }
        }
        if (val == domain.length - 1)
            val = EMPTY;
        else {
            if (child != NULL) {
                if (val != -1 && exploreValue.get(child).contains(val)) {
                    exploreValue.get(child).remove(exploreValue.get(child).indexOf(val));
                }
                while (!exploreValue.get(child).isEmpty()) {
                    val = exploreValue.get(child).getFirst();
                    if (domainLb[val] < ub)
                        break;
                    exploreValue.get(child).removeFirst();
                }
                if (exploreValue.get(child).isEmpty())
                    val = EMPTY;
            }
            else
                while (++val < domain.length && domainLb[val] >= ub) ;
        }
        if (val == domain.length){
            val = EMPTY;
        }

        boolean flag = false;
        if (child != NULL && val == EMPTY){
            srchVal.put(child,EMPTY);
            boolean tmpFlag = true;
            for (int c : children){
                if (srchVal.get(c) != EMPTY){
                    tmpFlag = false;
                    break;
                }
            }
            flag = tmpFlag;
        }

        if (child == NULL && val == EMPTY || flag){
            if (!isRootAgent()) {
                int costStar = Integer.MAX_VALUE;
                int value = -1;
                for (int i = 0; i < domain.length; i++) {
                    if (highCost[i] < costStar) {
                        costStar = highCost[i];
                        value = i;
                    }

                }

                if (isLeafAgent()) {
                    sendMessage(new Message(id,parent,MSG_BACKTRACK,new BacktrackMsg(INFINITE,costStar)));
                    int totalUB = receiveCost + costStar;
                    Map<Integer,Integer> newChild = new HashMap<>(cpaPTFB.assignment);
                    newChild.put(id, value);
                    if (totalUB < ub){
                        ub = totalUB;

                        for (int ancestor : latestDividers){
                            sendMessage(new Message(id, ancestor, MSG_UB, new UB(totalUB, newChild)));
                        }
                    }

                }

                else {

                    int totalUB = Integer.MAX_VALUE;
                    for (int z = 0; z < domain.length; z++) {
                        int costOpt = 0;
                        for (int c : children) {
                            costOpt += opt.get(c)[z].costStar + highCost[z];
                        }
                        totalUB = Math.min(totalUB, costOpt);
                    }

                    int newUB = receiveCost + totalUB;
                    if (newUB < ub) {
                        ub = newUB;
                        for (int ancestor : latestDividers){
                            sendMessage(new Message(id,ancestor,MSG_UB,new UB(ub,new HashMap<>(childAssignment))));
                        }
                    }

                    backTrack();
                }
            }
            else {

                for (int c : children) {
                    sendMessage(new Message(id, c, MSG_TERMINATE, null));
                }
                stopProcess();
            }
        }
        else {
            if (isLeafAgent()){
                continueAssignment(val,child);
            }
            else if (val < EMPTY){
                for (int c : pcb.get(child)){
                    sendMessage(new Message(id,c,MSG_REQUEST,val));
                }
            }
        }
    }

    private void backTrack(){
        fillOptHistory();
        int costStar = localBound();
        int receiveUb = INFINITE;
        if ( costStar > sendUb && optContainsInfinity())
            receiveUb = sendUb;

        sendMessage(new Message(id,parent,MSG_BACKTRACK,new BacktrackMsg(receiveUb, costStar)));
    }

    @Override
    public void runFinished() {
        super.runFinished();
        ResultWithPrivacy cycle = new ResultWithPrivacy();
        if (id == 1)
            cycle.setUb(ub);
        cycle.setAgentValues(id,0);
        cycle.setCPAMsgCount(cpaMsgCount);
        cycle.setMessageSizeCount(messageSizeCount);
        mailer.setResultCycle(id,cycle);
    }

    private void continueAssignment(int val, int child){
        Map<Integer,Integer> newAssignment = new HashMap<>(cpaPTFB.assignment);
        newAssignment.put(id,val);
        if (isLeafAgent()){
            ub = receiveCost + localCosts.get(parent)[val];
            for (int ancestor : latestDividers){
                sendMessage(new Message(id,ancestor,MSG_UB,new UB(ub,newAssignment)));
            }
            assignNextVal(val,NULL);
        }
        else  {
            Map<Integer,Integer> newLbReports = new HashMap<>(parentLbReports);
            for (int id : lbAdjust.keySet()){
                if (newLbReports.containsKey(id)){
                    newLbReports.put(id,newLbReports.get(id) + lbAdjust.get(id));
                }
                else {
                    newLbReports.put(id,lbAdjust.get(id));
                }
            }
            if (children.size() == 1){
                int newCost = receiveCost + localCosts.get(parent)[val];
                lastSentUb = ub;
                sendUb = ub - newCost;
                sendMessage(new Message(this.id,child,MSG_CPA,new CPA(newAssignment,ub,newCost,newLbReports)));
            }
            else {
                int newCost = 0;
                int sum = 0;
                for (int c : children){
                    if (c == child || !subtreeLB.containsKey(c)){
                        continue;
                    }
                    sum += subtreeLB.get(c)[val];
                }
                int newUb = ub - receiveCost - localCosts.get(parent)[val] - sum;
                sendUb = newUb;
                if (!subtreeUB.containsKey(child)){
                    int[] stUb = new int[domain.length];
                    Arrays.fill(stUb,(int)1e7);
                    subtreeUB.put(child,stUb);
                }
                subtreeUB.get(child)[val] = newUb;
                opt.get(child)[val].sendUb = newUb;
                sendMessage(new Message(id,child,MSG_CPA,new CPA(newAssignment,newUb,newCost,newLbReports)));
            }
        }
    }

    private int[] updateLocalCost(int highId, int highVal){
        int eca = eca(highId);
        int[] costs = new int[domain.length];
        for (int i = 0; i < domain.length; i++){
            int base = eca == -1 ? 0 : localCosts.get(eca)[i];
            costs[i] = base + constraintCosts.get(highId)[i][highVal];
            ++ncccs;
        }
        localCosts.put(highId,costs);
        return costs;
    }

    protected void initLocalCost(){
        if (true) {
            for (int i = 0; i < domain.length; ++i) {
                int lc = 0;
                for (int pp : pseudoParents){
                    lc += constraintCosts.get(pp)[i][cpa.get(pp)];
                }
                if (!isRootAgent()){
                    lc += constraintCosts.get(parent)[i][cpa.get(parent)];
                }
                highCost[i] = lc;
            }
        }
    }
    protected int localBound(){
        int lowestBound = Integer.MAX_VALUE;
        for (int i = 0; i < domain.length; i++)
            if (isOptColFull(i))
                lowestBound = Integer.min(lowestBound,domainLb(i));
        return lowestBound;
    }
    boolean isOptColFull(int value){
        for (int child:children)
            if (exploreValue.get(child).contains(value))
                return false;
        return true;
    }


    private int eca(int pseudoParent){
        if (pseudoParentLevels.size() == 0){
            return -1;
        }
        if (pseudoParent == parent){
            return pseudoParentLevels.get(0).id;
        }
        for (int i = 1; i < pseudoParentLevels.size(); i++){
            if (pseudoParentLevels.get(i - 1).id == pseudoParent){
                return pseudoParentLevels.get(i).id;
            }
        }
        return -1;
    }

    private void dataStruct() {
        System.out.println("-------------------");
        System.out.println("id:" + id + " pcb:" + pcb + " latestDividers:" + latestDividers + "desc:" + desc);
        for (NeighborLevel pp : pseudoParentLevels) {
            System.out.println("pp.id ：" + pp.id + "pp,level : " + pp.level);
        }

        System.out.println("-------------------");
    }

    private class LBResponse{
        int value;
        int estimate;

        public LBResponse(int value, int estimate) {
            this.value = value;
            this.estimate = estimate;
        }
    }

    private class UB{
        int ub;
        Map<Integer,Integer> assignment;

        public UB(int ub, Map<Integer, Integer> assignment) {
            this.ub = ub;
            this.assignment = new HashMap<>(assignment);
        }
    }

    private class CPA{
        Map<Integer,Integer> assignment;
        int ub;
        int cpaCost;
        Map<Integer,Integer> lbReports;

        public CPA(Map<Integer, Integer> assignment, int ub, int cpaCost, Map<Integer, Integer> lbReports) {
            this.assignment = new HashMap<>(assignment);
            this.ub = ub;
            this.cpaCost = cpaCost;
            this.lbReports = new HashMap<>(lbReports);
        }
    }

    private class NeighborLevel{
        int id;
        int level;

        public NeighborLevel(int id, int level) {
            this.id = id;
            this.level = level;
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
}
