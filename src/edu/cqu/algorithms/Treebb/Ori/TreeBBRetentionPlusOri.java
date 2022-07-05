package edu.cqu.algorithms.Treebb.Ori;

import edu.cqu.core.Message;
import edu.cqu.core.SyncMailer;
import edu.cqu.result.ResultWithPrivacy;
import edu.cqu.result.annotations.NotRecordCostInCycle;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

@NotRecordCostInCycle
public class TreeBBRetentionPlusOri extends RetentionPlusFrameOri/*FIFO*//*LRU*/ {
    private final static int MSG_CPA = 0;
    private final static int MSG_BACKTRACK = 1;
    private final static int MSG_TERMINATE = 2;

    private Map<Integer,Integer> srchVal;
    private int ub;

    private final static int K = Integer.MAX_VALUE;

    public TreeBBRetentionPlusOri(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        srchVal = new HashMap<>();
        ub = Integer.MAX_VALUE;
    }

    @Override
    public void runFinished() {
        super.runFinished();
        ResultWithPrivacy cycle = new ResultWithPrivacy();
        if (isRootAgent())
            cycle.setUb(ub);
        cycle.setAgentValues(id,0);
        mailer.setResultCycle(id,cycle);
    }

    @Override
    protected void start() {
        acllocateK(K);
        if (isRootAgent())
            cpaNext();
    }

    @Override
    public void disposeMessage(Message message) {
        super.disposeMessage(message);
//        System.out.println(message);
        switch (message.getType()){
            case MSG_CPA:{
                CPAMsg cpaMsg = (CPAMsg)message.getValue();
                cpa = new HashMap<>(cpaMsg.Cpa);
                ub = cpaMsg.ub;
                if (isLeafAgent()){
                    initLocalCost();
                    sendMessage(new Message(id,parent,MSG_BACKTRACK,new BacktrackMsg(INFINITE,localBound())));
                }
                else{
                    cpaNext();
                    setPreviousCpa(new HashMap<>(cpa));
                }
                break;
            }
            case MSG_BACKTRACK:{
                BacktrackMsg backtrackMsg = (BacktrackMsg)message.getValue();
                int senderId = message.getIdSender();
                int vc = srchVal.get(senderId);
                opt.get(senderId)[vc].costStar =  backtrackMsg.costStar;
                opt.get(senderId)[vc].sendUb = backtrackMsg.receiveUb;
                exploreValue.get(senderId).remove(exploreValue.get(senderId).indexOf(vc));
                ub = Integer.min(ub, localBound());
                goNext(senderId);
                break;
            }
            case MSG_TERMINATE:{
                for (int c : children){
                    sendMessage(new Message(id,c,MSG_TERMINATE,null));
                }
                stopProcess();
            }
            break;
        }
    }

    private void cpaNext() {
        initVariables();
        if (isOptFull())
            backTrack();
        else {
            for (int child : children) {
                if (exploreValue.containsKey(child) && !exploreValue.get(child).isEmpty()) goNext(child);
            }
        }
    }

    @Override
    protected Set<Integer> getResetChildren() {
        Set<Integer> resetChildren = super.getResetChildren();
        Set<Integer> hitChild = writeOpt(); //fill opt
        Set<Integer> ret = new HashSet<>(resetChildren);
        for (int child : resetChildren) {
            if (hitChild.contains(child))
                ret.remove(child);
        }
        return ret;
    }


    private void backTrack(){
        fillOptHistory();
        int costStar = localBound();
        int receiveUb = INFINITE;
        if ( costStar > ub && optContainsInfinity())
            receiveUb = ub;
        sendMessage(new Message(id,parent,MSG_BACKTRACK,new BacktrackMsg(receiveUb, costStar)));
    }

    void goNext(int childId){
        int value = firstFeasibleAssignment(childId);
        if (isRootAgent())
            System.out.println("ub : " + ub);
        if (isOptFull()){
            if (isRootAgent()){
                System.out.println("UB:" + localBound());
                for (int child : children)
                    sendMessage(new Message(id,child,MSG_TERMINATE,null));
                stopProcess();
            }
            else{
                backTrack();
            }
        }
        else if (value != -1){
            int sendUb = (ub - domainLb(value));
            if (sendUb > opt.get(childId)[value].sendUb){
                srchVal.put(childId, value);
                Map<Integer,Integer> newCpa = new HashMap<>(cpa);
                newCpa.put(id, value);
                sendMessage(new Message(id, childId, MSG_CPA, new CPAMsg(newCpa, sendUb)));
            }
            else {
                exploreValue.get(childId).removeFirst();
                goNext(childId);
            }
        }
    }

    private int firstFeasibleAssignment(int childId){
        int value = -1;
        while(!exploreValue.get(childId).isEmpty()){
            value = exploreValue.get(childId).getFirst();
            if ( ub - domainLb(value) > 0){
                return value;
            }
            opt.get(childId)[value].costStar = INFINITE;
            opt.get(childId)[value].sendUb = ub - domainLb(value);
//            System.out.println("=====" + (ub - domainLb(value)));
            exploreValue.get(childId).remove(exploreValue.get(childId).indexOf(value));
        }
        if (exploreValue.get(childId).isEmpty())
            return -1;
        return value;
    }

    private class CPAMsg{
        Map<Integer, Integer> Cpa;
        int ub;
        public CPAMsg(Map<Integer, Integer> cpa, int ub) {
            Cpa = cpa;
            this.ub = ub;
        }
        public CPAMsg clone(){
            return new CPAMsg(new HashMap<>(this.Cpa), ub);
        }
    }

}
