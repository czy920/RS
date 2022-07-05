package edu.cqu.algorithms.Treebb.OCS;

import edu.cqu.core.Message;
import edu.cqu.core.SyncMailer;
import edu.cqu.ordering.DFSSyncAgent;

import java.util.*;

public abstract class RetentionFrameOCS extends DFSSyncAgent {

    private static final int MSG_BRANCH_PSEUDO_PARENTS = 0XFFFF4;
    protected static final int INFINITE = Integer.MAX_VALUE;

    int preUB;
    protected int[] highCost;
    protected Map<Integer,OptElement[]> opt;
    protected Map<Integer,Integer> cpa;
    protected Map<Integer,Integer> previousCpa;
    protected Map<Integer,Set<Integer>> branchPseudoParents;
    protected Map<Integer, LinkedList<Integer>> exploreValue;
    protected Set<Integer> pseudoChildren;
    protected OptElement[] localC; //我加的

    public RetentionFrameOCS(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        opt = new HashMap<>();
        cpa = new HashMap<>();
        previousCpa = new HashMap<>();
        branchPseudoParents = new HashMap<>();
        exploreValue = new HashMap<>();
        highCost = new int[domain.length];
        pseudoChildren = new HashSet<>();
        localC = new OptElement[domain.length];
    }

    @Override
    public void disposeMessage(Message message) {
        super.disposeMessage(message);
        switch (message.getType()) {
            case MSG_BRANCH_PSEUDO_PARENTS: {
                Set<Integer> receivedPesudoParents = (Set) message.getValue();
                if (receivedPesudoParents.contains(id)) {
                    receivedPesudoParents.remove(id);
                }
                branchPseudoParents.put(message.getIdSender(), receivedPesudoParents);
                if (branchPseudoParents.size() == children.size()) {
                    System.out.println("id : " + id + " branchPseudoParents : " + branchPseudoParents);
                    if (!isRootAgent()) {
                        Set<Integer> pp = new HashSet<>(pseudoParents);
                        for (Set<Integer> subPP : branchPseudoParents.values()) {
                            pp.addAll(subPP);
                        }
                        sendMessage(new Message(id, parent, MSG_BRANCH_PSEUDO_PARENTS, pp));
                    }
                    start();
                }
                break;
            }
        }
    }

    protected abstract void start();


    @Override
    protected void pseudoTreeCreated() {
        for (int neighbourId : neighbours)
            if (!children.contains(neighbourId) && parent != neighbourId && !pseudoParents.contains(neighbourId))
                pseudoChildren.add(neighbourId);
        for (int child : children) {
            OptElement[] optRow = new OptElement[domain.length];
            for (int i = 0; i < domain.length; ++i){
                optRow[i] = new OptElement();
            }
            opt.put(child,optRow);
        }
        initLocalC();
        if (isLeafAgent()) {
            sendMessage(new Message(id,parent,MSG_BRANCH_PSEUDO_PARENTS,new HashSet<>(pseudoParents)));
            start();
        }
    }

    public void setPreviousCpa(Map<Integer, Integer> previousCpa) {
        this.previousCpa = previousCpa;
    }


    protected Set<Integer> getResetChildren(){  //判断当前cpa是否与previousCpa一致
        if (previousCpa.isEmpty()){
            return new HashSet<>(children);
        }
        Set<Integer> childrenToBeReset = new HashSet<>();
        for (int child : children){
            boolean identity = true;
            for (int pp : branchPseudoParents.get(child)){
                if (previousCpa.get(pp).intValue() != cpa.get(pp)){
                    identity = false;
                    break;
                }
            }
            if (!identity){
                childrenToBeReset.add(child);
            }
        }
        return childrenToBeReset;
    }

    protected int domainLb(int value){
        long lb = 0;
        for (int child : children){
            int cost = opt.get(child)[value].costStar;
            if (exploreValue.containsKey(child) && !exploreValue.get(child).contains(value)){
                lb += cost;
            }
        }
        lb += highCost[value];
        return lb > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int)lb;
    }

    boolean isOptColFull(int value){
        for (int child:children)
            if (exploreValue.get(child).contains(value))
                return false;
        return true;
    }
    public boolean isOptFull(){
        for (int child : exploreValue.keySet()){
            if (!exploreValue.get(child).isEmpty())
                return false;
        }
        return true;
    }


    protected int localBound(){
        int lowestBound = Integer.MAX_VALUE;
        for (int i = 0; i < domain.length; i++)
            if (isOptColFull(i)) {
                lowestBound = Integer.min(lowestBound,domainLb(i));
                localC[i].sendUb = preUB;
                localC[i].costStar = domainLb(i);
            }

        return lowestBound;
    }

    private boolean reSetLocalCost(){
        for (int pp : pseudoParents){
            if (previousCpa.isEmpty() || (!previousCpa.isEmpty() && previousCpa.get(pp) != cpa.get(pp)))
                return true;
        }
        return false;
    }

    protected boolean optContainsInfinity(){
        for (int i = 0; i < domain.length; i++){
            for (int child : children){
                if (opt.get(child)[i].costStar == INFINITE){
                    return true;
                }
            }
        }
        return false;
    }

    protected void initLocalCost(){
        if (true) {//reSetLocalCost()){//
            for (int i = 0; i < domain.length; ++i) {
                int lc = 0;
                for (int pp : pseudoParents){
                    lc += constraintCosts.get(pp)[i][cpa.get(pp)];
                    ncccs++;
                }
                if (!isRootAgent()){
                    lc += constraintCosts.get(parent)[i][cpa.get(parent)];
                    ncccs++;
                }
                highCost[i] = lc;
            }
        }
    }
    protected void initVariables(){
        initLocalCost();
        initLocalC();
        Set<Integer> invalidChild = getResetChildren();
//        System.out.println("id : " + id + "invalidChild : " + invalidChild);
        for (int child : invalidChild){
            LinkedList<Integer> tmp = new LinkedList<>();
            for (int i = 0; i < domain.length; ++i) {
                tmp.add(i);
                opt.get(child)[i].sendUb = -1;
            }
            exploreValue.put(child, tmp);
        }
        for (int child : children) {
            if (!invalidChild.contains(child)) {
                LinkedList<Integer> tmp = new LinkedList<>();
                for (int i = 0; i < domain.length; i++) {
                    if (opt.get(child)[i].sendUb != INFINITE) {
                        tmp.add(i);
                    }
                }
                if (!tmp.isEmpty())
                    exploreValue.put(child, tmp);
            }
        }
    }

    protected  void initLocalC() {
        for (int i = 0; i < domain.length; i++) {
            OptElement temp = new OptElement();
            temp.sendUb = -1;
            temp.costStar = Integer.MAX_VALUE;
            localC[i] = temp;
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
            this.costStar = INFINITE;
            this.sendUb = -1;
        }

        @Override
        public String toString() {
            return "cost:" + costStar + " ub:" + sendUb;
        }
    }

    protected class BacktrackMsg{
        public int receiveUb;
        public int costStar;

        public BacktrackMsg(int receiveUb, int costStar) {
            this.receiveUb = receiveUb;
            this.costStar = costStar;
        }
    }
}
