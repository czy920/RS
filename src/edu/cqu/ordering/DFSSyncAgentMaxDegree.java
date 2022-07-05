package edu.cqu.ordering;

import edu.cqu.core.Message;
import edu.cqu.core.SyncMailer;
import edu.cqu.core.SyncAgent;

import java.util.*;

public abstract class DFSSyncAgentMaxDegree extends SyncAgent{

    private static final int MSG_DEGREE = 0XFFFF0;
    private static final int MSG_DFS = 0XFFFF1;
    private static final int MSG_DFS_BACKTRACK = 0XFFFF2;
    private static final int MSG_START = 0XFFFF3;
    private static final int MSG_CHOOSEROOT = 0XFFFF4;
    private static final int MSG_STARTROOT = 0XFFFF5;

    protected int parent;
    protected List<Integer> children;
    protected List<Integer> pseudoParents;
    protected List<Integer> pseudoChildren;
    protected int level;
    protected int height;
    protected Set<Integer> sep;
    protected static int INDUCED;

    private int maxInduced;
    private Map<Integer,Integer> neighborDegree;
    private int maxDegree;
    private int maxIdx;

    protected long msgSizeCnt;
    protected long ncccs;

    public DFSSyncAgentMaxDegree(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        children = new ArrayList<>();
        pseudoParents = new ArrayList<>();
        pseudoChildren = new ArrayList<>();
        sep = new HashSet<>();
        parent = -1;
        neighborDegree = new HashMap<>();
        maxDegree = 0;
        maxIdx = 0;
        maxInduced = 0;
    }


    protected boolean isRootAgent(){
        return parent <= 0;
    }

    protected boolean isLeafAgent(){
        return children.size() == 0;
    }

    @Override
    protected void initRun() {
        for (int neighbourId : neighbours){
            sendMessage(new Message(id,neighbourId,MSG_DEGREE,neighbours.length));
        }
        sendMessage(new Message(id,1, MSG_CHOOSEROOT, neighbours.length));
    }



    @Override
    public void runFinished() {

    }

    @Override
    public void allMessageDisposed() {
        super.allMessageDisposed();
        if(id == 1 && maxIdx != 0){
            sendMessage(new Message(id, maxIdx, MSG_STARTROOT, null));
            maxIdx = 0;
        }
    }

    @Override
    public void disposeMessage(Message message) {
        Set<Integer> visited;
        int choose;
        switch (message.getType()){
            case MSG_DEGREE:
                int nDegree = (int) message.getValue();
                neighborDegree.put(message.getIdSender(), nDegree);
                break;
            case MSG_CHOOSEROOT:
                int degree = (int) message.getValue();
                if (degree > maxDegree) {
                    maxDegree = degree;
                    maxIdx = message.getIdSender();
                } else if (degree == maxDegree) {
                    maxIdx = Integer.min(maxIdx, message.getIdSender());
                }
                break;
            case MSG_STARTROOT:
                visited = new HashSet<>();
                choose = chooseNextExpandChild(visited);
                visited.add(this.id);
                sendMessage(new Message(this.id, choose, MSG_DFS, visited));
                break;

            case MSG_DFS:
                visited = (Set<Integer>) message.getValue();
                parent = message.getIdSender();
                for(int n: neighbours){
                    if(visited.contains(n)&& n != parent){
                        pseudoParents.add(n);
                    }
                }
                visited.add(this.id);
                sep.addAll(pseudoParents);
                sep.add(parent);
                choose = chooseNextExpandChild(visited);
                if(choose != -1) {
                    sendMessage(new Message(this.id, choose, MSG_DFS, visited));
                }else {
                    BacktrackMessageContent send = new BacktrackMessageContent(visited,sep,sep.size());
                    sendMessage(new Message(this.id, parent, MSG_DFS_BACKTRACK, send));
                }
                break;
            case MSG_DFS_BACKTRACK:
                BacktrackMessageContent recv = (BacktrackMessageContent) message.getValue();
                visited = recv.visited;
                children.add(message.getIdSender());
                sep.addAll(recv.sep);
                sep.remove(this.id);
                maxInduced = Integer.max(maxInduced, recv.induced);
                choose = chooseNextExpandChild(visited);
                if(choose != -1) {
                    sendMessage(new Message(this.id, choose, MSG_DFS, visited));
                }else {
                    if(!isRootAgent()){
                        maxInduced = Integer.max(maxInduced, sep.size());
                        BacktrackMessageContent send = new BacktrackMessageContent(visited,sep,maxInduced);
                        sendMessage(new Message(this.id, parent, MSG_DFS_BACKTRACK, send));
                    }else{
                        level = 0;
                        INDUCED = Integer.max(maxInduced, sep.size());
                        calculatePC();
                        for(int c: children){
                            sendMessage(new Message(this.id, c, MSG_START, level));
                        }
                        pseudoTreeCreated();
                    }
                }
                break;
            case MSG_START:
                level = (int) message.getValue()+1;
                if(!isLeafAgent()){
                    calculatePC();
                    for(int c: children){
                        sendMessage(new Message(this.id, c, MSG_START, level));
                    }
                }
                pseudoTreeCreated();
                break;
        }

    }

    private void calculatePC(){
        for(int n : neighbours){
            if(!sep.contains(n) && !children.contains(n))
                pseudoChildren.add(n);
        }
    }

    private int chooseNextExpandChild(Set<Integer> visited){
        int  choose = -1;
        for(int i: visited){
            neighborDegree.remove(i);
        }
        int maxDegree = 0;
        for(int i : neighborDegree.keySet()){
            int degree = neighborDegree.get(i);
            if(degree > maxDegree){
                maxDegree = degree;
                choose = i;
            }else if(degree == maxDegree){
                choose = Integer.min(choose, i);
            }
        }
        return choose;
    }
    protected abstract void pseudoTreeCreated();

    private class BacktrackMessageContent{
        Set<Integer> visited;
        Set<Integer> sep;
        int induced;

        public BacktrackMessageContent(Set<Integer> visited, Set<Integer> sep, int induced) {
            this.visited = new HashSet<>(visited);
            this.sep = new HashSet<>(sep);
            this.induced = induced;
        }
    }

    public String toDOTString(){
        StringBuilder stringBuilder = new StringBuilder();
        if (parent > 0){
            stringBuilder.append("X" + parent + "->X" + id + ";\n");
        }
        for (int pp : pseudoParents){
            stringBuilder.append("X" + pp + "->X" + id + " [style=dotted];\n");
        }
        return stringBuilder.toString();
    }
}

