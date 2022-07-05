package edu.cqu.ordering;

import edu.cqu.core.AsyncAgent;
import edu.cqu.core.AsyncMailer;
import edu.cqu.core.Message;

import java.util.*;

public abstract class DFSAsyncAgent extends AsyncAgent {

    private static final int MSG_DEGREE = 0XFFFF0;
    private static final int MSG_DFS = 0XFFFF1;
    private static final int MSG_DFS_BACKTRACK = 0XFFFF2;
    private static final int MSG_START = 0XFFFF3;

    protected Map<Integer,Integer> degreeView;
    protected List<Map.Entry<Integer,Integer>> orderedDegree;
    protected int parent;
    protected List<Integer> children;
    protected List<Integer> pseduoChildren;
    protected List<Integer> pseudoParents;
    protected int level;
    private int currentChildIndex;
    protected int height;
    private int maxSubHeight;

    public DFSAsyncAgent(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, AsyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        degreeView = new HashMap<>();
        children = new LinkedList<>();
        pseduoChildren = new LinkedList<>();
        pseudoParents = new LinkedList<>();
        maxSubHeight = 0;
    }

    protected boolean isRootAgent(){
        return parent <= 0;
    }

    protected boolean isLeafAgent(){
        return children.size() == 0;
    }

    @Override
    protected void initRun() {
        for (int i : neighbours) {
            sendMessage(new Message(id, i, MSG_DEGREE, neighbours.length));
        }
    }

    @Override
    public void runFinished() {

    }

    @Override
    public void disposeMessage(Message message) {
        switch (message.getType()) {
            case MSG_DEGREE:{
                int sendId = message.getIdSender();
                int len = (int) message.getValue();
                degreeView.put(sendId, len);
                if (degreeView.size() == neighbours.length) {
                    orderedDegree = new ArrayList<>(degreeView.entrySet());
                    orderedDegree.sort(new Comparator<Map.Entry<Integer, Integer>>() {
                        @Override
                        public int compare(Map.Entry<Integer, Integer> o1, Map.Entry<Integer, Integer> o2) {
                            return o2.getValue().compareTo(o1.getValue());
                        }
                    });

                    if (id == 1) {
                        HashSet<Integer> visited = new HashSet<>();
                        visited.add(id);
                        parent = -1;
                        level = 0;
                        children.add(orderedDegree.get(0).getKey());
                        sendMessage(new Message(id, orderedDegree.get(0).getKey(), MSG_DFS, new DFSMsg(visited, level)));
                    }
                }
            }
            break;
            case MSG_DFS:{
                DFSMsg dfsMsg = (DFSMsg) message.getValue();
                Set<Integer> visited = dfsMsg.visited;
                visited.add(id);
                level = dfsMsg.level + 1;
                parent = message.getIdSender();
                //pseudo parent
                for (int i = 0; i < orderedDegree.size(); ++i) {
                    if (visited.contains(orderedDegree.get(i).getKey())) {
                        if (orderedDegree.get(i).getKey() != parent) {
                            pseudoParents.add(orderedDegree.get(i).getKey());
                        }
                    }
                }
                int selectChild = 0;
                for (int i = 0; i < orderedDegree.size(); ++i) {
                    if (visited.contains(orderedDegree.get(i).getKey())) {
                        continue;
                    }
                    selectChild = orderedDegree.get(i).getKey();
                    currentChildIndex = i;
                    break;
                }
                if (selectChild != 0) {
                    children.add(selectChild);
                    sendMessage(new Message(id, selectChild, MSG_DFS, new DFSMsg(visited, level)));
                }
                else {
                    height = 0;
                    sendMessage(new Message(id, parent, MSG_DFS_BACKTRACK, new BackDFSMsg(visited, height)));
                }
            }
            break;
            case MSG_DFS_BACKTRACK:{
                BackDFSMsg backDFSMsg = (BackDFSMsg) message.getValue();
                int sendId = message.getIdSender();
                Set<Integer> visited = backDFSMsg.visited;
                if (backDFSMsg.height > maxSubHeight){
                    maxSubHeight = backDFSMsg.height;
                }
                int selectChild = 0;
                for (int i = currentChildIndex + 1; i < orderedDegree.size(); ++i) {
                    if (visited.contains(orderedDegree.get(i).getKey())) {
                        continue;
                    }
                    selectChild = orderedDegree.get(i).getKey();
                    currentChildIndex = i;
                    break;
                }
                if (selectChild != 0) {
                    children.add(selectChild);

                    sendMessage(new Message(id, selectChild, MSG_DFS, new DFSMsg(visited, level)));
                }
                else {
                    height = maxSubHeight + 1;
                    if (id != 1) {
                        //
                        sendMessage(new Message(id, parent, MSG_DFS_BACKTRACK, new BackDFSMsg(visited, height)));
                    }
                    else {
                        for (int child : children) {
                            sendMessage(new Message(id, child, MSG_START, null));
                        }
                        for (int i : neighbours) {
                            if (!(i==parent || children.contains(i) || pseudoParents.contains(i))) {
                                pseduoChildren.add(i);
                            }
                        }
                        pseudoTreeCreated();
                    }
                }
            }
            break;
            case MSG_START:{
                for (int child : children) {
                    sendMessage(new Message(id, child, MSG_START, null));
                }
                for (int i : neighbours) {
                    if (!(i==parent || children.contains(i) || pseudoParents.contains(i))) {
                        pseduoChildren.add(i);
                    }
                }
                pseudoTreeCreated();
            }
            break;
        }
    }

    protected abstract void pseudoTreeCreated();
    class DFSMsg{
        Set<Integer> visited;
        int level;

        public DFSMsg(Set<Integer> visited, int level) {
            this.visited = new HashSet<>();
            this.visited.addAll(visited);
            this.level = level;
        }
    }
    class BackDFSMsg{
        Set<Integer> visited;
        int height;

        public BackDFSMsg(Set<Integer> visited, int height) {
            this.visited = new HashSet<>();
            this.visited.addAll(visited);
            this.height = height;
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
