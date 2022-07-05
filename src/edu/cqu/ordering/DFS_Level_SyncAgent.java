package edu.cqu.ordering;

import edu.cqu.core.Message;
import edu.cqu.core.SyncAgent;
import edu.cqu.core.SyncMailer;

import java.util.*;

public abstract class DFS_Level_SyncAgent extends SyncAgent{

    private static final int MSG_DEGREE = 0XFFFF0;
    private static final int MSG_DFS = 0XFFFF1;
    private static final int MSG_DFS_BACKTRACK = 0XFFFF2;
    private static final int MSG_START = 0XFFFF3;
    private static final int MSG_ASK_LEVEL = 0XFFFF4;
    private static final int MSG_RESPONSE_LEVEL = 0XFFFF5;

    protected Map<Integer,Integer> degreeView;
    protected List<Map.Entry<Integer,Integer>> orderedDegree;
    protected int parent;
    protected List<Integer> children;
    protected List<Integer> pseudoParents;
    protected int level;
    protected int height;
    private int maxSubHeight;

    private Set<Integer> toVisit;
    private Map<Integer,Double> toVisitLevel;
    protected Map<Integer, Integer> visited;
    private double[] weight;
    public DFS_Level_SyncAgent(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        degreeView = new HashMap<>();
        children = new LinkedList<>();
        pseudoParents = new LinkedList<>();
        parent = -1;
        toVisit = new HashSet<>();
        toVisitLevel = new HashMap<>();
        visited = new HashMap<>();
        weight = new double[4];
        weight[0] = 5.0/4;  //level
//        weight[1] = -1.0/4;  //cnt
//        weight[2] = -3.0/4;  //degree - cnt
        weight[3] = -2.0/4;  //degree
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
//        sendMessage(new Message(id,1,MSG_DEGREE,neighbours.length));
    }

    @Override
    public void runFinished() {

    }

    @Override
    public void disposeMessage(Message message) {
        switch (message.getType()){
            case MSG_DEGREE:
                degreeView.put(message.getIdSender(),(int)message.getValue());
                if (degreeView.size() == neighbours.length){
                    orderedDegree = new ArrayList<>(degreeView.entrySet());
                    orderedDegree.sort(new Comparator<Map.Entry<Integer, Integer>>() {
                        @Override
                        public int compare(Map.Entry<Integer, Integer> o1, Map.Entry<Integer, Integer> o2) {
                            return o1.getValue().compareTo(o2.getValue()); //min
                            //oreder max
//                            return o2.getValue().compareTo(o1.getValue());
                        }
                    });
                    if (id == 1){
                        Map<Integer, Integer> visited = new HashMap<>();
                        parent = -1;
                        level = 0;
                        visited.put(id, level);
                        children.add(orderedDegree.get(0).getKey());
                        sendMessage(new Message(id,orderedDegree.get(0).getKey(),MSG_DFS,new DFSMessageContent(visited,level)));
                    }
                }
                break;
            case MSG_DFS: {
//                System.out.println(message);
                DFSMessageContent content = (DFSMessageContent) message.getValue();
                visited = content.visited;
                level = content.level + 1;
                visited.put(id,level);
                parent = message.getIdSender();
                toVisit.clear();
                toVisitLevel.clear();
                for (int i : neighbours) {
                    if (visited.keySet().contains(i)) {
                        if (i != parent)
                            pseudoParents.add(i);
                    }
                    else {
                        toVisit.add(i);
                    }
                }
                if (toVisit.isEmpty()) {
                    height = 0;
                    sendMessage(new Message(id, parent, MSG_DFS_BACKTRACK, new BacktrackMessageContent(visited,height)));
                }
                else {
                    for (int i : toVisit) {
                        sendMessage(new Message(id, i, MSG_ASK_LEVEL, visited));
                    }
                }
                break;
            }
            case MSG_ASK_LEVEL:{
                int sender = message.getIdSender();
                int highLevel = Integer.MAX_VALUE;
                int cnt = 0;
                Map<Integer,Integer> visited = (HashMap<Integer, Integer>)message.getValue();
                for (int neiId : neighbours) {
                    if (visited.containsKey(neiId)) {
                        highLevel = Integer.min(highLevel, visited.get(neiId));
                    }
                    else {
                        ++cnt;
                    }
                }
                sendMessage(new Message(id, sender, MSG_RESPONSE_LEVEL, new ResLevel(highLevel, cnt)));
                break;
            }
            case MSG_RESPONSE_LEVEL:{
                ResLevel resLevel = (ResLevel) message.getValue();
                int sender = message.getIdSender();
                double childLevel = 0;
//                childLevel = resLevel.level ;
                //case 2: consider those not visited node
                childLevel = (level - resLevel.level + 1) * weight[0] + resLevel.cnt * weight[1] +
                        (degreeView.get(sender) - resLevel.cnt) * weight[2] + degreeView.get(sender) * weight[3];
                toVisitLevel.put(sender, childLevel);
                if (toVisitLevel.size() == toVisit.size()) {
                    int selectedChild = 0;
                    //two strategy for select child 1.the minimal level 2.the probability distribution
                    //1.
                    double maxLevel= -100;
                    for (int i : toVisit) {
                        if (toVisitLevel.get(i) > maxLevel) {
                            maxLevel = toVisitLevel.get(i);
                            selectedChild = i;
                        }
                    }
                    //2.
//                    int sum = 0;
//                    Map<Integer, Double> toVisitPro = new HashMap<>();
//                    for (int i : toVisit) {
//                        int tmp = level - toVisitLevel.get(i) + 1;
//                        sum += tmp;
//                        toVisitLevel.put(i, sum);
//                    }
//                    double p = Math.random();
//                    for (int i : toVisit) {
//                       if (p <= (toVisitLevel.get(i)*1.0)/sum) {
//                           selectedChild = i;
//                           break;
//                       }
//                    }
                    children.add(selectedChild);
                    sendMessage(new Message(id, selectedChild, MSG_DFS, new DFSMessageContent(visited,level)));
                }
                break;
            }
            case MSG_DFS_BACKTRACK:
                BacktrackMessageContent content = (BacktrackMessageContent) message.getValue();
                visited = content.visited;
                if (content.height > maxSubHeight){
                    maxSubHeight = content.height;
                }
                toVisitLevel.clear();
                toVisit.clear();
                for (int i : neighbours){
                    if (!visited.keySet().contains(i)) {
                        toVisit.add(i);
                    }
                }
                if (toVisit.isEmpty()) {
                    height = maxSubHeight + 1;
                    if (id != 1) {
                        sendMessage(new Message(id, parent, MSG_DFS_BACKTRACK, new BacktrackMessageContent(visited,height)));
                    }
                    else {
                        for (int childId : children){
                            sendMessage(new Message(id,childId,MSG_START,null));
                        }
                        pseudoTreeCreated();
                    }
                }
                else {
                    for (int i : toVisit) {
                        sendMessage(new Message(id, i, MSG_ASK_LEVEL, visited));
                    }
                }

                break;
            case MSG_START:
                for (int childId : children){
                    sendMessage(new Message(id,childId,MSG_START,null));
                }
                pseudoTreeCreated();
                break;
        }
    }
    class ResLevel{
        int level;
        int cnt;

        public ResLevel(int level, int cnt) {
            this.level = level;
            this.cnt = cnt;
        }
    }

    protected abstract void pseudoTreeCreated();
    private class DFSMessageContent{
        Map<Integer,Integer> visited;
        int level;

        public DFSMessageContent(Map<Integer,Integer> visited, int level) {
            this.visited = visited;
            this.level = level;
        }
    }

    private class BacktrackMessageContent{
        Map<Integer,Integer> visited;
        int height;

        public BacktrackMessageContent(Map<Integer,Integer> visited, int height) {
            this.visited = visited;
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
