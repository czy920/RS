package edu.cqu.algorithms.HSCAI.Retention;

import edu.cqu.algorithms.dcop.incomplete.ADPOP.NDData;
import edu.cqu.core.Message;
import edu.cqu.core.SyncMailer;
import edu.cqu.ordering.DFSSyncAgent;
import edu.cqu.result.ResultWithPrivacy;

import java.util.*;



public class PTISBB_T extends DFSSyncAgent {

    private static final int MSG_BRANCH_PSEUDO_PARENTS = 10086;

    private static final int MSG_CPA = 0;
    private static final int MSG_BACKTRACK = 1;
    private static final int MSG_TERMINATE = 2;
    private static final int MSG_PREUTIL = 3;
    //    private static final int  MSG_BACKINFER = 5;
    private static final int  MSG_INFERCTXT = 6;
    private static final int  MSG_CTXTUTIL = 7;

    private static final int NULL = -100000;
    private static final int INFINTY = 100000;

    private static final int kp = edu.cqu.algorithms.HSCAI.Retention.Parameter.kp;
    private int ub;
    private boolean collected = false;
    private int t;
    //    private Set<Integer> rcvCtxtCnt;
    private Map<Integer,Integer> sListCounter;
    //    private Map<Integer,Integer> rcvCtxt;
    private Map<Integer, CtxtUtil> childCtxtUtils;

    private Map<Integer, Map<Integer, Integer>> childInferCtxt;
    private Map<Integer, Integer> cpa;
    private Map<Integer, OptElement[]> opt;
    private Map<Integer, int[]> lb;
    private int[] subtreeLb;
    private int[] localCost;
    private Map<Integer,Integer> srchVal;
    //add
    protected Map<Integer, LinkedList<Integer>> exploreValue;
    protected Map<Integer,Integer> previousCpa;
    protected Map<Integer,Set<Integer>> branchPseudoParents;
    protected Set<Integer> pseudoChildren;
    private ArrayList<OptHistory> optHistories;
    private Map<Integer,Integer> proportion;


    private Map<Integer, Set<Integer>> childSi;
    private Set<Integer> si;

    private Map<Integer, NDData> localUtilMap;
    private Map<Integer,NDData> childPreUtils;
    private Set<Integer> childDims;
    private Set<Integer> sList;


    private Map<Integer, CostList> costTable;

    private long msgSizeCnt;
    private long ncccsPreInference;
    private long ncccsSearchPart;
    private long ncccsContextInferencePart;


    private long msgSizeCntPreInference;
    private long msgSizeCntSearchPart;
    private long msgSizeCntContextInferencePart;
    private long msgPreInference;
    private long msgSearchPart;
    private Map<Integer,Integer> inferCtxt;
    private long msgContextInferencePart;
    private int childSiNoEmpty;

    private long CPAMsgCount;
    private Set<Integer> idleChild;
    private Set<Integer> inferChild;
    public PTISBB_T(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        childCtxtUtils = new HashMap<>();
        sListCounter = new HashMap<>();
        cpa = new HashMap<>();
        opt = new HashMap<>();
        lb = new HashMap<>();
        subtreeLb = new int[domain.length];
        localCost = new int[domain.length];
        srchVal = new HashMap<>();
        childSi = new HashMap<>();
        si = new HashSet<>();
        childPreUtils = new HashMap<>();
        localUtilMap = new HashMap<>();
        sList = new HashSet<>();
        childDims = new HashSet<>();
        costTable = new HashMap<>();
        childInferCtxt = new HashMap<>();
        inferCtxt = new HashMap<>();
//        rcvCtxtCnt = new HashSet<>();
        inferChild = new HashSet<>();
        idleChild = new HashSet<>();
        exploreValue = new HashMap<>();
        previousCpa = new HashMap<>();
        branchPseudoParents = new HashMap<>();
        pseudoChildren = new HashSet<>();
        optHistories = new ArrayList<>();
        proportion = new HashMap<>();
    }

    @Override
    protected void pseudoTreeCreated() {
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

        for (int pp : pseudoParents) {
            localUtilMap.put(pp, new NDData(constraintCosts.get(pp),id,pp));
            costTable.put(pp, new CostList());
        }
        if (!isRootAgent()){
            localUtilMap.put(parent, new NDData(constraintCosts.get(parent),id,parent));
            costTable.put(parent, new CostList());
        }
        if (isLeafAgent()) {
            computeSi(new HashMap<>());// childPreUtils = empty set
            sendUtil(new HashMap<>(), new HashMap<>());// childPreUtils = empty set, assign = empty set
        }

    }


    void alloCtxt(Map<Integer,Integer> inferCtxt){
        idleChild = new HashSet<>();
        inferChild = new HashSet<>();
        for (int child : childSi.keySet()) {
            Map<Integer,Integer> ctxt = new HashMap<>();
            for (int i : childSi.get(child)) {
                if (inferCtxt.containsKey(i)) {
                    ctxt.put(i, inferCtxt.get(i));
                }
            }
            if (ctxt.size() == 0) {
                idleChild.add(child);
            }
            else if(!childCtxtUtils.containsKey(child) || !equal(childCtxtUtils.get(child).ctxt, ctxt)){
                childInferCtxt.put(child, ctxt);
                inferChild.add(child);
                sendMessage(new Message(id, child, MSG_INFERCTXT, ctxt));
            }
        }
    }

    Map<Integer, Integer> computeCtxtD(){
        Map<Integer, Integer> map = new HashMap<>();
        for (int key : sList) {
            if (cpa.containsKey(key)) {
                map.put(key, cpa.get(key));
            }
        }
        return map;
    }
    private void ctxtCpa() {
        if (!collected) {
            Map<Integer, Integer> ctxt = computeCtxtD();
            if (ctxt.size() >= t) {
                collected = true;
                inferCtxt = new HashMap<>();
//                System.out.println("id " + id + " start inference:" + ctxt);
                alloCtxt(ctxt);
            }
        }
    }
    //    private void ctxtCpa(Map<Integer,Integer> oldCpa) {
//
//        updateSCounter(oldCpa);
//        if (!collected) {
//            Map<Integer,Integer> ctxt = compuetCtxt();
//            if (ctxt.size() > 0 && !ctxt.containsKey(parent)) {
//                System.out.println(id + " start back infer context to " + parent + " " + ctxt);
//                sendMessage(new Message(id, parent, MSG_BACKINFER, ctxt));
//                collected = true;
//            }
//        }
//    }
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
//                    System.out.println("id : " + id + " branchPseudoParents : " + branchPseudoParents);
                    if (!isRootAgent()) {
                        Set<Integer> pp = new HashSet<>(pseudoParents);
                        for (Set<Integer> subPP : branchPseudoParents.values()) {
                            pp.addAll(subPP);
                        }
                        sendMessage(new Message(id, parent, MSG_BRANCH_PSEUDO_PARENTS, pp));
                    }
                    acllocateK(27);
                }
                break;
            }

            case MSG_PREUTIL:{
                ++msgPreInference;
                PreUtilMsg preUtilMsg = (PreUtilMsg) message.getValue();
                msgSizeCnt += preUtilMsg.data.data.length;
                msgSizeCntPreInference += preUtilMsg.data.data.length;
                int senderId = message.getIdSender();
                Set<Integer> tmp = new HashSet<>(preUtilMsg.siList);
//                tmp.remove(id);
                childSi.put(senderId, tmp);
                childPreUtils.put(senderId, preUtilMsg.data);
                if (childPreUtils.size() == children.size()) {
                    childSiNoEmpty = 0;
                    for (int child : childSi.keySet()) {
                        if (childSi.get(child).size() > 0){
                            ++childSiNoEmpty;
                        }
                    }
                    if (isRootAgent()) {
                        //todo start search phase
                        ub = Integer.MAX_VALUE;
//                        System.out.println("start search phase");
                        initVariables();
                        for (int child : children) {
                            sendCpa(child,0);
                        }
                    }
                    else {
                        computeSi(childPreUtils);
                        sendUtil(childPreUtils, new HashMap<>());
                    }
                }

                break;
            }
            case MSG_CPA:{
                ++CPAMsgCount;
                ++msgSearchPart;
                CpaMsg cpaMsg = (CpaMsg) message.getValue();
                msgSizeCnt += cpaMsg.cpa.size()*2 + 1;
                msgSizeCntSearchPart += cpaMsg.cpa.size()*2 + 1;
                Map<Integer,Integer> oldCpa = cpa;
                collected = cpaMsg.haveBeenRuled;
                ub = cpaMsg.ub;
                cpa = cpaMsg.cpa;
                ctxtCpa();
                if (isLeafAgent()) {
                    initLocalCost();
                    sendMessage(new Message(id, parent, MSG_BACKTRACK, new BacktrackMsg(INFINTY,optRep())));
                }
                else {
                    cpaNext();
                    setPreviousCpa(new HashMap<>(cpa));
                    /*initVariables();
                    if (isOptFull()) {
                        sendMessage(new Message(id, parent, MSG_BACKTRACK, INFINTY));
                    }
                    for (int child : children) {
                        int val = firstFeasibleAssignment(child);
                        if (val < domain.length) {
                            sendCpa(child, val);
                        }
                    }*/
                }
                break;
            }
            case MSG_BACKTRACK:{
                msgSizeCnt++;
                ++msgSearchPart;
                msgSizeCntSearchPart++;
                BacktrackMsg backtrackMsg = (BacktrackMsg)message.getValue();
                int senderId = message.getIdSender();
//                System.out.println(senderId + "->" +  id  + " backtrack ");
                int val = srchVal.get(senderId);
                opt.get(senderId)[val].costStar = backtrackMsg.costStar;
                opt.get(senderId)[val].sendUb = backtrackMsg.receiveUb;
                subtreeLb[val] += backtrackMsg.costStar - lb.get(senderId)[val];
                if (isOptFull(val)) {
                    ub = Integer.min(ub, subtreeLb[val]);
                }
                exploreValue.get(senderId).remove(exploreValue.get(senderId).indexOf(val));
                goNext(senderId);
//                if (isOptFull(val)) {
//                    ub = Integer.min(ub, subtreeLb[val]);
//                }
//                int nextVal = firstFeasibleAssignment(senderId);
//                if (nextVal < domain.length) {
//                    sendCpa(senderId, nextVal);
//                }
//                if(isOptFull()) {
//                    if (isRootAgent()) {
//                        for (int child : children) {
//                            sendMessage(new Message(id, child, MSG_TERMINATE, null));
//                        }
//                        stopProcess();
//                    }
//                    else {
//                        sendMessage(new Message(id, parent, MSG_BACKTRACK, optRep()));
//                    }
//                }
                break;
            }
            case MSG_INFERCTXT:{
                ++ msgContextInferencePart;
//                System.out.println(message.getValue() instanceof BacktrackMsg);
                inferCtxt = (Map)message.getValue();
//                System.out.println(id + " received inference context from parent " + parent + " " + inferCtxt.toString() );
                alloCtxt(inferCtxt);
                if (inferChild.size() == 0 && inferCtxt.size() > 0) {
                    String str = "received ctxt context from " + parent + " with context:" + (inferCtxt);
                    sendCtxtUtil(str);
                }
                break;
            }
            case MSG_CTXTUTIL:{
                int sender  = message.getIdSender();
                CtxtUtil ctxtUtil = (CtxtUtil)message.getValue();
                childCtxtUtils.put(sender, ctxtUtil);
                ++ msgContextInferencePart;
                msgSizeCnt+= ctxtUtil.ndData.data.length;
                msgSizeCntContextInferencePart+= ctxtUtil.ndData.data.length;
                if (equal(childInferCtxt.get(sender), ctxtUtil.ctxt)) {
                    inferChild.remove(sender);
                    if (inferChild.size() == 0 && inferCtxt.size() > 0) {
                        String str = "received ctxt util from " + sender + " with context:" + (childCtxtUtils.get(sender).ctxt);
                        sendCtxtUtil(str);
                    }
                    if (inferCtxt.size() == 0) {
//                        System.out.println(" id " + id + " end context-based inference.");
                    }
                }
                break;
            }
            case MSG_TERMINATE:{
                ++msgSearchPart;
                for (int child : children) {
                    sendMessage(new Message(id, child, MSG_TERMINATE, null));
                }
                stopProcess();
                break;
            }
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

    private void goNext(int childId) {
        int value = firstFeasibleAssignment(childId);
//        if (isRootAgent())
//            System.out.println("ub : " + ub);
        if (isOptFull()){
            if (isRootAgent()){
//                System.out.println("UB:" + localBound());
                for (int child : children)
                    sendMessage(new Message(id,child,MSG_TERMINATE,null));
                stopProcess();
            }
            else{
                backTrack();
            }
        }
        else if (value != -1){
            int sendUb = (ub - subtreeLb[value] + lb.get(childId)[value]);
            if (sendUb > opt.get(childId)[value].sendUb){
                srchVal.put(childId, value);
                Map<Integer,Integer> newCpa = new HashMap<>(cpa);
                newCpa.put(id, value);
                sendMessage(new Message(id, childId, MSG_CPA, new CpaMsg(sendUb, newCpa, collected)));
            }
            else {
//                System.out.println("=======");
                exploreValue.get(childId).removeFirst();
                goNext(childId);
            }
        }
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

    private void backTrack() {
        fillOptHistory();
        int costStar = optRep();
        int receiveUb = INFINTY;
        if ( costStar > ub && optContainsInfinity())
            receiveUb = ub;
        sendMessage(new Message(id,parent,MSG_BACKTRACK,new BacktrackMsg(receiveUb, costStar)));
    }

    public void setPreviousCpa(Map<Integer, Integer> previousCpa) {
        this.previousCpa = previousCpa;
    }

    void sendCtxtUtil(String str) {
        Map<Integer, NDData> ndDataMap = new HashMap<>();
        for (int child : children) {
            if (idleChild.contains(child)) {
                ndDataMap.put(child, childPreUtils.get(child));
            }
            else {
                ndDataMap.put(child, childCtxtUtils.get(child).ndData);
            }
        }
        sendUtil(ndDataMap, inferCtxt);
//        System.out.println(" since " + str+"\n");
    }

    private boolean equal(Map<Integer,Integer> map1, Map<Integer,Integer> map2) {
        Set<Integer> keys1 = new HashSet<>(map1.keySet());
        Set<Integer> keys2 = new HashSet<>(map2.keySet());
        if (keys1.containsAll(keys2) && keys2.containsAll(keys1)) {
            return compatiable(map1, map2);
        }
        else{
            return false;
        }
    }
    private boolean compatiable(Map<Integer,Integer> map1, Map<Integer,Integer> map2) {
        if (map1.size()==0 || map2.size() == 0)
            return false;
        Set<Integer> keys = new HashSet<>(map1.keySet());
        keys.retainAll(map2.keySet());
        for (int i : keys) {
            if (!map1.get(i).equals(map2.get(i)))
                return false;
        }
        return true;
    }

    void initVariables() {
        initLocalCost();
        Map<Integer, Integer> assign = new HashMap<>(cpa);
        for (int i = 0; i < domain.length; ++i) {
            assign.put(id, i);
            subtreeLb[i] = localCost[i];
            for (int child : children) {
//                opt.get(child)[i].costStar = NULL;
                if (childCtxtUtils.containsKey(child) && compatiable(cpa,childCtxtUtils.get(child).ctxt)) {
                    lb.get(child)[i] = childCtxtUtils.get(child).ndData.getValue(assign);
                }
                else {
                    lb.get(child)[i] = childPreUtils.get(child).getValue(assign);
                }
                subtreeLb[i] += lb.get(child)[i];
            }
        }


        Set<Integer> invalidChild = getResetChildren();
        for (int child : invalidChild){
            LinkedList<Integer> tmp = new LinkedList<>();
            for (int i = 0; i < domain.length; ++i) {
                tmp.add(i);
                opt.get(child)[i].sendUb = -1;
                opt.get(child)[i].costStar = NULL;
            }
            exploreValue.put(child, tmp);
        }

        for (int child : children) {
            if (!invalidChild.contains(child)) {
                LinkedList<Integer> tmp = new LinkedList<>();
                for (int i = 0; i < domain.length; i++) {
                    if (opt.get(child)[i].sendUb != INFINTY) {
                        tmp.add(i);
                    }
//                    else
//                        System.out.println("======");
                }
                if (!tmp.isEmpty())
                    exploreValue.put(child, tmp);
//                else
//                    exploreValue.put(child, null);
            }
        }


//        rcvCtxtCnt = new HashSet<>();
//        rcvCtxt = new HashMap<>();
    }

    private Set<Integer> getResetChildren() {
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
        Set<Integer> hitChild = writeOpt(); //fill opt
        Set<Integer> ret = new HashSet<>(childrenToBeReset);
        for (int child : childrenToBeReset) {
            if (hitChild.contains(child))
                ret.remove(child);
        }
        return ret;
    }

    private Set<Integer>writeOpt() {
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

    private int firstFeasibleAssignment(int childId){
        int value = -1;
        while(!exploreValue.get(childId).isEmpty()){
            value = exploreValue.get(childId).getFirst();
            if ( ub - subtreeLb[value] > 0){
                return value;
            }
            opt.get(childId)[value].costStar = INFINTY;
            opt.get(childId)[value].sendUb = ub - subtreeLb[value];
            subtreeLb[value] = INFINTY;
//            System.out.println("=====" + (ub - domainLb(value)));
            exploreValue.get(childId).remove(exploreValue.get(childId).indexOf(value));
        }
        if (exploreValue.get(childId).isEmpty())
            return -1;
        return value;
    }

/*int nextFeasibleAssignment(int child, int val) {
        ++val;
        while (val < domain.length && subtreeLb[val] >= ub) {
            opt.get(child)[val] = INFINTY;
            subtreeLb[val] = INFINTY;
            ++ val;
        }
        return val;
    }*/


    void sendCpa(int child, int val) {
        Map<Integer, Integer> newCpa = new HashMap<>(cpa);
        newCpa.put(id, val);
        srchVal.put(child,val);
        int newub = ub - subtreeLb[val] + lb.get(child)[val];
        sendMessage(new Message(id, child, MSG_CPA, new CpaMsg(newub,newCpa,collected)));
    }

    void computeSi(Map<Integer, NDData> childUtils) {
        Set<Integer> allDim = new HashSet<>();
        allDim.addAll(pseudoParents);
        if (!isRootAgent()) {
            allDim.add(parent);
        }
        childDims = new HashSet<>();
        for (int child : children){
            childDims.addAll(childUtils.get(child).orderedId);
        }
        allDim.addAll(childDims);
        childDims.remove(id);
        allDim.remove(id);

        TreeMap<Integer,Integer> ancLevel = new TreeMap<>();
        for (int i : allDim) {
            ancLevel.put(visited.get(i),i);
        }
        int dimCount = allDim.size() - kp;
        Set<Integer> removeDims = new HashSet<>();
        for (int le : ancLevel.navigableKeySet()){
            int sep = ancLevel.get(le);
            if (allDim.contains(sep)){
                if (dimCount-- <= 0){
                    break;
                }
                removeDims.add(sep);
            }
        }
        si = new HashSet<>(removeDims);
    }

    void sendUtil(Map<Integer, NDData> childUtils, Map<Integer, Integer> assign) {
        Set<Integer> localDim = new HashSet<>();//in local
        Set<Integer> joinDim = new HashSet<>();//from children
        Set<Integer> bothDim = new HashSet<>();//both in child and local

        int ncccs1 = ncccs;
        for (int id : si){
            if (localUtilMap.containsKey(id)){
                if (childDims.contains(id)){
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
        NDData joinUtil = null;
        for (int dim : joinDim){
            for (NDData data : childUtils.values()){
                if (data.containsDim(dim) && !mergedData.contains(data)){
                    if (joinUtil == null){
                        joinUtil = data.copy();
                    }
                    else {
                        joinUtil.merge(data);
                    }
                    mergedData.add(data);
                }
            }
            if (assign.containsKey(dim)) {
                joinUtil = joinUtil.restrict(dim, assign.get(dim));
            }
            else {
                joinUtil = joinUtil.min(dim);
                ncccs += joinUtil.operationCount;
            }
        }
        for (int dim : bothDim){
            NDData util = localUtilMap.get(dim);
            if (joinUtil == null){
                joinUtil = util.copy();
            }
            else {
                joinUtil.merge(util);
            }
            for (NDData data : childUtils.values()){
                if (!mergedData.contains(data) && data.containsDim(dim)){
                    joinUtil.merge(data);
                    mergedData.add(data);
                }
            }
            if (assign.containsKey(dim)) {
                joinUtil = joinUtil.restrict(dim, assign.get(dim));
            }
            else {
                joinUtil = joinUtil.min(dim);
                ncccs += joinUtil.operationCount;
            }
        }
        for (int dim : localDim){
            NDData data;
            if (assign.containsKey(dim)) {
                data = localUtilMap.get(dim).restrict(dim,assign.get(dim));
            }
            else {
                data = localUtilMap.get(dim).min(dim);
                ncccs += data.operationCount;
            }
            if (joinUtil == null){
                joinUtil = data.copy();
            }
            else {
                joinUtil.merge(data);
            }
        }
        for (NDData data : childUtils.values()){
            if (!mergedData.contains(data)){
                if (joinUtil == null){
                    joinUtil = data.copy();
                }
                else {
                    joinUtil.merge(data);
                }
                mergedData.add(data);
            }
        }
        for (int key : localUtilMap.keySet()) {
            if (!si.contains(key)) {
                if (joinUtil == null) {
                    joinUtil = localUtilMap.get(key).copy();
                }
                else {
                    joinUtil.merge(localUtilMap.get(key));
                }
            }
        }
        if (mergedData.size() != childUtils.size()){
            throw new IllegalStateException("error in merged child utility at utility phase");
        }
        joinUtil = joinUtil.min(id);
        ncccs += joinUtil.operationCount;
        sList.addAll(si);
        for (int child : childSi.keySet()) {
            sList.addAll(childSi.get(child));
        }
        int ncccsDiff = (ncccs-ncccs1);
        if (assign.size() == 0) {
            ncccsPreInference += ncccsDiff;
            sendMessage(new Message(id, parent, MSG_PREUTIL, new PreUtilMsg(sList, joinUtil)));
//            System.out.println("id " + id + " - > " + parent + "pre util :" + joinUtil.orderedId + " slist : " + sList);
            t = (int)(Parameter.levelT * sList.size());
//            System.out.println("id:" + id + " " + level + " " + height + " t :" + t + " rate :" + Parameter.levelT);
        }
        else {
            ncccsContextInferencePart += ncccsDiff;
            sendMessage(new Message(id, parent, MSG_CTXTUTIL, new CtxtUtil(assign, joinUtil)));
//            System.out.println("id " + id + " - > " + parent + " context util :" + joinUtil.orderedId + " context : " + assign);
        }
    }

    private void initLocalCost() {

        int cost = 0;
        for (int pp : localUtilMap.keySet()){
            if (costTable.get(pp).value != cpa.get(pp)) {
                for (int i = 0; i < domain.length; i++) {
                    costTable.get(pp).cost[i] = constraintCosts.get(pp)[i][cpa.get(pp)];
                    ncccs++;
                    ncccsSearchPart++;
                }
            }
            costTable.get(pp).value = cpa.get(pp);
        }
        for (int i = 0; i < domain.length; ++i) {
            int tmp = 0;
            for (int pp : costTable.keySet()) {
                tmp += costTable.get(pp).cost[i];
            }
            localCost[i] = tmp;
        }

    }

    private int optRep() {
        int optRet = Integer.MAX_VALUE;
        for (int i = 0; i < domain.length; ++i) {
            optRet = Integer.min(optRet, optRep(i));
        }
        return optRet;
    }

    private int optRep(int valueIndex) {
        int tmp = localCost[valueIndex];
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

    private boolean isOptFull() {
        /*for (int i = 0; i < domain.length; ++i) {
            for (int child : children) {
                if (opt.get(child)[i].costStar == NULL)
                    return false;
            }
        }
        return true;*/
        for (int child : exploreValue.keySet()){
            if (!exploreValue.get(child).isEmpty())
                return false;
        }
        return true;
    }
    private boolean isOptFull(int i) {
        for (int child : children) {
            if (opt.get(child)[i].costStar == NULL)
                return false;
        }
        return true;
    }

    @Override
    public void runFinished() {
        super.runFinished();

        ResultWithPrivacy cycle = new ResultWithPrivacy();
        cycle.setAgentValues(id,0);
        cycle.setMessageSizeCount(msgSizeCnt);

        cycle.setMsgSizeCntSearchPart(msgSizeCntSearchPart);
        cycle.setMsgSizeCntPreInference(msgSizeCntPreInference);
        cycle.setMsgSizeCntContextInferencePart(msgSizeCntContextInferencePart);
        cycle.setNcccsContextInferencePart(ncccsContextInferencePart);
        cycle.setMsgContextInferencePart(msgContextInferencePart);
        cycle.setMsgSearchPart(msgSearchPart);
        cycle.setMsgPreInference(msgPreInference);
        cycle.setCPAMsgCount(CPAMsgCount);

        cycle.setNcccsPreInference(ncccsPreInference);
        cycle.setNcccsSearchPart(ncccsSearchPart);

        if (isRootAgent())
            cycle.setUb(optRep());
        mailer.setResultCycle(id,cycle);
    }

    private class PreUtilMsg {
        Set<Integer> siList;
        NDData data;

        public PreUtilMsg(Set<Integer> siList, NDData data) {
            this.siList = new HashSet<>(siList);
            this.data = data.copy();
        }
    }
    private class CpaMsg{
        int ub;
        Map<Integer, Integer> cpa;
        boolean haveBeenRuled;

        public CpaMsg(int ub, Map<Integer, Integer> cpa, boolean haveBeenRuled) {
            this.ub = ub;
            this.cpa = new HashMap<>(cpa);
            this.haveBeenRuled = haveBeenRuled;
        }
    }
    private class CostList{
        int value;
        int[] cost;

        public CostList() {
            this.value = -10;
            this.cost = new int[domain.length];
        }
    }
    class CtxtUtil{
        Map<Integer,Integer> ctxt;
        NDData ndData;

        public CtxtUtil(Map<Integer, Integer> ctxt, NDData ndData) {
            this.ctxt = new HashMap<>(ctxt);
            this.ndData = ndData.copy();
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
