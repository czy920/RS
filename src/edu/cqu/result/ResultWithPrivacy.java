package edu.cqu.result;

import edu.cqu.result.annotations.AverageField;

public class ResultWithPrivacy extends ResultCycle {
    @AverageField
    protected int totalEntropy;
    @AverageField
    protected int leakedEntropy;
    @AverageField
    protected int ub;
    @AverageField
    protected long CPAMsgCount;
    @AverageField
    protected int maxLen;

    @AverageField
    protected int maxInduceWidth;
    @AverageField
    protected long messageSizeCount;

    @AverageField
    protected long ncccsPreInference;
    @AverageField
    protected long ncccsSearchPart;
    @AverageField
    protected long ncccsContextInferencePart;
    @AverageField
    protected long msgSizeCntPreInference;
    @AverageField
    protected long msgSizeCntSearchPart;
    @AverageField
    protected long msgSizeCntContextInferencePart;
    @AverageField
    protected long msgPreInference;
    @AverageField
    protected long msgSearchPart;
    @AverageField
    protected long msgContextInferencePart;
    @AverageField
    protected int leakedSearchEntropy;
    @AverageField
    protected int leakedInferenceEntropy;

    public int getLeakedSearchEntropy() {
        return leakedSearchEntropy;
    }

    public void setLeakedSearchEntropy(int leakedSearchEntropy) {
        this.leakedSearchEntropy = leakedSearchEntropy;
    }

    public int getLeakedInferenceEntropy() {
        return leakedInferenceEntropy;
    }

    public void setLeakedInferenceEntropy(int leakedInferenceEntropy) {
        this.leakedInferenceEntropy = leakedInferenceEntropy;
    }

    public long getCPAMsgCount() {
        return CPAMsgCount;
    }

    public void setCPAMsgCount(long CPAMsgCount) {
        this.CPAMsgCount = CPAMsgCount;
    }

    public int getTotalEntropy() {
        return totalEntropy;
    }

    public int getLeakedEntropy() {
        return leakedEntropy;
    }

    public long getNcccsPreInference() {
        return ncccsPreInference;
    }

    public void setNcccsPreInference(long ncccsPreInference) {
        this.ncccsPreInference = ncccsPreInference;
    }

    public long getNcccsSearchPart() {
        return ncccsSearchPart;
    }

    public void setNcccsSearchPart(long ncccsSearchPart) {
        this.ncccsSearchPart = ncccsSearchPart;
    }

    public long getNcccsContextInferencePart() {
        return ncccsContextInferencePart;
    }

    public void setNcccsContextInferencePart(long ncccsContextInferencePart) {
        this.ncccsContextInferencePart = ncccsContextInferencePart;
    }

    public long getMsgSizeCntPreInference() {
        return msgSizeCntPreInference;
    }

    public void setMsgSizeCntPreInference(long msgSizeCntPreInference) {
        this.msgSizeCntPreInference = msgSizeCntPreInference;
    }

    public long getMsgSizeCntSearchPart() {
        return msgSizeCntSearchPart;
    }

    public void setMsgSizeCntSearchPart(long msgSizeCntSearchPart) {
        this.msgSizeCntSearchPart = msgSizeCntSearchPart;
    }

    public long getMsgSizeCntContextInferencePart() {
        return msgSizeCntContextInferencePart;
    }

    public void setMsgSizeCntContextInferencePart(long msgSizeCntContextInferencePart) {
        this.msgSizeCntContextInferencePart = msgSizeCntContextInferencePart;
    }

    public long getMsgPreInference() {
        return msgPreInference;
    }

    public void setMsgPreInference(long msgPreInference) {
        this.msgPreInference = msgPreInference;
    }

    public long getMsgSearchPart() {
        return msgSearchPart;
    }

    public void setMsgSearchPart(long msgSearchPart) {
        this.msgSearchPart = msgSearchPart;
    }

    public long getMsgContextInferencePart() {
        return msgContextInferencePart;
    }

    public void setMsgContextInferencePart(long msgContextInferencePart) {
        this.msgContextInferencePart = msgContextInferencePart;
    }

    public int getMaxLen() {
        return maxLen;
    }

    public void setMaxLen(int maxLen) {
        this.maxLen = maxLen;
    }

    public int getMaxInduceWidth() {
        return maxInduceWidth;
    }

    public void setMaxInduceWidth(int maxInduceWidth) {
        this.maxInduceWidth = maxInduceWidth;
    }

    public long getMessageSizeCount() {
        return messageSizeCount;
    }

    public void setMessageSizeCount(long messageSizeCount) {
        this.messageSizeCount = messageSizeCount;
    }

    public int getUb() {
        return ub;
    }

    public void setUb(int ub) {
        this.ub = ub;
    }

    public void setTotalEntropy(int totalEntropy) {
        this.totalEntropy = totalEntropy;
    }


    public double getLossRate(){
        return leakedEntropy * 1.0 / totalEntropy;
    }
    public double getSearchLossRate(){
        return leakedSearchEntropy * 1.0 / totalEntropy;
    }
    public double getInferenceLossRate(){
        return leakedInferenceEntropy * 1.0 / totalEntropy;
    }

    public void setLeakedEntropy(int leakedEntropy) {
        this.leakedEntropy = leakedEntropy;
    }
}
