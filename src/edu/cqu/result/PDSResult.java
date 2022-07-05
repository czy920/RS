package edu.cqu.result;

import edu.cqu.result.annotations.AverageField;

import java.util.Set;

/**
 * Created by JXQ on 2018/3/4.
 */
public class PDSResult extends ResultAls {
    @AverageField
    protected int triggerCount;
    @AverageField
    protected int acceptedCount;
    @AverageField
    protected double averageAcceptedDistance;
    @AverageField
    protected double averageRejectedDistance;
    @AverageField
    protected double averageCrossDistance;

    public double getAverageAcceptedDistance() {
        return averageAcceptedDistance;
    }

    public void setAverageAcceptedDistance(double averageAcceptedDistance) {
        this.averageAcceptedDistance = averageAcceptedDistance;
    }

    public double getAverageRejectedDistance() {
        return averageRejectedDistance;
    }

    public void setAverageRejectedDistance(double averageRejectedDistance) {
        this.averageRejectedDistance = averageRejectedDistance;
    }

    public double getAverageCrossDistance() {
        return averageCrossDistance;
    }

    public void setAverageCrossDistance(double averageCrossDistance) {
        this.averageCrossDistance = averageCrossDistance;
    }

    public void setTriggerCount(int triggerCount) {
        this.triggerCount = triggerCount;
    }

    public int getTriggerCount() {
        return triggerCount;
    }

    public void setAcceptedCount(int acceptedCount) {
        this.acceptedCount = acceptedCount;
    }

    public int getAcceptedCount() {
        return acceptedCount;
    }
    public double getAcceptedRatio(){
        return acceptedCount == 0 ? 0:triggerCount*1.0/acceptedCount;
    }
}
