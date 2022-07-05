package edu.cqu.benchmark.scalefreenetworks;

import edu.cqu.benchmark.AbstractGraph;

import java.util.*;

/**
 * Created by YanChenDeng on 2016/4/20.
 */
public class AsymScaleFreeNetworkGenerator extends ScaleFreeNetworkGenerator {

    public AsymScaleFreeNetworkGenerator(String name, int nbAgent, int domainSize, int minCost, int maxCost, int m1, int m2) {
        super(name, nbAgent, domainSize, minCost, maxCost, m1, m2);
    }

    @Override
    protected String getTuple() {
        StringBuilder stringBuilder = new StringBuilder();
        for (int i = 1; i <= domainSize; i++){
            for (int j = 1; j <= domainSize; j++){
                int cost1 = randomCost(i,j);
                int cost2 = randomCost(j,i);
                stringBuilder.append(cost1 + " " + cost2 + ":");
                stringBuilder.append(i + " " + j + "|");
            }
        }
        stringBuilder.deleteCharAt(stringBuilder.length() - 1);
        return stringBuilder.toString();
    }
}
