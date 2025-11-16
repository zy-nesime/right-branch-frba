/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2025, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.failurebased.alg;

import gnu.trove.list.array.TIntArrayList;
import gnu.trove.map.hash.TObjectIntHashMap;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.search.loop.monitors.IMonitorContradiction;
import org.chocosolver.solver.search.loop.monitors.IMonitorDownBranch;
import org.chocosolver.solver.search.strategy.assignments.DecisionOperatorFactory;
import org.chocosolver.solver.search.strategy.decision.Decision;
import org.chocosolver.solver.search.strategy.decision.DecisionPath;
import org.chocosolver.solver.search.strategy.selectors.values.IntValueSelector;
import org.chocosolver.solver.search.strategy.strategy.AbstractStrategy;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Variable;

import java.util.Random;

/**
 * FRB4 --> FailureBased4(vars, seed, 0)
 * FRBA4 --> FailureBased4(vars, seed, 1)
 */
public class FailureBased4 extends AbstractStrategy<IntVar>
        implements IMonitorContradiction, IMonitorDownBranch {

    private final int varNum;
    private final Random ran;
    private final Solver solver;
    private final TIntArrayList bests = new TIntArrayList();
    private final TIntArrayList failureQueue = new TIntArrayList();
    private final IntValueSelector valueSelector;
    private int currentVarIndex = -1;
    private long maxFailLength = 0;
    private boolean isContradiction = false;
    private final double failureBoundsFactorAlpha;
    private final double[] failures;
    private final double[] assignTimes;
    private final double[] lastFailure;
    private final TObjectIntHashMap<Variable> varToIndex;

    public FailureBased4(IntVar[] vars, IntValueSelector valueSelector, long seed,
            double failureBoundsFactorAlpha) {
        super(vars);
        ran = new Random(seed);
        solver = vars[0].getModel().getSolver();
        this.valueSelector = valueSelector;
        varNum = vars.length;
        varToIndex = new TObjectIntHashMap<Variable>(varNum); // 一次性分配，避免扩容时间

        this.failureBoundsFactorAlpha = failureBoundsFactorAlpha;

        failures = new double[varNum];
        lastFailure = new double[varNum];
        assignTimes = new double[varNum];

        for (int i = 0; i < varNum; i++) {
            failures[i] = 1;
            assignTimes[i] = 1;
        }

        for (int i = 0; i < vars.length; i++) {
            varToIndex.put(vars[i], i);
        }
    }

    @Override
    public Decision<IntVar> getDecision() {
        IntVar best = null;
        bests.resetQuick();
        double w = Double.NEGATIVE_INFINITY;
        for (int idx = 0; idx < varNum; idx++) {
            int dsize = vars[idx].getDomainSize();
            if (dsize > 1) {
                double weight = weight(idx, dsize);
                if (w < weight) {
                    bests.resetQuick();
                    bests.add(idx);
                    w = weight;
                } else if (w == weight) {
                    bests.add(idx);
                }
            }
        }
        if (!bests.isEmpty()) {
            best = vars[bests.get(ran.nextInt(bests.size()))];

        }
        return computeDecision(best);
    }

    @Override
    public Decision<IntVar> computeDecision(IntVar var) {
        if (var == null || var.isInstantiated()) {
            return null;
        }
        int currentVal = valueSelector.selectValue(var);
        return solver.getDecisionPath().makeIntDecision(var,
                DecisionOperatorFactory.makeIntEq(),
                currentVal);
    }

    @Override
    public void beforeDownBranch(boolean left) {
        isContradiction = false;
        DecisionPath decisionPath = solver.getDecisionPath();
        Variable v = decisionPath.getLastDecision().getDecisionVariable();
        currentVarIndex = varToIndex.get(v);

        if (left) {
            failureQueue.resetQuick();

            maxFailLength = 1; // the last decision is add to decision path, and it could cause a failure. So
                               // the initial value is 1.
            for (int i = 1; i < decisionPath.size(); i++) {
                if (decisionPath.getDecision(i).hasNext()) {
                    maxFailLength++;
                }
            }

            assignTimes[currentVarIndex] += 1;

        }

    }

    public void onContradiction(ContradictionException cex) {
        if (cex.c instanceof Propagator<?>) {
            isContradiction = true;
            lastFailure[currentVarIndex] = solver.getFailCount();
            failureQueue.add(currentVarIndex);
        }
    }

    @Override
    public void afterDownBranch(boolean left) {
        if (!isContradiction && !failureQueue.isEmpty()) {
            failures[failureQueue.get(0)] += (double) failureQueue.size() / maxFailLength;
        }

    }

    protected double weight(int id, int ds) {
        double finalScore = 0;
        double failureBoundsFactor = 1 / (solver.getFailCount() - lastFailure[id] + 1);
        double failure = failures[id];
        double afl = failure / assignTimes[id];
        finalScore = (afl + this.failureBoundsFactorAlpha * failureBoundsFactor) / ds;
        return finalScore;
    }

    @Override
    public boolean init() {
        if (!solver.getSearchMonitors().contains(this)) {
            solver.plugMonitor(this);
        }
        return true;
    }

    @Override
    public void remove() {
        if (solver.getSearchMonitors().contains(this)) {
            solver.unplugMonitor(this);
        }
    }
}
