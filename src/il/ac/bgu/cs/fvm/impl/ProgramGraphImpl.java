package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;

import java.util.*;

/**
 * Created by Elad Rapaport on 19-Nov-18.
 */
public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {

    private Map<L, Boolean> loc = new HashMap<L, Boolean>();
    private Set<List<String>> vars = new HashSet<>();
    private Set<PGTransition<L, A>> transitions = new HashSet<>();
    private String name;

    @Override
    public void addInitalization(List<String> init) {
        vars.add(init);
    }

    @Override
    public void setInitial(L location, boolean isInitial) {
        loc.put(location, isInitial);
    }

    @Override
    public void addLocation(L l) {
        loc.put(l, false);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        transitions.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return vars;
    }

    @Override
    public Set<L> getInitialLocations() {
        Set<L> ans = new HashSet<>();
        loc.forEach((key,value) -> {if(value) ans.add(key);});
        return ans;
    }

    @Override
    public Set<L> getLocations() {
        Set<L> ans = new HashSet<>();
        loc.forEach((key,value) -> {ans.add(key);});
        return ans;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return transitions;
    }

    @Override
    public void removeLocation(L l) {
        loc.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        transitions.remove(t);
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
