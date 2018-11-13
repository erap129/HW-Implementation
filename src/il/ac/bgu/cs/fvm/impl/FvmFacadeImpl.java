package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its 
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {
	
	public FvmFacadeImpl() {
	}
	
    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
    	return new TransitionSystemImpl<S, A, P>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
       for (Transition<S, A> t1: ts.getTransitions()){
    	   if(post(ts, t1.getFrom(), t1.getAction()).size() > 1)
    	   	return false;
       }
       return ts.getInitialStates().size() == 1;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
		for(S state1: ts.getInitialStates()){
			int count = 0;
			for(S state2: ts.getInitialStates())
				if(ts.getLabelingFunction().get(state1).equals(ts.getLabelingFunction().get(state2))) // check if equals works..........
					count++;
			if(count > 1)
				return false;
		}

		for (S state1 : ts.getStates()){
			for (S state2 : post(ts, state1)){
				int count = 0;
				for (S state3 : post(ts, state1)){
					if(ts.getLabelingFunction().get(state2).equals(ts.getLabelingFunction().get(state3))) // check if equals works..........
						count++;
				}
				if(count > 1)
					return false;
			}
		}
		return true;
    }


    
    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isExecution
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if(e.size() == 1)
        	return true;
        S state1 = e.head();
        AlternatingSequence<A, S> e_op = e.tail();
        while(true){
        	A action = e_op.head();
        	e = e_op.tail();
        	S state2 = e.head();
        	if(!checkTransition(state1, action, state2, ts))
        		return false;
        	if(e.size() == 1)
        		return true;
        	state1 = state2;
        	e_op = e.tail();
        }
    }
    
    private <S, A, P> boolean checkTransition(S state1, A action, S state2, TransitionSystem<S, A, P> ts){
    	for(Transition<S, A> t : ts.getTransitions()){
    		if(t.getFrom().equals(state1) && t.getAction().equals(action) && t.getTo().equals(state2))
    			return true;
    	}
    	return false;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return ts.getInitialStates().contains(e.head()) && isExecution(ts, e);
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return post(ts, e.last()).size() == 0 && isExecution(ts, e);
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
    	return post(ts, s).size() == 0;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) throws StateNotFoundException{
    	if(!ts.getStates().contains(s))
    		throw new StateNotFoundException(s);
    	Set<S> res = new HashSet<S>(); 
		for (Transition<S, ?> trans : ts.getTransitions())
			if (trans.getFrom().equals(s))
				res.add(trans.getTo());				
		return res;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
    	Set<S> res = new HashSet<S>(); 
    	for(S state : c)
    		res.addAll(post(ts, state));
    	return res;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
    	Set<S> res = new HashSet<S>(); 
		for(S state : post(ts, s))
			if(checkTransition(s, a, state, ts))
				res.add(state);
    	return res;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
    	Set<S> res = new HashSet<S>(); 
    	for(S state : c)
    		res.addAll(post(ts, state, a));
    	return res;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) throws StateNotFoundException {
		if(!ts.getStates().contains(s))
			throw new StateNotFoundException(s);
    	Set<S> res = new HashSet<S>(); 
		for (Transition<S, ?> trans : ts.getTransitions())
			if (trans.getTo().equals(s))
				res.add(trans.getFrom());				
		return res;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
    	Set<S> res = new HashSet<S>(); 
    	for(S state : c)
    		res.addAll(pre(ts, state));
    	return res;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
    	Set<S> res = new HashSet<S>(); 
		for(S state : pre(ts, s))
			if(checkTransition(state, a, s, ts))
				res.add(state);
    	return res;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
    	Set<S> res = new HashSet<S>(); 
    	for(S state : c)
    		res.addAll(pre(ts, state, a));
    	return res;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
    	Set<S> res = new HashSet<S>(); 
    	for(S state : ts.getInitialStates())
    		addAllReachable(res, ts, state);
    	return res;
    }
    
    private <S, A> void addAllReachable(Set<S> res, TransitionSystem<S, A, ?> ts, S state){
    	for(S s : post(ts, state)){
    		if(res.add(s))
    			addAllReachable(res, ts, s);
    	}
    }

    private <S1, S2> Pair<S1, S2> getStatePair(TransitionSystem<Pair<S1, S2>, ?, ?> ts, S1 s1, S2 s2){
    	for(Pair <S1, S2> state_pair : ts.getStates())
    		if(state_pair.first.equals(s1) && state_pair.second.equals(s2))
    			return state_pair;
    	return null;
    }
    
	@Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
		TransitionSystem<Pair<S1, S2>, A, P> ts = new TransitionSystemImpl<Pair<S1, S2>, A, P>(); 
		for(P prop : ts1.getAtomicPropositions())
			ts.addAtomicProposition(prop);
		for(P prop : ts2.getAtomicPropositions())
			ts.addAtomicProposition(prop);
		for(A act : ts1.getActions())
			ts.addAction(act);
		for(A act : ts2.getActions())
			ts.addAction(act);
		for(S1 s1 : ts1.getStates())
			for(S2 s2 : ts2.getStates()){
				Pair<S1, S2> state_pair = new Pair<S1, S2>(s1, s2);
				ts.addState(state_pair);
				Set<P> all_props = ts1.getLabel(s1);
				all_props.addAll(ts2.getLabel(s2));
				for(P prop : all_props)
					ts.addToLabel(state_pair, prop);
				if(ts1.getInitialStates().contains(s1) && ts2.getInitialStates().contains(s2))
					ts.setInitial(state_pair, true);
			}
		for(Transition<S1, A> t : ts1.getTransitions()){
			for(Pair<S1, S2> state_pair : ts.getStates()){
				if(t.getFrom().equals(state_pair.first)){
					for(Pair<S1, S2> to_state_pair : ts.getStates())
						if(to_state_pair.first.equals(t.getTo())){
							ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, state_pair.first, state_pair.second), t.getAction(),
									getStatePair(ts, to_state_pair.first, to_state_pair.second)));
						}		
				}
				if(t.getFrom().equals(state_pair.second)){
					for(Pair<S1, S2> to_state_pair : ts.getStates())
						if(to_state_pair.second.equals(t.getTo())){
							ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, state_pair.first, state_pair.second), t.getAction(),
									getStatePair(ts, to_state_pair.first, to_state_pair.second)));
						}		
				}
			}
		}
		return ts;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
    	TransitionSystem<Pair<S1, S2>, A, P> ts = new TransitionSystemImpl<Pair<S1, S2>, A, P>(); 
		for(P prop : ts1.getAtomicPropositions())
			ts.addAtomicProposition(prop);
		for(P prop : ts2.getAtomicPropositions())
			ts.addAtomicProposition(prop);
		for(A act : ts1.getActions())
			ts.addAction(act);
		for(A act : ts2.getActions())
			ts.addAction(act);
		for(S1 s1 : ts1.getStates())
			for(S2 s2 : ts2.getStates()){
				Pair<S1, S2> state_pair = new Pair<S1, S2>(s1, s2);
				ts.addState(state_pair);
				Set<P> all_props = ts1.getLabel(s1);
				all_props.addAll(ts2.getLabel(s2));
				for(P prop : all_props)
					ts.addToLabel(state_pair, prop);
				if(ts1.getInitialStates().contains(s1) && ts2.getInitialStates().contains(s2))
					ts.setInitial(state_pair, true);
			}
		for(Transition<S1, A> t : ts1.getTransitions()){
			for(Pair<S1, S2> state_pair : ts.getStates()){
				if(t.getFrom().equals(state_pair.first)){
					for(Pair<S1, S2> to_state_pair : ts.getStates())
						if(to_state_pair.first.equals(t.getTo())){
							if(!handShakingActions.contains(t.getAction()))
								ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, state_pair.first, state_pair.second), t.getAction(),
										getStatePair(ts, to_state_pair.first, to_state_pair.second)));
						}		
				}
				if(t.getFrom().equals(state_pair.second)){
					for(Pair<S1, S2> to_state_pair : ts.getStates())
						if(to_state_pair.second.equals(t.getTo())){
							if(!handShakingActions.contains(t.getAction()))
								ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, state_pair.first, state_pair.second), t.getAction(),
										getStatePair(ts, to_state_pair.first, to_state_pair.second)));
						}		
				}
			}
		}
		for(A action : handShakingActions)
			for(Transition<S1, A> t1 : ts1.getTransitions())
				if(t1.getAction().equals(action))
					for(Transition<S2, A> t2 : ts2.getTransitions())
						if(t2.getAction().equals(action))
							ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, t1.getFrom(), t2.getFrom()), action,
									getStatePair(ts, t1.getTo(), t2.getTo())));

		return ts;
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createProgramGraph
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }
   
}
