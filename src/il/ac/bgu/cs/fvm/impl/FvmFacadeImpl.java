package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import org.svvrl.goal.core.util.Lists;

import javax.naming.event.ObjectChangeListener;
import java.io.InputStream;
import java.util.*;
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
        return isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
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
    	checkState(ts, state1);
		checkState(ts, state2);
		checkAction(ts, action);
		for(Transition<S, A> t : ts.getTransitions()){
    		if(t.getFrom().equals(state1) && t.getAction().equals(action) && t.getTo().equals(state2))
    			return true;
    	}
    	return false;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return ts.getInitialStates().contains(e.head()) && isExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return post(ts, e.last()).size() == 0 && isExecutionFragment(ts, e);
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
    	return post(ts, s).size() == 0;
    }

    private <L, A> Set<L> post(ProgramGraph<L, A> pg, L loc){
        Set<L> res = new HashSet<>();
        for (PGTransition<L, A> trans : pg.getTransitions())
            if (trans.getFrom().equals(loc))
                res.add(trans.getTo());
        return res;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) throws StateNotFoundException{
    	checkState(ts, s);
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
		checkState(ts, s);
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
    	res.addAll(ts.getInitialStates());
    	return res;
    }

    private <L, A> Set<L> reach(ProgramGraph<L, A> pg){
        Set<L> res = new HashSet<>();
        for(L loc : pg.getInitialLocations())
            addAllReachable(res, pg, loc);
        res.addAll(pg.getInitialLocations());
        return res;
    }
    
    private <S, A> void addAllReachable(Set<S> res, TransitionSystem<S, A, ?> ts, S state){
    	for(S s : post(ts, state)){
    		if(res.add(s))
    			addAllReachable(res, ts, s);
    	}
    }

    private <L, A> void addAllReachable(Set<L> res, ProgramGraph<L, A> pg, L loc){
        for(L l : post(pg, loc)){
            if(res.add(l))
                addAllReachable(res, pg, l);
        }
    }

    private <S1, S2> Pair<S1, S2> getStatePair(TransitionSystem<Pair<S1, S2>, ?, ?> ts, S1 s1, S2 s2){
    	for(Pair <S1, S2> state_pair : ts.getStates())
    		if(state_pair.first.equals(s1) && state_pair.second.equals(s2))
    			return state_pair;
    	return null;
    }

	private <L1, L2> Pair<L1, L2> getLocPair(ProgramGraph<Pair<L1, L2>, ?> pg, L1 l1, L2 l2){
		for(Pair <L1, L2> loc_pair : pg.getLocations())
			if(loc_pair.first.equals(l1) && loc_pair.second.equals(l2))
				return loc_pair;
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

		for(Transition<S1, A> t : ts1.getTransitions())
			for(Pair<S1, S2> state_pair : ts.getStates())
				if(t.getFrom().equals(state_pair.first))
					for(Pair<S1, S2> to_state_pair : ts.getStates())
						if(to_state_pair.first.equals(t.getTo()) && state_pair.second.equals(to_state_pair.second))
							ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, state_pair.first, state_pair.second), t.getAction(),
									getStatePair(ts, to_state_pair.first, to_state_pair.second)));

		for(Transition<S2, A> t : ts2.getTransitions())
			for (Pair<S1, S2> state_pair : ts.getStates())
				if (t.getFrom().equals(state_pair.second))
					for (Pair<S1, S2> to_state_pair : ts.getStates())
						if (to_state_pair.second.equals(t.getTo()) && state_pair.first.equals(to_state_pair.first))
							ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, state_pair.first, state_pair.second), t.getAction(),
									getStatePair(ts, to_state_pair.first, to_state_pair.second)));

		Set<Pair<S1, S2>> reach_states = reach(ts);
		for(Pair<S1, S2> state_pair : ts.getStates())
			if(!reach_states.contains(state_pair)) {
				for (Transition<Pair<S1, S2>, A> t : ts.getTransitions())
					if (t.getFrom().equals(state_pair) || t.getTo().equals(state_pair))
						ts.removeTransition(t);
				ts.removeState(state_pair);
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

		for(Transition<S1, A> t : ts1.getTransitions())
			for(Pair<S1, S2> state_pair : ts.getStates())
				if(t.getFrom().equals(state_pair.first))
					for(Pair<S1, S2> to_state_pair : ts.getStates())
						if(to_state_pair.first.equals(t.getTo()))
							if(!handShakingActions.contains(t.getAction()) && state_pair.second.equals(to_state_pair.second))
								ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, state_pair.first, state_pair.second), t.getAction(),
										getStatePair(ts, to_state_pair.first, to_state_pair.second)));

		for(Transition<S2, A> t : ts2.getTransitions())
			for (Pair<S1, S2> state_pair : ts.getStates())
				if (t.getFrom().equals(state_pair.second))
					for (Pair<S1, S2> to_state_pair : ts.getStates())
						if (to_state_pair.second.equals(t.getTo()))
							if (!handShakingActions.contains(t.getAction()) && state_pair.first.equals(to_state_pair.first))
								ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, state_pair.first, state_pair.second), t.getAction(),
										getStatePair(ts, to_state_pair.first, to_state_pair.second)));

		for(A action : handShakingActions)
			for(Transition<S1, A> t1 : ts1.getTransitions())
				if(t1.getAction().equals(action))
					for(Transition<S2, A> t2 : ts2.getTransitions())
						if(t2.getAction().equals(action))
							ts.addTransition(new Transition<Pair<S1, S2>, A>(getStatePair(ts, t1.getFrom(), t2.getFrom()), action,
									getStatePair(ts, t1.getTo(), t2.getTo())));

		Set<Pair<S1, S2>> reach_states = reach(ts);
		for(Pair<S1, S2> state_pair : ts.getStates())
			if(!reach_states.contains(state_pair)) {
				for (Transition<Pair<S1, S2>, A> t : ts.getTransitions())
					if (t.getFrom().equals(state_pair) || t.getTo().equals(state_pair))
						ts.removeTransition(t);
				ts.removeState(state_pair);
			}

		return ts;
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
		ProgramGraph<Pair<L1, L2>, A> pg = new ProgramGraphImpl<>();
		for(List<String> init1 : pg1.getInitalizations())
			for(List<String> init2 : pg2.getInitalizations()) {
				List<String> combinedInit = new LinkedList<>();
				combinedInit.addAll(init1);
				combinedInit.addAll(init2);
				pg.addInitalization(combinedInit);
			}
		for(L1 l1 : pg1.getLocations())
			for(L2 l2 : pg2.getLocations()){
				Pair<L1, L2> loc_pair = new Pair<>(l1, l2);
				pg.addLocation(loc_pair);
				if(pg1.getInitialLocations().contains(l1) && pg2.getInitialLocations().contains(l2))
					pg.setInitial(loc_pair, true);
			}

		for(PGTransition<L1, A> t : pg1.getTransitions())
			for(Pair<L1, L2> loc_pair : pg.getLocations())
				if(t.getFrom().equals(loc_pair.first))
					for(Pair<L1, L2> to_loc_pair : pg.getLocations())
						if(to_loc_pair.first.equals(t.getTo()) && loc_pair.second.equals(to_loc_pair.second))
							pg.addTransition(new PGTransition<>(getLocPair(pg, loc_pair.first, loc_pair.second), t.getCondition(),
									t.getAction(), getLocPair(pg, to_loc_pair.first, to_loc_pair.second)));

		for(PGTransition<L2, A> t : pg2.getTransitions())
			for(Pair<L1, L2> loc_pair : pg.getLocations())
				if(t.getFrom().equals(loc_pair.second))
					for(Pair<L1, L2> to_loc_pair : pg.getLocations())
						if(to_loc_pair.second.equals(t.getTo()) && loc_pair.first.equals(to_loc_pair.first))
							pg.addTransition(new PGTransition<>(getLocPair(pg, loc_pair.first, loc_pair.second), t.getCondition(),
									t.getAction(), getLocPair(pg, to_loc_pair.first, to_loc_pair.second)));

		return pg;
    }

	private boolean[] convertToBinary(int no, int num_of_inputs){
		boolean container[] = new boolean[num_of_inputs];
		int i = 1;
		while (no > 0){
			container[container.length - i] = no%2 != 0;
			i++;
			no = no/2;
		}
		return container;
	}

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
		TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> res = new TransitionSystemImpl<>();
		for(String x : c.getInputPortNames())
			res.addAtomicProposition(x);
		for(String r : c.getRegisterNames())
			res.addAtomicProposition(r);
		for(String y : c.getOutputPortNames())
			res.addAtomicProposition(y);
		for(int i=0; i<Math.pow(2, c.getInputPortNames().size()); i++){
			Set<String> aps = new HashSet<>();
    		Map<String, Boolean> xs = new HashMap<>();
			boolean[] bin_array_x = convertToBinary(i, c.getInputPortNames().size());
			String[] input_arr_x = c.getInputPortNames().toArray(new String[c.getInputPortNames().size()]);
			for(int j=0; j<bin_array_x.length; j++) {
				xs.put(input_arr_x[j], bin_array_x[j]);
				if(bin_array_x[j])
					aps.add(input_arr_x[j]);
			}
			res.addAction(xs);
			for(int k=0; k<Math.pow(2, c.getRegisterNames().size()); k++) {
				Map<String, Boolean> rs = new HashMap<>();
				boolean[] bin_array_reg = convertToBinary(k, c.getInputPortNames().size());
				String[] input_arr_reg = c.getRegisterNames().toArray(new String[c.getRegisterNames().size()]);
				for (int l = 0; l < bin_array_reg.length; l++) {
					rs.put(input_arr_reg[l], bin_array_reg[l]);
					if (bin_array_reg[l])
						aps.add(input_arr_reg[l]);
				}
				Map<String, Boolean> outputs = c.computeOutputs(xs, rs);
				outputs.forEach((key,value) -> {if(value) aps.add(key); });
				Pair<Map<String, Boolean>, Map<String, Boolean>> curr_state = new Pair<>(xs, rs);
				res.addState(curr_state);
				if(k == 0)
					res.setInitial(curr_state, true);
				for(String ap : aps)
					res.addToLabel(curr_state, ap);
				aps.removeAll(c.getRegisterNames());
				aps.removeAll(c.getOutputPortNames());
			}
		}
		for(Pair<Map<String, Boolean>, Map<String, Boolean>> state : res.getStates()){
			for(int i=0; i<Math.pow(2, c.getInputPortNames().size()); i++){
				Map<String, Boolean> xs = new HashMap<>();
				boolean[] bin_array_x = convertToBinary(i, c.getInputPortNames().size());
				String[] input_arr_x = c.getInputPortNames().toArray(new String[c.getInputPortNames().size()]);
				for(int j=0; j<bin_array_x.length; j++) {
					xs.put(input_arr_x[j], bin_array_x[j]);
				}
				Map<String, Boolean> registers = c.updateRegisters(state.getFirst(), state.getSecond());
				Pair<Map<String, Boolean>, Map<String, Boolean>> to_state = getStatePair(res, xs, registers);
				Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> t = new Transition<>(
						state, xs, to_state);
				res.addTransition(t);
			}
		}

		Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> reach_states = reach(res);
		for(Pair<Map<String, Boolean>, Map<String, Boolean>> state_pair : res.getStates())
			if(!reach_states.contains(state_pair)) {
				for (Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> t : res.getTransitions())
					if (t.getFrom().equals(state_pair) || t.getTo().equals(state_pair))
						res.removeTransition(t);
				Set<Object> labels = res.getLabel(state_pair);
				for(Object label : labels)
					res.removeLabel(state_pair, label);
				res.removeState(state_pair);
			}

		return res;
    }

	private <L, A> void addAllTransitions(ChannelSystem<L, A> cs, TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts, Set<Pair<List<L>, Map<String, Object>>> allStates,
										  Set<Pair<List<L>, Map<String, Object>>> levelStates, ActionDef csActionDef, ActionDef pgActionDef, ConditionDef condDef) {
		Set<Pair<List<L>, Map<String, Object>>> recursionStates = new HashSet<>();
		for(Pair<List<L>, Map<String, Object>> curr_state : levelStates){
			boolean found = false;
			for(Pair<List<L>, Map<String, Object>> state : allStates)
				if(curr_state.equals(state))
					found = true;
			if (found)
				continue;
			allStates.add(curr_state);
			List<L> curr_loc = curr_state.first;
			for(int pgnum = 0; pgnum < cs.getProgramGraphs().size(); pgnum++){
				ProgramGraph<L, A> pg = cs.getProgramGraphs().get(pgnum);
				for(PGTransition<L, A> t : pg.getTransitions()) {
					if (t.getFrom().equals(curr_loc.get(pgnum)) && condDef.evaluate(curr_state.second, t.getCondition())){
//						&& pgActionDef.effect(curr_state.second, t.getAction()) != null) {
						if(!t.getAction().toString().startsWith("_") && pgActionDef.effect(curr_state.second, t.getAction()) != null){
							List<L> newLocs = new LinkedList<>(curr_loc);
							newLocs.set(pgnum, t.getTo());
							Pair<List<L>, Map<String, Object>> to_state = new Pair<>(newLocs, pgActionDef.effect(curr_state.second, t.getAction()));
							ts.addState(to_state);
							Transition<Pair<List<L>, Map<String, Object>>, A> state_trans = new Transition<>(
									curr_state, t.getAction(), to_state
							);
							ts.addTransition(state_trans);
							for(int i=0; i<curr_state.first.size(); i++)
								if(i != pgnum)
									ts.addToLabel(to_state, curr_state.first.get(i).toString());
							ts.addAtomicProposition(t.getTo().toString());
							ts.addToLabel(to_state, t.getTo().toString());
							to_state.getSecond().forEach((key, value) -> {
								ts.addAtomicProposition(key + " = " + value);
							});
							Iterator it = to_state.getSecond().entrySet().iterator();
							while (it.hasNext()) {
								Map.Entry pair = (Map.Entry)it.next();
								ts.addToLabel(to_state, pair.getKey() + " = " + pair.getValue());
							}
							recursionStates.add(to_state);
						}
						else{ // handshake operation
							for(int pgnum2 = 0; pgnum2 < cs.getProgramGraphs().size(); pgnum2++){
								ProgramGraph<L, A> pg2 = cs.getProgramGraphs().get(pgnum2);
								for(PGTransition<L, A> t2 : pg2.getTransitions()) {
									if (t2.getFrom().equals(curr_loc.get(pgnum2))){
										String[] t1Act = t.getAction().toString().split("\\?|!");
										String[] t2Act = t2.getAction().toString().split("\\?|!");
										if(pgnum != pgnum2 && t1Act[0].equals(t2Act[0]) && t.getAction().toString().startsWith("_") && t2.getAction().toString().startsWith("_") &&
												((t.getAction().toString().contains("?") && t2.getAction().toString().contains("!"))
														|| (t2.getAction().toString().contains("?") && t.getAction().toString().contains("!")))
												) {
											List<L> newLocs = new LinkedList<>(curr_loc);
											newLocs.set(pgnum, t.getTo());
											newLocs.set(pgnum2, t2.getTo());
											A combinedAction = (A)(t.getAction() + "|" + t2.getAction());
											ts.addAction(combinedAction);
											Pair<List<L>, Map<String, Object>> to_state = new Pair<>(newLocs, csActionDef.effect(curr_state.second, combinedAction));
											ts.addState(to_state);
											Transition<Pair<List<L>, Map<String, Object>>, A> state_trans = new Transition<>(
													curr_state, combinedAction, to_state
											);
											ts.addTransition(state_trans);
											for (int i = 0; i < curr_state.first.size(); i++)
												if (i != pgnum && i != pgnum2)
													ts.addToLabel(to_state, curr_state.first.get(i).toString());
											ts.addAtomicProposition(t.getTo().toString());
											ts.addToLabel(to_state, t.getTo().toString());
											ts.addAtomicProposition(t2.getTo().toString());
											ts.addToLabel(to_state, t2.getTo().toString());
											to_state.getSecond().forEach((key, value) -> {
												ts.addAtomicProposition(key + " = " + value);
											});
											Iterator it = to_state.getSecond().entrySet().iterator();
											while (it.hasNext()) {
												Map.Entry pair = (Map.Entry) it.next();
												ts.addToLabel(to_state, pair.getKey() + " = " + pair.getValue());
											}
											recursionStates.add(to_state);
										}
									}
								}
							}
						}
					}
				}
			}
		}
		if(recursionStates.size() > 0)
			addAllTransitions(cs, ts, allStates, recursionStates, csActionDef, pgActionDef, condDef);
	}

    private <L, A> void addAllTransitions(ProgramGraph<L, A> pg, TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts,
										  L curr_loc, Pair<L, Map<String, Object>> curr_state, ActionDef actiondef, ConditionDef conditionDef,
										  Set<Pair<L, Map<String, Object>>> allStates){

		List<L> recursionLocs = new LinkedList<>();
		List<Pair<L, Map<String, Object>>> recursionStates = new LinkedList<>();
		for(PGTransition<L, A> t : pg.getTransitions()){
			if(t.getFrom().equals(curr_loc) && conditionDef.evaluate(curr_state.second, t.getCondition())) {
				Pair<L, Map<String, Object>> to_state = new Pair<>(t.getTo(), actiondef.effect(curr_state.second, t.getAction()));
				ts.addState(to_state);
				Transition<Pair<L, Map<String, Object>>, A> state_trans = new Transition<>(
						curr_state, t.getAction(), to_state
				);
				ts.addTransition(state_trans);
				ts.addAtomicProposition(t.getTo().toString());
				ts.addToLabel(to_state, t.getTo().toString());
				to_state.getSecond().forEach((key, value) -> {ts.addAtomicProposition(key + " = " + value);});
				Iterator it = to_state.getSecond().entrySet().iterator();
				while (it.hasNext()) {
					Map.Entry pair = (Map.Entry)it.next();
					ts.addToLabel(to_state, pair.getKey() + " = " + pair.getValue());
				}
				recursionLocs.add(t.getTo());
				recursionStates.add(to_state);
			}
		}
		for(int i=0; i<recursionLocs.size(); i++){
			boolean found = false;
			for(Pair<L, Map<String, Object>> state : allStates)
				if(state.toString().equals(recursionStates.get(i).toString()))
					found = true;
			if(!found){
				allStates.add(recursionStates.get(i));
				addAllTransitions(pg, ts, recursionLocs.get(i), recursionStates.get(i), actiondef, conditionDef, allStates);
			}
		}
	}

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = new TransitionSystemImpl<>();
		for(PGTransition<L, A> t : pg.getTransitions())
			ts.addAction(t.getAction());
		for(L loc : pg.getInitialLocations())
			for (List<String> ass : pg.getInitalizations()) {
				Map<String, Object> var_inits = new HashMap<>();
				for (String s : ass) {
					String[] var_val = s.split(":=");
					var_inits.put(var_val[0], Integer.parseInt(var_val[1]));
				}
				Pair<L, Map<String, Object>> state = new Pair<>(loc, var_inits);
				ts.addState(state);
				ts.addAtomicProposition(loc.toString());
				ts.addToLabel(state, loc.toString());
				state.getSecond().forEach((key, value) -> {ts.addAtomicProposition(key + " = " + value);
															ts.addToLabel(state, key + " = " + value);});
				Pair<L, Map<String, Object>> curr_state = state;
				L curr_loc = loc;
				addAllTransitions(pg, ts, curr_loc, curr_state, actionDefs.iterator().next(), conditionDefs.iterator().next(),
						new HashSet<Pair<L, Map<String, Object>>>());
				ts.setInitial(state, true);
			}
		return ts;
    }

    private <L> Set<List<L>> cartesianProduct(int index, List<Set<L>> allLocs){
    	Set<List<L>> ret = new HashSet<>();
    	if(index == allLocs.size())
    		ret.add(new LinkedList<L>());
    	else{
    		for(L loc : allLocs.get(index))
				for(List<L> list : cartesianProduct(index+1, allLocs)){
					list.add(loc);
					ret.add(list);
				}
		}
    	return ret;
	}

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
		TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts = new TransitionSystemImpl<>();
		List<Set<L>> allLocs = new LinkedList<>();
		List<Map<String, Object>> all_inits = new LinkedList<>();
		for(ProgramGraph<L, A> pg : cs.getProgramGraphs()) {
			for (PGTransition<L, A> t : pg.getTransitions())
				ts.addAction(t.getAction());
			allLocs.add(pg.getInitialLocations());
			for (List<String> ass : pg.getInitalizations()) {
				Map<String, Object> var_inits = new HashMap<>();
				for (String s : ass) {
					String[] var_val = s.split(":=");
					var_inits.put(var_val[0], Integer.parseInt(var_val[1]));
				}
				all_inits.add(var_inits);
			}
		}
		Set<List<L>> initalLocs = cartesianProduct(0, allLocs);
		for(List<L> l : initalLocs)
			Collections.reverse(l);
		Set<Pair<List<L>, Map<String, Object>>> initialStates = new HashSet<>();
		for(List<L> initLoc: initalLocs)
			if(all_inits.size() > 0)
				for(Map<String, Object> var_inits : all_inits){
					Pair<List<L>, Map<String, Object>> state = new Pair<>(initLoc, var_inits);
					ts.addState(state);
					initLoc.forEach((loc) -> {ts.addAtomicProposition(loc.toString()); ts.addToLabel(state, loc.toString());});
					var_inits.forEach((key, value) -> {ts.addAtomicProposition(key + " = " + value);
						ts.addToLabel(state, key + " = " + value);});
					ts.setInitial(state, true);
				}
			else{
				Pair<List<L>, Map<String, Object>> state = new Pair<>(initLoc, new HashMap<>());
				ts.addState(state);
				initLoc.forEach((loc) -> {ts.addAtomicProposition(loc.toString()); ts.addToLabel(state, loc.toString());});
				ts.setInitial(state, true);
			}
		addAllTransitions(cs, ts, new HashSet<>(), ts.getInitialStates(), new ParserBasedInterleavingActDef(), new ParserBasedActDef(),
				new ParserBasedCondDef());

		return ts;
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

    private List<String> addPromelaLocation(NanoPromelaParser.StmtContext root){
		List<String> res = new LinkedList<>();
    	if(root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null ||
				root.atomicstmt() != null || root.skipstmt() != null){
			res.add("");
            res.add(root.getText());
		}
		else if(root.ifstmt() != null){
            res.add(root.getText());
			for(int i=1; i<root.getChild(0).getChildCount()-1; i++)
				res.addAll(addPromelaLocation((NanoPromelaParser.StmtContext)root.getChild(0).getChild(i).getChild(3)));
		}
		else if(root.dostmt() != null){
		    for(int i=1; i<root.getChild(0).getChildCount()-1; i++)
                res.addAll(addPromelaLocation((NanoPromelaParser.StmtContext)root.getChild(0).getChild(i).getChild(3)));
		    for(int i=0; i<res.size(); i++)
		        if(!res.get(i).equals(""))
		            res.set(i, res.get(i)+";"+root.getText());
            res.add(root.getText());
		}
		else{
			res.addAll(addPromelaLocation((NanoPromelaParser.StmtContext)root.getChild(0)));
            for(int i=0; i<res.size(); i++)
                if(!res.get(i).equals(""))
                    res.set(i, res.get(i)+";"+root.getChild(2).getText());
            res.addAll(addPromelaLocation((NanoPromelaParser.StmtContext)root.getChild(2)));
		}
		return res;
	}

	private void addPromelaEdges(ProgramGraph<String, String> pg, NanoPromelaParser.StmtContext root, Set<String> allEdges){
        if(allEdges.contains(root.getText()))
            return;
        else
            allEdges.add(root.getText());
        if(root.getText().equals("") || root == null)
            return;
        if(root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null ||
                root.atomicstmt() != null || root.skipstmt() != null){
            PGTransition<String, String> t = new PGTransition<>(root.getText(), "", root.getText(), "");
            pg.addTransition(t);
        }
        else if(root.ifstmt() != null){
            Set<PGTransition<String, String>> addTransitions = new HashSet<>();
            for(NanoPromelaParser.OptionContext op : root.ifstmt().option()){
                addPromelaEdges(pg, op.stmt(), allEdges);
                for(PGTransition<String, String> t : pg.getTransitions())
                    if(t.getFrom().equals(op.stmt().getText())){
                        String cond = op.boolexpr().getText();
                        if (!t.getCondition().equals(""))
                            cond = "("+ cond + ") && (" + t.getCondition() + ")";
                        else
                            cond = "("+ cond + ")";
                        PGTransition<String, String> trans = new PGTransition<>(root.getText(), cond, t.getAction(), t.getTo());
                        addTransitions.add(trans);
                    }
            }
            for(PGTransition<String, String> t : addTransitions)
                pg.addTransition(t);
        }
        else if(root.dostmt() != null){
            Set<PGTransition<String, String>> addTransitions = new HashSet<>();
            String allNot = "";
            for(NanoPromelaParser.OptionContext op : root.dostmt().option()){
                if(allNot.equals(""))
                    allNot += "(" + op.boolexpr().getText() +")";
                else
                    allNot += "|| (" + op.boolexpr().getText() +")";
                addPromelaEdges(pg, op.stmt(), allEdges);
                for(PGTransition<String, String> t : pg.getTransitions())
                    if(t.getFrom().equals(op.stmt().getText())){
                        String cond = op.boolexpr().getText();
                        if (!t.getCondition().equals(""))
                            cond = "("+ cond + ") && (" + t.getCondition() + ")";
                        else
                            cond = "("+ cond + ")";
                        PGTransition<String, String> trans;
                        if(t.getTo().equals(""))
                            trans = new PGTransition<>(root.getText(), cond, t.getAction(), root.getText());
                        else {
                            trans = new PGTransition<>(root.getText(), cond, t.getAction(), t.getTo() + ";" + root.getText());
                        }
                        addTransitions.add(trans);
                    }
            }
            addTransitions.add(new PGTransition(root.getText(), "!(" + allNot + ")", "",""));
            for(PGTransition<String, String> t : addTransitions)
                pg.addTransition(t);
        }
        else{
            NanoPromelaParser.StmtContext recursionThingy = null;
            Set<PGTransition<String, String>> addTransitions = new HashSet<>();
            addPromelaEdges(pg, root.stmt(0), allEdges);
            addPromelaEdges(pg, root.stmt(1), allEdges);
            for(PGTransition<String, String> t : pg.getTransitions())
            if(t.getFrom().equals(root.stmt(0).getText())) {
                PGTransition<String, String> trans;
                if (t.getTo().equals(("")))
                    trans = new PGTransition<>(root.stmt(0).getText() + ";" + root.stmt(1).getText(), t.getCondition(), t.getAction(), root.stmt(1).getText());
                else {
                    trans = new PGTransition<>(root.stmt(0).getText() + ";" + root.stmt(1).getText(), t.getCondition(), t.getAction(), t.getTo() + ";" + root.stmt(1).getText());
					String modifyRecursionStr = modifyOd(t.getTo() + ";" + root.stmt(1).getText());
                    recursionThingy = NanoPromelaFileReader.pareseNanoPromelaString(modifyRecursionStr);
                }
                addTransitions.add(trans);
            }
            for(PGTransition<String, String> t : addTransitions)
                pg.addTransition(t);
            if(recursionThingy != null) {
				addPromelaEdges(pg, recursionThingy, allEdges);
			}
        }

    }

    private String modifyOd(String s){
		int index = s.indexOf("od");
		while (index >= 0) {
			s = s.substring(0, index) + " " + s.substring(index);
			index = s.indexOf("od", index + 2);
		}
		return s;
	}
    private void wipeProgramGraph(ProgramGraph<String, String> pg, Set<String> reachLocs){
	    Set<PGTransition<String, String>> removeTrans = new HashSet<>();
	    Set<String> removeLocs = new HashSet<>();
	    for(PGTransition<String, String> t : pg.getTransitions())
	        if(!reachLocs.contains(t.getFrom()) || !reachLocs.contains(t.getTo()))
	            removeTrans.add(t);
        for(String loc : pg.getLocations())
            if(!reachLocs.contains(loc))
                removeLocs.add(loc);
        for(PGTransition<String, String> t: removeTrans)
            pg.removeTransition(t);
        for(String loc : removeLocs)
            pg.removeLocation(loc);
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
    	ProgramGraph<String, String> pg = new ProgramGraphImpl<>();
        NanoPromelaParser.StmtContext root = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
		List<String> subs = addPromelaLocation(root);
        Set<String> sub_set = new HashSet<>();
        sub_set.addAll(subs);
		for(String sub: sub_set)
		    pg.addLocation(sub);
		pg.setInitial(root.getText(), true);
		Set<String> allEdges = new HashSet<>();
		addPromelaEdges(pg, root, allEdges);
		Set<String> reachLocs = reach(pg);
		wipeProgramGraph(pg, reachLocs);
		return pg;
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

    private <S> void checkState(TransitionSystem<S, ?, ?> ts, S state){
		if(!ts.getStates().contains(state))
			throw new StateNotFoundException(state);
	}

	private <A> void checkAction(TransitionSystem<?, A, ?> ts, A action){
		if(!ts.getActions().contains(action))
			throw new ActionNotFoundException(action);
	}
   
}
