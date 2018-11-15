package il.ac.bgu.cs.fvm.impl;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

public class TransitionSystemImpl<STATE, ACTION, ATOMIC_PROPOSITION> implements TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> {
	
	private HashMap<STATE, Tuple<Boolean, Set<ATOMIC_PROPOSITION>>> states = new HashMap<STATE, Tuple<Boolean, Set<ATOMIC_PROPOSITION>>>();
	private Set<ATOMIC_PROPOSITION> aps = new HashSet<ATOMIC_PROPOSITION>();
	private Set<ACTION> actions = new HashSet<ACTION>(); 
	private Set<Transition<STATE, ACTION>> transitions = new HashSet<Transition<STATE, ACTION>>();
	private String name;
	
	@Override
	public String getName() {
		return this.name;
	}

	@Override
	public void setName(String name) {
		this.name = name;
	}

	@Override
	public void addAction(ACTION anAction) {
		actions.add(anAction);	
	}

	@Override
	public void setInitial(STATE aState, boolean isInitial) throws StateNotFoundException {
		if(!states.containsKey(aState))
			throw new StateNotFoundException(aState);
		states.put(aState, new Tuple<Boolean, Set<ATOMIC_PROPOSITION>>(isInitial, states.get(aState).second));
	}

	@Override
	public void addState(STATE state) {
		states.put(state, new Tuple<Boolean, Set<ATOMIC_PROPOSITION>>(false, new HashSet<ATOMIC_PROPOSITION>()));
	}

	@Override
	public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
		if(!states.containsKey(t.getFrom()) || !states.containsKey(t.getTo()) || !actions.contains(t.getAction()))
			throw new InvalidTransitionException(t);
		transitions.add(t);
	}

	@Override
	public Set<ACTION> getActions() {
		return actions;
	}

	@Override
	public void addAtomicProposition(ATOMIC_PROPOSITION p) {
		aps.add(p);
	}

	@Override
	public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
		return aps;
	}

	@Override
	public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
		if(!aps.contains(l))
			throw new InvalidLablingPairException(s, l);
		states.get(s).second.add(l);
	}

	@Override
	public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
		if(!states.containsKey(s))
			throw new StateNotFoundException(s);
		return new HashSet<ATOMIC_PROPOSITION>(states.get(s).second);
	}

	@Override
	public Set<STATE> getInitialStates() {
		Set<STATE> res = new HashSet<STATE>();
		states.forEach((key,value) -> {if(value.first) res.add(key); });
		return res;
	}

	@Override
	public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
		Map<STATE, Set<ATOMIC_PROPOSITION>> res = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>(); 
		states.forEach((key,value) -> res.put(key, value.second));
		return res;
	}

	@Override
	public Set<STATE> getStates() {
		Set<STATE> res = new HashSet<STATE>(); 
		states.forEach((key,value) -> res.add(key));
		return res;
	}
	
	@Override
	public Set<Transition<STATE, ACTION>> getTransitions() {
		return new HashSet<Transition<STATE, ACTION>>(this.transitions);
//		return this.transitions;
	}

	@Override
	public void removeAction(ACTION action) throws FVMException {
		if(!actions.contains(action))
			throw new FVMException("Invalid action");
		for(Transition<STATE, ACTION> t : transitions)
			if(t.getAction().equals(action))
				throw new DeletionOfAttachedActionException(action, TransitionSystemPart.ACTIONS);
		actions.remove(action);
	}

	@Override
	public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
		if (!aps.contains(p)) 
			throw new FVMException("Invalid atomic proposition");
		states.forEach((key,value) -> {if (value.second.remove(p))
											throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.ATOMIC_PROPOSITIONS); });
		aps.remove(p);

	}

	@Override
	public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
		states.get(s).second.remove(l);				
	}

	@Override
	public void removeState(STATE state) throws FVMException {
		if (!states.containsKey(state))
			throw new FVMException("Invalid state");
		if (states.get(state).first)
			throw new DeletionOfAttachedStateException(state, TransitionSystemPart.INITIAL_STATES);
		for(Transition<STATE, ACTION> t : transitions)
			if(t.getTo().equals(state) || t.getFrom().equals(state))
				throw new DeletionOfAttachedStateException(state, TransitionSystemPart.STATES);
		if(!states.get(state).second.isEmpty())
			throw new DeletionOfAttachedStateException(state, TransitionSystemPart.LABELING_FUNCTION);
		states.remove(state);
	}

	@Override
	public void removeTransition(Transition<STATE, ACTION> t) {
		transitions.remove(t);	
	}

}
