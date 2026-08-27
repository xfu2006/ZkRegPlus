extern crate fast_paths;
extern crate serde;
use crate::{
    automaton::{Automata, Automaton, Buildable, FromRawError},
    nfa::{ToNfa, NFA},
    regex::{Regex, ToRegex},
};
use std::{
    cmp::{Ordering, Ordering::*, PartialEq, PartialOrd},
    collections::{HashMap, HashSet,VecDeque,hash_map::Entry},
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Add, Mul, Neg, Not, RangeBounds, Sub},
    str::FromStr,
};
use fast_paths::*;
use serde::{Serialize,Deserialize};

const B_DEBUG: bool = false;

// Added by BORA paper author
#[derive(Eq, PartialEq,Clone,Debug)]
struct MyHashSet(HashSet<usize>);
impl std::hash::Hash for MyHashSet{
	fn hash<H>(&self, state: &mut H)
	where H: std::hash::Hasher{
		let mut vec = self.0.clone().into_iter().collect::<Vec<usize>>();
		vec.sort();
		for x in &vec{
			state.write_usize(*x);
		}
		state.finish();
	}
}

/// <https://en.wikipedia.org/wiki/Deterministic_finite_automaton>
#[derive(Debug, Clone, Serialize,Deserialize)]
pub struct DFA<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> {
//    pub(crate) alphabet: HashSet<V>,
 //   pub(crate) initial: usize,
  //  pub(crate) finals: HashSet<usize>,
   // pub(crate) transitions: Vec<HashMap<V, usize>>,
   //CHANGED BY BORA paper author for viewing data
    pub alphabet: HashSet<V>,
    pub initial: usize,
    pub finals: HashSet<usize>,
    pub transitions: Vec<HashMap<V, usize>>,
	pub raw_str: String,
}

/// An interface for structs that can be converted into a DFA.
pub trait ToDfa<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> {
    fn to_dfa(&self) -> DFA<V>;
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> DFA<V> {
    pub fn intersect(self, b: DFA<V>) -> DFA<V> {
        self.negate().unite(b.negate()).negate()
    }

	//STOP once it enters a final state
    pub fn debug_run(&self, v: &[V]) {
        let mut actual = self.initial;
		let mut _id = 0;
        for l in v {
			_id += 1;
            if let Some(t) = self.transitions[actual].get(l) {
				let _src = actual;
                actual = *t;
				let dst = actual;
				//println!("DEBUG RUN: id: {}: {} -- {} --> {}",
				// _id, _src, l, dst);
				if self.finals.contains(&dst){
					println!("DEBUG run: **** ACCEPTED ***");
					break;
				}
            } else {
				println!("DEBUG run STOP: not accepting");
				break;
            }
        }
    }

	// Added by BORA paper author
	// return the shorteed accepted word
	// if not found, return empty vector
	pub fn get_shortest_accepted(&self)->Vec<V>{
		//1. build the graph based on transitions
		let mut graph = InputGraph::new();
		for src in 0..self.transitions.len(){
			for (_c,dst) in &self.transitions[src]{
					graph.add_edge(src, *dst, 1);
			}
		}

		//2. get the shortest path (node list)
		graph.freeze();
		let fg = prepare(&graph);
		let spath = calc_path(&fg, self.initial, self.finals.iter().next().unwrap().clone());
		if spath.is_none() {return vec![];}

		//3. from the node list get the accepted words 
		let spath2= spath.unwrap();
		let nodes = spath2.get_nodes();
		let mut vec = vec![];
		for i in 1..nodes.len(){
			let prev = nodes[i-1];
			let cur = nodes[i];
			let trans = &self.transitions[prev];
			let mut bfound = false;
			for c in &self.alphabet{
				if trans.get(&c).unwrap().clone()==cur{
					vec.push(*c);
					bfound = true;
				}
			}
			assert!(bfound, "cannot find transition from {} -> {}", prev, cur);
		}

		vec
	}

	// Added by BORA paper author
	// build the tuples of states and transition tables
	pub fn intersect2(self, b:DFA<V>) -> DFA<V>{
		let mut hash_states = HashMap::<(usize,usize), usize>::new();
		let mut processed = HashSet::<(usize, usize)>::new();
		let mut q:VecDeque<(usize,usize)> = VecDeque::<(usize,usize)>::new();
		q.push_back( (self.initial, b.initial) );
		let mut finals = HashSet::<usize>::new();
		if self.finals.contains(&self.initial) && b.finals.contains(&b.initial){
			finals.insert(0);
		}
		hash_states.insert( (self.initial, b.initial), 0 );
		//process until q has no elements
		let mut cur_state:usize = 0;
		let mut new_trans = HashMap::<usize,HashMap<V,usize>>::new();
		while !q.is_empty(){
			let t_state = q.pop_front().unwrap();
			if processed.contains(&t_state) {
				continue;
			}
			processed.insert( t_state );
			let src_state = *hash_states.get(&t_state).unwrap();
			let mut new_map = HashMap::<V,usize>::new();
			let map1 = &self.transitions[t_state.0];
			let map2 = &b.transitions[t_state.1];
			//println!(" -- DEBUG 200: process {:?}", t_state);
			for c in &self.alphabet{
				if !map1.contains_key(&c) || !map2.contains_key(&c){
					continue;
				}
				let dt_state = (*map1.get(&c).unwrap(), *map2.get(&c).unwrap());
				if !hash_states.contains_key( &dt_state ){
					cur_state += 1;
					hash_states.insert( dt_state.clone(), cur_state);
					q.push_back(dt_state);
				}
				let nxt_state = hash_states.get(&dt_state).unwrap();
				new_map.insert(*c, *nxt_state);
				if self.finals.contains(&dt_state.0) && b.finals.contains(&dt_state.1){
					finals.insert(*nxt_state);
				}
			}
			new_trans.insert(src_state, new_map);
		}

		//println!(" -- DEBUG 301 add transitions: {}", new_trans.len());
		let mut trans = vec![];
		for i in 0..new_trans.len(){
			trans.push( new_trans.get(&i).unwrap().clone() );
		}
		//println!(" -- RETURN! --");
		//return
		DFA{
			alphabet: self.alphabet.clone(),
			initial: 0,
			finals: finals,
			transitions: trans,
			raw_str: format!("{} and {}", self.raw_str, b.raw_str),
		}
	}

    /// The algorithm used is <https://en.wikipedia.org/wiki/DFA_minimization#Brzozowski's_algorithm>.
    pub fn minimize(self) -> DFA<V> {
        let new_dfa = self.reverse().to_dfa().reverse().to_dfa();
		new_dfa
    }

	/// build the reverse transitions, added by BORA paper author
	fn build_reverse_trans(&self)->Vec<HashMap<V,Vec<usize>>>{
		let n_states = self.transitions.len();
		let mut res = vec![];
		for _i in 0..n_states{
			res.push( HashMap::<V,Vec<usize>>::new() );
		}
		for i in 0..n_states{
			let m = &self.transitions[i];
			for c in &self.alphabet{
				if m.contains_key(&c){
					let j = m.get(&c).unwrap(); 
					match res[*j].entry(*c){
						Entry::Vacant(e) => {e.insert(vec![i]);}
						Entry::Occupied(mut e) => {e.get_mut().push(i);}
					}
				}
			}
		}
		return res;
	}

	/// get the set of reachable 
	fn get_reach(set_states: &HashSet<usize>, trans: &Vec<HashMap<V,Vec<usize>>>, c: V)->HashSet<usize>{
		let mut res = HashSet::<usize>::new();
		for s in set_states{
			let map = &trans[*s];
			if map.contains_key(&c){
				let vec_nx = map.get(&c).unwrap();
				for nx in vec_nx{
					res.insert(*nx);
				}
			}
		}
		return res;
	}

	/// Added by BORA paper author, used for Hopcroft's algorithm
	/// map each state in a partition to its new ID
	fn partition_to_mapping(partitions: &HashSet<MyHashSet>)
	-> HashMap<usize, usize>{
		let mut cur_id = 0;
		let mut map1 = HashMap::<MyHashSet,usize>::new();
		let mut map2 = HashMap::<usize, usize>::new();
		for x in partitions{
			map1.insert(x.clone(), cur_id);
			cur_id += 1;
		}
		for x in partitions{
			let sid = map1.get(&x).unwrap();
			for ele in &x.0{
				map2.insert(*ele, *sid);
			}
		}
		return map2;
	}

	/// Added by BORA paper author. Only call it for SMALL dfa
	pub fn dump(&self, name: &str){
		println!("-- DUMP: {} --", name);
		println!("initial state: {}", self.initial);
		for id in 0..self.transitions.len(){
			println!("{}: {:?}", id, self.transitions[id]);
		}
		println!("final states: {:?}\n-------", self.finals);
	}

	/// Added by BORA paper author, Hopcroft's algorithm
	/// see wiki: <https://en.wikipedia.org/wiki/DFA_minimization>
	pub fn minimize_hop(self) -> DFA<V>{
		//1. build the equivalent classes
		let mut p = HashSet::<MyHashSet>::new();
		let mut w = HashSet::<MyHashSet>::new();
		let mut q = HashSet::new();
		for x in 0..self.transitions.len(){q.insert(x);}
		let f = self.finals.clone();
		let q_minus_f = q.difference(&f).cloned().collect::<HashSet<usize>>();
		p.insert(MyHashSet(f.clone()));
		p.insert(MyHashSet(q_minus_f.clone()));
		w.insert(MyHashSet(f.clone()));
		w.insert(MyHashSet(q_minus_f.clone()));

		let rev_trans = &self.build_reverse_trans();
		while !w.is_empty(){
			let a = w.iter().next().unwrap();	
			let mut p_to_add = HashSet::<MyHashSet>::new();
			let mut p_to_remove = HashSet::<MyHashSet>::new();
			let mut w_to_add = HashSet::<MyHashSet>::new();
			let mut w_to_remove = HashSet::<MyHashSet>::new();
			w_to_remove.insert(a.clone());
			for c in &self.alphabet{
	  			let x = Self::get_reach(&a.0, &rev_trans, *c);
				//println!(" -- c: {}, x: {:?}", c, x);
	  			for y in &p{
	  				let x_and_y = MyHashSet(y.0.intersection(&x).cloned().collect::<HashSet<usize>>());
	  				let y_minus_x = MyHashSet(y.0.difference(&x).cloned().collect::<HashSet<usize>>());
	  				if x_and_y.0.is_empty() || y_minus_x.0.is_empty(){
	  					continue;
	  				}
	  				p_to_add.insert(x_and_y.clone());
	  				p_to_add.insert(y_minus_x.clone());
	  				p_to_remove.insert(y.clone());
	  				if w.contains(y){
						//println!(" -- y in w, replace y in w by two sets");
	  					w_to_add.insert(x_and_y);
	  					w_to_add.insert(y_minus_x);
	  					w_to_remove.insert(y.clone());
	  				}else{
	  					if x_and_y.0.len()<=y_minus_x.0.len(){
							//println!(" -- add x_and_y to w");
	  						w_to_add.insert(x_and_y);
	  					}else{
							//println!(" -- add y_minus_x to w");
	  						w_to_add.insert(y_minus_x);
	  					}
	  				}
	  			}
			}
			//println!("DEBUG 300: BEFORE update p: {}, w: {}", p.len(), w.len());
			for x in &p_to_remove{ p.remove(x); }
			for x in &p_to_add{ p.insert(x.clone()); }
			for x in &w_to_remove{ w.remove(x); }
			for x in &w_to_add{ w.insert(x.clone()); }
			//println!("DEBUG 301: p: {}, w: {}", p.len(), w.len());
		}

		//2. build the dfa based on p
		let part_2_state = Self::partition_to_mapping(&p);
		let mut new_trans = vec![HashMap::<V,usize>::new(); p.len()];
		let mut new_finals = HashSet::<usize>::new();
		let mut new_init = 0;
		for subset in p{
			if subset.0.len()==0 {continue;}

			let st0 = subset.0.iter().next().unwrap();
			let sid = part_2_state.get(&st0).unwrap();
			if self.finals.contains(st0){
				new_finals.insert(*sid);
			}
			if subset.0.contains(&self.initial){
				new_init = *sid;
			}
			let transmap = &self.transitions[*st0];
			let mut newmap = HashMap::<V,usize>::new();
			for c in &self.alphabet{
				if transmap.contains_key(c){
					let dst = transmap.get(c).unwrap();
					let newdst = part_2_state.get(dst).unwrap();
					newmap.insert(*c, *newdst);
				}
			}
			new_trans[*sid] =  newmap;
		}

		DFA{
			alphabet: self.alphabet.clone(),
			initial: new_init,
			finals: new_finals,
			transitions: new_trans,
			raw_str: self.raw_str.clone(),
		}
	}

    /// A contains B if and only if for each `word` w, if B `accepts` w then A `accepts` w.
    pub fn contains(&self, b: &DFA<V>) -> bool {
        self.to_nfa().contains(&b.to_nfa())
    }

    /// Returns a string containing the dot description of the automaton
    pub fn to_dot(&self) -> String {
        self.to_nfa().to_dot()
    }

    /// Returns an empty automaton with the given alphabet.
    pub fn new_empty(alphabet: &HashSet<V>) -> DFA<V> {
        DFA {
            alphabet: alphabet.clone(),
            initial: 0,
            finals: HashSet::new(),
            transitions: vec![HashMap::new()],
			raw_str: format!(""),
        }
    }

    /// Returns an automaton built from the raw arguments.
    pub fn from_raw(
        alphabet: HashSet<V>,
        initial: usize,
        finals: HashSet<usize>,
        transitions: Vec<HashMap<V, usize>>,
    ) -> Result<Self, FromRawError<V>> {
        let len = transitions.len();

        if initial >= len {
            return Err(FromRawError::InvalidInitial(initial));
        }

        if let Some(state) = finals.iter().find(|&&state| state >= len) {
            return Err(FromRawError::InvalidFinal(*state));
        }

        for (state, map) in transitions.iter().enumerate() {
            if let Some(&letter) = map.keys().find(|&x| !alphabet.contains(x)) {
                return Err(FromRawError::UnknownLetter(letter));
            }

            if let Some((&letter, &destination)) =
                map.iter().find(|(_, &destination)| destination >= len)
            {
                return Err(FromRawError::InvalidTransition(state, letter, destination));
            }
        }

        Ok(DFA {
            alphabet,
            initial,
            finals,
            transitions,
			raw_str: format!("unknown"),
        })
    }
}


impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> Automata<V> for DFA<V> {
    fn run(&self, v: &[V]) -> bool {
		let b_debug = B_DEBUG;
        let mut actual = self.initial;
		let mut id = 0;
        for l in v {
            if let Some(t) = self.transitions[actual].get(l) {
                actual = *t;
            } else {
                return false;
            }
			id += 1;
        }
        self.finals.contains(&actual)
    }

    fn is_complete(&self) -> bool {
        for map in &self.transitions {
            for v in &self.alphabet {
                if !map.contains_key(&v) {
                    return false;
                }
            }
        }

        true
    }

    fn is_reachable(&self) -> bool {
        let mut stack = vec![self.initial];
        let mut acc = HashSet::new();
        acc.insert(self.initial);
        while let Some(e) = stack.pop() {
            for v in self.transitions[e].values() {
                if !acc.contains(&v) {
                    acc.insert(*v);
                    stack.push(*v);
                }
            }
        }
        acc.len() == self.transitions.len()
    }

    fn is_coreachable(&self) -> bool {
        self.to_nfa().is_coreachable()
    }

    fn is_trimmed(&self) -> bool {
        self.to_nfa().is_trimmed()
    }

    fn is_empty(&self) -> bool {
        self.to_nfa().is_empty()
    }

    fn is_full(&self) -> bool {
        self.to_nfa().is_full()
    }

    fn negate(mut self) -> DFA<V> {
        self = self.complete();
        self.finals = (0..self.transitions.len())
            .filter(|x| !self.finals.contains(&x))
            .collect();
        self
    }

    fn complete(mut self) -> DFA<V> {
        if self.is_complete() {
            return self;
        }

        let l = self.transitions.len();
        self.transitions.push(HashMap::new());
        for map in &mut self.transitions {
            for v in &self.alphabet {
                if !map.contains_key(&v) {
                    map.insert(*v, l);
                }
            }
        }

        self
    }

    fn make_reachable(self) -> DFA<V> {
        self.to_nfa().make_reachable().to_dfa()
    }

    fn make_coreachable(self) -> DFA<V> {
        self.to_nfa().make_coreachable().to_dfa()
    }

    fn trim(self) -> DFA<V> {
        self.to_nfa().trim().to_dfa()
    }

    fn reverse(self) -> DFA<V> {
        self.to_nfa().reverse().to_dfa()
    }
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> Buildable<V> for DFA<V> {
    fn unite(self, b: DFA<V>) -> DFA<V> {
        self.to_nfa().unite(b.to_nfa()).to_dfa()
    }

    fn concatenate(self, b: DFA<V>) -> DFA<V> {
        self.to_nfa().concatenate(b.to_nfa()).to_dfa()
    }

    fn kleene(self) -> DFA<V> {
        self.to_nfa().kleene().to_dfa()
    }

    fn at_most(self, u: usize) -> DFA<V> {
        self.to_nfa().at_most(u).to_dfa()
    }

    fn at_least(self, u: usize) -> DFA<V> {
        self.to_nfa().at_least(u).to_dfa()
    }

    fn repeat<R: RangeBounds<usize>>(self, r: R) -> DFA<V> {
        self.to_nfa().repeat(r).to_dfa()
    }
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> ToDfa<V> for DFA<V> {
    fn to_dfa(&self) -> DFA<V> {
        self.clone()
    }
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> ToRegex<V> for DFA<V> {
    fn to_regex(&self) -> Regex<V> {
        self.to_nfa().to_regex()
    }
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> ToNfa<V> for DFA<V> {
    fn to_nfa(&self) -> NFA<V> {
        let mut initials = HashSet::new();
        initials.insert(self.initial);
        let mut transitions = Vec::new();
        for map in &self.transitions {
            transitions.push(map.iter().map(|(k, v)| (*k, vec![*v])).collect());
        }
        NFA {
            alphabet: self.alphabet.clone(),
            initials,
            finals: self.finals.clone(),
            transitions,
        }
    }
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> PartialEq<DFA<V>> for DFA<V> {
    fn eq(&self, b: &DFA<V>) -> bool {
        self.le(&b) && self.ge(&b)
    }
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> PartialEq<NFA<V>> for DFA<V> {
    fn eq(&self, b: &NFA<V>) -> bool {
        self.to_nfa().eq(b)
    }
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> PartialEq<Regex<V>> for DFA<V> {
    fn eq(&self, b: &Regex<V>) -> bool {
        self.to_nfa().eq(&b.to_nfa())
    }
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> PartialEq<Automaton<V>> for DFA<V> {
    fn eq(&self, b: &Automaton<V>) -> bool {
        match b {
            Automaton::DFA(v) => self.eq(&*v),
            Automaton::NFA(v) => self.eq(&*v),
            Automaton::REG(v) => self.eq(&*v),
        }
    }
}

impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> PartialOrd for DFA<V> {
    fn partial_cmp(&self, other: &DFA<V>) -> Option<Ordering> {
        match (self.ge(&other), self.le(&other)) {
            (true, true) => Some(Equal),
            (true, false) => Some(Greater),
            (false, true) => Some(Less),
            (false, false) => None,
        }
    }

    fn lt(&self, other: &DFA<V>) -> bool {
        other.contains(&self) && !self.contains(&other)
    }

    fn le(&self, other: &DFA<V>) -> bool {
        other.contains(&self)
    }

    fn gt(&self, other: &DFA<V>) -> bool {
        self.contains(&other) && !other.contains(&self)
    }

    fn ge(&self, other: &DFA<V>) -> bool {
        self.contains(&other)
    }
}

impl FromStr for DFA<char> {
    type Err = String;

    fn from_str(s: &str) -> Result<DFA<char>, Self::Err> {
        NFA::from_str(s).map(|x| x.to_dfa())
    }
}

/// The multiplication of A and B is A.concatenate(B)
impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> Mul for DFA<V> {
    type Output = Self;

    fn mul(self, other: DFA<V>) -> DFA<V> {
        self.concatenate(other)
    }
}

/// The negation of A is A.negate().
impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> Neg for DFA<V> {
    type Output = Self;

    fn neg(self) -> DFA<V> {
        self.negate()
    }
}

/// The opposite of A is A.reverse().
impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> Not for DFA<V> {
    type Output = Self;

    fn not(self) -> DFA<V> {
        self.reverse()
    }
}

/// The substraction of A and B is an automaton that accepts a word if and only if A accepts it and B doesn't.
impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> Sub for DFA<V> {
    type Output = Self;

    fn sub(self, other: DFA<V>) -> DFA<V> {
        self.intersect(other.negate())
    }
}

/// The addition fo A and B is an automaton that accepts a word if and only if A or B accept it.
impl<V: Eq + Hash + Display + Copy + Clone + Debug + Ord> Add for DFA<V> {
    type Output = Self;

    fn add(self, other: DFA<V>) -> DFA<V> {
        self.unite(other)
    }
}
