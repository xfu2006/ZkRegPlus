/// Common utility functions for parsing PCRE regex and conversion
/// between PCRE and the regex syntax accepted by rustomaton library
/*
	Created 06/13/2024
 	Modified 06/22/2024: added handling of pcre to pm structure
	Ported 07/24/2024
*/
extern crate regex_syntax;
extern crate serde;
extern crate common_substrings;
extern crate rustomaton;
use std::collections::{HashSet, HashMap};
use std::mem::{discriminant};
use self::serde::{Serialize,Deserialize};
use self::regex_syntax::{
	ast::{parse::Parser},
	hir::{translate::TranslatorBuilder, Hir, HirKind, Repetition, Class,
		Capture,  Look,
		Class::{Bytes,Unicode}, 
		HirKind::{Empty},
	}
};
use self::common_substrings::get_substrings;
use utils::{
	data::{u8_to_hex, char_arr_to_u8},
};
use crate::{
	strings::{split, find_all, is_match},
	fsa_utils::{build_dfa}, 
	preprocess::{to_ignore_case,handle_location, handle_negation,
		handle_range_without_approx, handle_modifier, extract_clamav_reg},
	type_def::{PcreInfo, ClamavApproxConfig},
};

use self::rustomaton::dfa::{DFA};
use self::rustomaton::automaton::{Buildable};



impl PcreInfo{
	/// create a false instance
	pub fn new_false() -> Self{
		Self{b_pcre: false, b_backref: false, b_zero_assert: false,
			b_begin: false, b_end: false, b_boundary: false,
			original_str: String::new()}
	}
	///constructor
	pub fn new_pcre() -> Self{
		Self{b_pcre: true, b_backref: false, b_zero_assert: false,
			b_begin: false, b_end: false, b_boundary: false,
			original_str: String::new()}
	}
	/// do logical or on boolean flags
	pub fn or(&self, other: &Self) -> Self{
		Self{
			b_pcre: self.b_pcre || other.b_pcre,
			b_backref: self.b_backref || other.b_backref,
			b_zero_assert: self.b_zero_assert || other.b_zero_assert,
			b_begin: self.b_begin || other.b_begin,
			b_end: self.b_end || other.b_end,
			b_boundary: false, //after one layer, eliminated
			original_str: String::new()
		}
	}
}

/// More details about the type of group/capture
/// and their information
#[derive(Serialize,Deserialize, Clone,Debug)]
enum MoreGroupInfo{
	DeclareNamedGroup{name: String, content: String},
	UseNamedGroup{name: String},
	DeclareUnnamedGroup{content: String},
	UseUnnamedGroup{id: usize}, //LIMIT no two digit backreferences 
}

/// information of Group(captures)
#[derive(Serialize,Deserialize, Clone,Debug)]
struct GroupInfo{
	pub start: usize,
	pub end: usize,
	///id is usize::MAX for UseGroup objects
	pub id: usize, 
	pub more_info: MoreGroupInfo,
	pub b_not_cap: bool,//non captured group
}

impl GroupInfo{
	/// return true if it is DeclareNamed or DeclareUnanedGroup
	pub fn is_define_group(&self)->bool{
		self.id < usize::MAX
	}
}

/// given a named group , capture its name and contents
fn parse_group(s: &str, start: usize, end: usize, id: usize) -> GroupInfo{
	//assuming s is (?P=<name> ...) or (....)
	let chars = s[start..end+1].chars().collect::<Vec<char>>();
	let news = s[start..end+1].chars().collect::<String>();
	assert!(chars[0]=='(' && chars[chars.len()-1]==')',"start/end not paren!");
	if chars[1]=='?'{
		if chars[2]=='P' && chars[3]=='<' || chars[2]=='<'{
			let arr = find_all(r"<(.*?)>", &news);
			assert!(arr.len()==1, "ERROR in parsing: news: {}", &news);
			let name = arr[0][1..arr[0].len()-1].to_string();
			let arr2 = split(&news, &format!("<{}>", &name));
			assert!(arr2.len()==2, "ERROR in split: news: {}, name: {} => {:?}", &news, &name, arr2);
			let content = arr2[1][0..arr2[1].len()-1].to_string();
			GroupInfo{
				start: start, end: end, id: id, b_not_cap: false ,
				more_info: MoreGroupInfo::DeclareNamedGroup{
					name: name, content: content}
			}
		}else if chars[2]=='P' && chars[3]=='='{//use type
			let arr = find_all(r"P=(.*?)\)", &news);
			assert!(arr.len()==1, "ERROR in parsing: news: {}, arr: {:?}", 
				&news, &arr);
			let name = arr[0][2..arr[0].len()-1].to_string();
			GroupInfo{
				start: start, end: end, id: usize::MAX, 
				 b_not_cap: false,
				more_info: MoreGroupInfo::UseNamedGroup{
					name: name}
			}
		}else if chars[2]==':'{//actually non-cap noname group
			let ctn = chars[3..chars.len()-1].iter().collect::<String>();
			GroupInfo{start: start, end: end, id: id, b_not_cap: true, 
				more_info: MoreGroupInfo::DeclareUnnamedGroup{content: ctn}}
		}else{
			panic!("cannot handle: s: {}", &news);
		}
	}else{
		let ctn = chars[1..chars.len()-1].iter().collect::<String>();
		GroupInfo{start: start, end: end, id: id, b_not_cap: false, 
			more_info: MoreGroupInfo::DeclareUnnamedGroup{content: ctn}}
	}

}

/// join the vector of strings
fn join_vs(v: &Vec<String>) -> String{
	assert!(v.len()>0, "join_vstr: vec.len==0!");
	if v.len()==1 {v[0].clone()} 
	else{ "(".to_string() + &v.join("|") + &")".to_string() }
}

/// Aggressive SDE fan-out (M3): expand small-cardinality class
/// repetitions in `orig` (raw PCRE) into a union of concrete SED subsig
/// variants -- one more-constrained PCRE per pinned-byte combination.
/// `cfg.sde_rep_fanout_cap` is the fan-out cap B; `b_igc` (the subsig's
/// case-insensitive flag) folds letter classes to lowercase so igc fan-out
/// pins even whole-byte anchors with no redundant `a`/`A` (digits are
/// caseless -> unaffected). No nibble-borrow here: anchors stay byte-PCRE,
/// a tighter-but-sound over-approx (the constant high nibble of an adjacent
/// same-block class is already present downstream). Returns None when
/// disabled, when there is no class run, or when no slot is selectable
/// (wildcard-only, or B below the smallest class) -> caller keeps the
/// single-object path. Over-approximation: the variant union always
/// contains the original, so discharge stays sound.
///
/// Examples (B = cfg.sde_rep_fanout_cap):
///  - "[0-9]{3}-[0-9]{3}-[0-9]{3}", B=1000, gate on -> Some(1000): pin
///    the 1st digit of every leg (10*10*10); middles stay class.
///  - "[a-fA-F]{3}", B=100, gate on, b_igc -> Some(36): folds 12->6, so
///    two positions fit (6*6); cs would be Some(12) (one position, 12<144).
///  - ".{4}" (wildcard-only), or gate off -> None.
pub fn expand_rep_subsig(orig: &str, b_igc: bool,
	cfg: &ClamavApproxConfig) -> Option<Vec<String>> {
	if !cfg.b_aggressive_sde_for_rep { return None; }
	let hir = to_hir(orig);
	//Scope the fan-out to the regex part beyond `[ws]KW[ws].{0,N}`, so
	//budget never lands on a boundary `[ws]` delimiter. The keyword side
	//+ gap is re-emitted verbatim and concatenated back onto each
	//variant. Non-matching shapes keep the whole-HIR path (unchanged).
	let (head, regex_hir, tail) = match partition_keyword_gap(&hir, None) {
		Some(arm) if arm.dir == 0 =>
			(render_verbatim(&arm.anchor), concat_hir(&arm.regex),
			 String::new()),
		Some(arm) =>
			(String::new(), concat_hir(&arm.regex),
			 render_verbatim(&arm.anchor)),
		None => (String::new(), hir, String::new()),
	};
	let legs = find_class_runs(&regex_hir);
	if legs.is_empty() { return None; }
	let slots = select_slots(&legs, cfg.sde_rep_fanout_cap, b_igc,
		cfg.b_sde_rep_tight_first_leg);
	//no selectable slot (wildcard-only, or B below smallest card):
	//nothing to fan out -> caller keeps the single-object path.
	if slots.is_empty() { return None; }
	Some(render_variants(&regex_hir, &legs, &slots, b_igc).iter()
		.map(|r| format!("{}{}{}", head, r, tail)).collect())
}

/// We ignore other clamAV pcre flags: g (global), r( rolling), e(encompass),
/// x - extended, a - anchored, e - dollar endonly, u - ungreedy
/// by default we do dotall, multiline, we only check if it is case
/// sensitive. Return trigger, the regex string itself, and the
///   trigger. The regex string is approximated
///   to rustomaton format -> note we have to approxiamte backreferences
///    as it's beyond regular; we do NOT handle lookaround (anyway
///         there are only 6 in clamav, we rewrote them manually in dataset)
pub fn parse_pcre_subsig(s: &str, combination_limit: usize, repeat_limit: usize)
	->(String, String, bool, PcreInfo){
	let (mut trigger, reg_s, flags) = extract_clamav_reg(s);
	let b_ignore_case = flags.contains("i");
	let (rustomaton_reg_s, pcre_info) = pcre_to_rustomaton_regex(&reg_s, combination_limit, repeat_limit);

	//very rare, trigger might have location decorator 0:, in this
	//case we chop it off for engineering convenience. can be improved.
	if trigger.contains(":"){
		let arr_t = trigger.split(":").map(str::to_string).collect::<Vec<String>>();
		assert!(arr_t.len()==2, "arr_t.len() != 2 for {}", &trigger);
		trigger = arr_t[1].clone();
	}
	(trigger, rustomaton_reg_s, !b_ignore_case, pcre_info)
}



/// convert string to sir
pub fn to_hir(s: &str)->Hir{
	let mut parser= Parser::new();
	let ast = parser.parse(s).unwrap();
	let mut builder = TranslatorBuilder::new();
	builder.dot_matches_new_line(true);
	builder.utf8(false);
	builder.unicode(false);
	let mut translator = builder.build();
	let hir = translator.translate(s, &ast).expect("err in hir");

	hir
}

/// rustomaton cannot handle cases like {5,}
/// put a max case over there 999777979
/// later replace it back
fn preprocess_rep(s: &str)->String{
	let arr = find_all(r"\{[0-9]+,\}", s);
	let mut s2 = s.to_string();
	for x in arr{
		let newx = x[0..x.len()-1].to_string() + "999777979}";
		s2 = s2.replace(&x, &newx);
	}

	s2
}

/// preprocess some chars not accepted by the rustomaton
fn preprocess_badchars(s: &str, b_double_dot: bool)->String{
	//1. handle slash
	let s2 = s.replace("\\/", "\\x2f");
	//for each "." as long as it is continued with alpha-numeric letter
	//(but not *, ?), it is converted to a sequenc of ".."
	//the reason is that one "." in pcre is 2-hex nibbles

	//2. handle dot. ONLY on nibble paths (b_double_dot): a PCRE '.'
	//before a hex literal must become ".." (2 nibbles = 1 byte). On
	//the byte-level DFA path '.' is already a full byte
	//(handle_class_full), so doubling there double-encodes -> skip
	//it (#3 fix).
	if !b_double_dot { return s2; }
	let mut s3 = String::with_capacity(s2.len());
    let mut chars = s2.chars().peekable();
    let mut bs = 0usize; //consecutive '\' just before current char

    while let Some(c) = chars.next() {
        //only double an UNescaped '.' (even # of preceding '\').
        //an escaped "\." is a literal period -> HIR emits byte 2e,
        //already 2 nibbles, so doubling injects a spurious wildcard
        //nibble (#4 fix).
        if c == '.' && bs % 2 == 0 {
            if let Some(&next) = chars.peek() {
                if next == '.' || next.is_ascii_alphanumeric() {
                    s3.push_str("..");
                    bs = 0;
                    continue;
                }
            }
        }
        if c == '\\' { bs += 1; } else { bs = 0; }
        s3.push(c);
    }

	s3
}

/// preprocess named references and numbered backreferences
fn preprocess_backref(s: &str) -> (String, bool){
	//1. PROTECT the "\\"
	let holder = "pl29341l234234234xi1";
	let s_copy = s.to_owned();
	let s = s.replace("\\\\", holder); 
	//1. scan from left to right using a stack and note
	// all capture groups, each group has a name (optional)
	// an ID, and the corresponding regex, and the (start, end) idx
	//let mut vec_group = vec![];
	let chars = s.chars().collect::<Vec<char>>();
	let mut stack: Vec<usize> = vec![];
	let mut vec_groups_def = vec![]; 
	let mut vec_groups_use = vec![]; 
	let mut backslahes = 0;
	let mut i = 0;
	let mut gid = 1;
	while i<chars.len(){
		let ch = chars[i];
		if ch=='('{
			//only there are even backslahes before it is NOT escaled
			if backslahes%2==0{
				stack.push(i); 
			}
		}else if ch==')'{
			if backslahes%2==0{
				let (start, end) = (stack.pop().expect(&format!("ERROR no pop for stack for case: {}", &s)), i);
				let group_info = parse_group(&s, start, end, gid);
				if !group_info.b_not_cap { gid+=1; }
				if group_info.is_define_group(){
					vec_groups_def.push( group_info );
				}else{
					vec_groups_use.push( group_info );
				}
			}
		}else if ch=='\\' && chars[i+1]>='0' && chars[i+1]<='9'{
			assert!(chars.len()<=i+2 || (chars.len()>i+2 && chars[i+2]<'0' || chars[i+2]>'9'), "we do not allow backreferences with more than 1 digit");
			let refid = chars[i+1] as usize - '0' as usize;
			let group_info = GroupInfo{start: i, end: i+1, id: usize::MAX,
				b_not_cap: false,
				more_info: MoreGroupInfo::UseUnnamedGroup{id: refid}};
			vec_groups_use.push( group_info );
			i+=1;
		}
		backslahes = if ch=='\\' {backslahes+1} else {0};
		//println!("-- i: {}, ch: {}, backshales: {}, stack: {:?}, ", 
		//	i, ch, backslahes, stack);
		i +=1;
	}

	//3. replace the USE of groups first and replace the group definitions
	// as it's processed by stack, the OUTER layer will be guaranteed to
	//be processed first
	let find_by_name = |v: &Vec<GroupInfo>, n: &str| -> Vec<GroupInfo>{
		v.iter().filter(|s| {
				match &s.more_info{
					MoreGroupInfo::DeclareNamedGroup{name, content:_}=>name==n,
					_ => false
				}
			}).map(|s| s.clone())
			.collect::<Vec<GroupInfo>>()
	};
	let find_by_id= |v: &Vec<GroupInfo>, n: usize| -> Vec<GroupInfo>{
		v.iter().filter(|s| {
				match &s.more_info{
					MoreGroupInfo::DeclareNamedGroup{name:_, content:_}
						=> s.id==n && !s.b_not_cap,
					MoreGroupInfo::DeclareUnnamedGroup{content:_} => s.id==n
						&& !s.b_not_cap,
					_ => false
				}
			}).map(|s| s.clone())
			.collect::<Vec<GroupInfo>>()
	};
	let slice = |s: &str, start: usize, end: usize| -> String{
		s[start..end+1].to_string()
	};
	let mut res = s.to_string();
	for useitem in &vec_groups_use{
		let minfo = &useitem.more_info;
		let vdef = match minfo{
			MoreGroupInfo::UseNamedGroup{name} => {
				find_by_name(&vec_groups_def, &name)
			},
			MoreGroupInfo::UseUnnamedGroup{id} => {
				find_by_id(&vec_groups_def, *id)
			}
			_ => panic!("ERROR passing minfo: {:?}", minfo)
		};
		assert!(vdef.len()==1, "find group by: {:?} resulting in array: {:?}", 
			&minfo, &vdef);
		let src_s = match &vdef[0].more_info{
			MoreGroupInfo::DeclareNamedGroup{name:_, content} 
				=> content.clone(),
			MoreGroupInfo::DeclareUnnamedGroup{content} => content.clone(),
			_ => panic!("ERROR in src_s: {:?}", vdef[0])
		};
		let old_s = slice(&s, useitem.start, useitem.end);  
		res = res.replace(&old_s, &src_s);
	}

	for defitem in &vec_groups_def{
		let old_s= slice(&s, defitem.start, defitem.end);
		let new_s = match &defitem.more_info{
			MoreGroupInfo::DeclareNamedGroup{name:_,content} 
				=> {content.clone()},
			MoreGroupInfo::DeclareUnnamedGroup{content:_}
				=>{old_s.clone()},
			_ => panic!("ERROR passing defitem: {:?}", defitem)
		};
		res = res.replace(&old_s, &new_s);
		res = res.replace("?:", ""); //remove the ?: of non-capture group
	}

	let res = res.replace(holder, "\\\\");
	let b_changed = res == s_copy; 
	(res.clone(), b_changed)
}

/// pcre regex to dfa directly
/// takes the entire input like 0&1/abc/i
pub fn pcre_to_dfa(s: &str, combination_limit: usize, repeat_limit: usize)->DFA<char>{
	let (_trigger, _src, b_c, pi) = parse_pcre_subsig(s, combination_limit, repeat_limit);
	let b_ignore_case = !b_c;
	let (_, s, _) = extract_clamav_reg(s);
	let s = preprocess_badchars(&s, false);//#3: dots already bytes
	let (s, _b_backref) = preprocess_backref(&s);
	let mut s = preprocess_rep(&s);
	if !pi.b_begin{ s = ".*".to_string() + &s; }
	if !pi.b_end{ s = s + ".*"; }
	let hir  = to_hir(&s);
	let dfa = hex_hir_to_dfa(&s, &hir, b_ignore_case, true);

	dfa
}

/// general regex to dfa
pub fn clamav_genregex_to_dfa(s: &str) -> DFA<char>{
	//1. preprocessing just like clamav.rs::preprocess_regex()
	// general regex part for clamav

	let mut s = s.to_lowercase();
	let _old_s = s.clone();
	let b_case_sensitive;
	s = s.replace("*", ".*");
	s = s.replace("?", ".");
	s = handle_range_without_approx(&s, true); //no unrolling
	(s, b_case_sensitive) = handle_modifier(&s);
	let b_ignore_case = !b_case_sensitive;
	s = handle_location(&s);
	s = handle_negation(&s);

	//2. conversion
	let hir  = to_hir(&s);
	let dfa = hex_hir_to_dfa(&s, &hir, b_ignore_case, false);
	dfa
}

/// convert a a class structure into an array (set) of u8 values
/// _limit: combination limit, not used here.
fn class_to_arr(v: &Class, _limit: &mut usize)->Vec<u8>{
	let res = match v{
		Unicode(x) => {
			let vbytes = x.ranges().iter().map(|r|{
				let (s, e) = (r.start() as u8, r.end() as u8);
				let vec:Vec<u8> = (s..=e).collect();

				vec
			}).flat_map(|v| v).collect::<Vec<u8>>();

			vbytes
		},
		Bytes(y) => {
			let vbytes = y.ranges().iter().map(|r|{
				let (s, e) = (r.start(), r.end());
				let vec:Vec<u8> = (s..=e).collect();

				vec
			}).flat_map(|v| v).collect::<Vec<u8>>();

			vbytes
		}
	};

	res
}

/// Case-fold a class's candidate byte set for igc fan-out. When `b_igc`,
/// map each ASCII uppercase byte to lowercase, then sort+dedup so the
/// result is ascending and unique; the cs path (`b_igc==false`) returns
/// the bytes unchanged. Folding to ONE case (lowercase, matching the
/// new_adv_new to_v8_lower direction) keeps igc fan-out from emitting
/// redundant `a`&`A` variants: under igc a pinned lowercase byte already
/// matches BOTH cases, so the folded set is sound (variant union still
/// >= original) and smaller.
/// Examples: cs `[A-F]` 0x41..0x46 -> unchanged; igc `[A-F]` -> 0x61..
/// 0x66; igc `[a-fA-F]` (12 bytes) -> 0x61..0x66 (6); digits fold to self.
fn fold_bytes_igc(bytes: &[u8], b_igc: bool) -> Vec<u8> {
	if !b_igc { return bytes.to_vec(); }
	let mut out: Vec<u8> = bytes.iter()
		.map(|b| b.to_ascii_lowercase()).collect();
	out.sort();
	out.dedup();
	out
}

/// Folded cardinality of `class` under igc = number of DISTINCT bytes the
/// fan-out will actually enumerate. cs path == card(); igc collapses case
/// pairs (e.g. hex `[a-fA-F]` 12 -> 6). Used as the per-leg budget
/// multiplier in select_slots so the chosen slot count matches the
/// rendered variant count under igc. (Wildcard stays excluded via raw
/// card, NOT this, so 256 is unaffected by folding.)
fn card_igc(class: &Class, b_igc: bool) -> usize {
	let mut dummy = 0usize;
	fold_bytes_igc(&class_to_arr(class, &mut dummy), b_igc).len()
}

/// True iff every byte the class matches is an ASCII digit (0x30..=0x39).
/// A pure-digit leg pins to a digit in EVERY variant, so its high-nibble
/// borrow always yields a clean 3-nibble anchor; a mixed leg (e.g. a
/// `[\x2D0-9]` dash-or-digit column from an APPROX merge) has non-digit
/// variants that produce no anchor. select_slots funds pure-digit legs
/// first so the fan-out budget is never starved on a mixed column before
/// reaching a clean digit run.
fn leg_is_pure_digit(class: &Class) -> bool {
	let mut dummy = 0usize;
	let bytes = class_to_arr(class, &mut dummy);
	!bytes.is_empty() && bytes.iter().all(|&b| (0x30..=0x39).contains(&b))
}

/// One pinnable character-class "leg", e.g. `[0-9]{3}` or `[0-9]{2,5}`.
/// `min` = guaranteed occurrences (only these positions are safely
/// pinnable); `max` = upper bound (None = unbounded), kept for the
/// variable-tail renderer (M3). Bare class / `{1}` -> min=max=1.
/// Produced by find_class_runs; consumed by select_slots (M2) and the
/// fan-out renderer (M3+). SDE-rep aggressive expansion.
#[derive(Clone)]
struct Leg {
	class: Class,
	min: usize,
	max: Option<usize>,
	/// Not a guaranteed match position: the leg sits under an optional
	/// repetition (`?`/`*`/`{0,k}`) or inside an alternation branch, so a
	/// real match may omit it. select_slots funds these only after every
	/// mandatory leg, since the pm-reg layer collapses non-guaranteed
	/// legs to wildcards (their pins never become anchors).
	optional: bool,
}

/// Walk `hir` left-to-right and collect each character-class run as a
/// Leg, in source order. Captures: fixed reps `[0-9]{n}`, variable reps
/// `[0-9]{a,b}` / `+` / `{n,}` (pinnable count = min), and bare classes
/// `[0-9]` / `[0-9]{1}` (min=max=1; to_hir simplifies `{1}` to Class).
/// Skips bare min==0 class reps (`*`,`?`,`{0,k}` -> no guaranteed
/// position). A leg is `optional` when it sits under a min==0 wrapper or
/// inside an alternation branch. Read-only, order-preserving.
fn find_class_runs(hir: &Hir) -> Vec<Leg> {
	let mut legs = Vec::new();
	collect_class_runs(hir, false, &mut legs);
	legs
}

fn collect_class_runs(hir: &Hir, in_optional: bool,
	legs: &mut Vec<Leg>) {
	match hir.kind() {
		//bare class (incl. `{1}`) = one guaranteed position.
		HirKind::Class(c) =>
			legs.push(Leg { class: c.clone(), min: 1,
				max: Some(1), optional: in_optional }),
		HirKind::Repetition(rep) => match rep.sub.kind() {
			HirKind::Class(c) => {
				let min = rep.min as usize;
				if min >= 1 {
					//normalize the {n,} sentinel to unbounded.
					let max = match rep.max {
						Some(999777979) | None => None,
						Some(x) => Some(x as usize),
					};
					legs.push(Leg { class: c.clone(),
						min, max, optional: in_optional });
				}
				//min==0: no guaranteed position -> skip.
			}
			//non-class body (e.g. `([0-9]{2})?`): a min==0 wrapper
			//makes everything inside non-guaranteed.
			_ => collect_class_runs(&rep.sub,
				in_optional || rep.min == 0, legs),
		},
		//concat preserves the guarantee; each alternation branch is
		//conditional, so its legs are never guaranteed.
		HirKind::Concat(v) =>
			{ for h in v { collect_class_runs(h, in_optional, legs); } }
		HirKind::Alternation(v) =>
			{ for h in v { collect_class_runs(h, true, legs); } }
		HirKind::Capture(cap) =>
			collect_class_runs(&cap.sub, in_optional, legs),
		_ => {}
	}
}

/// Aggressive-mode shape rejection reasons. Unbounded = a `.*`/`{n,}`
/// gap (no finite halo); KwInMiddle = keyword interleaved with regex;
/// NoAnchor = regex run with no keyword literal to anchor on.
#[derive(Debug, Clone, PartialEq)]
pub enum AggShapeErr { Unbounded, KwInMiddle, NoAnchor }

/// Shape-guard result for one subsig body. `anchor`: Some(0)=keyword
/// leftmost (forward), Some(1)=keyword rightmost (backward), None=no
/// regex (pure literal). `max_span_bytes`: longest match (finite).
#[derive(Debug, Clone, PartialEq)]
pub struct ShapeInfo { pub anchor: Option<i8>, pub max_span_bytes: usize }

/// Longest possible match of `hir` in bytes. Err(Unbounded) on any
/// `.*`/`.+`/`{n,}` (max None or the {n,} sentinel). Read-only walk.
fn max_match_bytes(hir: &Hir) -> Result<usize, AggShapeErr> {
	match hir.kind() {
		HirKind::Empty | HirKind::Look(_) => Ok(0),
		HirKind::Literal(x) => Ok(x.0.len()),
		HirKind::Class(_) => Ok(1),
		HirKind::Repetition(rep) => {
			let max = match rep.max {
				None | Some(999777979) =>
					return Err(AggShapeErr::Unbounded),
				Some(x) => x as usize,
			};
			Ok(max * max_match_bytes(&rep.sub)?)
		}
		HirKind::Concat(v) => {
			let mut s = 0; for h in v { s += max_match_bytes(h)?; } Ok(s)
		}
		HirKind::Alternation(v) => {
			let mut m = 0;
			for h in v { m = m.max(max_match_bytes(h)?); } Ok(m)
		}
		HirKind::Capture(c) => max_match_bytes(&c.sub),
	}
}

/// A literal segment shorter than this many bytes is regex content
/// (e.g. the leading digit of a number pattern), not a proximity
/// keyword anchor. Real DLP keywords are multi-byte words.
const MIN_KW_ANCHOR_BYTES: usize = 2;

/// A `.{0,N}` gap with N at least this big is the keyword/regex
/// separator (DLP proximity windows are >=100). Bounded only --
/// unbounded gaps are rejected upstream by max_match_bytes.
const GAP_MIN: usize = 100;

/// Whitespace-only class: every byte is tab/newline/CR/space. These are
/// the keyword word-boundary delimiters; they belong to the anchor, not
/// the fan-out regex part.
fn is_ws_class(c: &Class) -> bool {
	let mut dummy = 0usize;
	let bytes = class_to_arr(c, &mut dummy);
	!bytes.is_empty() && bytes.iter().all(|&b|
		b == 0x09 || b == 0x0a || b == 0x0d || b == 0x20)
}

/// N of a `.{0,N}` big gap (bounded N >= GAP_MIN over a wildcard class),
/// else None. Lets the partition pick the LONGEST proximity gap when a
/// pattern has several gaps.
fn gap_size(h: &Hir) -> Option<usize> {
	match h.kind() {
		HirKind::Repetition(rep) => match rep.max {
			Some(m) if (m as usize) >= GAP_MIN
				&& matches!(rep.sub.kind(),
					HirKind::Class(c) if card(c) >= 256) => Some(m as usize),
			_ => None,
		},
		_ => None,
	}
}

/// True for a `.{0,N}` (dot-class repetition) with bounded N >= GAP_MIN.
fn is_big_gap(h: &Hir) -> bool { gap_size(h).is_some() }

/// One DLP arm split around its proximity gap. `dir` 0 = keyword left of
/// the gap (forward), 1 = keyword right (backward). `anchor` = the
/// keyword side plus the gap (re-emitted verbatim); `regex` = the
/// far-side segments (the only fan-out target).
struct ArmShape { dir: i8, anchor: Vec<Hir>, regex: Vec<Hir> }

/// Recognize `[ws]? KW [ws]? .{0,N>=GAP_MIN} REGEX` and its mirror. The
/// keyword side must be only literal(s) and whitespace delimiters; the
/// far side must hold at least one class run. None for any other shape
/// -> caller keeps the whole-HIR path.
fn partition_keyword_gap(hir: &Hir, dir_hint: Option<i8>)
	-> Option<ArmShape> {
	let segs: Vec<&Hir> = match hir.kind() {
		HirKind::Concat(v) => v.iter().collect(),
		_ => return None,
	};
	//longest proximity gap (idea 3): disambiguates multiple gaps.
	let gap = segs.iter().enumerate()
		.filter_map(|(i, s)| gap_size(s).map(|n| (i, n)))
		.max_by_key(|&(_, n)| n).map(|(i, _)| i)?;
	//direction: the caller's hint (from the .fwd/.bwd sig name) wins; else
	//guess from the keyword-literal position (legacy path).
	let dir = match dir_hint {
		Some(d) => d,
		None => {
			let kw = segs.iter().position(|s| matches!(s.kind(),
				HirKind::Literal(x) if x.0.len() >= MIN_KW_ANCHOR_BYTES))?;
			if kw < gap { 0i8 } else { 1i8 }
		}
	};
	let (anchor_rng, regex_rng) = if dir == 0 {
		(0..gap + 1, gap + 1..segs.len())
	} else {
		(gap..segs.len(), 0..gap)
	};
	//keyword side = only literals + whitespace classes (and the gap).
	for i in anchor_rng.clone() {
		if i == gap { continue; }
		match segs[i].kind() {
			HirKind::Literal(_) => {}
			HirKind::Class(c) if is_ws_class(c) => {}
			_ => return None,
		}
	}
	//far side must contain at least one fan-out leg -- only when guessing.
	//With an authoritative dir_hint the far side IS the regex by
	//definition, so a fully-concrete fanned variant (no class run) is fine.
	if dir_hint.is_none()
		&& !regex_rng.clone().any(|i| !find_class_runs(segs[i]).is_empty()) {
		return None;
	}
	Some(ArmShape {
		dir,
		anchor: anchor_rng.map(|i| segs[i].clone()).collect(),
		regex: regex_rng.map(|i| segs[i].clone()).collect(),
	})
}

/// Build a Concat HIR from owned segments (single seg passes through).
fn concat_hir(segs: &[Hir]) -> Hir { Hir::concat(segs.to_vec()) }

/// Re-emit `segs` as PCRE with no pins (faithful). Used for the keyword
/// + gap anchor that surrounds a fanned-out regex part.
fn render_verbatim(segs: &[Hir]) -> String {
	let h = concat_hir(segs);
	let legs = find_class_runs(&h);
	let mut ctr = 0usize;
	emit_variant(&h, &legs, &HashMap::new(), &mut ctr)
}

/// Validate one subsig regex body for aggressive mode and measure span.
/// The keyword literal must sit at exactly one end of the top-level
/// chain (else KwInMiddle / NoAnchor); unbounded gaps rejected. A
/// ws-delimited keyword arm (`[ws]KW[ws].{0,N}REGEX`) is accepted via
/// partition_keyword_gap before the generic check.
pub fn analyze_aggressive_shape(hir: &Hir, dir_hint: Option<i8>)
	-> Result<ShapeInfo, AggShapeErr> {
	let span = max_match_bytes(hir)?;           // also rejects Unbounded
	if let Some(arm) = partition_keyword_gap(hir, dir_hint) {
		return Ok(ShapeInfo { anchor: Some(arm.dir),
			max_span_bytes: span });
	}
	let segs: Vec<&Hir> = match hir.kind() {
		HirKind::Concat(v) => v.iter().collect(),
		_ => vec![hir],
	};
	let (mut lit, mut non) = (Vec::new(), Vec::new());
	for (i, s) in segs.iter().enumerate() {
		if max_match_bytes(s)? == 0 { continue; }   // zero-width: skip
		match s.kind() {
			HirKind::Literal(x)
				if x.0.len() >= MIN_KW_ANCHOR_BYTES => lit.push(i),
			_ => non.push(i),   // short literals = regex content
		}
	}
	if non.is_empty() {
		return Ok(ShapeInfo{anchor: None, max_span_bytes: span});
	}
	if lit.is_empty() { return Err(AggShapeErr::NoAnchor); }
	let (lmin, lmax) = (*lit.iter().min().unwrap(),
		*lit.iter().max().unwrap());
	let (nmin, nmax) = (*non.iter().min().unwrap(),
		*non.iter().max().unwrap());
	if lmax < nmin {
		Ok(ShapeInfo{anchor: Some(0), max_span_bytes: span})   // fwd
	} else if lmin > nmax {
		Ok(ShapeInfo{anchor: Some(1), max_span_bytes: span})   // bwd
	} else {
		Err(AggShapeErr::KwInMiddle)
	}
}

/// Anchor direction from a generator sig name: 'fwd' -> 0 (keyword left),
/// 'bwd' -> 1 (keyword right). Asserts the name carries a 'fwd'/'bwd'
/// keyword (the generator always appends .fwd/.bwd to a DLP proximity
/// sig); a missing one is a generator/format bug.
pub fn direction_from_name(name: &str) -> i8 {
	assert!(name.contains("fwd") || name.contains("bwd"),
		"aggressive shape: sig name '{}' must contain a 'fwd'/'bwd' \
		 direction keyword", name);
	if name.contains("bwd") { 1 } else { 0 }
}

/// Cardinality of a character class = count of distinct bytes it
/// matches. `[0-9]`=10, hex=16, `[a-z]`/`[A-Z]`=26, alnum=62,
/// wildcard=256. Used as the per-leg fan-out multiplier in
/// select_slots. Reuses class_to_arr for an identical byte set.
fn card(class: &Class) -> usize {
	let mut dummy = 0usize;
	class_to_arr(class, &mut dummy).len()
}

/// True iff every byte matched by `class` shares one high nibble
/// (byte>>4). `[0-9]`=3_, `[a-f]`=6_, `[A-O]`=4_ -> true;
/// `[a-z]`/`[A-Z]`/alnum span two blocks -> false. Tier-1 (free
/// borrow) eligibility for the SDE-rep anchor renderer (M4, cs path).
/// Empty class -> false (nothing to anchor).
fn is_single_hi_nibble_block(class: &Class) -> bool {
	let mut dummy = 0usize;
	let bytes = class_to_arr(class, &mut dummy);
	match bytes.first() {
		None => false,
		Some(&first) => {
			let hi = first >> 4;
			bytes.iter().all(|&b| b >> 4 == hi)
		}
	}
}

/// Position priority within a leg of length `n`: first, last, then
/// inward from the end -> [0, n-1, n-2, .., 1]. Spreads pinned digits
/// across the run (first & last before any middle) for wider positional
/// coverage, mirroring the leg-level priority.
fn pos_priority(n: usize) -> Vec<usize> {
	let mut q = Vec::with_capacity(n);
	if n == 0 { return q; }
	q.push(0);
	for i in (1..n).rev() { q.push(i); }
	q
}

/// Like `pos_priority` but biased for the LAST leg: visit position n-2
/// first so the pinned byte sits next to a trailing factored class.
/// After factoring, that produces a `<pin>3(<low>)` literal whose
/// fixed prefix is 3 hex chars (pinned byte + next class's high
/// nibble) — a pm-reg anchor. Falls back to standard order when n<2.
fn pos_priority_last(n: usize) -> Vec<usize> {
	if n < 2 { return pos_priority(n); }
	let target = n - 2;
	let mut q = Vec::with_capacity(n);
	q.push(target);
	q.push(0);
	for i in (1..n).rev() {
		if i != target { q.push(i); }
	}
	q
}

/// Max concrete values a single pinned position may fan out to. Legs
/// whose folded cardinality exceeds this are skipped in select_slots:
/// keeps digits (10), hex (16) and single-case letters (26); drops
/// combined letters (52), alnum (62) and the full wildcard (256/128).
const SINGLE_FANOUT_MAX: usize = 26;

/// Choose which (leg, position) slots to pin for fan-out, under a
/// product budget `b` (= combination_limit). Walk round-major: for each
/// round, visit legs in priority [0, m-1, m-2, .., 1] (first leg, last
/// leg, then middles right-to-left); within a leg the round indexes its
/// pos_priority (first, last, then inward). Take a slot iff
/// product*card(leg) <= b (then grow the product); else skip and keep
/// going so leftover budget can flow to a cheaper leg / position.
/// Returns chosen slots in consideration order; the product of their
/// cardinalities is the fan-out size (<= b). Cardinality for the budget
/// is FOLDED under `b_igc` (igc collapses case pairs, e.g. hex 12->6, so
/// more positions fit). A leg whose folded cardinality exceeds
/// SINGLE_FANOUT_MAX is never pinned -- weak high-card legs (combined
/// letters 52, alnum 62, full wildcard) yield poor anchors, so budget is
/// kept for selective ones (digits 10, hex 16, single-case letters 26).
fn select_slots(legs: &[Leg], b: usize,
	b_igc: bool, tight: bool) -> Vec<(usize, usize)> {
	let m = legs.len();
	if m == 0 { return Vec::new(); }
	//leg priority:
	// - default: first leg, last leg, then middles right-to-left
	// - tight  : first + last only (middles stay as full classes)
	let prio: Vec<usize> = if tight {
		if m == 1 { vec![0] } else { vec![0, m - 1] }
	} else {
		let mut p = Vec::with_capacity(m);
		p.push(0);
		for i in (1..m).rev() { p.push(i); }
		p
	};
	//per-leg position priority:
	// - last leg (incl. single-leg case): pos_priority_last
	// - first leg in tight mode (only when there is a distinct
	//   last leg): forward [0,1,..,n-1] so adjacent bytes get
	//   pinned together -> longer fixed-literal anchor
	// - all other legs: pos_priority (= [0, n-1, n-2, .., 1])
	let qs: Vec<Vec<usize>> = legs.iter().enumerate()
		.map(|(idx, l)| {
			if idx == m - 1 {
				pos_priority_last(l.min)
			} else if tight && idx == 0 {
				(0..l.min).collect()
			} else {
				pos_priority(l.min)
			}
		}).collect();

	let max_n = legs.iter().map(|l| l.min).max().unwrap_or(0);
	let mut chosen = Vec::new();
	let mut product = 1usize;
	//passes: fund guaranteed (mandatory) legs before optional ones, and
	//within each, pure-digit legs before mixed (separator+digit) ones.
	//Mandatory pins become pm-reg anchors; optional ones collapse to
	//wildcards. A pure-digit leg anchors in every variant, so funding it
	//first keeps the budget from being starved on a mixed column (e.g.
	//`[\x2D0-9]`) before a clean digit run. Pure-digit-only inputs (the
	//NEEDS drivers) are unchanged: the mixed pass finds nothing.
	for want_optional in [false, true] {
	for want_pure in [true, false] {
		for round in 0..max_n {
			for &leg in &prio {
				if legs[leg].optional != want_optional { continue; }
				if leg_is_pure_digit(&legs[leg].class) != want_pure {
					continue; }
				if round >= qs[leg].len() { continue; }
				//budget uses folded cardinality (igc collapses cases).
				let c = card_igc(&legs[leg].class, b_igc);
				//cap one position's fan-out: skip weak high-card legs
				//(combined letters/alnum/full wildcard); keep selective
				//ones so budget flows to strong anchors.
				if c > SINGLE_FANOUT_MAX { continue; }
				let pos = qs[leg][round];
				if product.saturating_mul(c) <= b {
					product *= c;
					chosen.push((leg, pos));
				}
			}
		}
	}
	}
	chosen
}

/// Render one concrete byte as a PCRE hex escape, e.g. 0x35 -> `\x35`.
/// Uniformly safe for non-printable / regex-special bytes. Two-nibble
/// (even) anchor -> compatible with the igc whole-byte fold (M4).
fn byte_to_pcre(b: u8) -> String {
	format!("\\x{:02x}", b)
}

/// Render a character class as a compact PCRE bracket expression over
/// hex escapes, coalescing consecutive bytes into ranges, e.g.
/// `[0-9]` -> `[\x30-\x39]`, full wildcard -> `[\x00-\xff]`. Endpoints
/// are `\xNN` so `]`,`-`,`^`,`\` never need special escaping. Empty
/// class -> empty string. Reuses class_to_arr for the byte set.
fn class_to_pcre(class: &Class) -> String {
	let mut dummy = 0usize;
	let bytes = class_to_arr(class, &mut dummy);
	if bytes.is_empty() { return String::new(); }
	// M9 fix-A (2026-06-02): collapse the full-byte class to "."
	// instead of "[\x00-\xff]". The variant string is only consumed
	// by pcre_to_rustomaton_regex downstream; in the rustomaton-hex
	// domain "." matches any single nibble, so ".?.?" per byte gives
	// the same matching power as the 256-element byte alternation but
	// at ~200x smaller string size. Soundness: every real
	// SubSigObj.value consumer is gated on CounterConstraint or
	// DFA-routed sigs; DLP variants are GeneralRegex/SED-routed and
	// pass through this path only at the rustomaton level.
	if bytes.len() == 256 {
		return ".".to_string();
	}
	let mut s = String::from("[");
	let mut i = 0;
	while i < bytes.len() {
		let start = bytes[i];
		let mut end = start;
		while i + 1 < bytes.len()
			&& end < u8::MAX && bytes[i + 1] == end + 1 {
			end = bytes[i + 1];
			i += 1;
		}
		s.push_str(&byte_to_pcre(start));
		if start != end {
			s.push('-');
			s.push_str(&byte_to_pcre(end));
		}
		i += 1;
	}
	s.push(']');
	s
}

/// PCRE quantifier suffix for a `{min,max}` run (None = unbounded):
/// `*` `+` `?` `{n}` `{n,}` `{0,n}` `{m,n}`. Used to re-emit an
/// unpinned leg compactly and to wrap a non-class repetition body.
fn quantifier_str(min: usize, max: Option<usize>) -> String {
	match max {
		None => match min {
			0 => "*".to_string(),
			1 => "+".to_string(),
			_ => format!("{{{},}}", min),
		},
		Some(mx) => {
			if min == 0 && mx == 1 { "?".to_string() }
			else if mx == min { format!("{{{}}}", min) }
			else if min == 0 { format!("{{0,{}}}", mx) }
			else { format!("{{{},{}}}", min, mx) }
		}
	}
}

/// Re-emit one class-repetition leg with its pinned positions fixed to
/// concrete bytes. Positions `0..min` are guaranteed (pinnable); each is
/// a `\xNN` if assigned, else the class. The optional `min..max` tail
/// stays as the class (`*` if unbounded, `?`/`{0,t}` otherwise). With no
/// pin, emit the compact `class{min,max}` form. `idx` = this leg's index.
fn emit_leg(leg: &Leg, idx: usize,
	assign: &HashMap<(usize, usize), u8>) -> String {
	let cp = class_to_pcre(&leg.class);
	let has_pin = (0..leg.min)
		.any(|p| assign.contains_key(&(idx, p)));
	if !has_pin {
		return format!("{}{}", cp,
			quantifier_str(leg.min, leg.max));
	}
	let mut s = String::new();
	for p in 0..leg.min {
		match assign.get(&(idx, p)) {
			Some(b) => s.push_str(&byte_to_pcre(*b)),
			None => s.push_str(&cp),
		}
	}
	//variable tail: the optional (max-min) positions stay class.
	match leg.max {
		None => { s.push_str(&cp); s.push('*'); }
		Some(mx) => {
			let t = mx - leg.min;
			if t == 1 { s.push_str(&cp); s.push('?'); }
			else if t > 1 {
				s.push_str(&format!("{}{{0,{}}}", cp, t));
			}
		}
	}
	s
}

/// Re-emit `hir` as a PCRE string with the pinned (leg, pos) slots in
/// `assign` fixed to concrete bytes; everything else is reproduced
/// faithfully. `ctr` tracks the leg index, incremented at exactly the
/// nodes collect_class_runs treats as legs (bare Class, Repetition over
/// a Class) so indices stay aligned with `legs`. M3 = no borrow / no
/// igc fold; pinned bytes are plain whole-byte anchors.
fn emit_variant(hir: &Hir, legs: &[Leg],
	assign: &HashMap<(usize, usize), u8>, ctr: &mut usize) -> String {
	match hir.kind() {
		Empty => String::new(),
		HirKind::Literal(x) => x.0.iter()
			.map(|b| byte_to_pcre(*b)).collect::<String>(),
		HirKind::Class(_) => {
			let idx = *ctr; *ctr += 1;
			match assign.get(&(idx, 0)) {
				Some(b) => byte_to_pcre(*b),
				None => class_to_pcre(&legs[idx].class),
			}
		}
		HirKind::Repetition(rep) => match rep.sub.kind() {
			// class-rep with min>=1 is a leg in collect_class_runs;
			// consume ctr and emit pinned/unpinned via emit_leg.
			HirKind::Class(_) if rep.min >= 1 => {
				let idx = *ctr; *ctr += 1;
				emit_leg(&legs[idx], idx, assign)
			}
			// class-rep with min==0 (`.{0,k}`, `[-\s]?`, `[0-9]{2}?`)
			// is NOT a leg in collect_class_runs (line 524 skip);
			// re-emit faithfully WITHOUT consuming ctr so leg indices
			// stay aligned with collect_class_runs.
			HirKind::Class(c) => {
				let cp = class_to_pcre(c);
				let max = match rep.max {
					Some(999777979) => None,
					m => m.map(|x| x as usize),
				};
				format!("{}{}", cp,
					quantifier_str(rep.min as usize, max))
			}
			//non-class body (e.g. `(ab)+`): descend, wrap, no pin.
			_ => {
				let inner =
					emit_variant(&rep.sub, legs, assign, ctr);
				let max = match rep.max {
					Some(999777979) => None,
					m => m.map(|x| x as usize),
				};
				format!("(?:{}){}", inner,
					quantifier_str(rep.min as usize, max))
			}
		},
		HirKind::Concat(v) => v.iter()
			.map(|h| emit_variant(h, legs, assign, ctr))
			.collect::<String>(),
		HirKind::Alternation(v) => {
			let parts: Vec<String> = v.iter()
				.map(|h| emit_variant(h, legs, assign, ctr))
				.collect();
			format!("(?:{})", parts.join("|"))
		}
		HirKind::Capture(cap) =>
			format!("({})", emit_variant(&cap.sub, legs, assign, ctr)),
		HirKind::Look(l) => match l {
			Look::Start => "^".to_string(),
			Look::End => "$".to_string(),
			Look::WordAscii => "\\b".to_string(),
			_ => String::new(),
		},
	}
}

/// Enumerate concrete fan-out variants of `hir`: the cross product of
/// candidate bytes over the chosen `slots`, one PCRE string each.
/// Slots are sorted to canonical (leg, pos) order and each slot's bytes
/// are ascending, so the enumeration is LEXICOGRAPHIC (first slot most
/// significant) -> deterministic goldens & stable SNARK cache. Count =
/// product of the selected legs' cardinalities (== fan-out budget use).
///
/// Example: `[0-9]{3}` with slots `[(0,0),(0,2)]` (pin first & last
/// digit, middle stays class) -> 100 variants, lexicographic:
///   out[0]  = `\x30[\x30-\x39]\x30`
///   out[1]  = `\x30[\x30-\x39]\x31`
///   ...
///   out[99] = `\x39[\x30-\x39]\x39`
/// Under `b_igc` the per-slot candidate bytes are case-FOLDED to
/// lowercase (digits unchanged), so igc variants pin even 2-nibble
/// lowercase anchors and never duplicate an `a`/`A` pair.
fn render_variants(hir: &Hir, legs: &[Leg],
	slots: &[(usize, usize)], b_igc: bool) -> Vec<String> {
	let mut order = slots.to_vec();
	order.sort();
	//candidate bytes per slot (folded under igc; ascending -> lex enum).
	let cands: Vec<Vec<u8>> = order.iter().map(|&(l, _)| {
		let mut dummy = 0usize;
		let raw = class_to_arr(&legs[l].class, &mut dummy);
		fold_bytes_igc(&raw, b_igc)
	}).collect();
	let total: usize = cands.iter().map(|c| c.len()).product();
	let mut out = Vec::with_capacity(total);
	let mut idxs = vec![0usize; order.len()];
	loop {
		let mut assign = HashMap::new();
		for (k, &(l, p)) in order.iter().enumerate() {
			assign.insert((l, p), cands[k][idxs[k]]);
		}
		let mut ctr = 0usize;
		out.push(emit_variant(hir, legs, &assign, &mut ctr));
		//mixed-radix increment, last slot least significant.
		let mut k = order.len();
		loop {
			if k == 0 { return out; }
			k -= 1;
			idxs[k] += 1;
			if idxs[k] < cands[k].len() { break; }
			idxs[k] = 0;
		}
	}
}

/// encoded string is in hex,
/// b_process_literal is set then convert every char e.g., 'a' to '61'
/// IT IS USED when in hex mode
fn hex_hir_to_dfa(s: &str, hir: &Hir, b_ignore_case: bool, b_process_literal: bool) -> DFA<char>{
	let mut res = match hir.kind(){
		Empty => build_dfa("", false),
		HirKind::Concat(v) => {
			let mut dfa_res = build_dfa("", false);
			//IT looks like concat "" with any would have problem
			//have to take out dfa_res from v[0] first.
			let dummy_fa = build_dfa("", false);
			let mut b_initialized = false;
			for i in 0..v.len(){
				let x = &v[i];
				let cur_dfa = hex_hir_to_dfa("",x, b_ignore_case, b_process_literal);
				let cur_dfa = cur_dfa.minimize();
				if !b_initialized && (cur_dfa.transitions.len()>1
					|| cur_dfa != dummy_fa){ 
					//if never initialized and cur_dfa is NOT empty
					dfa_res = cur_dfa.clone();
					b_initialized = true;
				}else if b_initialized && (cur_dfa.transitions.len()>1
					|| cur_dfa != dummy_fa){
					dfa_res = dfa_res.clone().concatenate(cur_dfa);
				}else{//skip it because cur_dfa is EMPTY and cause
						//problem with concat
				}
				dfa_res = dfa_res.minimize();

			}

			dfa_res
		},
		HirKind::Literal(x) => {
			let sx = if b_process_literal {
				u8_to_hex(&char_arr_to_u8(&x.0.to_vec()))
			}else{
				String::from_utf8(x.0.to_vec()).expect("failed u8_to_s")
			};
			let sx = if b_ignore_case {to_ignore_case(&sx)} else {sx};
			build_dfa(&sx, false)
		},
		HirKind::Repetition(v) =>{
			let (min,mut max) = (v.min as usize, v.max);
			if max==Some(999777979){ max = None;}  //deal with preproces logic
			//1. deal with the [0, min] case
			let empty_dfa = build_dfa("", false);
			let unit_dfa = hex_hir_to_dfa("",&v.sub, b_ignore_case, b_process_literal);
			let dfa_res = if max.is_none(){ unit_dfa.at_least(min) }
			else{ unit_dfa.repeat( min..(max.unwrap() as usize + 1) ) };
			//somehow cannot handle .* well, union with empty dfa if
			//min is 0
			let dfa_res = if min>0 {dfa_res} else {dfa_res.unite(empty_dfa)};

			dfa_res
		},
		HirKind::Class(v) => {
			let dfa = if b_process_literal{//PCRE mode
				//limit 256 guarantees to cover all
				let mut limit = 256;
				let (v_str, _pcre_info) = handle_class_full(&v, &mut limit);
				let v_str = v_str.into_iter().map(|s| 
					if b_ignore_case {to_ignore_case(&s)} else {s}
				).collect::<Vec<String>>();
				let rust_reg = join_vs(&v_str);
				let dfa = build_dfa(&rust_reg, false);

				dfa
			}else{//pure hex mode. NOTE that parse WRONGLY parses '.'
				  //as [0x00-0xFF] but it actually SHOULD be 0x0-0xF
				  let mut limit = 256;
				  let vbytes = class_to_arr(&v, &mut limit);
				  let dfa = if vbytes.len()==256{
				  	let rust_reg = "(0|1|2|3|4|5|6|7|8|9|a|b|c|d|e|f)";
				  	let dfa = build_dfa(&rust_reg, false);

				  	dfa
				  }else{
				  	assert!(vbytes.len()<=16, "CANNOT handle cases OTHER than full 0x0-0xf case.");
					let v_str = vbytes.iter().map(|x| format!("{}", (*x as char))).collect::<Vec<String>>();
					let v_str = v_str.into_iter().map(|s| 
						if b_ignore_case {to_ignore_case(&s)} else {s}
					).collect::<Vec<String>>();

					let rust_reg = join_vs(&v_str);
					let dfa = build_dfa(&rust_reg, false);


				  	dfa
				};
				dfa
			};
			let dfa = dfa.minimize();
			dfa
		},
		HirKind::Look(v) => {//no need to handle, later pcre info
			//will have it
			match v{
				Look::WordAscii => {
					let mut vec:Vec<u8> = vec![];
					for i in 0..=255{
						if i!=0x09 && i!=0x0a && i!=0x0d && i!=0x20{
							vec.push(i);
						}
					}
					let vstr = vec.iter().map(|v| 
						(&format!("{:#04x}",v)[2..]).to_string())
						.collect::<Vec<String>>();
					let s = join_vs(&vstr);
					build_dfa(&s, false)
				}
				_ => build_dfa("", false)
			}
		}
		HirKind::Alternation(v) => {
			let mut dfa_res = build_dfa("", false);
			let dummy_fa = build_dfa("", false);
			let mut b_initialized = false;
			for i in 0..v.len(){
				let x = &v[i];
				let cur_dfa = hex_hir_to_dfa("",x, b_ignore_case, b_process_literal);
				if !b_initialized && (cur_dfa.transitions.len()>1
					|| cur_dfa != dummy_fa){ 
					//if never initialized and cur_dfa is NOT empty
					dfa_res = cur_dfa.clone();
					b_initialized = true;
				}else if b_initialized && (cur_dfa.transitions.len()>1
					|| cur_dfa != dummy_fa){
					dfa_res = dfa_res.clone().unite(cur_dfa);
				}else{//skip it because cur_dfa is EMPTY and cause
						//problem with concat
				}
			}
			dfa_res
		},
		HirKind::Capture(v) => hex_hir_to_dfa("", &v.sub, b_ignore_case, b_process_literal) 
	};

	let min_bar = 256;
	if res.transitions.len()<min_bar{ res = res.minimize();} 
	res.raw_str = format!("{}", s);

	res
}


/// convert a pcre regex to the rustomaton format of hex strings
/// e.g., "AB.*" to "4142.*"
pub fn pcre_to_rustomaton_regex(s: &str, combination_limit: usize, repeat_limit: usize) -> (String, PcreInfo){
	let s = preprocess_badchars(&s, true);//nibble path: keep doubling
	let (s, b_backref) = preprocess_backref(&s);
	let s = preprocess_rep(&s);
	let hir  = to_hir(&s);
	
	let mut limit = combination_limit;
	let (vec_s, mut pi) = pcre_hir_to_rustomaton_regex(&hir, &mut limit, repeat_limit);

	pi.b_backref = b_backref;
	let mut res = join_vs(&vec_s);
	if !pi.b_begin{ res = ".*".to_string() + &res; }
	if !pi.b_end{ res = res + ".*"; }

	(res, pi)
}



/// convert hir of PCRE regex to regex accepted by rustomaton
/// return a collection of regex accepted by rustomaton,
/// their relation is union, limit is the combination limit so that
/// it returns a vector of strings of no more than limit
fn pcre_hir_to_rustomaton_regex(hir: &Hir, combination_limit: &mut usize, repeat_limit: usize) -> (Vec<String>, PcreInfo){
	let res = match hir.kind(){
		Empty => (vec![String::new()], PcreInfo::new_pcre()),
		HirKind::Literal(x) => (vec![u8_to_hex(&char_arr_to_u8(&x.0.to_vec()))],			PcreInfo::new_pcre()),
		HirKind::Concat(v) => handle_concat(&v, combination_limit, repeat_limit),
		HirKind::Repetition(v) => handle_repeat(&v, combination_limit, repeat_limit),
		HirKind::Class(v) => handle_class(&v, combination_limit, repeat_limit),
		HirKind::Capture(v) => handle_capture(&v, combination_limit, repeat_limit),
		HirKind::Alternation(v) => handle_alt(&v, combination_limit, repeat_limit),
		HirKind::Look(v) => handle_look(&v, combination_limit, repeat_limit),
	};

	res
}


/// simply return empty string for zero assertions
/// we handle 3 cases only: (1) beginning, (2) end, (3) \b
/// for begin and end case, eventually no .* is appended at
/// the beginning and end of the generated regex, and for (3)
/// we require that either the previous one is a repeat pattern (which
/// we minus the repeat length by 1), or at the beginning of the
/// entire pattern (so that it's actually -1 for the .* at the beginning)
/// of pattern. For others we use the APPROXIMATATION of no look
/// given that the subsignatures are not negated, this is over approximation.
fn handle_look(v: &Look, _limit: &mut usize, _repeat_limit: usize) -> (Vec<String>, PcreInfo){
	let (mut b_begin, mut b_end, mut b_boundary) = (false, false, false);
	match v{
		Look::Start => b_begin = true,
		Look::End =>  b_end = true,
		Look::WordAscii => b_boundary = true,
		_ => println!("WARN: look: {:?} not handled", v)
	}
	let fill_str = if b_boundary {"!(09|0a|0d|20)".to_string()}
		else {"".to_string()}; //assuming the previous item's length -1
	(vec![fill_str], PcreInfo{b_pcre: true, b_backref: false, b_zero_assert: true, b_begin: b_begin, b_end: b_end, b_boundary: b_boundary, original_str: String::new() })
}

/// only handle it in the concat case,  for all other cases
/// just do not handle (do not enforce, over approximation). 
/// In the concat has two cases to handle:
/// (1) left_case: it is located at the beginning or
/// its right is a fixed word, in this case insert a 
/// whitespace char and reduce the previous item by one.
/// (2) right_case: it is located at the right end of a word
/// the resulting vec of Hir is either a copy of the original,
/// or with a \W item inserted (with preceding item or subsequent item
/// modified.
fn handle_boundary(vec: &Vec<Hir>, b_can_handle: bool) -> Vec<Hir>{
	if !b_can_handle {return vec.clone()};
	let mut vec = vec.clone();

	//1. some assisting functions
	let is_boundary = |h: &Hir| -> bool {
		match h.kind(){
			HirKind::Look(v) => {*v==Look::WordAscii},
			_ => false
		}
	};
	let idx_bitem = |v: &Vec<Hir>|->usize {
		for i in 0..v.len(){ if is_boundary(&v[i]) {return i;} }
		v.len()
	};
	let is_leftcase = |v: &Vec<Hir>, i: usize| -> bool{
		i==0 || match v[i-1].kind(){
			HirKind::Repetition(_v) => true,
			_ => false
		}
	};
	let is_rightcase = |v: &Vec<Hir>, i: usize| -> bool{
		i==v.len()-1 || match v[i+1].kind(){
			HirKind::Repetition(_v) => true,
			_ => false
		}
	};
	let reduced = |h: &Hir| -> Hir{//if possible reduce length by one
		match h.kind(){
			HirKind::Repetition(v) => {
				let min = if v.min>1 {v.min-1} else {v.min};
				let max = if v.max.is_none() {v.max} else {
					if v.max.unwrap()>1 {Some(v.max.unwrap()-1)} 
					else {Some(v.max.unwrap())}
				};
				let mut v2 = v.clone();
				v2.min = min;
				v2.max = max;
				Hir::repetition(v2)
			},
			_ => h.clone()
		}
	};
	let spaceclass = || -> Hir{
		to_hir("[ \t\n]")
	};
			
	while idx_bitem(&vec) < vec.len(){//break
		let idx = idx_bitem(&vec);
		if is_leftcase(&vec, idx){
			vec[idx] = spaceclass();
			if idx>=1 {vec[idx-1] = reduced(&vec[idx-1]);}
		}
		if is_rightcase(&vec, idx){
			vec[idx] = spaceclass();
			if idx+1<=vec.len()-1 {vec[idx+1] = reduced(&vec[idx+1]);}
		}
	}

	vec
}

/// check if all components are literal strings recursively
fn is_all_literals(hir: &Hir)->bool{
	let res = match hir.kind(){
		Empty => true,
		HirKind::Literal(_x) => true,
		HirKind::Concat(v) => {
			let mut res = true;
			for x in v{ res = res & is_all_literals(x); }
			res
		},
		HirKind::Capture(v) => {
			is_all_literals(&v.sub)
		},
		HirKind::Look(_v) => true,
		HirKind::Class(v) => {
			let mut _limit = 1024usize;
			let vbytes = class_to_arr(v, &mut _limit);
			//so that it's not translated to .
			vbytes.len()!=256 
		}
		HirKind::Alternation(v) => {
			let mut res = true;
			for x in v{ res = res & is_all_literals(x); }
			res
		},
		HirKind::Repetition(v) => {//only ok if fixed pattern
			!v.max.is_none() && v.min==v.max.unwrap()
		}
	};
	res
}

/// convert a concat structure into regex accepted by rustomaton
/// use the limit to control the number of alternation substrings,
/// e.g. (a|b)(c|d) generates blow up of (ab|ad|bc|bd), if the limit
/// is 3 then the function does not generate the combinations.
fn handle_concat(vec: &Vec<Hir>, limit: &mut usize, repeat_limit: usize)->(Vec<String>, PcreInfo){
	let vec = handle_boundary(vec, true);
	let mut vres:Vec<String> = vec![String::new()];
	let mut cur_pi = PcreInfo::new_pcre(); 
	let mut last_is_lit = true;
	for hir in vec{
		let is_lit = is_all_literals(&hir);
		let (cur_v, pi) = pcre_hir_to_rustomaton_regex(&hir, limit, repeat_limit);
		cur_pi = cur_pi.or(&pi);
		if cur_v.len()*vres.len()<*limit && is_lit && last_is_lit{
			vres = vres.iter().map(|x|
					cur_v.iter().map(|y| x.to_string() + &y)
						.collect::<Vec<String>>())
					.fold(vec![], |mut acc, mut vec|{
						acc.append(&mut vec);
						acc
					});
		}else{
			let cur_s = join_vs(&cur_v);
			vres = vres.iter().map(|s| s.to_string() + &cur_s)
				.collect::<Vec<String>>();
		}
		last_is_lit = is_lit;
	}

	(vres, cur_pi)
}

/// convert a concat structure into regex accepted by rustomaton
/// _limit: combination limit, not used here.
fn handle_class(v: &Class, _limit: &mut usize, _repeat_limit: usize)->(Vec<String>, PcreInfo){
	let vbytes = class_to_arr(v, _limit);

	let vstr = if vbytes.len()==256 {vec![".".to_string()]} else{
		factor_high_nibble(&vbytes)
	};
	(vstr, PcreInfo::new_pcre())
}

/// Emit a byte class as rustomaton-hex. The returned Vec<String> is
/// joined by `join_vs` as an ALT, so we return a single-element vec
/// to keep the factored form as a concat. Bytes are grouped by high
/// nibble; each group emits `<h>(<lows>)` and the groups are joined
/// by `|`. This exposes the high nibble as a fixed-literal anchor for
/// pm-reg whenever the byte run lives in a single high-nibble row,
/// and even across rows gives each branch a fixed leading nibble.
fn factor_high_nibble(vbytes: &[u8]) -> Vec<String> {
	if vbytes.len() < 2 {
		return vbytes.iter()
			.map(|v| (&format!("{:#04x}", v)[2..]).to_string())
			.collect();
	}
	let mut groups: std::collections::BTreeMap<u8, Vec<u8>>
		= std::collections::BTreeMap::new();
	for &b in vbytes {
		groups.entry(b >> 4).or_default().push(b & 0x0f);
	}
	let fmt_group = |high: u8, lows: &[u8]| -> String {
		if lows.len() == 1 {
			format!("{:x}{:x}", high, lows[0])
		} else {
			let alt = lows.iter()
				.map(|l| format!("{:x}", l))
				.collect::<Vec<_>>().join("|");
			format!("{:x}({})", high, alt)
		}
	};
	if groups.len() == 1 {
		let (h, ls) = groups.iter().next().unwrap();
		return vec![fmt_group(*h, ls)];
	}
	let branches: Vec<String> = groups.iter()
		.map(|(h, ls)| fmt_group(*h, ls)).collect();
	vec![format!("({})", branches.join("|"))]
}

/// Expose the fixed high nibble of a single-high-nibble class group so it sits
/// CONTIGUOUS with an adjacent pinned/literal byte, giving the pm-reg extractor
/// a >=3-hex anchor (e.g. a pinned `30` before a digit class yields `303`).
/// In one non-overlapping pass over a rustomaton-hex string:
///   `(h(l|l|..))`     -> `h(l|l|..)`                  (paren is redundant)
///   `(h(l|l|..)){n}`  -> `h(l|l|..)(h(l|l|..)){n-1}`  (PEEL one iteration)
/// Peeling -- never bare-stripping a quantified group -- keeps the language
/// identical. Used ONLY on aggressive fan-out variant real_values, so the
/// non-aggressive pipeline is byte-identical. Multi-high-nibble groups (letters:
/// `(4..|5..)`) and `(?:..)` never match (`[0-9a-f]\(` needs a single hex digit
/// right after `(`), so alternations are left untouched.
pub fn expose_hi_nibble_anchor(hex: &str) -> String {
	let rx = match regex::Regex::new(
		r"\(([0-9a-f]\([^()]*\))\)(?:\{(\d+)\})?") {
		Ok(r) => r, Err(_) => return hex.to_string(),
	};
	rx.replace_all(hex, |c: &regex::Captures| {
		let inner = &c[1];
		match c.get(2).map(|m| m.as_str().parse::<usize>().unwrap_or(1)) {
			None | Some(0) | Some(1) => inner.to_string(),
			Some(k) => format!("{}({}){{{}}}", inner, inner, k - 1),
		}
	}).to_string()
}

/// no packing to . trick
fn handle_class_full(v: &Class, _limit: &mut usize)->(Vec<String>, PcreInfo){
	let vbytes = class_to_arr(v, _limit);
	let vstr = vbytes.iter().map(|v| 
					(&format!("{:#04x}",v)[2..]).to_string())
					.collect::<Vec<String>>();
	(vstr, PcreInfo::new_pcre())
}


/// convert concat structure into regex accepted by rustomaton
/// _limit: combination limit, not used here.
/// it uses consants: REPEAT_LEN_LIMIT
/// sometimes numbered repetions creates too long string
/// for fixed number reps, e.g., [^"]{1000, 2000}, the char
/// class has 255 chars, and the long string is repeated for many times
/// in this case, when length exceeding the limit, approximate the
/// substr with .
fn handle_repeat(v: &Repetition, limit: &mut usize, repeat_limit: usize)->(Vec<String>, PcreInfo){
	let vec = handle_boundary(&vec![*v.sub.clone()], false);
	let (vstr, pi) = pcre_hir_to_rustomaton_regex(&vec[0], limit, repeat_limit);
	let sub_str = join_vs(&vstr);
	let sub_str = if sub_str=="." {sub_str} else {"(".to_string() + &sub_str 
		+ ")"};
	let (min,mut max) = (v.min as usize, v.max);
	if max==Some(999777979){ max = None;} 
	let substr_len =sub_str.len();

	//min2 is the approximated part
	//1. decide if needs to approximate
	let b_approx = substr_len * min > repeat_limit;
	let (min1, min2) = if !b_approx || min<repeat_limit/substr_len
		{(min, 0usize)} else 
		{( repeat_limit/substr_len, min - repeat_limit/substr_len)};

	//2. decide (heurstics) if all unioned substrings have equal length
	let mut b_literal = true;
	let mut min_unit_len = repeat_limit;
	let mut max_unit_len = 0;
	for s in &vstr {
		b_literal = b_literal && is_match(r"[0-9a-f]+", s);
		min_unit_len = if s.len()<min_unit_len {s.len()} else {min_unit_len};
		max_unit_len = if s.len()>max_unit_len {s.len()} else {max_unit_len};
	}
	// deep approx happens when we are not sure of the substr length
	// simply padd the rest with .*
	let deep_approx = !b_literal || min_unit_len != max_unit_len;
	
	let res = match max{
		Some(max_v) => {
			let max_v = max_v as usize;
			if min2==0{
				sub_str.repeat(min) + 
					&format!("{}?", &sub_str).repeat(max_v - min)
			}else{
				if !deep_approx{
					sub_str.repeat(min1) + 
						&".".to_string().repeat(min2*min_unit_len) + 
						&".?".repeat( (max_v - min)*min_unit_len)
				}else{
					sub_str.repeat(min1) + ".*" //deep approx
				}
			}
		},
		None => if min2==0{
			sub_str.repeat(min) + &format!("{}*", &sub_str)
		}else{
			if !deep_approx{
				sub_str.repeat(min1) + 
				&".".to_string().repeat(min2*min_unit_len) + ".*"
			}else{
				sub_str.repeat(min1) + ".*" //deep approx 
			}
		}
	};

	if b_approx {
		println!("WARN: handle_repeat apparoax: {:?} => len: {}", 
		v, res.len()); 
	}

	(vec![res], pi)
}

/// handle capture (group). Note we do not support named group
/// or backreferences (as Rust regex).
/// _limit: combination limit, not used here.
fn handle_capture(v: &Capture, limit: &mut usize, repeat_limit: usize)->(Vec<String>, PcreInfo){
	let vec = handle_boundary(&vec![*v.sub.clone()], false);
	assert!(vec.len()==1, "handle_capture: after handle boundary vec.len!=1");
	pcre_hir_to_rustomaton_regex(&vec[0], limit, repeat_limit)
}

/// handle alternation
/// _limit: combination limit, not used here.
fn handle_alt(v: &Vec<Hir>, limit: &mut usize, repeat_limit: usize)->(Vec<String>, PcreInfo){
	let _vec = handle_boundary(&v, false);
	let mut vec = vec![];
	let mut cur_pi = PcreInfo::new_pcre();
	for hir in v{
		let (v1, pi) = pcre_hir_to_rustomaton_regex(hir, limit, repeat_limit);
		cur_pi = cur_pi.or(&pi);
		vec.append(&mut v1.clone());
	}

	(vec, cur_pi)
}

/// collect bag of words by parsing rustomaon regex syntax
/// required that the regex follows rustomaton regex syntax and
/// all chars converted to hex nibbles
pub fn collect_bag_words_from_rustomaton_regex(s: &str, min_bag_len: usize, combination_limit: usize) -> HashSet<Vec<String>>{
	let hir = rustomaton_to_hir(s);
	let mut limit = combination_limit;
	let (hs, _b) = collect_bag_words_from_rustomaton_regex_worker(&hir,
		&mut limit, min_bag_len);
	hs
}

/// filter all VECs that contain at least one word less than min_word_len
pub fn filter_bag_of_words(bags: &HashSet<Vec<String>>, min_bag_len:  usize) -> HashSet<Vec<String>>{
	let mut res3 = HashSet::new();
	for v in bags{
		let mut b_include = true;
		for x in v{
			  if x.len()<min_bag_len { b_include = false; break;}
		}
		if	v.len()<1 {b_include = false;}
		if b_include {res3.insert( v.clone() );}
	}
	res3
}

//do not enforce min_bag_len until last moment
fn add_to_hs (hs_res: &mut HashSet<Vec<String>>, vec: &Vec<String>, _min_bag_len: usize){
	let vec = vec.into_iter()
		//.filter(|x| x.len()>0 && x.len()>=min_bag_len)
		.map(|x| x.to_string())
		.collect::<Vec<String>>();
	let hs = vec.iter().map(|s| s.to_string()).collect::<HashSet<String>>();
	let mut vec2 = hs.into_iter().map(|s| s).collect::<Vec<String>>();
	vec2.sort();
	if vec2.len()>0{ hs_res.insert(vec2); }
}


/// handle the concat case, whenever possible explore the
/// combination by concat
fn handle_concat_bagwords(vec: &Vec<Hir>, limit: &mut usize, min_bag_len: usize)
	->(HashSet<Vec<String>>, bool){
	let mut b_full_res = true;
	let mut cur_bag:Vec<String> = vec!["".to_string()];
	let mut res = HashSet::<Vec<String>>::new();
	for (_id, hir) in vec.iter().enumerate(){
		let (bag_words, b_full) 
			= collect_bag_words_from_rustomaton_regex_worker(hir, limit, min_bag_len);

		if b_full{
			if bag_words.len()>1{
				println!("ERROR in b_full value: hir: {:?} => bag_words: {:?}",
					hir, bag_words);
			}
			assert!(bag_words.len()<=1, "for b_full bag_words len must be 1.");
		}
		let next_bag = if bag_words.len()>0 {(&bag_words).into_iter()
				.map(|v| v.clone())
				.collect::<Vec<Vec<String>>>()[0].clone()} 
				else {vec!["".to_string()]};

		b_full_res = b_full_res & b_full && bag_words.len()<=1;
		if b_full && next_bag.len()*cur_bag.len()<*limit{//concat
			cur_bag = cur_bag.iter().map(|x|
					next_bag.iter().map(|y| x.to_string() + &y)
						.collect::<Vec<String>>())
					.fold(vec![], |mut acc, mut vec|{
						acc.append(&mut vec);
						acc
					});
		}else{
			add_to_hs(&mut res, &cur_bag, min_bag_len);
			if b_full{ //update the current bag, wait for next
				cur_bag = next_bag.clone();
			}else{
				for bag in &bag_words{ add_to_hs(&mut res, &bag, min_bag_len); }
				cur_bag= vec!["".to_string()];
			}
		}
	}
	if cur_bag.len()>0 { 
		add_to_hs(&mut res, &cur_bag, min_bag_len);
	}
	b_full_res = b_full_res && res.len()<=1;
	(res, b_full_res)
}

/// handle alternation
/// _limit: combination limit, not used here.
/// the bool indicates if ALL words are matches of the regex
fn handle_alt_bagwords(v: &Vec<Hir>, limit: &mut usize, min_bag_len: usize)
->(HashSet::<Vec<String>>, bool){
	let mut res = HashSet::<Vec<String>>::new();
	res.insert(vec![]);
	let mut b_full_res = true;
	for hir in v{
		let (bag, b_full) = collect_bag_words_from_rustomaton_regex_worker(
			hir, limit, min_bag_len);
		b_full_res = b_full_res && b_full;
		let mut hs = HashSet::<Vec<String>>::new();
		if res.len() * bag.len() < *limit{//try every combination
			for x in &res{
				for y in &bag{
					let mut newvec = x.clone();
					newvec.append(&mut y.clone());
					add_to_hs(&mut hs, &newvec, min_bag_len);
				}
			}
		}else{//less accurate in discharging
			let n1 = res.len();
			let n2 = bag.len();
			let mut vec1 = res.iter().map(|x| x.clone())
				.collect::<Vec<Vec<String>>>();
			let mut vec2 = bag.iter().map(|x| x.clone())
				.collect::<Vec<Vec<String>>>();
			//Only the aggressive-SDE pipeline opts into the
			//deterministic longest-clause-first pairing; other
			//runners keep the original (HashSet-random) order
			//so their baselines are byte-identical.
			if utils::consts::read_global_config()
				.clamav_cfg.b_aggressive_sde_for_rep {
				let key = |c: &Vec<String>| c.iter()
					.map(|s| s.len()).min().unwrap_or(0);
				vec1.sort_by(|a, b| key(b).cmp(&key(a)));
				vec2.sort_by(|a, b| key(b).cmp(&key(a)));
			}
			let n = if n1>n2 {n1} else {n2};
			for i in 0..n{
				let u = if i<n1 {i} else {n1-1};
				let v = if i<n2 {i} else {n2-1};
				let mut newvec = vec1[u].clone();
				newvec.append(&mut vec2[v].clone());
				add_to_hs(&mut hs, &newvec, min_bag_len);
			}
		}
		res = hs;
	}

	b_full_res = b_full_res && res.len()<=1;
	(res, b_full_res)
}

/// for a known rustomaton regex convert to support ignore case
pub fn rustomaton_regex_to_ignore_case(s: &str, repeat_limit: usize) -> String{
	let hir = rustomaton_to_hir(s); 
	let res = rustomaton_hir_to_ignore_case(&hir, repeat_limit);

	res
}

/// assuming the hir is already converted from rustomaton
fn rustomaton_hir_to_ignore_case(hir: &Hir, repeat_limit: usize)->String{
	let res = match hir.kind(){
		Empty => "".to_string(),
		HirKind::Literal(x) => {
			let sx = String::from_utf8(x.0.to_vec()).expect("failed u8_to_s");
			to_ignore_case(&sx)
		},
		HirKind::Concat(v) => {
			let mut s = "".to_string();
			for x in v{
				let s2 = rustomaton_hir_to_ignore_case(x, repeat_limit);
				s = s + &s2;
			}
			s
		},
		HirKind::Capture(v) => {
			let item_s = rustomaton_hir_to_ignore_case(&v.sub, repeat_limit);
			 "(".to_string() + &item_s  + ")" 
		},
		HirKind::Look(v) => {
			panic!("rustomaton_to_igc cannot handle look: {:?}", v)
		},
		HirKind::Class(v) => {
			let mut limit = 255;
			let (vs, _info) = handle_class(v, &mut limit, repeat_limit);
			join_vs(&vs)
		},
		HirKind::Alternation(v) => {
			let mut s = "(".to_string();
			for id in 0..v.len(){
				let x = &v[id];
				let s2 = rustomaton_hir_to_ignore_case(x, repeat_limit);
				let s2 = if id==0 {s2} else { "|".to_string() + &s2};
				s = s + &s2;
			}
			s = s + ")";
			s
		},
		HirKind::Repetition(v) =>{
			assert!(v.min==0 && v.max.is_none(), "rustomaton_regex should already be processed, only allowing 0 and max inf. rep info wrong: min: {}, max: {:?}", v.min, v.max);
			let new_substr = rustomaton_hir_to_ignore_case(&v.sub, repeat_limit);
			"(".to_string() + &new_substr + ")*"
		}
	};
	res
}

/// additional bool results indicates if the collection of bag of words
/// are ALL of its matches (this allows some quick heurstics of generating
/// better bag of words such as concat "abc" and "(12|34)"
/// where the first bag is {["abc"]} and second {["12", "34"]}
/// we could generate combinations {["abc12", "abc34"]} this only
/// happens when the elements are FULL MATCH of the regex.
fn collect_bag_words_from_rustomaton_regex_worker(hir: &Hir, limit: &mut usize,
	min_bag_len: usize) 	-> (HashSet<Vec<String>>, bool){
	let mut set = HashSet::<Vec<String>>::new();
	let (res, bfull) = match hir.kind(){
		Empty => { (set, true) },
		HirKind::Literal(x) => {
			let sx = String::from_utf8(x.0.to_vec())
				.expect("failed u8 to str");
			set.insert( vec![sx] );
			(set, true)
		},
		HirKind::Concat(v) => handle_concat_bagwords(&v, limit, min_bag_len),
		HirKind::Repetition(v) => {
			let (bag, b_full) =collect_bag_words_from_rustomaton_regex_worker(
				&v.sub.clone(), limit, min_bag_len);
			let (min, max) = (v.min as usize, v.max);
			let bag_res = if min>=1 {bag} 
				else {HashSet::<Vec<String>>::new()};
			let b_full_res = (min==1 && max==Some(1)) && b_full;
			(bag_res, b_full_res)
		},
		HirKind::Class(v) => {
			let vbytes = class_to_arr(v, limit);
			let res = vbytes.iter().map(|v| 
					(&format!("{:#04x}",v)[2..]).to_string())
					.collect::<Vec<String>>();
			let mut hs = HashSet::<Vec<String>>::new();
			hs.insert(res);
			(hs, true)
		},
		HirKind::Capture(v) => {
			let (res, b_res) = collect_bag_words_from_rustomaton_regex_worker(&v.sub, limit, min_bag_len);
			(res, b_res)
		},
		HirKind::Alternation(v) => {
			let (res, b_res) = handle_alt_bagwords(&v, limit, min_bag_len);
			(res, b_res)
		}
		HirKind::Look(v) => panic!("rustomaton regex should not have zero-length assertion! Details: {:?}", v),
	};

	(res, bfull)
}

/// convert rustomaton to Hir
pub fn rustomaton_to_hir(s: &str) -> Hir{
	//1. double check syntax
	assert!(is_match(r"[0-9a-f().*?]*", s), 
		"s: {} is not regex accepted by rustomaton!", s);
	let hir = to_hir(s);

	hir
}


/// represent one limb in pm-reg 
#[derive(Serialize,Deserialize, Clone,Debug)]
pub enum PMRegItem{
	/// literal string with fixed length
	Literal(String),
	/// wildcard like .{min, max}
	Wildcard((usize, usize)),
}

/// min len of PMRegItem
pub fn min_len(p: &PMRegItem)->usize{
	match p{
		PMRegItem::Literal(x) => x.len(),
		PMRegItem::Wildcard( (mi, _ma) ) => *mi
	}
}

/// max_len of PMRegItem
pub fn max_len(p: &PMRegItem)->usize{
	match p{
		PMRegItem::Literal(x) => x.len(),
		PMRegItem::Wildcard( (_mi, ma) ) => *ma
	}
}

/// if wildcard already return itself;
/// otherwise convert to a wildcard type
fn to_wild(p: &PMRegItem) ->PMRegItem{
	match p{
		PMRegItem::Literal(x) => PMRegItem::Wildcard( (x.len(), x.len()) ),
		PMRegItem::Wildcard( (_mi,_ma) ) => p.clone() ,
	}
}

/// sum two PMRegItem. Assumption they should be
/// of the same type
fn sum(a: &PMRegItem, b: &PMRegItem)->PMRegItem{
	assert!(discriminant(a)==discriminant(b), "type not same!");
	let sum_num = |x: usize, y: usize| -> usize {
		if x==usize::MAX || y==usize::MAX {usize::MAX}
		else {x+y}
	};
	let res = match a{
		PMRegItem::Literal(x) => {
			let PMRegItem::Literal(y) = b else {panic!("unmatching type b")};
			PMRegItem::Literal(x.clone() + &y)
		},
		PMRegItem::Wildcard(x) => {
			let PMRegItem::Wildcard(y) = b else {panic!("unmatching type b")};
			let z = (sum_num(x.0, y.0), sum_num(x.1, y.1));
			PMRegItem::Wildcard(z)
		}
	};
	res
}

/// compute the union (min of the min, max of max values)
/// require a and b are both wildcard items
fn union(a: &PMRegItem, b: &PMRegItem) -> PMRegItem{
	let PMRegItem::Wildcard(x) = a else {panic!("a is not wildcard")};
	let PMRegItem::Wildcard(y) = b else {panic!("a is not wildcard")};
	let newmin = if x.0<y.0 {x.0} else {y.0};
	let newmax = if x.1>y.1 {x.1} else {y.1};
	let res = PMRegItem::Wildcard( (newmin, newmax) );
	res
}

/// sum all as wildcards and return one item of the sum of min, max
fn sum_as_wildcards(v: &Vec<PMRegItem>)->PMRegItem{
	assert!(v.len()>=1, "ERROR v.len==0!");
	let vec = v.iter().map(|x| to_wild(x)).collect::<Vec<PMRegItem>>();
	let mut res = vec[0].clone();
	for i in 1..vec.len(){
		res = sum(&res, &vec[i]);
	}
	res
}

/// normalize the concat PMRegItem of the same type into the same
fn normalize(v: &Vec<PMRegItem>) -> Vec<PMRegItem>{
	if v.len()==0 {return vec![];}

	let mut res = vec![];
	let mut cur = v[0].clone();
	for i in 1..v.len(){
		let next = v[i].clone();
		if discriminant(&cur)!=discriminant(&next){
			res.push(cur);
			cur = next;
		}else{//merge
			cur = sum(&cur, &next);
		}
	}
	res.push(cur);

	res
}

/// normalize the vec and convert to pm-reg result
pub fn vec_pmreg_to_res(vec: &Vec<PMRegItem>)->Vec<(String,(usize,usize))>{
	let vec_items = normalize(&vec);
	if vec_items.len()==0 {return vec![];}
	let mut min = 0;
	let mut max = 0;
	let b_start_literal = match vec_items[0] {
		PMRegItem::Literal(_) =>true,
		_ => false
	};
	let mut res = vec![];
	for i in 0..vec_items.len(){
		match &vec_items[i]{
			PMRegItem::Literal(x) => {
				assert!( (i%2==0) == b_start_literal, 
					"ERROR at idx {} should be wildcard", i);
				res.push( (x.clone(), (min, max)) );
			},
			PMRegItem::Wildcard(x)=>{
				assert!( (i%2==1) == b_start_literal, 
					"ERROR at idx {} should be literal", i);
				(min, max) = (x.0, x.1);
			},
		}
	}

	res
}
/// collect pm-reg information from a regex
/// each item (String, usize, usize) indicates a literal string
/// and the min distance from its previous item, i.e., the
/// min and max length of the item in-between
pub fn collect_pm_reg_from_rustomaton_regex(s: &str, min_pm_word_len: usize) 
-> Vec<(String,(usize, usize))>{
	let hir = rustomaton_to_hir(s);
	let vec_items = collect_pm_reg_from_rustomaton_regex_worker(&hir, min_pm_word_len);
	let res = vec_pmreg_to_res(&vec_items);
	res
}

/// return a vector of PMRegItems
pub fn collect_pm_reg_from_rustomaton_regex_worker(hir: &Hir, 
	min_pm_word_len: usize) 
-> Vec<PMRegItem>{
	let res = match hir.kind(){
		Empty => vec![],
		HirKind::Literal(x) => {
			let s = String::from_utf8(x.0.to_vec()).unwrap();
			let res = if s.len()>=min_pm_word_len{
				vec![PMRegItem::Literal(s)]
			}else{
				vec![PMRegItem::Wildcard( (s.len(), s.len()) )]
			};
			res
		},
		HirKind::Look(v) => panic!("rustomaton regex should not have zero-length assertion! Details: {:?}", v),
		HirKind::Capture(v) => {
			collect_pm_reg_from_rustomaton_regex_worker(&v.sub, min_pm_word_len)
		},
		HirKind::Class(v) => { 
			let arr = class_to_arr(&v, &mut 0); //limit not used
			let v_size = arr.len();
			let res = if v_size<16 {vec![ PMRegItem::Wildcard((1, 1)) ]}
				else if v_size==256 {//this is specific for handling "."
					vec![ PMRegItem::Wildcard((1, 1)) ]
				}else{vec![ PMRegItem::Wildcard((2,2))]}; 
			res
		},
		HirKind::Alternation(v) => { 
			let (vec, bres) = heu_handle_alt_pm_reg(&v);
			if bres {vec} else{
				let vec = v.iter().map(|x| {
					let vec = collect_pm_reg_from_rustomaton_regex_worker(x, min_pm_word_len);
					let v = sum_as_wildcards(&vec);
					v
				}).collect::<Vec<PMRegItem>>();
				assert!(vec.len()>0, "alt error: vec.len=0");
				let mut res = vec[0].clone();
				for i in 1..vec.len(){ res = union(&res, &vec[i]); }
				vec![res]
			}
		},
		HirKind::Concat(v) => {
			let vec = v.iter()
				.map(|x| collect_pm_reg_from_rustomaton_regex_worker(x, min_pm_word_len)).fold(vec![], |mut acc, x| {acc.extend(x); acc});
			let vec = normalize(&vec);
			vec
		},
		HirKind::Repetition(v) => {
			let vec = collect_pm_reg_from_rustomaton_regex_worker(&v.sub, min_pm_word_len);
			let (min, max) = (v.min, v.max);
			let mut res = vec![];
			//mandatory `min` copies. When the sub collapses to exactly
			//one wildcard (e.g. `.` -> W(1,1), as for begin-offset
			//`.{n,m}`), fold in O(1) instead of cloning `min` times;
			//this matches what normalize() would sum from min copies.
			//Single-literal / multi-item subs keep the loop (their
			//segments must survive), so output is unchanged for them.
			match vec.as_slice() {
				[PMRegItem::Wildcard((a, b))] if min > 0 =>
					res.push(PMRegItem::Wildcard((min as usize * *a,
						min as usize * *b))),
				_ => for _i in 0..min {res.append(&mut vec.clone());},
			}
			if max.is_none(){//unlimited case
				res.push(PMRegItem::Wildcard( (0, usize::MAX) ) );
			}else{
				let v = sum_as_wildcards(&vec);
				let (_vmin, vmax) = match v{
					PMRegItem::Wildcard((x,y)) => (x,y),
					_ => panic!("Expecting v to be a wildcard")
				};
				let max_num_segs =  max.unwrap() as usize - min as usize; //max number of optional segments
				let pm = PMRegItem::Wildcard( (0, max_num_segs * vmax) );
				res.push(pm);
			}
			let res = normalize(&res);
			res
		}
	};

	res
}

/// Use heurstic to handle alternation
/// if successful, the last bool is set to true
/// Idea: extract longest common substring. If all are
/// Liberal type
fn heu_handle_alt_pm_reg(v: &Vec<Hir>)->(Vec<PMRegItem>, bool){
	//0. utility function
	let first_appear = |vec: &Vec<String>, s: &str| -> String{
		let mut min_idx = s.len();
		let mut res_idx = 0;
		for id in 0..vec.len(){
			let idx = s.find(&vec[id]).expect(
				&format!("s: {} does not contain t: {}", s, &vec[id]));
			if idx<min_idx || (idx==min_idx && vec[idx].len()>vec[min_idx].len()){
				min_idx = idx;
				res_idx = id;
			}
		}
		vec[res_idx].clone()
	};

	
	//1. check if all are literal and collect strings
	let mut cur_strs= vec![];
	for h in v{ 
		if let HirKind::Literal(x) = h.kind(){
			cur_strs.push(String::from_utf8(x.0.to_vec()).unwrap());
		}else{
			return (vec![], false);
		}
	}

	//2. while loop extract longgest substring and repeat the process
	let mut vec_res = vec![];
	let n = cur_strs.len(); 
	let min_len = 6; //update later
	loop {
		//1. find the longest common substr
		let cur_s = cur_strs.iter().map(|s|
			&s.as_str()[0..]).collect::<Vec<&str>>();
		let first_s = cur_s[0];
		let res_subs = get_substrings(cur_s.clone(), n, min_len);
		if res_subs.len()>0{
			//2.1 identify a word
			let candidates = res_subs.iter().map(|s| s.name.clone())
				.collect::<Vec<String>>();
			let mut new_word = first_appear(&candidates, first_s);
			let pos1 = first_s.find(&new_word).unwrap();
			//make sure new_word is even len
			if new_word.len()%2==1{
				if pos1 % 2==0{//cut the last char
					new_word = new_word[0..new_word.len()-1].to_string();
				}else{
					new_word = new_word[1..new_word.len()].to_string();
				}
			}
			assert!(new_word.len()%2==0, "new_word: {} len is not even", new_word);

			//2.2 collect start idx in cur_s, find the min_max idx
			let v_idx = cur_s.iter().map(|s| s.find(&new_word).expect(
				&format!("ERROR cannot find word: {} in {}", new_word, s)) ).
				collect::<Vec<usize>>();
			let idx_min = v_idx.iter().min().unwrap();
			let idx_max = v_idx.iter().max().unwrap();

			//2.3 push the two PMRegItems
			let nw_len = new_word.len();
			let pm1 = PMRegItem::Wildcard( (*idx_min, *idx_max) );
			let pm2 = PMRegItem::Literal(new_word);
			vec_res.push(pm1);
			vec_res.push(pm2);

			//2.4 cut the new words
			cur_strs = cur_s.iter().zip(v_idx.iter()).map(|(s,i)| 
				s[*i + nw_len..].to_string()).collect::<Vec<String>>();
		}else{
			let v_len = cur_strs.iter().map(|s| s.len())
				.collect::<Vec<usize>>();
			let (minlen,maxlen) = (v_len.iter().min().unwrap(), 
				v_len.iter().max().unwrap());
			let pm = PMRegItem::Wildcard( (*minlen, *maxlen) );
			vec_res.push(pm);
			break;
		}
	}
	(vec_res, true)
}


#[cfg(test)]
mod tests_pcre{
	extern crate rustomaton;
	extern crate utils;

	use crate::{
		pcre::{pcre_to_rustomaton_regex, rustomaton_regex_to_ignore_case, pcre_to_dfa, clamav_genregex_to_dfa, collect_pm_reg_from_rustomaton_regex}
	};
	use crate::preprocess::handle_location_for_pm;
	use utils::{data::{str_to_hex}, os::{perl_is_match}};
	use self::rustomaton::automaton::{Automata};
	use super::to_hir;

	const REPEAT_LEN_LIMIT:usize=1024*6;
	const COMBINATION_LIMIT:usize = 127;

	#[test]
	pub fn test_convert(){
		let tcs = vec![
			(	//name
				"fix1",
				//PCRE
				"ABC", 
				//Strings satisfying both
				vec!["ABC"], //Strings satisfying none 
				vec!["abc"]
			), 
			("concat1", "AB.*", vec!["ABCD", "AB1"], vec!["aB1"]),
			("smartconcat1", r"AB(ab|cd)(12|34)1122", 
				vec!["ABab341122", "ABcd121122"],
				vec!["ABaB341122", "ABcdcd1122"]),
			("look1", r"A\b+.*B", 
				vec!["A B", "A  B"],
				vec!["A C", "AA"]),
			("class1", r"\d+abc", 
				vec!["123abc", "ABC123abc"],
				vec!["A C", "AA223"]),
			("cve_2016_3376_1", r"string[\x28\s]+(\x26[oh])?[a-f0-9]{5}", 
				vec!["string\x28 \x28 \x26o12345"],
				vec!["string\x28 \x29     \x26o12345"]),
			("CVE_2018_4957-6544942-1",
			 r"<progress[^<]{0,15}<meta",
			 vec!["<progress 12345<meta"],
			 vec!["<progres<meta"]),
			("backref1", r"A(B*)(C+)D\1A\2", 
			 	vec!["ABBCDBBAC"], vec!["ABBBBAD"]),
			// note all named ref are approximated by regex
			// (not exact matching of backref as it's beyond regular)
			("namedref1", r"A(?P<tag>BBC+)D00(?P=tag)11",
				vec!["ABBCCCD00BBCCC11"], vec!["ABBCCCD00BBDDD11"]),
			 (
			 	"ModifiedHtml.Exploit.CVE_2016_0184-1", r"willReadFrequently.*?(?P<source_img>(\w+|\w+\x5B\w+\x5D))\.createImageData.*?(?P<target_img>(\w+|\w+\x5B\w+\x5D))\s*\x3D\s*(?P=source_img)\.getImageData.*?(?P=source_img)\.putImageData\s*\x28\s*(?P=target_img).*", 
			 	vec!["willReadFrequently a.createImageData b\x3d a.getImageData a.putImageData\x28b"],
			 	vec!["00willReadFrequently000a.jpg.createImageData 00b.jpgabc \x3d  a.jpg.getImageData a.jpg.putImageData \x29 b.jpg"],
			 ),
			// #4 escaped-dot regression: "\." is a LITERAL period
			// (1 byte = 2e), must NOT gain a spurious wildcard nibble.
			("escdot1", r"a\.createImageData",
				vec!["a.createImageData"],
				vec!["aXcreateImageData"]),
			// two literal periods in a row
			("escdot2", r"x\.\.y", vec!["x..y"],
				vec!["x.ay", "xaby"]),
			// unescaped '.' = exactly ONE byte (regression guard)
			("wilddot1", r"a.b", vec!["a.b", "aXb", "a1b"],
				vec!["ab", "aXYb"]),
			// mix: literal '.', then a one-byte wildcard
			("escwild1", r"a\.b.c", vec!["a.bXc", "a.b.c"],
				vec!["axbXc", "a.bc"]),
			("lookend1", "AA.*BB$", vec!["AA123BB"], vec!["AA11BBC"]),
			("lookbegin1", "^AA.*", vec!["AA123"], vec!["BAA123"]),
			("boundary1", r".*\bGreat", vec!["AA Great"], vec!["AAGreat"]),
			("Txt.Downloader.Generic-5657800-0", 
				//r"\x3B function\s+(?P<function_name>[a-z]{5,})\x28\x29 \{var [a-z]{5,} = [\x22\x27][0-9]{6,}[\x22\x27]\x3B var[^}]+} (?P=function_name)\x28\x29\x3B",
				r"\x3B function\s+(?P<function_name>[a-z]{5,})\x28\x29 \{var [a-z]{5,} = [\x22\x27][0-9]{6,}[\x22\x27]\x3B var[^}]+\} (?P=function_name)\x28\x29\x3B",
				vec!["\x3b function aaaaaa\x28\x29 {var abcdef = \x271234567\x27\x3b var aaa} aaaaaa\x28\x29\x3b",
				],
				vec!["\x3b functin aaaaa\x28\x29 {var aaaaaa = \x220002222A\x22\x3b var bbb aaaaa\x28\x29\x3b"],
			),
			 ("classchar1", "[abc][cde]", vec!["ac", "ad"], vec!["aa", "ab"]),
			 ("classrep1", "[abc]*[cde]", vec!["1ac", "1aac", "1c2"], vec!["11", "1a"]),
			 ("classchar2", "[\x22\x27]", vec!["\x27", "\\\""], vec!["\x25"]),
			("longrep1","1[abcdefghijklm]{5,10}2", vec!["1abcdefg2"], vec!["1abcd2"]),
			//VERY SLOW
			//("Js.Downloader.Nemucod-6297599-0", //r"function\s[a-z0-9]+\x28\x29\s\x7B\svar\s[a-z0-9]+=(\x34[0-9a-z]{3,4}\x34\x2B\s){2}", r"function\s[a-z0-9]+\x28\x29\s\x7B\svar\s[a-z0-9]+=(\x34[0-9a-z]{3,4}\x34\x2B\s){2}", vec![ "function abc\x28\x29 \x7b var abc=\x34a234\x34\x2b \x34a234\x34\x2b "], vec!["function 123"]),
			("deepapproxrep1","1(ab|2345){5,10}2", vec!["1ab2345ab2345ababab2"], vec!["1abcd2"]),
		]; 

		let massage = |r: &str| ->String{
			let prefix = if r.chars().next()==Some('^') {""} else {".*"};
			let suffix = if r.ends_with("$") {""} else {".*"};
			prefix.to_string() + r + &suffix
		};
		for tc in tcs{
			let pcre_reg = tc.1;
			let processed_pcre_reg = &massage(tc.1);
			let (rustomaton2_reg, _) = pcre_to_rustomaton_regex(pcre_reg, COMBINATION_LIMIT, REPEAT_LEN_LIMIT); 
			for s in tc.2{//yes case
				let ns = str_to_hex(s);
				let (b1, b2) = (perl_is_match(processed_pcre_reg, s), 
					perl_is_match(&rustomaton2_reg, &ns));
				assert!(b1, "ERROR on case: {} PCRE yes for s: {}", tc.0, s);
				assert!(b2, "ERROR on case: {},rustomaton::yes {} for s: {}", 
					tc.0, rustomaton2_reg, s);
			}

			for s in tc.3{//no case
				let ns = str_to_hex(s);
				let (b1, b2) = (perl_is_match(processed_pcre_reg, &ns), 
						perl_is_match(&rustomaton2_reg, &ns));
				assert!(!b1, "ERROR on case: {} PCRE no for s: {}", tc.0, s);
				assert!(!b2, "ERROR on case: {},rustomaton::no {} for s: {}", 
					tc.0, rustomaton2_reg, s);
			}
		}
	}

	#[test]
	pub fn test_rustomaton_to_ignore_case(){
		let testcases = vec![
			( //ignore case 
				"6162(11|22)3132", 
				//expected conversion
				"(61|41)(62|42)((11|22))3132"
			),
			("(6111)*", "(((61|41)11))*")
		];
		for tc in testcases{
			let src = tc.0;
			let dst = tc.1;
			let act = rustomaton_regex_to_ignore_case(src, REPEAT_LEN_LIMIT);
			assert!(dst==act, "ERROR: converting src: {} => {}, expected: {}",
				src, act, dst);
		}
	}

	#[test]
	pub fn test_pcre_to_dfa(){
		let testcases = vec![
			(//pcre regex following clamav pcre regex subsig
			 //NOTE: the actual reg will be .*123.* based on
			 //if zero length assertion such as ^, $ is used
				"/123/", 
			  //accepted strings. "a1235" is ok because the regex is
			  //actually .*123.*, i.e., meaning it is ok as long as
			  // it contains pattern "123"
				vec!["123", "a1235"],
				//denied strings
				vec!["223", "a2234"]
			),
			// test simple ignore case
			("/abc/i",  vec!["abc", "aBc"], vec!["ab1d", "A123"]),
			("/abc/",  vec!["abc"], vec!["aBc", "A123"]),
			("/abc1a2/i",  vec!["abc1A2", "aBc1a2gg"], vec!["abcd", "abc1b2"]),
			// kleene
			("/c+/",  vec!["c", "ccc"], vec!["", "d"]),
			("/c*1/",  vec!["c1", "1"], vec!["d"]),
			// class
			("/[1|2]/",  vec!["1", "2"], vec!["3", "3355"]),
			// concat
			("/./",  vec!["1", "a"], vec![""]),
			("/../",  vec!["12", "ab"], vec![""]),
			// '.' = exactly ONE byte; /.../ auto-wraps .* both ends
			("/.a/", vec!["Xa","XYa","1a"], vec!["a","bc"]),
			("/..a/", vec!["XYa","XYZa","12ba"], vec!["Xa","a"]),
			("/a.b/", vec!["aXb","zaybz"], vec!["ab","axyb"]),
			("/..*/", vec!["a","ab","1"], vec![""]),
			("/^a.b$/", vec!["aXb","a1b"], vec!["ab","aXYb","Xab"]),
			("/^..$/", vec!["ab","12"], vec!["a","abc",""]),
			// class with repetition
			(r"/[1|2|3]+ab/", vec!["122ab", "12232ab"], vec!["a14ab"]),
			(r"/[1|2|3]{1,3}ab/", vec!["12ab", "122ab"], vec!["ab", "a5555ab"]),
			(r"/[1|2|3]{1,}ab/", vec!["12ab", "12222223ab"], vec!["ab", "1232b"]),
			(r"/[1|2|3]{0,}ab/", vec!["ab", "12222223ab"], vec!["1b"]),
			(r"/[1|2|3]+ab/", vec!["23ab", "3ab"], vec!["123a", "ab"]),
			(r"/[1|2|3]*ab/", vec!["ab", "3ab"], vec!["123a", "ac1"]),
			// zero position lookups
			(r"/^123$/", vec!["123"], vec!["123a", "a123"]),
			(r"/^[1|2|3]{1,3}ab$/", vec!["123ab", "1ab"], vec!["1a", "1234ab", "ab", "123a"]),
			(r"/.*\b[1|2|3]ab$/", vec!["aa1ab", "bb1ab"], vec!["a 1ab", "4ac", "ab", "123b"]),
			// capture
			(r"/^(ab(cd)+)+12$/", vec!["abcdcdabcd12"], vec!["abcdab12"]),
			// alternation
			(r"/^(a|bc)+12$/", vec!["aa12", "aabcaa12"], vec!["aab12"]),
			// macros
			(r"/^\w+$/", vec!["aa12", "aabcaa12"], vec!["aa b12"]),
			//Email.Phisihing.VOF1-6295631-2
			(r"/(Fedex|DHL|US?PS).{1,5}\.(exe|scr|js)/", 
				vec!["DHL12345.scr", "UPS1234.js"],
				vec!["DHL123455.js", "UPS123456.exe", "Fedex.exe"]
			),
			(r"/^\w+$/", vec!["aa12", "aabcaa12"], vec!["aa b12"]),
			(r"/[\x22\x27]/", vec![" '", "a\"b"], vec![" [134] "]),
			(r"/^\w+\s*(\x5b\d+\x5d){2}$/", vec!["aa12 [2][3]", "aa [34][56]"], vec!["aa b12"]),
			(r"/[\x22\x27][^\x22\x27]*?(\s*\x5b\s*\d+\s*\x5d){2}/", vec!["' [1ab] [2] [3]"], vec![" [134] "]),
			
			//more macros with ignore cases
			(r"/^\d$/i", vec!["1"], vec!["x"]), 
			(r"/^\d+$/i", vec!["1", "120"], vec!["x", "12x"]), 
			(r"/^\d$/", vec!["1"], vec!["x"]), 
			(r"/^\d+$/", vec!["1", "120"], vec!["x", "12x"]), 
			(r"/^\s$/", vec![" ", "\t", "\n"], vec!["x"]), 
			(r"/^\s+$/i", vec![" ", "\t", "\n "], vec!["x"]), 
			(r"/^\w+$/", vec!["ab", "cd", "a12"], vec!["x y"]), 
			(r"/^\w+$/i", vec!["ab", "cd", "a12"], vec!["x y"]), 
			//Pdf.Exploit.APSB16_26-1
			(r"/<xsl\x3a[^>]*?(test|value|select)\s*=\s*\x5c[\x22\x27][^\x22\x27]*?\w+(\s*\x5b\s*\d+\s*\x5d){10}/i",
				vec!["<xsl:  select = \\' abc [1] [2] [3] [4] [5] [6] [7] [8] [9] [10]"], 
				vec!["<xsl:  select = \\' [1] [2] [3] [4] [5] [6] [7] [8] [9] [10ab]"], 
			),
		];
		for tc in testcases{
			let yes_strs = tc.1;
			let no_strs = tc.2;
			let src = tc.0;
			let dfa = pcre_to_dfa(&src, COMBINATION_LIMIT, REPEAT_LEN_LIMIT);

			for s in yes_strs{
				let s2 = str_to_hex(&s);
				let s2 = s2.chars().collect::<Vec<char>>();
				assert!(true==dfa.run(&s2), "FAIL true str: {} for regex: {}",
				 	s, src);
			}
			for s in no_strs{
				let s2 = str_to_hex(&s);
				let s2 = s2.chars().collect::<Vec<char>>();
				assert!(false==dfa.run(&s2),"FAIL false str: {} for regex: {}", s, src);
			}
		}
	}

	#[test]
	pub fn test_hex_reg_dfa(){
		// test the general regex of clamav patterns when converted to 
		// DFA if it is working ok.
		let testcases = vec![
			(	//regex just like general regex subsignature
				"1?2",
				//yes strings
				vec!["1a23"],
				//no strings
				vec!["12"]
			),
			//simple literal
			("0:61",vec!["61"], vec!["62"]),
			("0:616263",vec!["616263", "61626364"], vec!["6263", "62616263"]),
			//simple wildcards
			("12??13", vec!["aa12ab13", "12ab13cd"], vec!["12a13", "aa12b13"]),
			("12*13", vec!["12aaa13", "1213"], vec!["12aa14", "12ab1"]),
			("12{1-2}14", vec!["12aa14", "12aabb14"], vec!["1214", "12aabbcc14"]),
			("12{1-}15", vec!["12aabbcc15"], vec!["1215"]),
			("12{-3}15", vec!["12aabbcc15"], vec!["12aabbccdd15"]),
			//ignore case
			("6162??1122::i", vec!["6162aa1122", "6142aa1122"], vec!["44"]),
			("6162??1122", vec!["6162aa1122"], vec!["6142aa1122"]),
			//alternation
			("(11|22)(33|44)aa", vec!["1133aa", "2244aa"], vec!["1234aa"]),
			//sipmle negation
			("!(00|12)aa", vec!["3344aa"], vec!["12aa", "3300aa"]),
			//begin-offset: "4:" = 4 BYTES = exactly 8 leading nibbles,
			//anchored at start (ClamAV byte-offset convention)
			("4:61626364",
			 vec!["aaaaaaaa61626364", "0000000061626364"],
			 vec!["aaaaaa61626364", "aaaaaaaaaa61626364", "61626364"]),
		];
		for tc in testcases{
			let yes_strs = tc.1;
			let no_strs = tc.2;
			let src = tc.0;
			let dfa = clamav_genregex_to_dfa(&src);
			for s in yes_strs{
				let s2 = s.chars().collect::<Vec<char>>();
				assert!(true==dfa.run(&s2), "FAIL true str: {} for regex: {}",
				 	s, src);
			}
			for s in no_strs{
				let s2 = s.chars().collect::<Vec<char>>();
				assert!(false==dfa.run(&s2), "FAIL false str: {} for regex: {}",
					s, src);
			}
		}
	}

	#[test]
	pub fn test_pm_reg_offset_fold(){
		//equivalence guard for the single-wildcard Repetition fold.
		//m=2 keeps "616263" (6 chars) a Literal.
		let m = 2;
		//fixed begin-offset .{4,4} -> bound (4,4)
		let r = collect_pm_reg_from_rustomaton_regex(".{4,4}616263.*", m);
		assert!(r.iter().any(|(s,b)| s=="616263" && *b==(4,4)), "{:?}", r);
		//range begin-offset .{10,20} -> (10,20)
		let r = collect_pm_reg_from_rustomaton_regex(".{10,20}616263.*", m);
		assert!(r.iter().any(|(s,b)| s=="616263" && *b==(10,20)), "{:?}", r);
		//optional .? (min==0): fold guard skips -> loop, bound (0,1)
		let r = collect_pm_reg_from_rustomaton_regex(".?616263.*", m);
		assert!(r.iter().any(|(s,b)| s=="616263" && *b==(0,1)), "{:?}", r);
		//unbounded .+ (min==1): fast path fires, lower bound stays 1
		let r = collect_pm_reg_from_rustomaton_regex(".+616263.*", m);
		assert!(r.iter().any(|(s,b)| s=="616263" && b.0==1), "{:?}", r);
		//single-Literal repetition must NOT fold: 3 copies expand
		//(normalize merges the adjacent literals into one).
		let r = collect_pm_reg_from_rustomaton_regex("(616263){3,3}", m);
		let want = "616263".repeat(3);
		assert!(r.iter().any(|(s,b)| *s==want && *b==(0,0)),
			"literal rep must expand to 3 copies: {:?}", r);
		//large offset must be O(1) (folded, not 1e6 clones) and exact
		let r = collect_pm_reg_from_rustomaton_regex(
			".{1000000,1000000}616263.*", m);
		assert!(r.iter().any(|(s,b)| s=="616263" && *b==(1000000,1000000)),
			"{:?}", r);
	}

	#[test]
	pub fn test_pm_reg_offset_pm_path(){
		//covers handle_location_for_pm (not exercised by small_dna gate)
		let s = handle_location_for_pm("4:616263");
		let r = collect_pm_reg_from_rustomaton_regex(&s, 2);
		//"4:" = 4 BYTES = 8 nibbles (ClamAV byte-offset convention)
		assert!(r.iter().any(|(t,b)| t=="616263" && *b==(8,8)),
			"pm-path: {:?} (from {})", r, s);
	}

	#[test]
	pub fn tests_sde_rep_find_runs(){
		use super::find_class_runs;
		//fixed rep -> one leg, min == count
		let legs = find_class_runs(&to_hir("[0-9]{3}"));
		assert_eq!(legs.len(), 1);
		assert_eq!(legs[0].min, 3);
		//four legs across literals, order + counts preserved
		let legs = find_class_runs(&to_hir(
			"[0-9]{3}-[0-9]{3}-[0-9]{3}-[0-9]{4}"));
		assert_eq!(legs.iter().map(|l| l.min).collect::<Vec<_>>(),
			vec![3,3,3,4]);
		//variable rep: pinnable count = guaranteed minimum
		let legs = find_class_runs(&to_hir("[0-9]{2,5}"));
		assert_eq!(legs.len(), 1);
		assert_eq!((legs[0].min, legs[0].max), (2, Some(5)));
		//'+' : min 1, unbounded above
		let legs = find_class_runs(&to_hir("[0-9]+"));
		assert_eq!((legs[0].min, legs[0].max), (1, None));
		//bare class / `{1}` (to_hir simplifies {1} to Class)
		assert_eq!(find_class_runs(&to_hir("[0-9]")).len(), 1);
		assert_eq!(find_class_runs(&to_hir("[0-9]{1}"))[0].min, 1);
		//min-0 reps have no guaranteed position -> skipped
		assert_eq!(find_class_runs(&to_hir("[0-9]*")).len(), 0);
		assert_eq!(find_class_runs(&to_hir("[0-9]?")).len(), 0);
		//pure literals -> no legs
		assert_eq!(find_class_runs(&to_hir("abc")).len(), 0);
		//optional GROUP `([0-9]{2})?` -> leg kept (ctr alignment) but
		//flagged optional; following mandatory leg stays guaranteed.
		let legs = find_class_runs(&to_hir("([0-9]{2})?[0-9]{6}"));
		assert_eq!(legs.iter().map(|l| l.optional)
			.collect::<Vec<_>>(), vec![true, false]);
		//alternation branches are conditional -> their legs optional;
		//the mandatory prefix leg stays guaranteed.
		let legs = find_class_runs(&to_hir(
			"[0-9]{4}([A-Z]{3}|[0-9]{3})"));
		assert_eq!(legs.iter().map(|l| l.optional)
			.collect::<Vec<_>>(), vec![false, true, true]);
	}

	#[test]
	pub fn tests_sde_rep_shape_guard(){
		use super::{analyze_aggressive_shape, AggShapeErr};
		//T1 F1 forward: keyword SSN leftmost, span 78 bytes.
		let r = analyze_aggressive_shape(&to_hir(
			"SSN.{0,64}[0-9]{3}[-\\s]?[0-9]{2}[-\\s]?[0-9]{4}"), None)
			.unwrap();
		assert_eq!((r.anchor, r.max_span_bytes), (Some(0), 78));
		//T2 F2 single backward: SSN rightmost, span 78.
		let r = analyze_aggressive_shape(&to_hir(
			"[0-9]{3}[-\\s]?[0-9]{2}[-\\s]?[0-9]{4}.{0,64}SSN"), None)
			.unwrap();
		assert_eq!((r.anchor, r.max_span_bytes), (Some(1), 78));
		//T3 F2 multi backward: trailing literal, span 90.
		let r = analyze_aggressive_shape(&to_hir(
			"([0-9]{3}\\s){2}[0-9]{3}.{0,64}driving\\x20license"), None)
			.unwrap();
		assert_eq!((r.anchor, r.max_span_bytes), (Some(1), 90));
		//T4 unbounded gap rejected.
		assert_eq!(analyze_aggressive_shape(&to_hir("SSN.*[0-9]{3}"), None),
			Err(AggShapeErr::Unbounded));
		//T5 keyword in the middle rejected.
		assert_eq!(analyze_aggressive_shape(&to_hir(
			"[0-9]{3}.{0,9}SSN.{0,9}[0-9]{3}"), None),
			Err(AggShapeErr::KwInMiddle));
		//T6 no keyword anchor rejected.
		assert_eq!(analyze_aggressive_shape(&to_hir(
			"[0-9]{3}.{0,9}[0-9]{3}"), None),
			Err(AggShapeErr::NoAnchor));
		//T7 number pattern with a leading 1-byte literal digit (ITIN:
		//`9[0-9]{2}...`) is NOT a middle keyword -- the lone `9` is
		//regex content, so keyword `ITIN` anchors forward / backward.
		let r = analyze_aggressive_shape(&to_hir(
			"ITIN.{0,64}9[0-9]{2}[-\\s]?[0-9]{4}"), None).unwrap();
		assert_eq!(r.anchor, Some(0));
		let r = analyze_aggressive_shape(&to_hir(
			"9[0-9]{2}[-\\s]?[0-9]{4}.{0,64}ITIN"), None).unwrap();
		assert_eq!(r.anchor, Some(1));
		tests_sde_rep_name_direction();
	}

	/// Name-driven direction (idea 1/3): the .fwd/.bwd sig name selects the
	/// anchor side, so a leading short literal (e.g. "00") can't be mistaken
	/// for the keyword. Longest-gap split + far-side relaxation for a
	/// fully-concrete fanned variant.
	fn tests_sde_rep_name_direction(){
		use super::{analyze_aggressive_shape, direction_from_name, to_hir};
		// real bora .bwd arm (leading "00") that used to panic KwInMiddle:
		// the backward hint accepts it.
		let r = analyze_aggressive_shape(&to_hir(
			"00[0-9]{2}\\x2D?[0-9]{4}\\x2D?[0-9].{0,300}\
			 [\\x20\\x09\\x0a\\x0d]aba\\x20number[\\x20\\x09\\x0a\\x0d]"),
			Some(1)).unwrap();
		assert_eq!(r.anchor, Some(1));
		// same SIT, forward arm with the forward hint.
		let r = analyze_aggressive_shape(&to_hir(
			"[\\x20\\x09\\x0a\\x0d]aba\\x20number[\\x20\\x09\\x0a\\x0d]\
			 .{0,300}00[0-9]{2}\\x2D?[0-9]{4}\\x2D?[0-9]"),
			Some(0)).unwrap();
		assert_eq!(r.anchor, Some(0));
		// multiple gaps -> the LONGEST one is the split (idea 3).
		let r = analyze_aggressive_shape(&to_hir(
			"[0-9]{3}.{0,150}[0-9]{4}.{0,300}KEYWORD"), Some(1)).unwrap();
		assert_eq!(r.anchor, Some(1));
		// fully-concrete far side (no class run) still accepted via the
		// hint (far-side relaxation); keyword side stays clean.
		let r = analyze_aggressive_shape(&to_hir(
			"0012345678.{0,300}[\\x20]aba\\x20number[\\x20]"),
			Some(1)).unwrap();
		assert_eq!(r.anchor, Some(1));
		// direction_from_name keyword assertion.
		assert_eq!(direction_from_name("Dlp.x.kw00.p00.fwd"), 0);
		assert_eq!(direction_from_name("Dlp.x.kw00.p00.bwd"), 1);
	}

	#[test]
	#[should_panic]
	fn tests_sde_rep_name_direction_missing(){
		super::direction_from_name("Dlp.x.kw00.p00");
	}

	#[test]
	pub fn tests_sde_rep_card(){
		use super::{find_class_runs, card};
		let c = |p| find_class_runs(&to_hir(p))[0].class.clone();
		assert_eq!(card(&c("[0-9]{2}")), 10);
		assert_eq!(card(&c("[0-9a-f]{2}")), 16);
		assert_eq!(card(&c("[a-z]{2}")), 26);
		assert_eq!(card(&c("[a-zA-Z0-9]{2}")), 62);
		//'.' (dot_matches_new_line + byte mode) = all 256 bytes
		assert_eq!(card(&c(".{2}")), 256);
	}

	#[test]
	pub fn tests_sde_rep_hi_nibble_block(){
		use super::{find_class_runs, is_single_hi_nibble_block};
		let c = |p| find_class_runs(&to_hir(p))[0].class.clone();
		//single high-nibble block -> true
		assert!(is_single_hi_nibble_block(&c("[0-9]{2}")));//3_
		assert!(is_single_hi_nibble_block(&c("[a-f]{2}")));//6_
		assert!(is_single_hi_nibble_block(&c("[a-o]{2}")));//6_
		assert!(is_single_hi_nibble_block(&c("[A-O]{2}")));//4_
		//straddles two high-nibble blocks -> false
		assert!(!is_single_hi_nibble_block(&c("[a-z]{2}")));
		assert!(!is_single_hi_nibble_block(&c("[A-Z]{2}")));
		assert!(!is_single_hi_nibble_block(&c("[a-zA-Z0-9]{2}")));
	}

	#[test]
	pub fn tests_sde_rep_select_slots(){
		use super::{find_class_runs, select_slots};
		//driverlic: leg priority [0,3,2,1], all card 10. Last leg
		//(idx 3, n=4) uses pos_priority_last -> pos n-2 = 2 first.
		let legs = find_class_runs(&to_hir(
			"[0-9]{3}-[0-9]{3}-[0-9]{3}-[0-9]{4}"));
		assert_eq!(select_slots(&legs, 1000, false, false),
			vec![(0,0),(3,2),(2,0)]);
		assert_eq!(select_slots(&legs, 100, false, false),
			vec![(0,0),(3,2)]);
		//single leg = also the last leg: pos n-2=7 first, then 0.
		let legs = find_class_runs(&to_hir("[0-9]{9}"));
		assert_eq!(select_slots(&legs, 100, false, false),
			vec![(0,7),(0,0)]);
		//mixed cardinalities (26*10=260<=300); last leg's first
		//pos is n-2 = 4 of `[0-9]{6}`.
		let legs = find_class_runs(&to_hir("[A-Z]{2}[0-9]{6}"));
		assert_eq!(select_slots(&legs, 300, false, false),
			vec![(0,0),(1,4)]);
	}

	/// Mandatory-first budgeting: with an optional leg present, the
	/// budget must skip it and pin the guaranteed legs (which become
	/// pm-reg anchors). Sweden-id shape `([0-9]{2})?[0-9]{6}[0-9]{4}`:
	/// legs [A optional, B mandatory, C mandatory]. B=100 -> pin the two
	/// mandatory legs (C last-leg pos n-2=2, then B pos 0); leg A unfunded.
	/// Pre-fix behavior pinned the optional leg A and yielded [(0,0),(2,2)].
	#[test]
	pub fn tests_sde_rep_select_slots_mandatory_first(){
		use super::{find_class_runs, select_slots};
		let legs = find_class_runs(&to_hir(
			"([0-9]{2})?[0-9]{6}[0-9]{4}"));
		assert_eq!(legs.iter().map(|l| l.optional)
			.collect::<Vec<_>>(), vec![true, false, false]);
		assert_eq!(select_slots(&legs, 100, false, false),
			vec![(2,2),(1,0)]);
	}

	#[test]
	pub fn tests_sde_rep_select_slots_tight(){
		use super::{find_class_runs, select_slots};
		//SSN-shape: 3 legs of [0-9] with sizes [3,2,4].
		//Tight: leg_priority=[0,2] (skip middle), first leg
		//forward, last leg n-2 first.
		//Round 0: (0,0)->10, (2,2)->100. Round 1: (0,1)->1000
		//take, (2,0)->10000 skip. Round 2: (0,2)->10000 skip.
		let legs = find_class_runs(&to_hir(
			"[0-9]{3}[-\\s]?[0-9]{2}[-\\s]?[0-9]{4}"));
		assert_eq!(select_slots(&legs, 1000, false, true),
			vec![(0,0),(2,2),(0,1)]);
		//License.B3 shape: digit/space alternation gives 5 legs
		//(3 digit + 2 \s). Tight mode skips middle legs (incl.
		//the \s ones), so only legs 0 and 4 are visited.
		//Last leg [0-9]{3}, pos_priority_last(3)=[1,0,2].
		let legs = find_class_runs(&to_hir(
			"[0-9]{3}\\s[0-9]{3}\\s[0-9]{3}"));
		assert_eq!(select_slots(&legs, 1000, false, true),
			vec![(0,0),(4,1),(0,1)]);
		//Passport-shape: leg 0 = [0-9a-zA-Z] (card 62) exceeds
		//SINGLE_FANOUT_MAX, so it is never pinned; budget falls
		//entirely on leg 1 = [0-9]{8} (10*10*10=1000), last-leg
		//pos order [6,0,7,..].
		let legs = find_class_runs(&to_hir(
			"[0-9a-zA-Z][0-9]{8}"));
		assert_eq!(select_slots(&legs, 1000, false, true),
			vec![(1,6),(1,0),(1,7)]);
		//Single leg = also the last leg: tight has no effect
		//(no separate first/last), use pos_priority_last.
		let legs = find_class_runs(&to_hir("[0-9]{9}"));
		assert_eq!(select_slots(&legs, 100, false, true),
			vec![(0,7),(0,0)]);
	}

	#[test]
	pub fn tests_sde_rep_fold_bytes(){
		use super::fold_bytes_igc;
		//cs: identity (bytes pass through unchanged).
		let up: Vec<u8> = (0x41u8..=0x46).collect();
		assert_eq!(fold_bytes_igc(&up, false), up);
		//igc: A-F -> a-f.
		assert_eq!(fold_bytes_igc(&up, true),
			(0x61u8..=0x66).collect::<Vec<u8>>());
		//igc: a-f + A-F dedups to a-f (12 -> 6), ascending.
		let mut mixed: Vec<u8> = (0x41u8..=0x46).collect();
		mixed.extend(0x61u8..=0x66);
		assert_eq!(fold_bytes_igc(&mixed, true),
			(0x61u8..=0x66).collect::<Vec<u8>>());
		//digits are caseless: fold is identity even under igc.
		let dig: Vec<u8> = (0x30u8..=0x39).collect();
		assert_eq!(fold_bytes_igc(&dig, true), dig);
	}

	#[test]
	pub fn tests_sde_rep_render_variants(){
		use super::{find_class_runs, render_variants};
		//middle position stays class; first+last pinned; lexicographic.
		let hir = to_hir("[0-9]{3}");
		let legs = find_class_runs(&hir);
		let v = render_variants(&hir, &legs, &[(0,0),(0,2)], false);
		assert_eq!(v.len(), 100);
		assert_eq!(v[0], "\\x30[\\x30-\\x39]\\x30");
		assert_eq!(v[1], "\\x30[\\x30-\\x39]\\x31");
		assert_eq!(v[99], "\\x39[\\x30-\\x39]\\x39");
		//bounded variable tail (max-min=2) stays class.
		let hir = to_hir("[0-9]{2,4}");
		let legs = find_class_runs(&hir);
		let v = render_variants(&hir, &legs, &[(0,0),(0,1)], false);
		assert_eq!(v.len(), 100);
		assert_eq!(v[0], "\\x30\\x30[\\x30-\\x39]{0,2}");
		//unbounded tail -> '*'.
		let hir = to_hir("[0-9]+");
		let legs = find_class_runs(&hir);
		let v = render_variants(&hir, &legs, &[(0,0)], false);
		assert_eq!(v.len(), 10);
		assert_eq!(v[0], "\\x30[\\x30-\\x39]*");
		assert_eq!(v[9], "\\x39[\\x30-\\x39]*");
		//literal between legs + canonical (leg,pos) ordering.
		let hir = to_hir("[0-9]{2}-[0-9]{2}");
		let legs = find_class_runs(&hir);
		let v = render_variants(&hir, &legs, &[(0,0),(0,1),(1,0)], false);
		assert_eq!(v.len(), 1000);
		assert_eq!(v[0], "\\x30\\x30\\x2d\\x30[\\x30-\\x39]");
	}

	#[test]
	pub fn tests_sde_rep_expand_count(){
		use super::expand_rep_subsig;
		use crate::clamav::default_clamav_cfg;
		let mut cfg = default_clamav_cfg();
		cfg.b_aggressive_sde_for_rep = true;
		cfg.sde_rep_fanout_cap = 1000;
		//pin 1st digit of all 3 legs: 10*10*10 = 1000 variants.
		let v = expand_rep_subsig(
			"[0-9]{3}-[0-9]{3}-[0-9]{3}", false, &cfg);
		assert_eq!(v.map(|x| x.len()), Some(1000));
	}

	#[test]
	pub fn tests_sde_rep_expand_igc(){
		use super::expand_rep_subsig;
		use crate::clamav::default_clamav_cfg;
		let mut cfg = default_clamav_cfg();
		cfg.b_aggressive_sde_for_rep = true;
		cfg.sde_rep_fanout_cap = 200;
		//cs: raw card 12 -> only 1 position fits (12<=100<144).
		let cs = expand_rep_subsig("[a-fA-F]{3}", false, &cfg)
			.expect("cs some");
		assert_eq!(cs.len(), 12);
		//igc: folds case pairs 12->6 -> 2 positions fit (6*6=36).
		let igc = expand_rep_subsig("[a-fA-F]{3}", true, &cfg)
			.expect("igc some");
		assert_eq!(igc.len(), 36);
		//folded variants pin LOWERCASE bytes; for a 3-byte leg the
		//last-leg priority pins pos n-2=1 first then pos 0, leaving
		//pos 2 (the trailing byte) as the full class.
		assert_eq!(igc[0], "\\x61\\x61[\\x41-\\x46\\x61-\\x66]");
		assert_eq!(igc[35], "\\x66\\x66[\\x41-\\x46\\x61-\\x66]");
		//digits are caseless: igc == cs (fold is identity).
		cfg.sde_rep_fanout_cap = 1000;
		let d_cs = expand_rep_subsig("[0-9]{3}", false, &cfg);
		let d_igc = expand_rep_subsig("[0-9]{3}", true, &cfg);
		assert_eq!(d_cs, d_igc);
	}

	#[test]
	pub fn tests_sde_rep_expand_none(){
		use super::expand_rep_subsig;
		use crate::clamav::default_clamav_cfg;
		//gate off (default) -> None even with an eligible run.
		let cfg = default_clamav_cfg();
		assert!(expand_rep_subsig("[0-9]{3}", false, &cfg).is_none());
		//gate on, but no eligible slot / run:
		let mut cfg = default_clamav_cfg();
		cfg.b_aggressive_sde_for_rep = true;
		cfg.sde_rep_fanout_cap = 1000;
		//wildcard-only: card 256 never selectable.
		assert!(expand_rep_subsig(".{4}", false, &cfg).is_none());
		//literal-only: no class run.
		assert!(expand_rep_subsig("abc", false, &cfg).is_none());
		//budget below smallest class card (10 > 5).
		cfg.sde_rep_fanout_cap = 5;
		assert!(expand_rep_subsig("[0-9]{3}", false, &cfg).is_none());
	}

	/// 2026-06-02 regression: min==0 class reps (`.{0,k}`, `[-\s]?`,
	/// `[0-9]{2}?`) are skipped by collect_class_runs but were
	/// (pre-fix) still consumed by emit_variant's ctr, causing
	/// legs[idx] OOB on any sig with such a rep next to fan-out
	/// legs. Real-world trigger = small_email DLP sigs
	/// (Passport/SSN/License/Bank/ITIN). This test pins the fix:
	/// expansion succeeds and yields the expected cross-product.
	#[test]
	pub fn tests_sde_rep_min0_class_rep(){
		use super::expand_rep_subsig;
		use crate::clamav::default_clamav_cfg;
		let mut cfg = default_clamav_cfg();
		cfg.b_aggressive_sde_for_rep = true;
		cfg.sde_rep_fanout_cap = 1000;
		// (a) `.{0,100}` between two class-reps -- the small_email
		// shape. Two legs at min>=1, dot-rep min=0 in the middle.
		let v = expand_rep_subsig(
			"[0-9]{3}.{0,100}[0-9]{3}", false, &cfg)
			.expect("expand none");
		// 2 fan-out legs * 10 cardinality * up to 3 positions each;
		// just assert non-empty + that the dot-rep quantifier
		// survived (class_to_pcre re-emits the dot as a byte-range
		// form like [\x00-\xff], so check the {0,100} suffix only).
		assert!(!v.is_empty(), "no variants");
		assert!(v[0].contains("{0,100}"),
			"dot-rep quantifier missing in v[0]: {}", v[0]);
		// (b) `[-\s]?` (min=0, max=1) between two class-reps -- the
		// SSN/ITIN shape. Class body, min=0, max=1.
		let v2 = expand_rep_subsig(
			"[0-9]{3}[-\\s]?[0-9]{3}", false, &cfg)
			.expect("expand none [b]");
		assert!(!v2.is_empty(), "no variants [b]");
		// (c) `[0-9]{2}?` (min=0, max=2). Verifies the optional
		// quantifier on a fan-out class still re-emits.
		let v3 = expand_rep_subsig(
			"[0-9]{3}[0-9]{2}?[0-9]{3}", false, &cfg)
			.expect("expand none [c]");
		assert!(!v3.is_empty(), "no variants [c]");
	}

	/// ws-delimited keyword arms (regenerated DLP format): the shape
	/// guard must NOT reject `[ws]KW[ws].{0,N}REGEX` as KwInMiddle, the
	/// direction comes from the gap, and the fan-out must scope to the
	/// regex part (keyword + ws + gap re-emitted verbatim, never pinned).
	#[test]
	pub fn tests_sde_rep_ws_keyword_arm(){
		use super::{partition_keyword_gap, analyze_aggressive_shape,
			expand_rep_subsig, to_hir};
		use crate::clamav::default_clamav_cfg;
		let mut cfg = default_clamav_cfg();
		cfg.b_aggressive_sde_for_rep = true;
		cfg.sde_rep_fanout_cap = 200;
		// forward arm -> dir 0, no KwInMiddle crash.
		let fwd = "[\\x20\\x09\\x0a\\x0d]insurance[\\x20\\x09\\x0a\\x0d]\
			.{0,300}[A-Za-z]{2}[0-9]{6}[ABCDabcd]";
		assert_eq!(partition_keyword_gap(&to_hir(fwd), None).unwrap().dir,
			0);
		assert_eq!(analyze_aggressive_shape(&to_hir(fwd), None).unwrap()
			.anchor, Some(0));
		let vf = expand_rep_subsig(fwd, false, &cfg).expect("fwd");
		// anchor (ws+KW+gap) is verbatim and identical across variants;
		// if a ws byte were pinned the shared prefix would break.
		let end = vf[0].find("{0,300}").unwrap() + "{0,300}".len();
		let pf = vf[0][..end].to_string();
		assert!(vf.iter().all(|s| s.starts_with(&pf)),
			"anchor not shared -> ws/keyword got fanned");
		// [A-Za-z]{2} (card 52) exceeds SINGLE_FANOUT_MAX, so it is NOT
		// pinned; budget lands on [0-9]{6} (10) + [ABCDabcd] (8) = 80
		// variants -> the number leg now anchors (was letter-only).
		assert_eq!(vf.len(), 80);
		// backward mirror -> dir 1, no crash.
		let bwd = "[A-Za-z]{2}[0-9]{6}[ABCDabcd].{0,300}\
			[\\x20\\x09\\x0a\\x0d]insurance[\\x20\\x09\\x0a\\x0d]";
		assert_eq!(partition_keyword_gap(&to_hir(bwd), None).unwrap().dir,
			1);
		assert_eq!(analyze_aggressive_shape(&to_hir(bwd), None).unwrap()
			.anchor, Some(1));
		// Sweden fwd: regex part = ([0-9]{2})?[0-9]{6}[+-]?[0-9]{4};
		// mandatory-first pins concrete digit bytes in the regex part.
		let swe = "[\\x20\\x09\\x0a\\x0d]id\\x20no[\\x20\\x09\\x0a\\x0d]\
			.{0,300}([0-9]{2})?[0-9]{6}[\\x2D\\x2B]?[0-9]{4}";
		assert_eq!(partition_keyword_gap(&to_hir(swe), None).unwrap().dir,
			0);
		let vs = expand_rep_subsig(swe, false, &cfg).expect("swe");
		assert!(vs.iter().any(|s| s.contains("\\x30")),
			"no pinned digit in regex part");
		// non-matching shapes -> None (keep whole-HIR path).
		assert!(partition_keyword_gap(&to_hir("[0-9]{3}-[0-9]{3}"), None)
			.is_none());
		assert!(partition_keyword_gap(&to_hir("foo[0-9]{3}"), None)
			.is_none());
	}

	#[test]
	pub fn tests_expose_hi_nibble_anchor(){
		use super::{expose_hi_nibble_anchor,
			collect_pm_reg_from_rustomaton_regex};
		// unquantified group -> de-paren; pinned 30 + exposed 3 = "303".
		let a = expose_hi_nibble_anchor("30(3(0|1|2|3|4|5|6|7|8|9))30");
		assert_eq!(a, "303(0|1|2|3|4|5|6|7|8|9)30");
		assert!(collect_pm_reg_from_rustomaton_regex(&a, 3).iter()
			.any(|(w, _)| w == "303"), "no 303 anchor: {:?}",
			collect_pm_reg_from_rustomaton_regex(&a, 3));
		// QUANTIFIED group -> PEEL (keeps {n} semantics, never corrupts).
		let b = expose_hi_nibble_anchor("30(3(0|1)){5}30");
		assert_eq!(b, "303(0|1)(3(0|1)){4}30");
		// letters (multi-hi-nibble) + non-capturing groups untouched.
		let c = "((?:4(1)|5(2))|3(0)3(1))";
		assert_eq!(expose_hi_nibble_anchor(c), c);
	}

}
