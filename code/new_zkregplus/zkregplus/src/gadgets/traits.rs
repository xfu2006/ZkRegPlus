/* Created 03/26/2025 */

// This module defines some commonly used traits and structs
// to build up proofs. The main purpose is to refactor
// component gadgets for better location/size control and
// memory saving.
//
// NOTE that the CP components are relatively simple and there
// is no need to use containers. Starting from the SED components,
// they leverage containers for simplifying serialization/deseiralization
// of claims and proofs (and in many cases having info embedded/correlated
// between sophisticated structs)


// ---------------------------------------------
//			Trait and Struct Declarations
// ---------------------------------------------
use ark_ff::{PrimeField};
use ark_relations::r1cs::SynthesisError;
use std::{rc::Rc,cell::RefCell,fmt::Debug};
use std::collections::{HashMap};
use folding_schemes::{
	folding::foldpot::{
		container_config::{ContainerConfig,Location},
		sigma_ir1cs::{WitnessSigmaIR1CSConfig, WitnessSigmaIR1CSVar},

	},
};
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::ConstraintSystemRef;
use crate::{gadgets::commons::{vec_to_var}};



pub const IDX_WORD:usize = 0;
pub const IDX_INP:usize = 1;
pub const IDX_OUP:usize = 2;
pub const IDX_DATA:usize = 3;
pub const IDX_SI_INP:usize = 4;
pub const IDX_SI_OUP:usize = 5;
pub const IDX_SI_DATA:usize = 6;
pub const IDX_FAILED_SIGS:usize = 7;
pub const IDX_DISCHARGED_SIGS:usize = 8;

/// An allocated column.
#[derive(Clone,Debug)]
pub struct Col<F: Clone>{
	/// its data, size must match the size attribute.
	pub data: Vec<F>, 
	/// its location (must be Col type)
	pub cfg: ContainerConfig,
	/// whether it is a constant col. 
	/// This is important for later converting to FpVar to save cost
	pub b_const: bool,
}

/// Two modes: single mode which consists of one Reference to a column.
/// NOTE that two containers may contain the same Col using Rc.
/// Complex mode is that it's a list of containers. The last 2 
/// Strings are (name, path) where path can be reset when the container
/// is placed as a child of another container. Iniitally, path = name (treat
/// it as root). For Single, its (name, path) is in the corresponding
/// Col's ContainerConfig::Column
#[derive(Clone,Debug)]
pub enum Container<F: Clone>{
	/// mode 1: single item 
	Single(Rc<RefCell<Col<F>>>),
	/// mode 2: a collection of containers
	Complex(Vec<Rc<RefCell<Container<F>>>>, HashMap<String,usize>, String, String),
}

/// Represents a component's Advice (used for SED components, the other
/// gadgets/components stay with legacy code)
pub trait ComponentAdvice<F:PrimeField>: Debug{
	/// generate the <inp,oup,data,subtbl_id_inp,subtbl_id_oup,subtbl_id_data>
	fn gen_stmt_components(&self)-> Vec<Vec<F>>{
		self.get_container().borrow().gen_stmt_components().0
	}


	/// generate the container config so that the circuit
	/// can use it to parse problem statement from its vector serialization
	/// NOTE that the config has relative references (qry strings).
	/// component mapper will run another round to resolve query strings.
	fn gen_raw_container_config(&self)->ContainerConfig{
		self.get_container().borrow().get_cfg()
	}

	fn get_container(&self)->Rc<RefCell<Container<F>>>;
}

// ---------------------------------------------
//			Implementations
// ---------------------------------------------
impl <F: Clone> Col<F>{
	/// construct a regular column. idx_seg is where it is located
	/// in statement vec. Its location will be later filled.
	/// NOTE: the name must be one word.
	pub fn new(data: Vec<F>, name: &str, idx_seg: usize)
	->Rc<RefCell<Self>>{
		//set to not resolved yet, it will be set to true in adjust_loc
		let loc = Location{src:(0,0,0,data.len(), String::new(), false), 
			dest: Some((idx_seg,0,data.len()))}; //revisable later
		let name = format!("{}", name);
		let b_const = false;
		let cfg = ContainerConfig::Column(loc, name.to_string(), 
			format!("{} {}", name.clone(), name), b_const); 
			//path can be later updated
		Rc::new(RefCell::new(Self{data, cfg, b_const: b_const}))
	}

	pub fn new_const(data: Vec<F>, name: &str, idx_seg: usize)
	->Rc<RefCell<Self>>{
		//set to not resolved yet, it will be set to true in adjust_loc
		let loc = Location{src:(0,0,0,data.len(), String::new(), false), 
			dest: Some((idx_seg,0,data.len()))}; //revisable later
		let name = format!("{}", name);
		let b_const = true;
		let cfg = ContainerConfig::Column(loc, name.to_string(), 
			format!("{} {}", name.clone(), name), b_const ); 
				//path can be later updated
		Rc::new(RefCell::new(Self{data, cfg, b_const}))
	}

	/// construct a foreign column. Still provides the data,
	/// but LATER when its VAR version is reconstructed, it will
	/// be retrieved from another gadget's statement using query string.
	/// NOTE: query string MUST BE ABSOLUTE PATH. (i.e., the source
	/// column's location should be FIXED (cannot be later added to another
	/// container) when this function is called.
	pub fn new_external(data: Vec<F>, name: &str, idx_seg: usize,
		gadget_offset: i32, qry_str: &str)->Rc<RefCell<Self>>{
		let loc = Location{src:(gadget_offset,idx_seg,0,data.len(), 
			qry_str.to_string(), false), 
			dest: None};
		let name = format!("{}", name);
		let b_const = false;
		let cfg = ContainerConfig::Column(loc, name.to_string(),
			format!("{} {}", name.clone(), name), b_const); 
				//path later to be updated
		Rc::new(RefCell::new(Self{data, cfg, b_const}))
	}

	/// generate the <inp,oup,data,subtbl_id_inp,subtbl_id_oup,subtbl_id_data,
	///   failed_sigs, discharged_sigs>
	/// RETURNS specifically: the chunk info of the subtbl_id_data for
	/// the id #5. It's a list of chunk info: (len, b_const)
	/// the total len of chunk info should be the same as subtbl_id_data.
	pub fn gen_stmt_components(&self)->(Vec<Vec<F>>, Vec<(usize,bool)>){
		//1. retrieve the save_to_location
		let loc = match &self.cfg{
			ContainerConfig::Column(loc,_,_,_) => loc,
			ContainerConfig::Complex(_,_,_) => 
				panic!("expect ContainerConfig of column to be Location")
		};
		let dest = loc.dest;
		let res:(Vec<Vec<F>>,Vec<(usize,bool)>) = dest.map_or(
			(vec![vec![]; 8], vec![]), 
			|(seg_id, _start, len)|{
				let mut res = vec![vec![]; 8];
				let mut info = vec![];
				if seg_id>0 {//not word, ignore word.
					let real_id = seg_id - 1;
					assert!(self.data.len()==len);
					res[real_id] = self.data.clone();
					if real_id==5{//subtbl_id_data
						info.push( (len, self.b_const) )
					}
				}
				(res, info)
			}
		);

		//it will be empty when dest is None or seg_id is 0 (word_seg)
		//because we return [inp/oup/data/subtbl_inp/sbutbl_data/subtbl_oup]
		res
	}
}


impl <F: Clone> Container<F>{
	/// get the name (same as get_name() keep it for legacy)
	pub fn name(&self)->String{self.get_name()}

	/// returning the  i'th layer1 element of complex, or itself for Single
	pub fn get_container_by_idx(&self, i: usize)->Rc<RefCell<Container<F>>>{
		match self{
			Container::Single(_) =>{
				assert!(i==0, "single only supports i=0");
				Rc::new(RefCell::new(self.clone()))
			},
			Container::Complex(vec,_,_,_)=>{
				assert!(i<vec.len());
				vec[i].clone() //not costly as cloning rc.
			}
		}
	}

	/// constructor. The name must be one word. Path will be determined later.
	pub fn new(name: &str)->Rc<RefCell<Self>>{
		Rc::new(RefCell::new(Container::Complex(vec![], HashMap::new(), 
			name.to_string(), name.to_string())))
	}

	pub fn new_single(col: Rc<RefCell<Col<F>>>)
	->Rc<RefCell<Self>>{
		Rc::new(RefCell::new(Container::Single(col)))
	}

	/// return its name 
	pub fn get_name(&self)->String{
		match self{
			Container::Single(rc_col)=>rc_col.borrow().cfg.get_name(),
			Container::Complex(_,_,name,_)=>name.to_string()
		}
	}

	/// return its current absolute path, this result can change if it's
	/// replaced as a child of another container.
	pub fn get_path(&self)->String{
		match self{
			Container::Single(rc_col)=>rc_col.borrow().cfg.get_path(),
			Container::Complex(_,_,_,path)=>path.to_string()
		}
	}

	/// insert the column (assumption no conflicts of names)
	pub fn add_col(&mut self, rc_col: Rc<RefCell<Col<F>>>){
		let single = Rc::new(RefCell::new(Container::Single(rc_col)));
		self.add_container(single);
	}

	/// serialize all
	pub fn to_vec(&self)->Vec<F>{
		match self{
			Container::Complex(vec,_map,_,_)=>{
				vec.iter().map(|x| x.borrow().to_vec()).flatten()
					.collect::<Vec<F>>()
			},
			Container::Single(col) =>{
				col.borrow().data.clone()
			}
		}
	}

	/// add a collection of cols
	pub fn concat_cols(cols: Vec<Rc<RefCell<Col<F>>>>, name: &str)
	->Rc<RefCell<Self>>{
		let res = Self::new(name);
		//not costing as clone Rc
		for x in cols {res.borrow_mut().add_col(x.clone());} 
	
		res
	}

	/// reset the config path for all descendents recursively,
	/// It eventuall boils down to the change of ContainerConfig
	/// for all columns
	pub fn reset_path(&mut self, parent_path: &String){
		match self{
			Container::Single(ref mut col)=>{
				col.borrow_mut().cfg.reset_path(parent_path);
			},
			Container::Complex(ref mut vec, _, name, ref mut path)=>{
				let new_path = format!("{} {}", parent_path, name);
				*path = new_path.clone();
				vec.iter().for_each(|v| 
					v.borrow_mut().reset_path(&new_path));
			}
		}
	}

	/// add a given container
	pub fn add_container(&mut self, cont: Rc<RefCell<Container<F>>>){
		let my_path = self.get_path();
		cont.borrow_mut().reset_path(&my_path);
		match self{
			Container::Complex(vec, map, _, _)=>{
				let name = cont.borrow().get_name();
				assert!(!map.contains_key(&name), "name: {} exists!", name);
				vec.push(cont);
				let id = vec.len()-1;
				map.insert(name, id);
			},
			_ => panic!("Container has to be complex to allow add_col")
		}
	}

	/// SPECIFIC NOTE: if the self is ALREADY fixed in a root container,
	/// pass nil for src_path; otherwise, pass the FUTURE fixed src_path
	/// of self.
	///
	/// duplicate itself recursively and make all columns to
	/// be duplicate columns, the gadget_id offset is
	/// the SRC_GADGET_ID - current (new hoster) gadet_id
	/// e.g., if the source gadget is one before us, the offset is -1.
	pub fn duplicate_as_external(&self, gid_offset: i32, 
		src_path: Option<String>)->Container<F>{
			self.duplicate_as_external_adv(gid_offset, src_path, None)
	}

	pub fn duplicate_as_external_adv(&self, gid_offset: i32, 
		src_path: Option<String>, new_name: Option<String>)
	->Container<F>{
		let exist_qry = if src_path.is_some() {src_path.unwrap()}
			else {self.get_path()}; //src one.

		match self{
			Container::Complex(vec, map, name, _)=>{
				let mut new_vec = vec![];
				let new_map = map.clone();
				for ele in vec{
					let path = format!("{} {}", 
						exist_qry, ele.borrow().get_name());
					let new_ele = ele.borrow().duplicate_as_external(
						gid_offset, Some(path));
					new_vec.push(Rc::new(RefCell::new(new_ele)));
				}
				let name2=if new_name.is_some(){new_name.unwrap()} 
					else {name.to_string()};
				Container::Complex(new_vec,new_map,name2.to_string(),exist_qry)
			},
			Container::Single(rc_col)=>{
				//make it an EXTERNAL column
				let new_cfg= match &rc_col.borrow().cfg{
					ContainerConfig::Column(loc, name, _, b_const)=> {
						//two cases to handle: (1) it's ALREADY an external col,
						//(2) it's a real DATA col.
						let name2=if new_name.is_some(){new_name.unwrap()} 
							else {name.to_string()};
						let (src,dest) = (&loc.src, &loc.dest);
						let new_src = if src.4.len()>0{//it's external
							//adjust the gid, but keep its ABSOLUTE 
							// exteranl qry str (src.4)
							let new_src = (src.0 + gid_offset, src.1, 
								src.2,src.3, 
								src.4.clone(), src.5);
							new_src
						}else{ //create external using the dest info
							assert!(dest.is_some());
							let dest = dest.unwrap();
							let new_src = (gid_offset,dest.0,dest.1,
								dest.2,exist_qry,src.5);  //set to
								//not src.5 (they will be resolved
								//in adjust_locations of ContainerConfig.
							new_src
						};

						let new_dest = None; //it will not be allocated because
						//it's referenceing external
						let new_loc = Location{src:new_src, dest: new_dest};
						ContainerConfig::Column(new_loc, name2.to_string(), 
							name2.to_string(), *b_const) //its path will be set later
					},
					_ => panic!("cannot handle complex")
				};
				let new_rc_col = Rc::new(RefCell::new(Col{
					data: rc_col.borrow().data.clone(),
					cfg: new_cfg,
					b_const: rc_col.borrow().b_const,
				}));
				Container::Single(new_rc_col)
			}
		}
	}


	/// return the column by name, only do one level search.
	pub fn get_col(&self, name: &str)->Result<Rc<RefCell<Col<F>>>, 
		SynthesisError>{
		match *self.get_container(name)?.borrow(){
			Container::Single(ref col) => Ok( col.clone() ),
			_ => panic!("expecting single col")
		}

	}

	/// return the container by name, only do one level search.
	pub fn get_container(&self, name: &str)->Result<Rc<RefCell<Container<F>>>, SynthesisError>{
		let name = format!("{}", name);
		match self{
			Container::Complex(vec, map, _, _)=>{
				if !map.contains_key(&name){
					println!("ERR DETAILS: cannot find name: {} in map: {:?}", 
					  name,	map);
				}
				assert!(map.contains_key(&name), "name: {} not exists in {}!. map: {:?}", name, self.name(), map);
				let id = map.get(&name).expect("err in hashmap");
				Ok(vec[*id].clone())
			},
			_ => panic!("has to be complex container!")
		}
	}

	/// get the container by path (absolute path string)
	/// its name must match the first element of the query string
	pub fn search_container(
		&self, 
		qry: &str //absolute path separated by space
	)->Result<Rc<RefCell<Container<F>>>, SynthesisError>{
		let vec_names = qry.split_whitespace().map(|x|
            x.to_string()).collect::<Vec<String>>();
		Ok( self.search_container_worker(&vec_names[0..])? )
	}

	fn search_container_worker(&self, qry_words: &[String])
	->Result<Rc<RefCell<Container<F>>>, SynthesisError>{
		
		assert!(&qry_words[0] == &self.get_name(), "search_container fails: cannot find qry_wd[0]: {}, self: {}", qry_words[0], self.get_name());
		match self{
			Container::Single(_)=>{ panic!("should not reach this level")},
			Container::Complex(vec, map, _name, _path)=>{
				let id = map.get(&qry_words[1]).expect(
					&format!("In {} cannot find {}", qry_words[0], qry_words[1] ));
				let new_qry = &qry_words[1..];
				if qry_words.len()==2{
					Ok(vec[*id].clone()) //does not cost anything for Rc clone
				}else{
					Ok(	vec[*id].borrow().search_container_worker(&new_qry)? )
				}
			}
		}
	}


	/// recursively collect the container (ignoring its own cfg depending
	/// on b_rec is true)
	pub fn get_cfg(&self)->ContainerConfig{
		match self{
			Container::Single(rc_col)=>{rc_col.borrow().cfg.clone()},
			Container::Complex(vec_con, _map, _, _)=>{
				let name = self.get_name();
				let path = self.get_path();
				let vec_cfg = vec_con.iter().map(|x| x.borrow().get_cfg())
					.collect::<Vec<ContainerConfig>>();
				ContainerConfig::Complex(vec_cfg, name, path)
			}
		}
	}

	/// generate the <inp,oup,data,subtbl_id_inp,subtbl_id_oup,subtbl_id_data>
	/// and the descriptor for sid_table_data.
	pub fn gen_stmt_components(&self)->(Vec<Vec<F>>, Vec<(usize,bool)>){
		match self{
			Container::Single(rc_col) => {
				rc_col.borrow().gen_stmt_components()
			},
			Container::Complex(vec_container,_,_,_) =>  {
				vec_container.iter().fold(
					(vec![vec![]; 8], vec![]),
					|sum, adv|{
						let (cps, sid_info)=adv.borrow().gen_stmt_components();
						assert!(cps.len()==8);
						let new_cps = sum.0.into_iter().zip(
							cps.into_iter()).map(|(a,b)|{
							let res:Vec<F> = vec![a, b].concat();
							res
						}).collect::<Vec<Vec<F>>>();
						let new_sid_info:Vec<(usize,bool)> = 
							[sum.1, sid_info].concat();
						(new_cps, new_sid_info)
					}
				)
			}
		}
	}

	/// dump its structure
	pub fn dump_structure(&self, indent: usize){
		let indent_str = std::iter::repeat(" ")
			.take(indent).collect::<String>();
		match self{
			Container::Single(_)=> println!("{}{}",indent_str,self.get_name()),
			Container::Complex(vec,_,_,_)=>{
				println!("{}{}",indent_str,self.get_name());
				for x in vec{x.borrow().dump_structure(indent+1);}
			}
		}
	}

}

/// The following only works for loading VAR version of container
impl <F: PrimeField> Container<FpVar<F>>{
	/// It extract stat_vec
	/// from witness given cfg. Notice that a stmt_vec
	/// corresponds to the FULL container serialized version (even
	/// with external source columns) we are assuming that
	/// the get_stmt_mapping_sintructions() implementation guarantees that.
	pub fn extract_stmt_vec(i: usize, cfg: &WitnessSigmaIR1CSConfig,
		wtns: &WitnessSigmaIR1CSVar<F>)->Vec<FpVar<F>>{
		let (stmt_idx, _, _, _) = cfg.get_gadget_indices(i);
		let my_stmt = stmt_idx.iter().map(|(a,b)|
			wtns.statement[*a..*b+1].to_vec()).flatten()
			.collect::<Vec<FpVar<F>>>();

		my_stmt	
	}

	/// return Rc<RefCell> version of from()
	pub fn rc_from(src: &Container<F>, cs:ConstraintSystemRef<F>)
	-> Rc<RefCell<Self>>{
		Rc::new(RefCell::new(Self::from(src, cs)))
	}

	/// convert the var version from the field version of the container
	/// retain the structure
	pub fn from(src: &Container<F>, cs: ConstraintSystemRef<F>)->Self{
		match src{
			Container::Single(rc_col) => {
				let col = Col::<FpVar<F>>{
					data: vec_to_var(&cs, &rc_col.borrow().data),
					cfg: rc_col.borrow().cfg.clone(),
					b_const: rc_col.borrow().b_const,
				};
				Container::Single(Rc::new(RefCell::new(col)))
			},
			Container::Complex(vec, map, name, path)=>{
				let new_vec = vec.iter().map(|c|
					Rc::new(RefCell::new(Self::from(&c.borrow(), cs.clone())))
				).collect();
				Container::Complex(new_vec, map.clone(),
					name.clone(), path.clone())
			}
		}
	}

	/// recursive worker function for load_from.
	/// return the next start position for next each container.
	fn load_from_worker(
		stmt_vec: &Vec<FpVar<F>>,
		cfg: &ContainerConfig,
		start_pos: usize)->Result<(Self, usize), SynthesisError>{
		match cfg{
			ContainerConfig::Column(loc, _name, _, b_const) => {
				let len = loc.src.3;
				let col = Col::<FpVar<F>>{
					data: stmt_vec[start_pos..start_pos+len].to_vec(),
					cfg: cfg.clone(), 
					b_const: *b_const
				};
				Ok( 
				 (Container::Single(Rc::new(RefCell::new(col))),start_pos+len) 
				)
			},
			ContainerConfig::Complex(vloc,myname,mypath)=>{
				let mut pos = start_pos;
				let mut vec_comp = vec![];
				let mut hs = HashMap::<String, usize>::new();
				for i in 0..vloc.len(){
					let (comp, new_pos) = Self
						::load_from_worker(stmt_vec, &vloc[i], pos)?;
					pos = new_pos;
					vec_comp.push(Rc::new(RefCell::new(comp)));
					let comp_name = vloc[i].get_name();
					assert!(!hs.contains_key(&comp_name), 
						"component name {} already exists", comp_name);
					hs.insert(comp_name, i);
				}
				Ok( (Container::Complex(vec_comp, hs, myname.to_string(),
					mypath.to_string()), pos) )
			}
		}
	}

	/// rebuild the i'th statement by retrieving contents
	/// from witness. The Witness config is given in wtns-cfg,
	/// the container config is given in cfg.
	/// NOTE that it might be retrieve contents from witness from other
	/// gadgets other than i'th.
	pub fn load_from(
		i: usize, 
		wtns_cfg: &WitnessSigmaIR1CSConfig,
		wtns: &WitnessSigmaIR1CSVar<F>, 
		cfg: &ContainerConfig)->Result<Self, SynthesisError>{
		let stmt_vec = Self::extract_stmt_vec(i, wtns_cfg, wtns);

		let (res, len) = Self::load_from_worker(&stmt_vec, cfg, 0)?;
		assert!(len==stmt_vec.len());

		Ok( res )
	}
}

#[cfg(test)]
pub mod tests_traits{
	use ark_bn254::{Fr};
	use crate::gadgets::traits::{Col,Container,IDX_SI_DATA,IDX_DATA,
		IDX_INP, IDX_SI_INP};

	#[test]
	pub fn test_const_cols(){
		let col1 = Col::<Fr>::new(vec![Fr::from(2u32);10], "col1", IDX_DATA); 
		let sid_col1 = Col::<Fr>::new_const(vec![Fr::from(20u32);10], "scol1", IDX_SI_DATA);
		let c1 = Container::<Fr>::new("c1");
		c1.borrow_mut().add_col(col1);
		c1.borrow_mut().add_col(sid_col1);

		let col21 = Col::<Fr>::new(vec![Fr::from(3u32);10], "col21", IDX_DATA); 
		let sid_col21 = Col::<Fr>::new(vec![Fr::from(30u32);20], "scol21", IDX_SI_DATA);
		let c2 = Container::<Fr>::new("c2");
		c2.borrow_mut().add_col(col21);
		c2.borrow_mut().add_col(sid_col21);

		let col31 = Col::<Fr>::new_const(vec![Fr::from(4u32);10], "col21", IDX_INP); 
		let sid_col31 = Col::<Fr>::new(vec![Fr::from(40u32);10], "scol21", IDX_SI_INP);
		let c3 = Container::<Fr>::new("c3");
		c3.borrow_mut().add_col(col31);
		c3.borrow_mut().add_col(sid_col31);

		let all = Container::<Fr>::new("all");
		all.borrow_mut().add_container(c1);
		all.borrow_mut().add_container(c2);
		all.borrow_mut().add_container(c3);

		let (_cps, sinfo) = all.borrow().gen_stmt_components();
		assert!(sinfo==vec![(10, true), (20, false)]);
	}
}
