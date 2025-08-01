/* Created 03/31/2025
*/

// this contains the location and container config used to support
// advanced gadgets with sophisticated structure which are not easy
// to track size manually. 
//
// Basic idea: each gadget's statement vector can be regarded
// as a serialized vector of a Container, which can recursively
// comprise of various proofs and claims, which are also expressed
// as containers. Columns are basic storage units, which can be
// used to construct tables. To avoid duplicates, each unique column
// have one storage location, but may be used ``virtually" in multiple
// containers, so care has to be taken care of the cross references.

#[derive(Clone,Debug)]
pub struct Location{
	/// Indicates the location to load when constructing
	/// VAR version of itself in a statement VAR. The source
	/// of information would be a vector of statement_vec()
	/// for all gadgets in the same component. Note that
	/// it is able to retrieve information from other gadget's statement.
	///
	/// Here i32 is the relative offset where 0 means this gadget,
	/// -1 means the previous gadget. usize indicates the
	/// segment ID (IDX_WORD, IDX_INP, .... IDX_SI_DATA).
	/// Typically, the i32 element is 0.
	/// The last String element represent the qry_str if it is foreign
	/// qry string should be separated by space
	/// the bool indicates whether it is resolved or not
	pub src: (i32, usize, usize, usize, String, bool),

	/// indicates where this col is to be located in the
	/// statement_vec of its owner gadget.
	/// the tuple indicates (seg_id, start, len).
	/// This location is used to indicate the location where
	/// the colun is SAVED into statement vec when advice is called
	/// to construct statement.
	pub dest: Option<(usize, usize, usize)>,
}

/// seralization and deserialization config for containers, which is used
/// to support more sophisticated gadgets in SED approach.
#[derive(Clone,Debug)]
pub enum ContainerConfig{
	/// for Column. Two strings are: name and abs_path 
	Column(Location, String, String),
	/// Complex case that it has a vector of container config
	Complex(Vec<ContainerConfig>, String, String),
}

// -----------------------------------------------
//  	Implementations
// -----------------------------------------------
impl Location{
	/// generate mapping instructions for generating the column
	/// from a statement vector
	pub fn gen_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
		assert!(self.src.5, "Location: {:?} not resolved yet", self);
		let tuple = (self.src.0, self.src.1, self.src.2, self.src.3);
		vec![tuple]
	}

	/// return the 9 segment sizes for 
	/// [word,inp,oup,data,si_inp, si_oup, si_data,failed_sigs,discharged_sigs ]
	/// This applies to the dest only
	pub fn get_to_add_size(&self)->Vec<usize>{
		let mut res = vec![0usize; 9];
		let (idx,to_add) = if self.dest.is_some(){
			let (seg_id, _start, len) = self.dest.unwrap();
			(seg_id, len)
		}else{
			(0, 0)
		};
		res[idx] += to_add;

		res
	}
}
impl ContainerConfig{
	pub fn reset_path(&mut self, parent_path: &String){
		match self{
			ContainerConfig::Column(_loc, name, ref mut path) => {
				let new_path = format!("{} {}", parent_path, name); 
				*path = new_path.to_string();
			},
			ContainerConfig::Complex(vec, name, ref mut path) => {
				let new_path = format!("{} {}", parent_path, name); 
				*path = new_path.to_string();
				for i in 0..vec.len(){//recursively
					vec[i].reset_path(&new_path);
				}
			},
		}
	}
	/// return its name
	pub fn get_name(&self)->String{
		match self{
			ContainerConfig::Column(_,name,_)=>name.to_string(),
			ContainerConfig::Complex(_,name,_)=>name.to_string()
		}
	}

	pub fn get_path(&self)->String{
		match self{
			ContainerConfig::Column(_,_,path)=>path.to_string(),
			ContainerConfig::Complex(_,_,path)=>path.to_string()
		}
	}

	/// update the col located at the path with its new value
	/// If not found, return 0. otherwise return the total
	/// number of columns updted (to verify correctness. a valid
	/// update returns 1). It's expected new_col is a Column config
	pub fn update_col(&mut self, path: &str, new_col: &ContainerConfig)
	->usize{
		match self{
			ContainerConfig::Column(ref mut loc,ref mut name,ref mut path)=>{
				match new_col{
					ContainerConfig::Column(newloc, newname, newpath)=>{
						if &path==&newpath{
							*loc = newloc.clone();
							*name= newname.to_string();
							*path = newpath.to_string();

							1//updated 1
						}else {0}
					},
					_ =>panic!("new_col has to be aoclumn")
				}
			}, 
												 //a container of a column
			ContainerConfig::Complex(vec, _name, _p1)=>{
				vec.iter_mut().map(|c|
					c.update_col(path, new_col)).sum::<usize>()
			}
		}
	}

	/// get the path of the parent
	pub fn get_parent_path(&self)->String{
		let mypath = self.get_path();
		let vec_names = mypath.split_whitespace().map(|x| 
			x.to_string()).collect::<Vec<String>>(); 
		let new_vec_names = &vec_names[0..vec_names.len()-1];
		if new_vec_names.len()==0{return "".to_string();}
		else{
			let mut res = new_vec_names[0].clone();
			for i in 1..new_vec_names.len(){
				res = format!("{} {}", res, new_vec_names[i]);
			}
			res
		}
	}

	/// search by a query string (which is split by a path)
	/// return Option, None when not found
	pub fn search_by_path(&self, qry_str: &String)
	->Option<Self>{
		let vec_names = qry_str.split_whitespace().map(|x| 
			x.to_string()).collect::<Vec<String>>(); 
		self.search_by_path_worker(&vec_names) 
	}


	fn search_by_path_worker(&self, vec_names: &Vec<String>)
	->Option<Self>{
		if vec_names[0]!=self.get_name() {return None;}
		if vec_names.len()==1 {return Some(self.clone());} //that's me

		match self{
			ContainerConfig::Column(_,_,_)=>{
				assert!(vec_names.len()==1);
				Some( self.clone() )
			},
			ContainerConfig::Complex(vec, _, _)=>{
				let next_comps = vec.iter().filter(|x| 
						x.get_name()==vec_names[1])
					.map(|x| x.clone())
					.collect::<Vec<ContainerConfig>>();
				assert!(next_comps.len()<=1, 
					"duplicate names in {}", self.get_path());
				if next_comps.len()==0 {return None;}
				let next_comp = &next_comps[0];
				next_comp.search_by_path_worker(&vec_names[1..].to_vec())
			}
		}
	}

	/// recursively convert all Location to map instructions
	pub fn gen_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
		match self{
			ContainerConfig::Column(loc,_,_) => loc.gen_stmt_map_instructions(),
			ContainerConfig::Complex(vec, _,_) => {
				vec.iter().fold(Vec::<(i32,usize,usize,usize)>::new(), 
				|sum, container|{
					let res = container.gen_stmt_map_instructions();
					vec![sum, res].concat()
				})
			}
		}
	}

	/// return the 9 segment sizes for 
	/// [word,inp,oup,data,si_inp, si_oup, si_data,failed_sigs, discharged_sigs]
	/// this is for building up statement (consider dest only).
	pub fn get_to_add_size(&self)->Vec<usize>{
		match self{
			ContainerConfig::Column(loc,_,_) => loc.get_to_add_size(),
			ContainerConfig::Complex(vec,_,_) => {
				vec.iter().fold(vec![0usize;9], 
				|sum: Vec<usize>, container|{
					let res: Vec<usize> = container.get_to_add_size();
					assert!(res.len()==9);
					sum.into_iter().zip(res.into_iter()).map(|(x,y)|
						x+y).collect::<Vec<usize>>()
				})
			}
		}
	}

	/// adjust the location of all configs in the vec.
	/// This vec of configs are for the collection of gadgets
	/// INSIDE one component_mapper (e.g., sed_mapper).
	/// All the positions adjusted are RELATIVE to the start position
	/// INSIDE the component_mpaper, where additional map instructions
	/// whill have position shifted in the mapper when it invokes
	/// gen_stmt_map_instructions().
	pub fn adjust_locations(vec_cfgs: &mut Vec<ContainerConfig>){
		let mut dst_locs = vec![0usize; 9];
		for i in 0..vec_cfgs.len(){
			let path_i = vec_cfgs[i].get_path();
			Self::recursive_adjust_location(&path_i, vec_cfgs, &mut dst_locs);
		}
	}

	/// Recursively adjust the cfg at path given.
	/// Assuming all its dependency records before it are resolved.
	/// Update the dst_loc whenever a 
	/// real (i.e., not external src) col is updated.
	/// NOTE that context is an array of ContainerConfig which provides
	/// resolving info, HOWEVER, itself might be changed during the process
	/// to allow resolving columns immediately after it's updated.
	fn recursive_adjust_location(
		path: &str, //the path of the cfg to be changed
		context: &mut Vec<ContainerConfig>, //root level to qry, can be updated.
		dst_locs: &mut Vec<usize>, //the info to update
	){
		//1. locate the cfg and its root container index
		assert!(dst_locs.len()==9);
		let path = format!("{}", path);
		let mut idx = 0;
		let mut cfg = None;
		for i in 0..context.len(){
			let res = context[i].search_by_path(&path);
			if res.is_some(){ idx = i; cfg = res; }
		}
		assert!(cfg.is_some());
		let cfg = cfg.unwrap();

		match cfg{//note cfg is just a copy
			ContainerConfig::Column(loc, name, p2)=>{
				assert!(&path==&p2);
				let (src,dest) = (loc.src.clone(), loc.dest.clone());
				if dest.is_some(){//regular column
					let (seg_idx, _, len) = dest.unwrap().clone();
					let start = dst_locs[seg_idx];
					let new_src = (0,seg_idx,start,len, "".to_string(),true);
					let new_dest = Some( (seg_idx, start, len) );
					let new_loc = Location{src:new_src, dest: new_dest};
					dst_locs[seg_idx] += len; //updated with len
					let new_col = ContainerConfig
						::Column(new_loc, name.to_string(), path.clone());
					let cnt_updates = context[idx].update_col(&path, &new_col);
					assert!(cnt_updates==1);
				}else{//foreign column
					let i32idx = idx as i32;  
					let (offset, _, _, _, qry_str, _b_resolved) = src;
					let srcidxi32 = i32idx + offset;
					let srcidx = srcidxi32 as usize;
					let src_container = context[srcidx]
						.search_by_path(&qry_str);
					if !src_container.is_some(){
						println!("ERROR cannot find qry: {}", qry_str);
						context[srcidx].dump(0);
						panic!("STOP HERE. check details above");
					}
					let src_container = src_container.unwrap();
					match src_container{
						ContainerConfig::Column(loc, _s, _) => {
							let (src_offset, segid, start, len, _s, b_resolved)
								= loc.src.clone();
							assert!(b_resolved);
							let new_offset = offset + src_offset;
							let new_src = (new_offset, segid, start, len, 
								qry_str.clone(), b_resolved);
							let new_loc = Location{src: new_src, dest: None};
							//no write to dst_locs because it's foreign
							let new_col = ContainerConfig
								::Column(new_loc,name.to_string(),path.clone());
							assert!(context[idx].update_col(&path, &new_col)==1);
						},
						_ => panic!("expect {} to be a column!", qry_str)
					}
				}//end else forieng colmn
			},//end match Column
			ContainerConfig::Complex(vec_loc, _name, _my_path)=>{
				vec_loc.iter().for_each(|c|{
					let path = c.get_path();
					Self::recursive_adjust_location(&path, context, dst_locs);
				});
			}//end match Complex
		}; //end of match vec_cfg[i]
	}//end of function

	/// dump itself, identation is determined by step
	pub fn dump(&self, step: usize){
		let indent_str = std::iter::repeat(" ").take(step).collect::<String>();
		match self{
			ContainerConfig::Column(_,s,_) 
				=> println!("{}{}", indent_str, s),
			ContainerConfig::Complex(vec, name, _)=>{
				println!("{}{}", indent_str, name);
				for x in vec{ x.dump(step+1); }
			}
		}
	}
}


