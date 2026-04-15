/// System related utilities such as read files etc.
/* Created 01/04/2024
*/
extern crate regex;

use regex::Regex;
use std::{
	process::{Stdio,Command},
	fs::{read_to_string,OpenOptions,remove_file,File,metadata},
	path::{Path},
	io::{Write,Read}
};
use project_root::{get_project_root};
use std::fs;

/// write sigs to dir where dir is relatively to the 
/// project root/data.
/// We assume contents are not large (and use in-efficient text write funcs)
pub fn write_sigs_to_dir(
	sigs: &Vec<String>, 
	dir: &str, 
	sigs_need_dfa: &Vec<String>,
	sigs_need_ised: &Vec<String>,
	sigs_need_ised_igc: &Vec<String>
){
	let rt = proj_root();
	let fnames = vec!["sigs.db", "needs_dfa.txt", 
		"needs_ised.txt", "needs_ised_igc.txt"];
	let v2d = vec![sigs, sigs_need_dfa, sigs_need_ised, sigs_need_ised_igc];
	for i in 0..fnames.len(){
		let filename= format!("{}/data/{}/{}", rt, dir, fnames[i]);
		write_to_file(&filename, &format!("# {}\n", fnames[i])); 
		for line in v2d[i]{
			append_to_file(&filename, &format!("{}\n",line));
		}
	}
}
/// return the absolute path of the project
pub fn proj_root()->String{
	match get_project_root(){
		Ok(p) => {
			let abspath = fs::canonicalize(&p);
			let res = abspath.expect("unable to extract proj path");
			res.into_os_string().into_string().expect("error in abspath")
		},
		Err(e) => panic!("ERROR: unable to retrieve project root: {}", e)
	}
}

/// create as new dir, the dir should ONLY be a file name.
/// the directory will be created under project_root/data/cache
pub fn create_new_cache_dir(dir: &str){
	//1. validate data
	let r1 = Regex::new(r"[0-9a-f_]+").unwrap();
	assert!(r1.is_match(dir), "INVALID dir: {}. Only alphanum allowed", dir);

	//2. create dir
	let abspath = format!("{}/data/cache/{}", &proj_root(), dir); 
	if file_exists(&abspath){
		fs::remove_dir_all(&abspath).
			expect(&format!("remove dir fails: {}", dir));
	}
	fs::create_dir_all(&abspath).expect(&format!("create dir fails: {}", abspath));
}

/// true if file exists
pub fn file_exists(fname: &str) -> bool{
	Path::new(fname).exists()
}

/// append a line to a file
pub fn append_to_file(fname: &str, line: &str){
    let mut fh = OpenOptions::new().append(true).open(fname)
		.expect(&format!("open {} failed", fname));
   	fh.write(line.as_bytes()).expect("write failed");
}

/// write a line to a file (erase contents if it exists)
pub fn write_to_file(fname: &str, line: &str){
	if Path::new(fname).exists(){
		remove_file(fname).unwrap();
	}
    let mut fh = OpenOptions::new().create_new(true).write(true).open(fname)
		.expect(&format!("open {} failed", fname));
   	fh.write(line.as_bytes()).expect("write failed");
}

/// write a vector of lines to file
pub fn write_lines(fname: &str, lines: &Vec<String>, b_create_new: bool){
   let fpath = format!("{}/{}", &proj_root(), fname);
   let mut fh = if b_create_new{
   		if Path::new(&fpath).exists(){ remove_file(&fpath).unwrap(); }
        OpenOptions::new().create_new(true).write(true).open(&fpath)
        .expect(&format!("open {} failed", &fpath))
    }else{
        OpenOptions::new().write(true).append(true).open(&fpath)
        .expect(&format!("open {} failed", &fpath))
    };

	for line in lines{
   		fh.write((line.to_owned() + "\n").as_bytes()).expect("write failed");
	}
}

/// read all lines out 
pub fn read_lines(fpath: &str)->Vec<String>{
	let mut res = vec![];
	for line in  read_to_string(fpath).expect(&format!("ERROR in read: {}", fpath)).lines(){
        res.push(line.to_string())
    }
   	res 
}

/// read file in one string 
pub fn read(fpath: &str) -> String{
	read_to_string(fpath).expect(&format!("error in read file: {}", fpath))
}

/// read all binary contents and return as a hex string
pub fn read_nibbles(fpath: &str) -> Vec<u8>{
	//1. read the file
	let mut file = File::open(fpath).expect(
		&format!("can't open file: {}", fpath));
    let metadata = metadata(fpath).expect("unable to read");
	let size = metadata.len() as usize;
    let mut buffer = vec![0; size];
    file.read(&mut buffer).expect("buffer overflow");

	//2. collet string
	let mut vres = vec![];
	for num in buffer{
		vres.push(num/16);
		vres.push(num%16);
	}

	vres	
}



/// check if s is a match of r by running perl.
/// NOTE: requires PERL installed
pub fn perl_is_match(r: &str, s: &str) -> bool{
	//1. write th efile
	let fname = "data/cache/to_remove.pl";
	let real_fname = format!("{}/{}", &proj_root(), fname);
	let prefix_s = if r.chars().next()==Some('^') 
		{"".to_string()} else {"^".to_string()};
	let suffix_s = if r.ends_with("$") {"".to_string()} else {"$".to_string()};
	let r = prefix_s + &r + &suffix_s;
	let lines = vec![
		format!("$s1 = \"{}\";", s),
		format!("print 'ok' if $s1 =~ /{}/;", r)
	];
	write_lines(fname, &lines, true);

	//2. run the perl and get the result
	let output = Command::new("perl")
		.arg(&real_fname)
		.stdout(Stdio::piped()).output().unwrap();
	let sout = String::from_utf8(output.stdout).unwrap();

	sout.contains("ok")
}

#[cfg(test)]
mod tests{
	use crate::os::{proj_root, create_new_cache_dir};

	#[test]
	fn test_proj_root(){
		let path = proj_root();
		assert!(path.contains("new_zkregplus"), "ERROR proj path: {}", path);
		create_new_cache_dir("dir1");
	}
}

