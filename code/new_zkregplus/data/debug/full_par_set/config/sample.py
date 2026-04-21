import os
import random

def sample(size_mb: int, id):

	"""
	Samples files from a source directory, sorted by size, until the total size
	is approximately the given size in MB, then writes the paths of the
	sampled files to an output file.

	Args:
		size_mb: The target sample size in megabytes.
	"""
	source_dir = "../../../../data/samples/binexec_merged128k/"
	output_filename = f"sample_{size_mb}M_{id}.dat"
	target_bytes = size_mb * 1024 * 1024

	if not os.path.isdir(source_dir):
		print(f"Error: Source directory not found at '{source_dir}'")
		return

	# 1. Discover files and collect metadata (path, size)
	all_files = []
	for filename in os.listdir(source_dir):
		file_path = os.path.join(source_dir, filename)
		if os.path.isfile(file_path):
			file_size = os.path.getsize(file_path)
			all_files.append((file_path, file_size))
			print("Adding file: " + file_path + ", file_size: " + str(file_size));

	if not all_files:
		print(f"Error: No files found in '{source_dir}'")
		return

	# 2. Sort files by size to better fit the target total size, then sample
	all_files.sort(key=lambda x: x[1])  # Sort by file_size (x[1]) ascending

	sampled_file_paths = []
	current_size = 0
	id = 0;
	for file_path, file_size in all_files:
		rand_offset = random.randint(0,5);
		if id + rand_offset < len(all_files):
			idx = id + rand_offset;
		else:
			idx = id;
		file_path = all_files[idx][0];
		file_size = all_files[idx][1]
		if current_size >= target_bytes:
			break
		sampled_file_paths.append(file_path)
		current_size += file_size

	# 3. Write the output file
	with open(output_filename, 'w') as f:
		for file_path in sampled_file_paths:
			arr = file_path.split("data/");
			if len(arr)!=2:
				print("ERROR on handling: " + file_path);
				os.exit(1);
			new_file_path = "data/" + arr[1];
			f.write(f"{new_file_path}\n")

	print(f"Successfully created sample file at '{output_filename}' with {len(sampled_file_paths)} files.")
	print(f"Total size of sampled files: {current_size / (1024 * 1024):.2f} MB")

if __name__ == "__main__":
	# Example usage: create a 1MB sample
	size = 4;
	for i in range(16):
		sample(size, i);
