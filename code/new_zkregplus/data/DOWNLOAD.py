import gdown
import os

#0. create cache folder
os.system("mkdir -p cache/main");

#1. download files (if not working - use the following to download manually)
# (1) https://drive.google.com/file/d/1OM_W54JxPEiV3S26XwY7f1qhEAVyFtv_/view?usp=drive_link (samples.7z)
# (2) https://drive.google.com/file/d/1zLN_7kGXH-1PWkrxUqwWhvmuDMRL3-Yl/view?usp=drive_link (src_sig.7z)
gdown.download("https://drive.google.com/uc?export=download&id=1OM_W54JxPEiV3S26XwY7f1qhEAVyFtv_", "samples.7z");
gdown.download("https://drive.google.com/uc?export=download&id=1zLN_7kGXH-1PWkrxUqwWhvmuDMRL3-Yl", "src_sig.7z");

#2. extract
os.system("7za x samples.7z");
os.system("7za x src_sig.7z");
print("extraction completed. SRC DATA => src_sig/ and samples/");
# overwrite the buggy gen_data.py extracted from samples.7z
# (its SPLIT_SIZE leaves only 16 bytes of margin under 32 MiB,
# which makes loc values overflow range2_bit=26 in full_data4).
os.system("cp gen_data.py samples/gen_data.py");
os.system("cd samples; python3 gen_data.py");

#3. verify split files leave >=100 KiB headroom under 32 MiB
#   (full_data4 uses range2_bit=26; loc encoding overshoots the
#   nibble count by ~tens of KB, so margin must be >= 100 KiB).
SPLIT_SIZE = 32 * 1024 * 1024 - 100 * 1024
probe = "samples/binexec_merged128k/anthoscli__00"
assert os.path.exists(probe), \
    "missing %s after gen_data.py" % probe
sz = os.path.getsize(probe)
assert sz == SPLIT_SIZE, \
    "%s is %d bytes, expected %d (32MiB - 100KiB). " \
    "samples/gen_data.py SPLIT_SIZE was not overwritten." \
    % (probe, sz, SPLIT_SIZE)
print("verified split size: %s = %d bytes" % (probe, sz))

