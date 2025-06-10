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
os.system("cd samples; python3 gen_data.py");

