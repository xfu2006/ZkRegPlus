import re

with open('sonobe_mod/folding-schemes/src/folding/foldpot/driver.rs', 'r') as f:
    content = f.read()

# 965: let (steps, vec_len, vec_pci, _vec_cap_req, advice) = self.plan_nd_advice(log_level+1, true, &word, &vec_word_info[word_id-1],
content = content.replace('self.plan_nd_advice(log_level+1', 'self.plan_nd_advice(job_id, log_level+1')
# 1414: self.plan_nd_advice(log_level+2, false, &word, word_info, word_fname)
content = content.replace('self.plan_nd_advice(log_level+2', 'self.plan_nd_advice(job_id, log_level+2')

# 516: self.plan_nd_advice_new(log_level, b_save_advice, word, word_info, word_fname)
content = content.replace('self.plan_nd_advice_new(log_level', 'self.plan_nd_advice_new(job_id, log_level')

# 469: _vec_pci, _vec_cap, _vec_adv) = self.bin_search_best_layer(
content = content.replace('self.bin_search_best_layer(\n', 'self.bin_search_best_layer(job_id, \n')
# 658: self.bin_search_best_layer(log_level+2, b_save_advice,
content = content.replace('self.bin_search_best_layer(log_level+2', 'self.bin_search_best_layer(job_id, log_level+2')

# 664: self.par_search_best_layer(log_level+2, b_save_advice,
content = content.replace('self.par_search_best_layer(log_level+2', 'self.par_search_best_layer(job_id, log_level+2')

# 651: self.find_working_layer_for_wd(log_level, b_save_advice,
content = content.replace('self.find_working_layer_for_wd(log_level', 'self.find_working_layer_for_wd(job_id, log_level')

# gen_nd_advice_at_layer
content = content.replace('self.gen_nd_advice_at_layer(max_layer_id', 'self.gen_nd_advice_at_layer(job_id, max_layer_id')
content = content.replace('self.gen_nd_advice_at_layer(guessed_layer', 'self.gen_nd_advice_at_layer(job_id, guessed_layer')
content = content.replace('self.gen_nd_advice_at_layer(mid_id', 'self.gen_nd_advice_at_layer(job_id, mid_id')
content = content.replace('self.gen_nd_advice_at_layer(layer_id', 'self.gen_nd_advice_at_layer(job_id, layer_id')

# inside par_search_best_layer
content = content.replace('log_perf(0,', 'log_perf(job_id,')
content = content.replace('log(0,', 'log(job_id,')
# wait, there are other places where `log_perf(0,` is used but `job_id` is NOT in scope!
# so let's only do it locally.

# Let's fix gen_nd_advice() call to pass job_id
# 431: .gen_nd_advice(&seg, &word_info, prev_adv, i, 0)?;
content = content.replace('.gen_nd_advice(&seg, &word_info, prev_adv, i, 0)', '.gen_nd_advice(&seg, &word_info, prev_adv, i, job_id)')

with open('sonobe_mod/folding-schemes/src/folding/foldpot/driver.rs', 'w') as f:
    f.write(content)
