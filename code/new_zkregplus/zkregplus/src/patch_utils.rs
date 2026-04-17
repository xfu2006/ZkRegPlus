
pub fn serialize_affines_raw<P: SWCurveConfig>(v: &[Affine<P>], path_prefix: &str) {
    let zero = P::BaseField::zero();
    let n = v.len();
    let mut vx = vec![zero; n];
    let mut vy = vec![zero; n];
    let mut vb = vec![false; n];
    
    // Convert to uncompressed coordinates
    v.par_iter().enumerate().for_each(|(i, pt)| {
        if pt.is_zero() {
            vx[i] = zero;
            vy[i] = zero;
            vb[i] = true;
        } else {
            // Unwrapping is safe because the point is not zero
            vx[i] = *pt.x().unwrap();
            vy[i] = *pt.y().unwrap();
            vb[i] = false;
        }
    });

    let path_vx = format!("{}_vx.data", path_prefix);
    let path_vy = format!("{}_vy.data", path_prefix);
    let path_vb = format!("{}_vb.data", path_prefix);

    let file = File::create(&path_vx).expect("create v_x err");
    let mut writer = BufWriter::new(file);
    vx.serialize_uncompressed(&mut writer).expect("serialize v_x err");

    let file = File::create(&path_vy).expect("create v_y err");
    let mut writer = BufWriter::new(file);
    vy.serialize_uncompressed(&mut writer).expect("serialize v_y err");
    
    let file = File::create(&path_vb).expect("create v_b err");
    let mut writer = BufWriter::new(file);
    vb.serialize_uncompressed(&mut writer).expect("serialize v_b err");
}

pub fn deserialize_affines_raw<P: SWCurveConfig>(path_prefix: &str) -> Vec<Affine<P>> {
    let path_vx = format!("{}_vx.data", path_prefix);
    let path_vy = format!("{}_vy.data", path_prefix);
    let path_vb = format!("{}_vb.data", path_prefix);

    let file_vx = File::open(&path_vx).expect("open v_x err");
    let mut reader_vx = BufReader::new(file_vx);
    let vx = Vec::<P::BaseField>::deserialize_uncompressed(&mut reader_vx).expect("deserialize v_x err");

    let file_vy = File::open(&path_vy).expect("open v_y err");
    let mut reader_vy = BufReader::new(file_vy);
    let vy = Vec::<P::BaseField>::deserialize_uncompressed(&mut reader_vy).expect("deserialize v_y err");

    let file_vb = File::open(&path_vb).expect("open v_b err");
    let mut reader_vb = BufReader::new(file_vb);
    let vb = Vec::<bool>::deserialize_uncompressed(&mut reader_vb).expect("deserialize v_b err");

    assert_eq!(vx.len(), vy.len());
    assert_eq!(vx.len(), vb.len());

    let mut v = vec![Affine::<P>::zero(); vx.len()];
    v.par_iter_mut().enumerate().for_each(|(i, pt)| {
        if vb[i] {
            *pt = Affine::<P>::zero();
        } else {
            *pt = Affine::<P>::new_unchecked(vx[i], vy[i]);
        }
    });

    v
}

pub fn write_g16_optimized<E: Pairing>(path: &Path, pk: &ProvingKey<E>, vk: &VerifyingKey<E>) 
where 
    E::G1Affine: From<Affine<<E::G1 as CurveGroup>::Config>>,
    E::G2Affine: From<Affine<<E::G2 as CurveGroup>::Config>>,
{
    let b_debug = true;
    let path_str = path.to_str().unwrap();

    // 1. Serialize single elements and small vectors into a metadata file
    let meta_path = format!("{}.meta", path_str);
    let file = File::create(&meta_path).expect("create meta err");
    let mut writer = BufWriter::new(file);
    vk.alpha_g1.serialize_compressed(&mut writer).expect("ser vk.alpha_g1");
    vk.beta_g2.serialize_compressed(&mut writer).expect("ser vk.beta_g2");
    vk.gamma_g2.serialize_compressed(&mut writer).expect("ser vk.gamma_g2");
    vk.delta_g2.serialize_compressed(&mut writer).expect("ser vk.delta_g2");
    // vk.gamma_abc_g1 is a vector, we'll save it raw
    
    pk.vk.alpha_g1.serialize_compressed(&mut writer).expect("ser pk.vk.alpha_g1");
    pk.beta_g1.serialize_compressed(&mut writer).expect("ser pk.beta_g1");
    pk.delta_g1.serialize_compressed(&mut writer).expect("ser pk.delta_g1");
    
    // 2. Serialize large vectors raw
    // Note: E::G1Affine and E::G2Affine might not be directly `Affine<P>`, 
    // but in arkworks, they are usually type aliases or wrappers.
    // Assuming they are compatible or we need to transmute/map.
    // Let's sketch it for Bn254 specifically if generic is too hard.
}

// Specific to Bn254 for simplicity, as we downcast to it in driver anyway.
pub fn write_g16_optimized_bn254(path: &Path, pk: &ark_groth16::ProvingKey<Bn254>, vk: &ark_groth16::VerifyingKey<Bn254>) {
    let b_debug = true;
    let path_str = path.to_str().unwrap();

    let meta_path = format!("{}.meta", path_str);
    let file = File::create(&meta_path).expect("create meta err");
    let mut writer = BufWriter::new(file);
    vk.alpha_g1.serialize_compressed(&mut writer).expect("ser vk.alpha_g1");
    vk.beta_g2.serialize_compressed(&mut writer).expect("ser vk.beta_g2");
    vk.gamma_g2.serialize_compressed(&mut writer).expect("ser vk.gamma_g2");
    vk.delta_g2.serialize_compressed(&mut writer).expect("ser vk.delta_g2");
    
    pk.vk.alpha_g1.serialize_compressed(&mut writer).expect("ser pk.vk.alpha_g1");
    pk.beta_g1.serialize_compressed(&mut writer).expect("ser pk.beta_g1");
    pk.delta_g1.serialize_compressed(&mut writer).expect("ser pk.delta_g1");

    serialize_affines_raw(&vk.gamma_abc_g1, &format!("{}_vk_gamma_abc_g1", path_str));
    serialize_affines_raw(&pk.a_query, &format!("{}_pk_a_query", path_str));
    serialize_affines_raw(&pk.b_g1_query, &format!("{}_pk_b_g1_query", path_str));
    serialize_affines_raw(&pk.b_g2_query, &format!("{}_pk_b_g2_query", path_str));
    serialize_affines_raw(&pk.h_query, &format!("{}_pk_h_query", path_str));
    serialize_affines_raw(&pk.l_query, &format!("{}_pk_l_query", path_str));

    // Calculate total size
    let mut total_size = metadata(&meta_path).map(|m| m.len()).unwrap_or(0);
    let prefixes = vec![
        format!("{}_vk_gamma_abc_g1", path_str),
        format!("{}_pk_a_query", path_str),
        format!("{}_pk_b_g1_query", path_str),
        format!("{}_pk_b_g2_query", path_str),
        format!("{}_pk_h_query", path_str),
        format!("{}_pk_l_query", path_str),
    ];
    for prefix in prefixes {
        total_size += metadata(&format!("{}_vx.data", prefix)).map(|m| m.len()).unwrap_or(0);
        total_size += metadata(&format!("{}_vy.data", prefix)).map(|m| m.len()).unwrap_or(0);
        total_size += metadata(&format!("{}_vb.data", prefix)).map(|m| m.len()).unwrap_or(0);
    }
    println!("PERF 1003: [write_g16key_optimized] elements: {}, size: {} bytes", pk.a_query.len(), total_size);

    if b_debug {
        let (pk_read, vk_read) = read_g16_optimized_bn254(path);
        assert_eq!(*pk, pk_read, "ProvingKey mismatch!");
        assert_eq!(*vk, vk_read, "VerifyingKey mismatch!");
        println!("Debug verification passed!");
    }
}

pub fn read_g16_optimized_bn254(path: &Path) -> (ark_groth16::ProvingKey<Bn254>, ark_groth16::VerifyingKey<Bn254>) {
    let path_str = path.to_str().unwrap();

    let meta_path = format!("{}.meta", path_str);
    let file = File::open(&meta_path).expect("open meta err");
    let mut reader = BufReader::new(file);
    
    let vk_alpha_g1 = <ark_ec::short_weierstrass::Affine<ark_bn254::g1::Config>>::deserialize_compressed(&mut reader).expect("deser vk.alpha_g1");
    let vk_beta_g2 = <ark_ec::short_weierstrass::Affine<ark_bn254::g2::Config>>::deserialize_compressed(&mut reader).expect("deser vk.beta_g2");
    let vk_gamma_g2 = <ark_ec::short_weierstrass::Affine<ark_bn254::g2::Config>>::deserialize_compressed(&mut reader).expect("deser vk.gamma_g2");
    let vk_delta_g2 = <ark_ec::short_weierstrass::Affine<ark_bn254::g2::Config>>::deserialize_compressed(&mut reader).expect("deser vk.delta_g2");
    
    let pk_vk_alpha_g1 = <ark_ec::short_weierstrass::Affine<ark_bn254::g1::Config>>::deserialize_compressed(&mut reader).expect("deser pk.vk.alpha_g1");
    let pk_beta_g1 = <ark_ec::short_weierstrass::Affine<ark_bn254::g1::Config>>::deserialize_compressed(&mut reader).expect("deser pk.beta_g1");
    let pk_delta_g1 = <ark_ec::short_weierstrass::Affine<ark_bn254::g1::Config>>::deserialize_compressed(&mut reader).expect("deser pk.delta_g1");

    let vk_gamma_abc_g1 = deserialize_affines_raw(&format!("{}_vk_gamma_abc_g1", path_str));
    let pk_a_query = deserialize_affines_raw(&format!("{}_pk_a_query", path_str));
    let pk_b_g1_query = deserialize_affines_raw(&format!("{}_pk_b_g1_query", path_str));
    let pk_b_g2_query = deserialize_affines_raw(&format!("{}_pk_b_g2_query", path_str));
    let pk_h_query = deserialize_affines_raw(&format!("{}_pk_h_query", path_str));
    let pk_l_query = deserialize_affines_raw(&format!("{}_pk_l_query", path_str));

    let vk = ark_groth16::VerifyingKey {
        alpha_g1: vk_alpha_g1,
        beta_g2: vk_beta_g2,
        gamma_g2: vk_gamma_g2,
        delta_g2: vk_delta_g2,
        gamma_abc_g1: vk_gamma_abc_g1,
    };

    let pk = ark_groth16::ProvingKey {
        vk: vk.clone(), // or we could reconstruct if we strictly read pk.vk, but usually pk.vk == vk. Here we just set it. Wait, the groth16 struct has `vk`. We read `pk_vk_alpha_g1` etc., we can just clone vk but replace alpha_g1 if it differs (it shouldn't). Actually, let's just clone vk.
        beta_g1: pk_beta_g1,
        delta_g1: pk_delta_g1,
        a_query: pk_a_query,
        b_g1_query: pk_b_g1_query,
        b_g2_query: pk_b_g2_query,
        h_query: pk_h_query,
        l_query: pk_l_query,
    };

    // calculate total size
    let mut total_size = metadata(&meta_path).map(|m| m.len()).unwrap_or(0);
    let prefixes = vec![
        format!("{}_vk_gamma_abc_g1", path_str),
        format!("{}_pk_a_query", path_str),
        format!("{}_pk_b_g1_query", path_str),
        format!("{}_pk_b_g2_query", path_str),
        format!("{}_pk_h_query", path_str),
        format!("{}_pk_l_query", path_str),
    ];
    for prefix in prefixes {
        total_size += metadata(&format!("{}_vx.data", prefix)).map(|m| m.len()).unwrap_or(0);
        total_size += metadata(&format!("{}_vy.data", prefix)).map(|m| m.len()).unwrap_or(0);
        total_size += metadata(&format!("{}_vb.data", prefix)).map(|m| m.len()).unwrap_or(0);
    }
    println!("PERF 1003: [read_g16key_optimized] elements: {}, size: {} bytes", pk.a_query.len(), total_size);

    (pk, vk)
}
