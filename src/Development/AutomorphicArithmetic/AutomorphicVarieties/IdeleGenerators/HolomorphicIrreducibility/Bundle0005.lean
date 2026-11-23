module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0002
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Sd

section Hecke

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem isAlgPos_mul {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem isAlgPos_inv {χ : HChar F} {n : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

private theorem alg_mul {ι : Qbar l ≃+* ℂ} {κ κ' : G F Ω →* (Qbar l)ˣ} (h : IsAlgChar ι κ) (h' : IsAlgChar ι κ') :
    IsAlgChar ι (κ * κ') := by
  obtain ⟨hc, art, χ, a, ha, h1, h2⟩ := h
  obtain ⟨hc', art', χ', a', ha', h1', h2'⟩ := h'
  obtain rfl : art = art' := GlobalTheory.ArtinUniq.globalArtin_unique F Ω art art' ha ha'
  exact ⟨hc.mul hc', art, _, _, ha, isAlgPos_mul h1 h1', h2.mul h2'⟩

private theorem alg_fin (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {φ : G F Ω →* (Qbar l)ˣ}
    (ho : IsOpen (φ.ker : Set (G F Ω))) : IsAlgChar ι φ := by
  obtain ⟨art, ha⟩ := H F Ω
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfi : Finite (G F Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, h2⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι φ (continuous_of_isOpen_ker' φ ho) hpos
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact φ.ker.pow_index_mem s)
  exact ⟨continuous_of_isOpen_ker' φ ho, art, χ, 0, ha, isAlgPos_zero_of_orderDvd hpos h1, h2⟩

private theorem alg_cyc (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (j : ℤ) :
    IsAlgChar ι (cycBar F Ω l ^ j) := by
  obtain ⟨hc, χ, art, a, h⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic H F Ω l ι j (cycBar F Ω l ^ j)
    ⟨1, 1, le_rfl, fun _ _ => rfl, (mul_one _).symm⟩
  exact ⟨hc, art, χ, a, h⟩

end Hecke

theorem UpperTheory.V.Sd.algCyc :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.AlgCyc := by
  intro P F Ω _ _ _ _ _ l _ ι
  refine ⟨fun j χ ho => alg_mul (alg_cyc P.litN.aut.art ι j) (alg_fin P.litN.aut.art ι ho),
    fun _ _ h h' => alg_mul h h', ?_⟩
  rintro κ ⟨hc, art, χ, a, ha, h1, h2⟩
  exact ⟨hc.inv, art, _, _, ha, isAlgPos_inv h1, h2.inv⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

private theorem val_of_norm
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [toAdd_pow, WithZero.toAdd_unzero_eq_log, WithZero.toAdd_unzero_eq_log, nsmul_eq_mul, h2]

variable [Algebra K L]

private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem tendsto_under' :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

omit [Algebra K L] in
private theorem ev_notMem (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)

variable (L) in
private noncomputable def cN (χ : HChar K) : HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩

private theorem cN_loc (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion L)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      (cN L χ).loc w x = χ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, congrArg χ.1 h, val_of_norm _ w _ x hm' f hf⟩

private theorem cN_val (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (hχ : χ.UnrAt (w.under (𝓞 K))) : (cN L χ).UnrAt w ∧ (cN L χ).val w = χ.val (w.under (𝓞 K)) ^ f := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := cN_loc χ w f hf x
    rw [hy]
    apply hχ
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := cN_loc χ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hu : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hχ _ hu
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3

private theorem norm_infDiag (k : Lˣ) :
    GroundTheory.Global.ideleNorm K L (infDiag k) = infDiag (Units.map (Algebra.norm K : L →* K) k) := by
  refine Units.ext (Prod.ext (funext fun v => ?_) (Subtype.ext (funext fun v => ?_)))
  · have h1 := GroundTheory.Global.ideleNorm_fst (K := K) (infDiag k) v
    have h2 := GroundTheory.Global.ideleNorm_fst (K := K) (GroundTheory.Global.IdeleGroup.diagonal L k) v
    rw [GroundTheory.Global.ideleNorm_diagonal] at h2
    rw [GlobalTheory.HeckeGal.infDiag_eq] at h1 ⊢
    rw [GlobalTheory.HeckeGal.infDiag_eq]
    exact h1.trans h2.symm
  · have h1 := GroundTheory.Global.ideleNorm_snd (K := K) (infDiag k) v
    rw [GlobalTheory.HeckeGal.infDiag_eq] at h1 ⊢
    rw [GlobalTheory.HeckeGal.infDiag_eq]
    refine h1.trans (Finset.prod_eq_one fun w _ => ?_)
    exact map_one _

open Classical in
private theorem emb_norm (φ : K →+* ℂ) (x : L) :
    φ (Algebra.norm K x) = ∏ ψ ∈ Finset.univ.filter fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ, ψ x := by
  letI := φ.toAlgebra
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have h := Algebra.norm_eq_prod_embeddings K ℂ x
  refine h.trans ?_
  refine Finset.prod_bij (fun σ _ => (σ : L →+* ℂ)) (fun σ _ => ?_) (fun a _ b _ e => AlgHom.coe_ringHom_injective e)
    (fun ψ hψ => ⟨⟨ψ, fun r => DFunLike.congr_fun (Finset.mem_filter.1 hψ).2 r⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, RingHom.ext σ.commutes⟩

private theorem norm_pos (k : Lˣ) (hk : ∀ φ : L →+* ℝ, 0 < φ (k : L)) (φ : K →+* ℝ) : 0 < φ (Algebra.norm K (k : L)) := by
  classical
  have h := emb_norm (Complex.ofRealHom.comp φ) (k : L)
  have h0 : ∀ ψ : L →+* ℂ, ψ (k : L) ≠ 0 := fun ψ => (map_ne_zero ψ).2 k.ne_zero
  have h1 : ∏ ψ ∈ Finset.univ.filter fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = Complex.ofRealHom.comp φ,
      (ψ (k : L) / ((‖ψ (k : L)‖ : ℝ) : ℂ)) = 1 := by
    refine Finset.prod_involution (fun ψ _ => ComplexEmbedding.conjugate ψ) (fun ψ _ => ?_) (fun ψ _ hne e => hne ?_)
      (fun ψ hψ => ?_) fun ψ _ => star_star ψ
    · have : ((‖ψ (k : L)‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0 ψ
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, div_eq_one_iff_eq (mul_ne_zero this this)]
      push_cast; ring
    · have hr : ComplexEmbedding.IsReal ψ := ComplexEmbedding.isReal_iff.2 e
      have := hk hr.embedding
      rw [← ComplexEmbedding.IsReal.coe_embedding_apply hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos this]
      exact div_self (Complex.ofReal_ne_zero.2 this.ne')
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, RingHom.ext fun r => ?_⟩
      have e : ψ (algebraMap K L r) = ((φ r : ℝ) : ℂ) := DFunLike.congr_fun (Finset.mem_filter.1 hψ).2 r
      show ComplexEmbedding.conjugate ψ (algebraMap K L r) = ((φ r : ℝ) : ℂ)
      rw [ComplexEmbedding.conjugate_coe_eq, e, Complex.conj_ofReal]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun ψ _ => by simpa using h0 ψ),
    ← Complex.ofReal_prod] at h1
  have h2 : ((φ (Algebra.norm K (k : L)) : ℝ) : ℂ) = _ := h.trans h1
  rw [Complex.ofReal_inj.1 h2]
  exact Finset.prod_pos fun ψ _ => norm_pos_iff.2 (h0 ψ)

private theorem cN_alg {χ : HChar K} {a : (K →+* ℂ) → ℤ} (h : IsAlgPos χ a) :
    IsAlgPos (cN L χ) fun ψ => a (ψ.comp (algebraMap K L)) := by
  classical
  intro k hk
  have e : (cN L χ).inf k = χ.inf (Units.map (Algebra.norm K : L →* K) k) := congrArg χ.1 (norm_infDiag k)
  rw [e, h _ (norm_pos k hk), ← Finset.prod_fiberwise (s := Finset.univ) (g := fun ψ : L →+* ℂ => ψ.comp (algebraMap K L))]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [Units.coe_map, emb_norm, ← Finset.prod_zpow]
  exact Finset.prod_congr (by convert rfl) fun ψ hψ => by simp only [(Finset.mem_filter.1 hψ).2]

end

theorem UpperTheory.V.Sd.algRes :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.AlgRes := by
  intro P F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι κ ⟨hc, art, χ, a, ha, h1, h⟩
  obtain ⟨art', ha'⟩ := P.litN.aut.art E Ω
  have h1' := cN_alg (L := E) h1
  obtain ⟨μ, hμ, hL⟩ := ha'.exists_isLAdicOf ι h1'
  have hc' : Continuous (κ.comp (galEmb F E Ω)) := hc.comp (continuous_restrictScalarsHom F E Ω)
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ (cN E χ).UnrAt w ∧
      CharEig ι (κ.comp (res F Ω E)) w ((cN E χ).val w : ℂˣ) := by
    filter_upwards [(tendsto_under' (K := F) (L := E)).eventually
      ((Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)).and (ev_notMem l)), ev_notMem (K := E) l]
      with w ⟨hu, hl⟩ hl'
    have hf := normV_under (K := F) w
    obtain ⟨k1, k2⟩ := cN_val χ w _ hf hu
    refine ⟨hl', k1, ?_⟩
    rw [k2, Units.val_pow_eq_pow_val]
    refine (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 κ _ fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => κ.comp (galEmb F E Ω) s) (f' := fun s => μ s)
    hc' hμ fun v hv _ A hA σ hσ => by
      obtain ⟨hl, hu, hE⟩ := not_not.1 hv
      have e := (hE A hA).2 σ hσ
      refine Units.ext ?_
      rw [hL.frob_unr ha' (Or.inl hl) hu hA hσ, ← e, ι.symm_apply_apply, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      rfl
  have e : κ.comp (galEmb F E Ω) = μ := MonoidHom.ext fun s => congrFun key s
  rw [e]
  exact ⟨hμ, art', _, _, ha', h1', hL⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DirOf
section
open UpperTheory.V in
theorem UpperTheory.V.Sd.dirOf :
    UpperTheory.V.Sd.DirOf := by
  intro l _ Ω _ _ _ ι N hN φ hφ
  have : NeZero N := ⟨hN.ne'⟩
  have hs := (Chr.clsOnto Ω N).1
  have hk : (Chr.cls ℚ Ω N).ker ≤ φ.ker := fun s h => by
    have h1 : Chr.cls ℚ Ω N s = 1 := h
    refine hφ s fun ζ hζ => ?_
    rw [Chr.cls_spec N s ζ hζ, h1, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  let f := MonoidHom.liftOfRightInverse (Chr.cls ℚ Ω N) (Function.surjInv hs)
    (Function.rightInverse_surjInv hs) ⟨φ, hk⟩
  have hf : ∀ s, f (Chr.cls ℚ Ω N s) = φ s := fun s =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hk⟩ s
  let χ₀ : DirichletCharacter ℂ N := MulChar.ofUnitHom ((Units.map ι.toRingHom.toMonoidHom).comp f)
  have hd : χ₀.conductor ∣ N := χ₀.conductor_dvd_level
  have hM : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  refine ⟨χ₀.conductor, hM, χ₀.primitiveCharacter, hd, χ₀.primitiveCharacter_isPrimitive, ?_⟩
  ext s
  have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 _ hd) s
  have h2 : χ₀.primitiveCharacter (ZMod.unitsMap hd (Chr.cls ℚ Ω N s)) = χ₀ (Chr.cls ℚ Ω N s) := by
    conv_rhs => rw [← χ₀.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    simp [ZMod.unitsMap_def]
  have h3 : χ₀ (Chr.cls ℚ Ω N s) = ι (φ s) := by
    rw [← hf]
    simp [χ₀]
  rw [Chr.dirG, MonoidHom.comp_apply, ← h1, MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, MonoidHom.comp_apply, h2, h3]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisReg
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd

private theorem eisReg_place {Ω : Type} [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  let R : Subring Ω := (Int.castRingHom Ω).range
  have hI : Ideal.span {((p : ℕ) : R)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨_, k, rfl⟩, hk⟩
    have h1 : ((p : ℕ) : Ω) * ((k : ℤ) : Ω) = 1 := congrArg Subtype.val hk
    have h2 : ((p : ℕ) : ℤ) * k = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
    exact hp.one_lt.ne' (by exact_mod_cast h3)
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : R), Ideal.mem_span_singleton_self _, by simp⟩)⟩

private theorem eisReg_charpoly {K : Type} [Field K] (g r : GL (Fin 2) K) (a b : K)
    (h : ∀ i j, j < i → (g * r * g⁻¹ : GL (Fin 2) K) i j = 0)
    (ha : (g * r * g⁻¹ : GL (Fin 2) K) 0 0 = a) (hb : (g * r * g⁻¹ : GL (Fin 2) K) 1 1 = b) :
    (r : Matrix (Fin 2) (Fin 2) K).charpoly = (X - C a) * (X - C b) := by
  have e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj g _
  rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two, ← ha, ← hb]

theorem UpperTheory.V.Sd.eisReg :
    UpperTheory.V.Sd.EisReg := by
  intro l hl Ω _ _ _ ι φ θ k hk ρ hρ H hH
  obtain ⟨A, hA⟩ := eisReg_place (Ω := Ω) l hl.out
  obtain ⟨κ, ⟨g, hg⟩, hκ, -⟩ := hρ.above A hA
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
  haveI : IsGalois ℚ Ω := {}
  haveI : Finite (G ℚ Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨n, hn, -, hnH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := H) Subgroup.FiniteIndex.index_ne_zero σ
  have hs : σ ^ n ∈ Ine (F := ℚ) A := pow_mem hσ n
  let s : ↥(Dec (F := ℚ) A) := ⟨σ ^ n, Ine_le_Dec A hs⟩
  refine ⟨σ ^ n, hnH, cycBar ℚ Ω l (σ ^ n) ^ ((k : ℤ) - 1), ?_, ?_⟩
  · rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨m, hm, h⟩
    have hinj : Function.Injective
        (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
      Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
    refine hu ((n : ℤ) * ((k : ℤ) - 1) * m) ?_ (hinj ?_)
    · have : (0 : ℤ) < (k : ℤ) - 1 := by omega
      positivity
    · rw [map_one, ← h, cycBar, MonoidHom.comp_apply, map_pow, hσu, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast,
        map_pow, map_zpow]
  · refine eisReg_charpoly g (ρ (σ ^ n)) _ _ (hg s).1 ?_ ?_
    · rw [show ρ (σ ^ n) = ρ s from rfl, (hg s).2 0, hκ 0 s hs]; rfl
    · rw [show ρ (σ ^ n) = ρ s from rfl, (hg s).2 1, hκ 1 s hs]; simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IrrAb
section
open Matrix Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.U3

theorem UpperTheory.V.Sd.irrAb :
    UpperTheory.V.Sd.IrrAb := by
  intro l _ Γ _ _ _ n r hr hio H H' hH hle hab
  have h0 := hio H hH
  have hne : (⊤ : Submodule (Formalism.ConjugateSelfDual.Qbar l) (Fin n → Formalism.ConjugateSelfDual.Qbar l)) ≠ ⊥ := h0.1
  haveI : Nontrivial (Fin n → Formalism.ConjugateSelfDual.Qbar l) := Submodule.nontrivial_iff (Formalism.ConjugateSelfDual.Qbar l) |>.mp ⟨_, _, hne⟩
  have hn : n ≠ 0 := by
    rintro rfl
    exact hne (Subsingleton.elim _ _)
  refine ⟨hne, fun _ _ _ => trivial, fun W _ hW => ?_⟩
  by_contra hcon
  have hab' : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ H'.subgroupOf H := fun a b =>
    Subgroup.mem_subgroupOf.mpr (hab a a.2 b b.2)
  haveI : (H'.subgroupOf H).Normal := ⟨fun x hx g => by
    have := (H'.subgroupOf H).mul_mem (hab' g x) hx
    simpa using this⟩
  obtain ⟨φ, hφ1, -, hφn, M, hM⟩ := exists_selfTwist (r.comp H.subtype) (H'.subgroupOf H) hab'
    (fun U hU => h0.2.2 U le_top fun g v hv => hU g trivial v hv)
    (fun h => hcon (h W fun g hg v hv => hW ⟨g, Subgroup.mem_subgroupOf.mp hg⟩ v hv))
  have hM' : ∀ g : H, ((φ g : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) • ((M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M := fun g => by
    have := hM g trivial
    rw [Matrix.mul_smul] at this
    exact this
  have hiff : ∀ g : H, φ g = 1 ↔ (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M := fun g => by
    constructor
    · intro h
      have := hM' g
      rwa [h, Units.val_one, one_smul] at this
    · intro h
      have h1 := hM' g
      rw [← h] at h1
      haveI : NeZero n := ⟨hn⟩
      have h2 : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) ≠ 0 :=
        (M * r g).ne_zero
      exact Units.ext (smul_left_injective _ h2 (h1.trans (one_smul _ _).symm))
  have hcl : IsClosed (φ.ker : Set H) := by
    have hc : Continuous fun g : H => (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) :=
      Units.continuous_val.comp (hr.comp continuous_subtype_val)
    have : (φ.ker : Set H) = {g : H | (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M} := Set.ext fun g => hiff g
    rw [this]
    exact isClosed_eq (continuous_const.mul hc) (hc.mul continuous_const)
  haveI : NeZero n := ⟨hn⟩
  have hrg : φ.range ≤ rootsOfUnity n (Formalism.ConjugateSelfDual.Qbar l) := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact DFunLike.congr_fun hφn g
  haveI : Finite φ.range := Finite.of_injective _ (Subgroup.inclusion_injective hrg)
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  have hop : IsOpen (φ.ker : Set H) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  have hop' : IsOpen ((φ.ker.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hop
  have h1 := hio _ hop'
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)))
  have htop := (h1.2.2 (Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a) le_top (by
    rintro ⟨_, g, hg, rfl⟩ v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    change (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v) =
      a • ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, (hiff g).mp hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul])).resolve_left ha
  have hMa : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = a • 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have : v ∈ Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a := by
      rw [htop]; trivial
    rw [Module.End.mem_eigenspace_iff] at this
    rw [this]; simp
  apply hφ1
  ext1 g
  exact (hiff g).mpr (by rw [hMa]; simp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IsAlgOfPos
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem isAlg_of_pos {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {κ : HChar K}
    {m : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ m) : κ.IsAlg m := fun k => hκ k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem UpperTheory.V.Sd.twC :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.TwC := by
  intro _ F Ω _ _ _ _ _ _ l _ ι n r κ ⟨_, art, χ, a, hart, hpos, hL⟩ ⟨π, hreg, hatt⟩
  exact ⟨π.twist χ, regAlg_twist hreg (isAlg_of_pos hpos),
    UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hatt art χ a κ hart hL⟩
end

