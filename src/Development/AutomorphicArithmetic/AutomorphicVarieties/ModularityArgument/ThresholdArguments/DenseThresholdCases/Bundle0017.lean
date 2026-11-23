module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

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
theorem UpperTheory.V.Sd.alg_cyclotomic_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.AlgCyc := by
  intro P F Ω _ _ _ _ _ l _ ι
  refine ⟨fun j χ ho => alg_mul (alg_cyc P.litN.aut.art ι j) (alg_fin P.litN.aut.art ι ho),
    fun _ _ h h' => alg_mul h h', ?_⟩
  rintro κ ⟨hc, art, χ, a, ha, h1, h2⟩
  exact ⟨hc.inv, art, _, _, ha, isAlgPos_inv h1, h2.inv⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgRes
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

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
  rw [toAdd_pow, nsmul_eq_mul, WithZero.toAdd_unzero_eq_log hy,
    WithZero.toAdd_unzero_eq_log hx, h2]
variable [Algebra K L]
private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Ideal.absNorm_eq_natCard]
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
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
theorem UpperTheory.V.Sd.alg_restriction_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.AlgRes := by
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
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TEpsAway
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.Ga
private theorem cyc_eq_of_pow {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal)
    (h : IsPlaceOver A w) {σ : G L Ω} {q : ℕ}
    (hσ : ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) :
    (cycBar L Ω l σ : Qbar l) = (q : Qbar l) := by
  have h1 : ((cycZ L Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hσ)
  simp [cycBar, h1]
end UpperTheory.V.Z.Sym.Ga
theorem UpperTheory.V.Z.Sym.Ga.cyc_char_eq_abs_pow_and_norm_pow_deg_away_l :
    _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ s : Weil h, ι (Ga.ep l (s : G L Ω)) = (absPow (w.adicCompletion L) 1 (a s) : ℂ) ∧ ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
  intro _ L Ω _ _ _ _ _ l _ ι w hl A h a ha s
  have hfrob : (cycBar L Ω l ((frob h : Weil h) : G L Ω) : Qbar l) = ((normV w : ℕ) : Qbar l) :=
    Ga.cyc_eq_of_pow hl h (isFrob_frob (h := h)).2
  set t : Weil h := s * (frob h) ^ (-deg s) with ht
  have hdt : deg t = 0 := by
    rw [ht, deg_mul, deg_zpow, deg_frob]
    ring
  have hI : (t : G L Ω) ∈ Ine (F := L) A :=
    actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hdt))
  have hine : (cycBar L Ω l (t : G L Ω) : Qbar l) = 1 := by
    have := Ga.cyc_eq_of_pow (σ := (t : G L Ω)) (q := 1) hl h (fun x hx => by simpa using hI.2 x hx)
    simpa using this
  have hs : s = t * (frob h) ^ (deg s) := by
    rw [ht, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hε : Ga.ep l (s : G L Ω) = ((normV w : ℕ) : Qbar l) ^ deg s := by
    show (cycBar L Ω l (s : G L Ω) : Qbar l) = _
    conv_lhs => rw [hs]
    rw [Subgroup.coe_mul, map_mul, Units.val_mul, hine, one_mul, Subgroup.coe_zpow, map_zpow,
      Units.val_zpow_eq_zpow_val, hfrob]
  have hq : ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
    rw [hε, map_zpow₀, map_natCast]
  refine ⟨?_, hq⟩
  have := DFunLike.congr_fun (ha.absPow_comp 1) s
  rw [Complex.ofReal_one] at this
  rw [hq, ← MonoidHom.comp_apply, this, GlobalTheory.WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val]
  simp
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGlobFixed
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Filter Topology Matrix
namespace UpperTheory.V.Af.GlobalFixedVectors
variable {F : Type} [Field F] [NumberField F] {n M : ℕ}
end UpperTheory.V.Af.GlobalFixedVectors
open UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors in
theorem UpperTheory.V.Af.globFixed_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.GlobFixed := by
  classical
  intro _ F _ _ n M _ V _ _ ρ hρ h
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), HasFixed ρ (KAway n M S) → HasFixed ρ (KAway n M ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      rintro ⟨v, hv0, hv⟩
      obtain ⟨σ, ⟨-, hσ⟩, hfix⟩ := h w
      let W : Submodule ℂ V := ⨅ k : KAway n M (insert w S), LinearMap.ker (ρ k - 1)
      have hWm : ∀ x, x ∈ W ↔ ∀ k ∈ KAway n M (insert w S), ρ k x = x := fun x => by
        simp [W, Submodule.mem_iInf, sub_eq_zero]
      obtain ⟨x, hxW, hx0, hx⟩ := sub_fixed σ.ρ σ.irred (ρ.comp (locGL F n w)) hσ W (fun g x hx => (hWm _).2 fun k hk => by
        have e : k * locGL F n w g = locGL F n w g * k := gl_ext fun u => by
          by_cases hu : u = w
          · subst hu; simp [(mem_KAway.1 hk).2 u (Finset.mem_insert_self _ _)]
          · simp [pLoc_locGL_of_ne hu]
        change ρ k (ρ (locGL F n w g) x) = ρ (locGL F n w g) x
        rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hWm x).1 hx k hk])
        (fun e => hv0 (by simpa [e] using (hWm v).2 hv)) _ hfix
      refine ih ⟨x, hx0, fun k hk => ?_⟩
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway n M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : ρ (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) x = x := hx _ h1
      have h4 := (hWm x).1 hxW _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨σ, ⟨hV, -⟩, -⟩ := h w
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) ((hρ v).mem_nhds (by simp))
  obtain ⟨x, hx0, hx⟩ := key S ⟨v, hv, fun k hk => hS hk⟩
  exact ⟨x, hx0, fun k hk => hx k (mem_KAway.2 ⟨hk, by simp⟩)⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TIsoOfFrob
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
theorem UpperTheory.V.Af.iso_of_frobenius_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.IsoOfFrob := by
  intro _ F Ω _ _ _ _ _ l _ ι n r r' hr hr' hs hs' hw
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix
section
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
private theorem iso_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    T x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩
private theorem iso_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ρ g x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap (ρ g) _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, f.2 g v⟩
end
theorem UpperTheory.V.Af.local_comp_complex_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.LocCompC := by
  intro P E _ _ _ a π w
  refine ⟨(LocEx.exists_isLocComp P.litN.aut.fin E a π w).imp fun _ h => h.1, fun σ hσ => ?_⟩
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  obtain ⟨f, h0, hf⟩ := hσ
  change ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ (o : Op E a) (x : π.V),
      x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) →
      π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 := by
    intro o x hx
    cases o with
    | fin k =>
      have h1 := iso_act σ.ρ (π.locRep w) (GeneralLinearGroup.map (pLoc E w) k) (iso_comm σ.ρ (π.locRep w)
        (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx)
      have e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k)
          (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
        (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1
  rcases π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h1 | h1
  · have h2 := hi (h1.trans (Submodule.map_bot _).symm)
    exact absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)
end
end

