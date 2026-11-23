module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.TorsionFreeOfField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlAllOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPKapEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
namespace KapEx
end KapEx
open UpperTheory.V.Cu2.KapEx in
theorem kapEx_alt (h1 : TwistIne) (h2 : AlgType) : _root_.UpperTheory.V.Cu2.KapExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK2 hTC hld hsp hcc
  obtain ⟨cc, hcc⟩ := hcc
  have : IsTotallyComplex K' := hTC
  have : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  have : CompactSpace (G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  obtain ⟨κ₀, htw⟩ := _root_.UpperTheory.V.Sd.twist_of_printed_results hP K' Ω hK2 l hl2 hld ι cc hcc
  obtain ⟨art, Y, a, τ, hart, hYa, hL, ha1, ha0, -⟩ := htw.alg
  obtain ⟨mo, hmo0, -, hmo⟩ := htw.ord
  have hi : (galOf ℚ K' Ω).index = 2 := (galEmbTop ℚ K' Ω).2.2.trans hK2
  have hccK : cc ∉ galOf ℚ K' Ω := cc_notMem K' hcc
  have hfix : ∀ t : G ℚ Ω, t ∈ K'.fixingSubgroup → t ∈ galOf ℚ K' Ω := fun t h =>
    (mem_galOf ℚ K' Ω).2 fun x => (IntermediateField.mem_fixingSubgroup_iff K' t).1 h x x.2
  have hIne : ∀ (A : ValuationSubring Ω) (h : G K' Ω), resQ K' h ∈ Ine (F := ℚ) A → h ∈ Ine (F := K') A :=
    fun A h hh => ⟨hh.1, hh.2⟩
  have hεc : Continuous (cycBar K' Ω l) := by
    have hf : Continuous (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom : ℤ_[l] → Qbar l) :=
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
    exact (Units.continuous_map hf).comp (continuous_cycZ K' Ω l)
  have hεunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ h ∈ Ine (F := K') A, cycBar K' Ω l h = 1 := by
    intro A hA h hh
    have e : cycZ K' Ω l h = 1 := MonoidHom.mem_ker.1 (((places K' Ω l A).2.2.2 hA) hh)
    simp only [cycBar, MonoidHom.comp_apply, e, map_one]
  have hεres : ∀ h : G K' Ω, cycBar K' Ω l h = cycBar ℚ Ω l (resQ K' h) := fun h => rfl
  have hlam : ∀ h : G K' Ω, (κ₀ ^ 2 * cycBar K' Ω l) h = κ₀ h ^ 2 * cycBar K' Ω l h := fun h => by
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply]
  have hlamc : Continuous ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) := by
    have e : ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) = fun h => κ₀ h ^ 2 * cycBar K' Ω l h := funext hlam
    rw [e]
    exact (htw.cont.pow 2).mul hεc
  obtain ⟨d, hd0, hd⟩ := exists_pow_cong _ hlamc
  refine ⟨d * mo, (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo), fun j hj => ?_⟩
  rw [← pow_mul]
  have hN : 0 < d * mo * j := Nat.mul_pos (Nat.mul_pos hd0 hmo0) (by omega)
  obtain ⟨Y', hY', hL'⟩ := h2 K' Ω l ι art Y a κ₀ hart hYa hL (2 * (d * mo * j)) (d * mo * j)
  have hpw : (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) =
      κ₀ ^ (2 * (d * mo * j)) * cycBar K' Ω l ^ (d * mo * j) := by
    rw [mul_pow, ← pow_mul]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ⇑((κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) : G K' Ω →* (Qbar l)ˣ) = fun h => (κ₀ h ^ 2 * cycBar K' Ω l h) ^ (d * mo * j) :=
      funext fun h => by rw [MonoidHom.pow_apply, hlam]
    rw [e]
    exact ((htw.cont.pow 2).mul hεc).pow _
  · refine ⟨art, Y', _, τ, hart, hY', by rw [hpw]; exact hL', ?_, ?_⟩
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a τ + ((d * mo * j : ℕ) : ℤ) = -((d * mo * j : ℕ) : ℤ)
      rw [ha1]
      push_cast
      ring
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a (ComplexEmbedding.conjugate τ) + ((d * mo * j : ℕ) : ℤ) = ((d * mo * j : ℕ) : ℤ)
      rw [ha0]
      push_cast
      ring
  · intro t ht h h' hh'
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have hu : cc⁻¹ * t ∈ galOf ℚ K' Ω := by
      rw [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff]
      exact iff_of_false hccK htg
    rw [← range_galEmb] at hu
    obtain ⟨v, hv⟩ := hu
    have hh'' : galEmb ℚ K' Ω h' = t * galEmb ℚ K' Ω h * t⁻¹ := hh'
    have hs : galEmb ℚ K' Ω h' = cc * galEmb ℚ K' Ω (v * h * v⁻¹) * cc⁻¹ := by
      rw [map_mul, map_mul, map_inv, hv, hh'']
      group
    have hc := htw.conj (v * h * v⁻¹) h' hs
    simp only [map_mul, map_inv, mul_inv_cancel_comm] at hc
    have hε' : cycBar K' Ω l h' = cycBar K' Ω l h := by
      rw [hεres, hεres h, hh', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, ← mul_pow, hlam, hlam, hε', mul_mul_mul_comm, ← mul_pow, hc,
      ← sq (cycBar K' Ω l h), inv_pow, inv_mul_cancel, one_pow]
  · intro t ht h hh
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have e1 := htw.ver h t htg hh
    have e2 : cycBar K' Ω l h = cycBar ℚ Ω l t * cycBar ℚ Ω l t := by
      rw [hεres, hh, map_mul]
    rw [MonoidHom.pow_apply, hlam, e1, e2, neg_sq, inv_pow, ← sq (cycBar ℚ Ω l t), inv_mul_cancel, one_pow]
  · intro h
    apply cong_of_mem
    rw [MonoidHom.pow_apply, pow_mul, pow_mul]
    exact pow_mem (pow_mem (hd h) mo) j
  · intro A hA h hh
    have h' := hIne A h hh
    rw [MonoidHom.pow_apply, hlam, hεunr A hA h h', mul_one, ← pow_mul,
      show 2 * (d * mo * j) = mo * (2 * d * j) by ring, pow_mul, hmo A hA h h', one_pow]
  · intro A hA
    rcases h1 Ω l ι K' hK2 hTC hld hsp cc κ₀ htw A hA with e | e
    · refine Or.inr fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), zpow_neg, zpow_natCast, sq, mul_assoc, inv_mul_cancel, mul_one,
        inv_pow]
    · refine Or.inl fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), one_pow, one_mul, zpow_natCast]
end UpperTheory.V.Cu2
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemOfNormVDvd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open UpperTheory.V UpperTheory.V.Af
open scoped Matrix
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform
local instance (priority := high + 1)  (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] :
    Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
private theorem cofinite_notMem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw
private theorem mem_of_normV_dvd {N : ℕ} {w : HeightOneSpectrum (𝓞 ℚ)} (h : normV w ∣ N) :
    ((N : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  obtain ⟨c, rfl⟩ := h
  have e : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [Nat.cast_mul, e]
  exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
private theorem charpoly_scale {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (B : Multiset ℂ)
    (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by linear_combination e0
  have ht : φ M.trace = x + y := by linear_combination e0 - e1
  simp only [hd, ht, C_add, C_mul]
  ring
private theorem scale_sat {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (B : Multiset ℂˣ) (q : ℕ)
    (u : ℂˣ) (hu : φ c = u) (P Q : ℂ[X]) (h : M.charpoly.map φ = P)
    (hP : ((algSat 2 q B).map fun b => X - C ((q : ℂ) ^ (0 : ℤ) * b)).prod = P)
    (hQ : ((algSat 2 q (B.map (· * u))).map fun b => X - C ((q : ℂ) ^ (0 : ℤ) * b)).prod = Q) :
    (c • M).charpoly.map φ = Q := by
  simp only [zpow_zero, one_mul] at hP hQ
  rw [charpoly_scale φ M c (algSat 2 q B) (h.trans hP.symm), ← hQ, hu]
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply, Units.val_mul]
  ring_nf
private theorem ss_twist {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).1 hW)
  exact ⟨W', (key W').2 hW', hc⟩
private theorem isOpen_ker {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] {N : ℕ} (hN : 1 ≤ N)
    {κ : G ℚ Ω →* C} (hκ : KillsMu N κ) : IsOpen (κ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ N = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hN] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hκ s fun ζ hζ => hs ζ hζ
theorem exists_newform_attached_twist_of_kills_mu (P : _root_.UpperTheory.V.Af.HypothesesH') {k : ℕ} (hk : 2 ≤ k) (f : Newform k) {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hf : f.Att ι V)
    (κ : G ℚ Ω →* (Qbar l)ˣ) {N : ℕ} (hN : 1 ≤ N) (hκ : KillsMu N κ) :
    ∃ g : Newform k, g.Att ι (tw V κ) := by
  obtain ⟨art, ha⟩ : ∃ art : Neutral.B1.Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art := P.toClassicalTheorems.litN.aut.art _ Ω
  have ho := isOpen_ker hN hκ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfi : Finite (G ℚ Ω ⧸ κ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hm : 0 < κ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι κ (continuous_of_isOpen_ker' κ ho) hm
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact κ.ker.pow_index_mem s)
  have hexpo : ∀ v, TR.expo χ v = 0 := GlobalTheory.HenQ.expo_eq_zero_of_pow χ hm h1
  obtain ⟨π, hinf, hsat⟩ := P.toClassicalTheorems.newform k hk f 0
  obtain ⟨g, hg⟩ := UpperTheory.V.Af.repNewform k hk 0 (π.twist χ) fun v => by
    have := (hinf v).twist χ
    rw [hexpo v] at this
    simpa using this
  refine ⟨g, ss_twist _ _ hf.1, ?_⟩
  filter_upwards [hf.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ), cofinite_notMem l hl.out.ne_zero,
    cofinite_notMem f.M f.pos.ne', cofinite_notMem g.M g.pos.ne'] with w hw hu hwl hwf hwg A hA
  obtain ⟨B, hB, hpB⟩ := hsat w fun h => hwf (mem_of_normV_dvd h)
  obtain ⟨S, hS, hpS⟩ := hg w fun h => hwg (mem_of_normV_dvd h)
  obtain rfl : S = B.map (· * χ.val w) := hS.unique (hB.twist hu)
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have e1 : κ s = 1 := (hL.unr_iff ha (Or.inl hwl) hA).2 hu s hs
    apply Units.ext
    rw [tw_val, e1, (hw A hA).1 s hs, Units.val_one, one_smul, Units.val_one]
  · have e1 : ι.toRingHom ((κ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (χ.val w : ℂ) := by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inl hwl) hu hA hσ, inv_inv]
      exact ι.apply_symm_apply _
    rw [tw_val]
    exact scale_sat ι.toRingHom _ _ B _ _ e1 _ _ ((hw A hA).2 σ hσ) hpB hpS
end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform
open UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twNew_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → GlobalTheory.Ord2.TwNewQ := by
  intro P l _ Ω _ _ _ ι e W _ he hA M φ hM hφ
  obtain ⟨f, M', φ', hM', hφ', hf⟩ := hA.modular
  have hMM : 1 ≤ M * M' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hκ : KillsMu (M * M') (φ * φ'⁻¹) := fun s hs => by
    have h1 : φ s = 1 := hφ s fun ζ hζ => hs ζ (by rw [pow_mul, hζ, one_pow])
    have h2 : φ' s = 1 := hφ' s fun ζ hζ => hs ζ (by rw [mul_comm, pow_mul, hζ, one_pow])
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, inv_one, one_mul]
  obtain ⟨g, hg⟩ := _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform.exists_newform_attached_twist_of_kills_mu P (by omega) f ι _ hf (φ * φ'⁻¹) hMM hκ
  refine ⟨g, ?_⟩
  convert hg using 1
  ext1 s
  apply Units.ext
  simp only [tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, ← Units.val_mul]
  congr 2
  rw [mul_comm (φ s) (φ' s)⁻¹, mul_assoc, ← mul_assoc (φ s), mul_comm _ (φ' s), inv_mul_cancel_left, mul_comm]
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumJ
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
  (lam : Wt L l n) (K : H.Lev) (P : (H.Gq →* GL (Fin n) (Qbar l)) → Prop)
end
def NumJAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : W.UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev) (J : Ideal B.B), r.V0ok → IsDomain Λ.Λ → R.IsJ B K J → J.IsRadical →
    UpperTheory.V.J.Num B Λ J
end UpperTheory.V.Z.J.D
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointRepresentationWeights
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.Pt.point_representation_weights :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : W.Resid V.frame c.O n) (B : W.UniversalOrdinaryDeterminantRing r) (ι : PadicAlgCl l ≃+* ℂ) (J : Ideal B.B), B.PointTheoremBaseObject ι J → ∀ (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)) (m : W.Vl l L → Fin n → ℤ), 2 ≤ n → n ≤ 4 → x.IsRep ρ → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) → (∀ v i j, i < j → m v j + 2 ≤ m v i) → (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) → (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) → J ≤ RingHom.ker x := by
  intro hP l _ L Ω _ _ _ _ _ _ s V c n r B ι J hJ x ρ m hn2 hn4 hrep hc haut hv0 hm hfl ⟨k, hk, hw⟩
  have hov : ∀ v : W.Vl l L, (s.A v).valuation (l : Ω) < 1 := fun v => by
    simpa using (s.hA v _).2 v.2
  have hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    refine (s.hw v _).1 ?_
    simpa using hov v
  refine hJ x (fun v j _ => -m v j) ρ hn2 hn4 ⟨fun v τ i j hij => ?_, fun v j => ?_⟩
    hrep hc haut hv0
    fun v => ⟨hfl v, fun i j hij => ?_⟩
  · have := hm v i j hij
    simp only
    omega
  · exact UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (psi_cont x v j) (m v j) k hk (hw v j)
  · have hne : 1 - m v i + m v j ≠ 0 := by
      rcases lt_trichotomy i j with h | h | h
      · have := hm v i j h
        omega
      · subst h
        omega
      · have := hm v j i h
        omega
    obtain ⟨g, hg, hg1⟩ := cycIne L Ω l (s.A v) (hov v) ((1 - m v i + m v j) * k)
      (mul_ne_zero hne (by exact_mod_cast hk.ne'))
    have hgD : g ∈ Dec (F := L) (s.A v) :=
      (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2
    have h1 := hw v i ⟨g, hgD⟩ hg
    have h2 := hw v j ⟨g, hgD⟩ hg
    have e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g := by
      rw [hij]; rfl
    apply hg1
    have e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) =
        (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j) := by
      rw [e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]
      congr 2
      ring
    change (x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1
    change (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2
    rw [e2, mul_pow, h2, one_mul] at h1
    rw [zpow_mul, zpow_natCast, h1]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SafeUP
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
namespace UpperTheory.V.Z.Win.A4
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
end
theorem safeUP'_alt (_P : _root_.UpperTheory.V.Af.Hypotheses') {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n M : ℕ}
    {m : Fin n → ℤ} {ι : Qbar l ≃+* ℂ} {r : G ℚ Ω →* GL (Fin n) (Qbar l)} (hi : IsIrr r) (hl : Level l M m r) (ha : IsAutQA ι r)
    (h : SafeRA l M m r) : SafePA l M m r :=
  h.imp_left fun ⟨h1, h2⟩ => ⟨h1, potQ flagLaws splitIrr Ω l ι n r hl.cont hi ha h2⟩
end UpperTheory.V.Z.Win.A4
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatK
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Af.satake_k_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.SatK := by
  intro P K _ _ _ n M π hπ w hw
  obtain ⟨⟨σ, hσ⟩, h⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
  exact sat_of_isotypic (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart hπ w hw σ (h σ hσ)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatakeGaloisCompatibilityOfHeckeEigensystem
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
theorem UpperTheory.satake_galois_link_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → SatLink := by
  intro PH E _ _ _ a π
  have P := PH.toClassicalTheorems
  refine ⟨fun w σ hσ B => (_root_.UpperTheory.V.Af.satake_local_of_printed_results P E a w σ).2 _ π.finPart ((_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w
    ⟨σ, hi σ hσ⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCardK
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
private theorem klev_three (K : Type) [Field K] [NumberField K] (n M : ℕ) :
    UpperTheory.V.Af.KLev K n (3 * M) ≤ UpperTheory.V.Af.KLev K n M := by
  refine Subgroup.map_mono fun k hk => ?_
  have hle : Ideal.span {((3 * M : ℕ) : ↥(UpperTheory.V.Af.Ohat K))} ≤ Ideal.span {(M : ↥(UpperTheory.V.Af.Ohat K))} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (Dvd.intro_left 3 rfl))
  have e := congrArg (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.factor hle)) (MonoidHom.mem_ker.1 hk)
  rw [map_one] at e
  exact e
theorem UpperTheory.V.Af.card_k_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.CardK := by
  intro P K _ _ _ n hn
  obtain ⟨c₁, A₁, hW⟩ := _root_.UpperTheory.V.Af.weyl_complex_of_printed_results P K n
  obtain ⟨c₂, A₂, hC⟩ := UpperTheory.V.Af.cohBoundFree K (Or.inl inferInstance) n ⊤ inferInstance
  refine ⟨c₂ * c₁, A₁ + A₂, fun m hm H hH M hM S hS hiso => ?_⟩
  obtain ⟨Ξ, hΞ, hd⟩ := hW m hm H hH
  have h3 : 1 ≤ 3 * M := by omega
  have hB := P.borelC K n (by omega) (UpperTheory.V.Af.KLev K n (3 * M)) (by apply UpperTheory.V.Af.isOpen_KLev; exact h3)
    (by apply UpperTheory.V.Af.isCompact_KLev; exact h3) Ξ S hiso fun π hπ =>
      ⟨P.cohC K n (by omega) π Ξ fun τ => ⟨_, (hS π hπ).1 τ, hΞ τ⟩,
        (hS π hπ).2.2.imp fun _ hv => ⟨hv.1, fun u hu => hv.2 u (klev_three K n M hu)⟩⟩
  have h1 : S.card ≤ c₂ * M ^ A₂ * Ξ.d := Nat.cast_le.1 (hB.trans (hC M hM _ _))
  have h2 : M ^ A₂ ≤ M ^ (A₁ + A₂) := Nat.pow_le_pow_right hM (by omega)
  have h4 : (H + 1) ^ A₁ ≤ (H + 1) ^ (A₁ + A₂) := Nat.pow_le_pow_right (by omega) (by omega)
  calc S.card ≤ c₂ * M ^ A₂ * Ξ.d := h1
    _ ≤ c₂ * M ^ (A₁ + A₂) * (c₁ * (H + 1) ^ (A₁ + A₂)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) (hd.trans (Nat.mul_le_mul_left _ h4))
    _ = c₂ * c₁ * (M * (H + 1)) ^ (A₁ + A₂) := by rw [mul_pow]; ring
end
end

