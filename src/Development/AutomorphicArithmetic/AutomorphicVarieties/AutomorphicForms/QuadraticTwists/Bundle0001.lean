module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
public import GroundTheory.GlobalFields.LocalAtPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem sat_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (P : CuspSub K n)
    {w : HeightOneSpectrum (𝓞 K)} {B : Multiset ℂˣ} (h : (CG.mk P).HasSat w B) {κ : HChar K} (hκ : κ.UnrAt w) :
    (CG.mk (P.twist κ)).HasSat w (B.map (· * κ.val w)) := by
  rw [CG.hasSat_mk] at h ⊢
  exact GlobalTheory.SphGal.hasSatGL_twist K n P κ w B hκ h

theorem UpperTheory.V.Af.Cq.attTwist :
    ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
        (R : G K Ω →* GL (Fin n) (Qbar l)) (P : CuspSub K n), AttC ι R P → ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ)
        (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → IsLAdicOf art ι κ m μ → AttC ι (tw R μ) (P.twist κ) := by
  intro K Ω _ _ _ _ _ _ l _ ι n R P hA art κ m μ ha h
  refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n R).2.2 μ hA.1, ?_⟩
  filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified κ), ev_notMem (K := K) l]
    with w ⟨B, hB, hE⟩ hu hl
  refine ⟨_, sat_twist P hB hu, ?_⟩
  have hc : UpperTheory.V.Af.Bc.CharEig ι μ w (κ.val w : ℂ) := by
    refine fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have h4 := UpperTheory.frobenius_eigenvalues_twist K Ω l ι n R μ w _ _ hE hc
  convert h4 using 1
  simp only [algSat_eq, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.ContraPair in
private theorem paired_twist {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π π' : CuspSub E n}
    (h : Paired π π' conjOp) (α ξ : HChar E)
    (hf : ∀ k : GL (Fin n) (Af E), opMul α (.fin k) * opMul ξ (conjOp (.fin k)) = 1)
    (hk : ∀ k : Kinf E n, opMul α (.cpt k) * opMul ξ (conjOp (.cpt k)) = 1)
    (hl : ∀ X : Lie E n, opAdd α (.lie X) + opAdd ξ (conjOp (.lie X)) = 0) :
    Paired (π.twist α) (π'.twist ξ) conjOp := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  let T := π.toTwist α
  let S := π'.toTwist ξ
  refine ⟨B.compl₁₂ T.symm.toLinearMap S.symm.toLinearMap, fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · exact T.symm.map_eq_zero_iff.1 (h1 _ fun ψ => by simpa using h (S ψ))
  · exact S.symm.map_eq_zero_iff.1 (h2 _ fun φ => by simpa using h (T φ))
  all_goals
    obtain ⟨φ, rfl⟩ := T.surjective φ
    obtain ⟨ψ, rfl⟩ := S.surjective ψ
    simp only [T, S, CuspSub.op_toTwist, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  · have e := h3 k φ ψ
    have e' := congrArg Units.val (hf k)
    simp only [conjOp, Units.val_mul, Units.val_one] at e e' ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_eq_mul]
    linear_combination (B φ ψ) * e'
  · have e := h4 k φ ψ
    have e' := congrArg Units.val (hk k)
    simp only [conjOp, Units.val_mul, Units.val_one] at e e' ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_eq_mul]
    linear_combination (B φ ψ) * e'
  · have e := h5 X φ ψ
    have e' := hl X
    have e3 : opMul ξ (conjOp (.lie X)) = 1 := rfl
    have e4 : opMul α (.lie X) = 1 := rfl
    rw [e3, e4]
    simp only [Units.val_one, one_smul, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination e + (B φ ψ) * e'

private theorem chiDet_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (χ : HChar E) (g : GA E n) :
    chiDet n (GlobalTheory.ThetaPull.thetaChar χ) g = chiDet n χ (GlobalTheory.ThetaPull.thetaA E n g) :=
  ((congrArg χ.1 (det_thetaGL _ g)).trans (map_inv χ.1 _)).symm

theorem UpperTheory.V.Af.Cq.csdTwist :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : CuspSub E n) (ψ ξ : HChar E), GlobalTheory.ContraPair.DualIsConjBy P ψ →
        compNorm E (GlobalTheory.HeightCounting.Blocks.resReal ξ) = ψ⁻¹ → GlobalTheory.ContraPair.DualIsConj (P.twist ξ) := by
  intro E _ _ _ n P ψ ξ h e
  have e1 := GlobalTheory.HeightCounting.Blocks.mul_inv_compNorm ξ
  have e2 : ψ⁻¹ * GlobalTheory.ThetaPull.thetaChar ξ = ξ := by
    rw [← e1, e, mul_comm ξ, mul_inv_cancel_left]
  have h' := paired_twist h (GlobalTheory.ThetaPull.thetaChar ξ) ξ (fun k => ?_) (fun k => ?_) (fun X => ?_)
  · rwa [← CuspSub.twist_mul, e2] at h'
  · have a := GlobalTheory.ContraPair.Model.sc_fin ξ k
    apply Units.ext
    simp only [thetaOp, GlobalTheory.ContraPair.conjOp, GlobalTheory.ContraPair.Model.sc, opTriv, opAdd, mul_one, add_zero] at a
    simp only [opMul, chiDet_theta, GlobalTheory.ThetaPull.thetaA_finGL, Units.val_mul, Units.val_one]
    exact a
  · have a := GlobalTheory.ContraPair.Model.sc_cpt ξ k
    apply Units.ext
    simp only [thetaOp, GlobalTheory.ContraPair.conjOp, GlobalTheory.ContraPair.Model.sc, opTriv, opAdd, mul_one, add_zero] at a
    simp only [opMul, chiDet_theta, GlobalTheory.ThetaPull.thetaA_infGL, Units.val_mul, Units.val_one,
      ← toUnits_conj_PhiK]
    exact a
  · have a := GlobalTheory.ContraPair.Model.dualIsConjBy_resReal ξ
    rw [GlobalTheory.ContraPair.DualIsConjBy, ← CuspSub.twist_mul, e1] at a
    have b := ((GlobalTheory.ContraPair.Model.paired_line_iff _ _ _ _).1 a).2.2 (fun _ _ => (Matrix.of X).trace)
    simp only [GlobalTheory.ContraPair.conjOp, GlobalTheory.ContraPair.Model.sc, opTriv, opAdd, mul_zero, zero_add] at b ⊢
    simpa [Matrix.trace, star_sum] using b
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.EmbPadic
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.embPadic :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], Nonempty (K →+* ℚ_[l]) → ∀ (j : K →+* Om l) (x : K),
        j x ∈ Set.range (algebraMap ℚ_[l] (Om l)) := by
  intro K _ _ hK l _ hι j x
  obtain ⟨ι⟩ := hι
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hmon : (minpoly ℚ x).Monic := minpoly.monic hint
  have hdle : (minpoly ℚ x).natDegree ≤ 2 := hK ▸ minpoly.natDegree_le x
  have hdpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hint
  have hroot : ∀ f : K →+* Om l, Polynomial.aeval (f x) (minpoly ℚ x) = 0 := by
    intro f
    rw [show f x = f.toRatAlgHom x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hy := hroot j
  have hw := hroot ((algebraMap ℚ_[l] (Om l)).comp ι)
  have hlead : (minpoly ℚ x).coeff (minpoly ℚ x).natDegree = 1 := hmon
  rw [Polynomial.aeval_eq_sum_range] at hy hw
  obtain hd | hd : (minpoly ℚ x).natDegree = 1 ∨ (minpoly ℚ x).natDegree = 2 := by omega
  · rw [hd] at hy hlead
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one,
      mul_one, zero_add, hlead, Rat.cast_one, one_mul] at hy
    refine ⟨-((minpoly ℚ x).coeff 0 : ℚ_[l]), ?_⟩
    rw [map_neg, map_ratCast]
    linear_combination -hy
  · rw [hd] at hy hw hlead
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one,
      mul_one, zero_add, hlead, Rat.cast_one, one_mul, RingHom.comp_apply] at hy hw
    have hfac : (j x - algebraMap ℚ_[l] (Om l) (ι x)) *
        (j x + algebraMap ℚ_[l] (Om l) (ι x) + ((minpoly ℚ x).coeff 1 : Om l)) = 0 := by
      linear_combination hy - hw
    rcases mul_eq_zero.1 hfac with h | h
    · exact ⟨ι x, (sub_eq_zero.1 h).symm⟩
    · refine ⟨-(ι x) - ((minpoly ℚ x).coeff 1 : ℚ_[l]), ?_⟩
      rw [map_sub, map_neg, map_ratCast]
      linear_combination -h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.exBridge :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), (∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1) →
        ∃ Bw' : LocBridge l K Ω (Dec (F := K) A) O, Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw hK
  haveI : IsGalois K Ω := {}
  haveI : IsGalois F Ω := {}
  haveI : T2Space (G F Ω) := krullTopology_t2
  let r : G K Ω →* G F Ω := AlgEquiv.restrictScalarsHom F
  have hr : Continuous r := continuous_restrictScalarsHom F K Ω
  have hinj : Function.Injective r := fun a b h => AlgEquiv.ext fun x => congrArg (fun g : G F Ω => g x) h
  have hind : Topology.IsInducing r := (hr.isClosedEmbedding hinj).isInducing
  have hmem : ∀ σ : G K Ω, σ ∈ Dec (F := K) A ↔ r σ ∈ Dec (F := F) A := fun σ => by
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  have hfix : ∀ (g : ↥(Dec (F := F) A)) (x : K), (g : G F Ω) (algebraMap K Ω x) = algebraMap K Ω x := fun g x => by
    apply Bw.j.injective
    rw [← Bw.e_comm]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Bw.e g).2 _ (hK x)
  let f : ↥(Dec (F := K) A) →* ↥(Dec (F := F) A) :=
    (r.comp (Dec (F := K) A).subtype).codRestrict _ fun σ => (hmem σ).1 σ.2
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (hinj (congrArg Subtype.val h)), fun g => ?_⟩
    let σ : G K Ω := AlgEquiv.ofRingEquiv (f := (g : G F Ω).toRingEquiv) (hfix g)
    have hσ : r σ = g := AlgEquiv.ext fun _ => rfl
    exact ⟨⟨σ, (hmem σ).2 (hσ ▸ g.2)⟩, Subtype.ext hσ⟩
  let φ : ↥(Dec (F := K) A) ≃* ↥(Dec (F := F) A) := MulEquiv.ofBijective f hf
  have hφ : Continuous φ := (hr.comp continuous_subtype_val).subtype_mk _
  have hφs : Continuous φ.symm := by
    rw [(hind.comp Topology.IsInducing.subtypeVal).continuous_iff]
    exact continuous_subtype_val.congr fun g => (congrArg Subtype.val (φ.apply_symm_apply g)).symm
  refine ⟨{ Kw := Bw.Kw, j := Bw.j, j_E := hK, j_dense := ?_, e := φ.trans Bw.e
            e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
            e_comm := fun g x => Bw.e_comm (φ g) x
            LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
            eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }, rfl, rfl, rfl⟩
  refine Bw.j_dense.trans (closure_mono ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨algebraMap F K x, by simp only [← IsScalarTower.algebraMap_apply]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

private theorem dense_of_approx {F K : Type} [Field F] [Field K] [NumberField K] (f : F →+* K)
    (w : HeightOneSpectrum (𝓞 K))
    (H : ∀ k a : K, a ≠ 0 → ∃ x : F, w.valuation K ((f x - k) / a) ≤ 1) :
    DenseRange fun x : F => algebraMap K (w.adicCompletion K) (f x) := by
  have hd := HeightOneSpectrum.denseRange_algebraMap K w
  refine Dense.of_closure (hd.mono ?_)
  rintro _ ⟨k, rfl⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := by simp [c]
  obtain ⟨a, ha⟩ := w.valuation_surjective K (c * WithZero.exp (-1 : ℤ))
  have ha1 : w.valuation K a ≠ 0 := by rw [ha]; exact mul_ne_zero hc0 WithZero.exp_ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha1
  obtain ⟨x, hx⟩ := H k a ha0
  refine ⟨_, hγ ?_, x, rfl⟩
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ha1), ha] at hx
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc, ← map_sub]
  have h1 : (Valued.v (algebraMap K (w.adicCompletion K) (f x - k)) : WithZero (Multiplicative ℤ)) =
      w.valuation K (f x - k) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  rw [h1]
  refine hx.trans_lt ?_
  refine mul_lt_of_lt_one_right (zero_lt_iff.2 hc0) ?_
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

private theorem surj_of_dense {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] (f : F →+* K)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (hv : ∀ x : F, w.valuation K (f x) ≤ 1 → v.valuation F x ≤ 1)
    (hd : DenseRange fun x : F => algebraMap K (w.adicCompletion K) (f x))
    (κ : v.adicCompletion F →+* w.adicCompletion K) (hc : Continuous κ)
    (hκ : ∀ x, κ (algebraMap F _ x) = algebraMap K _ (f x)) : Function.Surjective κ := by
  have hcomp : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  have hcl := (hcomp.image hc).isClosed
  have ho : IsOpen (w.adicCompletionIntegers K : Set (w.adicCompletion K)) := Valued.isOpen_valuationSubring _
  have key : (w.adicCompletionIntegers K : Set (w.adicCompletion K)) ⊆ κ '' (v.adicCompletionIntegers F) := by
    refine (Dense.open_subset_closure_inter hd ho).trans (closure_minimal ?_ hcl)
    rintro _ ⟨h1, x, rfl⟩
    refine ⟨algebraMap F _ x, ?_, hκ x⟩
    have h2 : (Valued.v (algebraMap K (w.adicCompletion K) (f x)) : WithZero (Multiplicative ℤ)) =
      w.valuation K (f x) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have h3 : (Valued.v (algebraMap F (v.adicCompletion F) x) : WithZero (Multiplicative ℤ)) =
      v.valuation F x := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rw [h3]
    exact hv x (h2 ▸ h1)
  intro y
  rcases (w.adicCompletionIntegers K).mem_or_inv_mem y with h | h
  · obtain ⟨x, -, hx⟩ := key h
    exact ⟨x, hx⟩
  · obtain ⟨x, -, hx⟩ := key h
    exact ⟨x⁻¹, by rw [map_inv₀, hx, inv_inv]⟩

theorem UpperTheory.V.Af.Cq.exPlaceIso :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O),
        Induces Bw → (∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1) → ∃ (w : HeightOneSpectrum (𝓞 K)) (_ : IsPlaceOver A w)
          (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A v h O _ _ _ Bw hj hK
  obtain ⟨w, hw⟩ := place_between (L := K) h
  obtain ⟨κ, hκc, hκ⟩ := GlobalTheory.CompositumCompletion.exists_completion_map (algebraMap F K) v w (fun x => by
    rw [← hw, ← h x]
    show A.valuation (algebraMap K Ω (algebraMap F K x)) < 1 ↔ _
    rw [← IsScalarTower.algebraMap_apply])
  have hd := dense_of_approx (algebraMap F K) w (fun k a ha => by
    have hpos : 0 < ‖Bw.j (algebraMap K Ω a)‖ := by simpa using ha
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (Bw.j_dense (hK k)) _ hpos
    refine ⟨x, ?_⟩
    rw [← TraceCompl.algebraMap_mem_iff hw, hj, map_div₀, map_div₀, norm_div, div_le_one hpos, map_sub, map_sub,
      ← IsScalarTower.algebraMap_apply, ← dist_eq_norm, dist_comm]
    exact hx.le)
  have hs := surj_of_dense (algebraMap F K) v w (fun x hx => by
    rw [← TraceCompl.algebraMap_mem_iff hw, ← IsScalarTower.algebraMap_apply,
      TraceCompl.algebraMap_mem_iff h] at hx
    exact hx) hd κ hκc hκ
  exact ⟨w, hw, RingEquiv.ofBijective κ ⟨κ.injective, hs⟩, fun _ => Iff.rfl,
    fun x => IsScalarTower.algebraMap_apply F K Ω x, hκc, hκ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.PstRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.pstRes :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O),
        Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
        IsPstAt (Loc.PP l) Bw' ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)).comp (Dec (F := K) A).subtype) := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hj hL n r hr
  obtain ⟨Kw', j', jE', jd', e', ec', esc', ecomm', LL0', hs', eO', h1', h2', h3'⟩ := Bw'
  dsimp only at hK hj hL
  subst hK hj hL
  obtain ⟨LL', r', ⟨hle, hmap⟩, hpst⟩ := hr
  refine ⟨LL', r'.comp (e'.trans Bw.e.symm).toMonoidHom, ⟨hle, ?_⟩, ?_⟩
  · refine MonoidHom.ext fun g => ?_
    have h1 := DFunLike.congr_fun hmap (Bw.e.symm (e' g))
    have h2 : ((Bw.e.symm (e' g) : ↥(Dec (F := F) A)) : Ω ≃ₐ[F] Ω) =
        AlgEquiv.restrictScalarsHom F (g : Ω ≃ₐ[K] Ω) := by
      refine AlgEquiv.ext fun x => Bw.j.injective ?_
      rw [← Bw.e_comm, MulEquiv.apply_symm_apply, ecomm']
      rfl
    refine h1.trans ?_
    exact congrArg r h2
  · convert hpst using 1
    refine MonoidHom.ext fun g => ?_
    simp [LocBridge.repE]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.RecTransport
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.recTransport :
    GlobalTheory.Published.LocalLanglandsGL → ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
                 [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v)
                 (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) j i →
                 ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin n) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V),
                   (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → ∀ rc rc', IsRec h rc → IsRec h' rc' →
                   ∀ y : WD h, WDRel (RingEquiv.refl Ω) y (rc' (algNorm σ')) → y = rc (algNorm σ) := by
  intro hL F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i P n σ σ' e he rc rc' hrc hrc' y hy
  obtain ⟨S, hS, -, -, -, -, hSt, -⟩ := GlobalTheory.WDTransport.exists_equiv_wd F Ω A v h K Ω A w h' (RingEquiv.refl Ω) j i P
  have hF := hL.2 F Ω A v h K Ω A w h' rc rc' hrc hrc' (RingEquiv.refl Ω) j i P.mem P.ext P.cont P.loc n
    { V := σ.V, ρ := σ.ρ, smooth := σ.smooth, irr := σ.irred }
    { V := σ'.V, ρ := σ'.ρ, smooth := σ'.smooth, irr := σ'.irred } e he
  have h1 : S (rc (IrrGL.of σ.ρ σ.smooth σ.irred)) = rc' (IrrGL.of σ'.ρ σ'.smooth σ'.irred) :=
    (hS _ _).1 ⟨n, hF⟩
  apply S.injective
  rw [(hS _ _).1 hy, rec_algNorm hrc, rec_algNorm hrc', hSt, h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.SignFix
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sf_isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem sf_quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]
end

