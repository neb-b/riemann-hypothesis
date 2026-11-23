module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.SkewLatSD

variable (D : D7)

theorem star_eq_conj' (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  have := D.host.isCMField_hostE
  exact D.host.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm)

theorem conj_conj' (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  rw [← star_eq_conj', ← star_eq_conj', star_star]

theorem conj_mul_conj : D.host.conj * D.host.conj = 1 :=
  AlgEquiv.ext fun x => conj_conj' D x

theorem conj_smul_conj_smul (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  rw [smul_smul, conj_mul_conj, one_smul]

variable {D}

theorem smul_ne_bot (g : Gal(D.host.E/ℚ)) {I : Ideal (𝓞 D.host.E)} (h : I ≠ ⊥) : g • I ≠ ⊥ := by
  obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  intro e
  have := Ideal.smul_mem_pointwise_smul g j I hj
  rw [e, Ideal.mem_bot, smul_eq_zero_iff_eq] at this
  exact hj0 this

theorem coe_ne_zero {I : Ideal (𝓞 D.host.E)} (h : I ≠ ⊥) : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
  rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

theorem map_mem_div (g : Gal(D.host.E/ℚ)) {I J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) {x : D.host.E}
    (hx : x ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) : g x ∈ ((g • I : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / ((g • J : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero hJ)] at hx
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero (smul_ne_bot g hJ))]
  intro c hc
  obtain ⟨c', hc', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hc
  have h1 : g⁻¹ • c' ∈ J := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hc'
  obtain ⟨i, hi, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, h1, rfl⟩))
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨g • i, Ideal.smul_mem_pointwise_smul g i I hi, ?_⟩
  have e' : ((i : 𝓞 D.host.E) : D.host.E) = x * ((g⁻¹ • c' : 𝓞 D.host.E) : D.host.E) := e
  show ((g • i : 𝓞 D.host.E) : D.host.E) = g x * (c' : D.host.E)
  have e2 : ((g • i : 𝓞 D.host.E) : D.host.E) = g (i : D.host.E) := rfl
  have e3 : ((g⁻¹ • c' : 𝓞 D.host.E) : D.host.E) = g⁻¹ (c' : D.host.E) := rfl
  rw [e2, e', e3, map_mul, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

end GlobalTheory.SkewLatSD

namespace GlobalTheory.SkewLatSD

variable {D : D7}

theorem mem_skewLat_iff {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} (y : Fin N → D.host.E) :
    y ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N ↔ ∀ i, y i ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  simp only [GlobalTheory.FunObj.SqNum.skewLat, Submodule.mem_pi, Set.mem_univ, true_implies]
  rfl

theorem skewLat_sd : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ), 𝔪 ≠ ⊥ → SD D (GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N) := by
  intro D 𝔪 N h𝔪
  letI := D.host.cmStar
  set σ := D.host.conj
  set 𝔫 : Ideal (𝓞 D.host.E) := σ • 𝔪 with h𝔫
  have h𝔫0 : 𝔫 ≠ ⊥ := smul_ne_bot σ h𝔪
  have hA0 : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := div_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hB0 : (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := div_ne_zero (coe_ne_zero h𝔫0) (coe_ne_zero h𝔪)
  have hBA : (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) = 1 := by
    rw [div_mul_div_comm, mul_comm (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), div_self (mul_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0))]
  have hσ𝔫 : σ • 𝔫 = 𝔪 := conj_smul_conj_smul D 𝔪

  have toB : ∀ x ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), σ x ∈ (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := fun x hx => by
    simpa only [← h𝔫, hσ𝔫] using (map_mem_div σ h𝔫0 hx)
  have toA : ∀ x ∈ (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), σ x ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := fun x hx => by
    simpa only [← h𝔫, hσ𝔫] using (map_mem_div σ h𝔪 hx)
  have hmem := fun y => mem_skewLat_iff (D := D) (𝔪 := 𝔪) (N := N) y
  refine ⟨?_, ?_, ?_⟩
  · unfold GlobalTheory.FunObj.SqNum.skewLat
    rw [← Submodule.iSup_map_single]
    exact Submodule.fg_iSup _ fun i => (FractionalIdeal.fg_of_isNoetherianRing le_rfl _).map _
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (show (((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ from fun e =>
        hA0 (FractionalIdeal.coeToSubmodule_injective (e.trans FractionalIdeal.coe_zero.symm)))
    have hs : ∀ i, (Pi.single i a : Fin N → D.host.E) ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N := fun i => by
      rw [hmem]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using ha
      · rw [Pi.single_eq_of_ne hj]; exact FractionalIdeal.zero_mem _
    rw [Submodule.eq_top_iff']
    intro v
    have hv : v = ∑ i, (v i * a⁻¹) • (Pi.single i a : Fin N → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, ha0]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))
  · intro y
    constructor
    · intro hy x hx
      rw [hmem] at hx hy
      unfold Formalism.BasicNotions.stdH
      refine Subring.sum_mem _ fun i _ => ?_
      rw [star_eq_conj']
      have := FractionalIdeal.mul_mem_mul (toB _ (hx i)) (hy i)
      rw [hBA, FractionalIdeal.mem_one_iff] at this
      obtain ⟨r, hr⟩ := this
      exact ⟨r, hr⟩
    · intro h
      rw [hmem]
      intro i
      rw [← one_div_div, FractionalIdeal.mem_div_iff_of_ne_zero hB0]
      intro b hb
      have ha := toA b hb
      have hx : (Pi.single i (σ b) : Fin N → D.host.E) ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N := by
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simpa using ha
        · rw [Pi.single_eq_of_ne hj]; exact FractionalIdeal.zero_mem _
      have := h _ hx
      unfold Formalism.BasicNotions.stdH at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun hi => absurd (Finset.mem_univ i) hi)] at this
      rw [Pi.single_eq_same, star_eq_conj', conj_conj'] at this
      obtain ⟨r, hr⟩ := this
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨r, by rw [hr, mul_comm]⟩

end GlobalTheory.SkewLatSD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceTransformSchwartzBijective
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapSliceBij

open GlobalTheory.SwapSlice

theorem totDisc_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TotallyDisconnectedSpace k := by
  haveI : T2Space k := inferInstance
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : f ∈ SB X) :
    (fun x => starRingEnd ℂ (f x)) ∈ SB X :=
  ⟨hf.1.comp (starRingEnd ℂ), hf.2.comp_left (map_zero _)⟩

theorem barL_bijOn {k Y : Type} [TopologicalSpace k] [TopologicalSpace Y] {κ : Type}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (h : Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ))) :
    Set.BijOn (barL ι) (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ)) := by
  refine ⟨fun φ hφ => conj_mem_SB (h.mapsTo (conj_mem_SB hφ)), fun φ hφ ψ hψ e => ?_, fun g hg => ?_⟩
  · have e' : ι (fun x => starRingEnd ℂ (φ x)) = ι (fun x => starRingEnd ℂ (ψ x)) := by
      funext y
      have := congrFun e y
      simp only [barL_apply] at this
      simpa using congrArg (starRingEnd ℂ) this
    have e'' := h.injOn (conj_mem_SB hφ) (conj_mem_SB hψ) e'
    funext x
    simpa using congrArg (starRingEnd ℂ) (congrFun e'' x)
  · obtain ⟨φ', hφ', e⟩ := h.surjOn (conj_mem_SB hg)
    refine ⟨fun x => starRingEnd ℂ (φ' x), conj_mem_SB hφ', ?_⟩
    funext y
    simp [barL_apply, e]

theorem boxFun_mem {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

variable {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] [LocallyCompactSpace k] [TotallyDisconnectedSpace k]
  {κ : Type} [Fintype κ]

theorem SB_le_span_boxFun :
    SB (κ ⊕ κ → k) ≤ Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} := by
  intro Φ hΦ
  let e := Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ)
  have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (κ → k) (κ → k)
  let T : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ e) ∘ₗ (GlobalTheory.SplitWeil.SB _).subtype
  have hΦ' : Φ ∘ e.symm ∈ GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) :=
    ⟨hΦ.1.comp_continuous e.symm.continuous, hΦ.2.comp_homeomorph e.symm⟩
  have key : Φ ∈ Submodule.map T ⊤ := ⟨⟨Φ ∘ e.symm, hΦ'⟩, trivial, by
    funext x; simp [T, LinearMap.funLeft]⟩
  rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
  refine Submodule.span_mono ?_ key
  rintro _ ⟨q, rfl⟩
  exact ⟨q.1.1, q.1.2, q.2.1, q.2.2, by funext x; rfl⟩

theorem mem_of_boxFun {M : Type} [AddCommGroup M] [Module ℂ M] (L : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] M) (P : Submodule ℂ M)
    (h : ∀ φ₁ ∈ SB (κ → k), ∀ φ₂ ∈ SB (κ → k), L (boxFun φ₁ φ₂) ∈ P) : ∀ Φ ∈ SB (κ ⊕ κ → k), L Φ ∈ P := by
  intro Φ hΦ
  have hle : Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} ≤ P.comap L :=
    Submodule.span_le.2 (by rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩; exact h φ₁ h₁ φ₂ h₂)
  exact hle (SB_le_span_boxFun hΦ)

end GlobalTheory.SwapSliceBij


open GlobalTheory.SwapSlice GlobalTheory.SwapSliceBij in
theorem GlobalTheory.SwapSliceBij.sliceT_bijOn : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type} [Fintype κ] {n d : ℕ}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB (Matrix (Fin n) (Fin d) k) : Set _) →
    Set.BijOn (GlobalTheory.SwapSlice.sliceT ι) (SB (κ ⊕ κ → k) : Set ((κ ⊕ κ → k) → ℂ))
      (SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k) : Set _) := by
  intro k _ _ _ _ κ _ n d ι hι
  haveI : T2Space k := inferInstance
  haveI := totDisc_localField k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → k))
  haveI : T2Space (Matrix (Fin n) (Fin d) k) := inferInstanceAs (T2Space (Fin n → Fin d → k))
  have hbar := barL_bijOn ι hι

  have hslice : ∀ x₂ : κ → k, ∀ Φ ∈ SB (κ ⊕ κ → k), (fun x₁ => Φ (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
    intro x₂
    refine mem_of_boxFun (LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ h₁

  have hcol : ∀ Z₁ : Matrix (Fin n) (Fin d) k, ∀ Φ ∈ SB (κ ⊕ κ → k),
      (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) ∈ SB (κ → k) := by
    intro Z₁
    refine mem_of_boxFun (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
        LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (boxFun φ₁ φ₂) = ι φ₁ Z₁ • φ₂ := by
      funext x₂
      have e' : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
        funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
      simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, e', map_smul, LinearMap.coe_proj,
        Function.eval, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]; exact Submodule.smul_mem _ _ h₂
  have hz : ∀ Φ ∈ SB (κ ⊕ κ → k), sliceT ι Φ = 0 → Φ = 0 := by
    intro Φ hΦ h0
    have h1 : ∀ Z₁, (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) = 0 := by
      intro Z₁
      refine hbar.injOn (hcol Z₁ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₂; exact congrFun h0 (Z₁, Z₂)
    have h2 : ∀ x₂, (fun x₁ => Φ (Sum.elim x₁ x₂)) = 0 := by
      intro x₂
      refine hι.injOn (hslice x₂ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₁; exact congrFun (h1 Z₁) x₂
    funext x
    have := congrFun (h2 (x ∘ Sum.inr)) (x ∘ Sum.inl)
    simpa [Sum.elim_comp_inl_inr] using this
  refine ⟨?_, fun Φ hΦ Ψ hΨ e => sub_eq_zero.1 (hz (Φ - Ψ) (sub_mem hΦ hΨ) (by rw [map_sub, e, sub_self])), ?_⟩
  · intro Φ hΦ
    refine mem_of_boxFun (sliceT ι) _ ?_ Φ hΦ
    intro φ₁ h₁ φ₂ h₂
    have e : sliceT ι (boxFun φ₁ φ₂) = GlobalTheory.LocFlat.CFac.prodFn (ι φ₁) (barL ι φ₂) := by
      funext Z; rw [sliceT_boxFun]; rfl
    rw [e]; exact GlobalTheory.LocFlat.CFac.prodFn_mem_SB (hι.mapsTo h₁) (hbar.mapsTo h₂)
  · intro g hg
    have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (Matrix (Fin n) (Fin d) k) (Matrix (Fin n) (Fin d) k)
    have key : g ∈ Submodule.map (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ⊤ :=
      ⟨⟨g, hg⟩, trivial, rfl⟩
    rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
    have hle : Submodule.span ℂ (Set.range ((GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ∘
        fun q : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) × GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) =>
          GlobalTheory.LocFlat.CFac.prodSB q.1 q.2)) ≤ Submodule.map (sliceT ι) (SB (κ ⊕ κ → k)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨q, rfl⟩
      obtain ⟨φ₁, h₁, e₁⟩ := hι.surjOn q.1.2
      obtain ⟨φ₂, h₂, e₂⟩ := hbar.surjOn q.2.2
      refine ⟨boxFun φ₁ φ₂, boxFun_mem h₁ h₂, ?_⟩
      funext Z
      rw [sliceT_boxFun, e₁, e₂]
      rfl
    obtain ⟨Φ, hΦ, e⟩ := Submodule.mem_map.1 (hle key)
    exact ⟨Φ, hΦ, e⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStepCharIdealValueEqBaseMulRootOfUnity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.SqStepIdeal

open GlobalTheory.LFun

theorem val_mem {D : D7} {χ : HChar D.host.E} {n : ℕ} (h1 : χ.OrderDvd n) (h2 : LocIn D.what₂.embLL χ)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) :
    χ.val w ^ n = 1 ∧ ((χ.val w : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  refine ⟨?_, ?_⟩
  · have e1 : (χ.1 : _ →* ℂˣ) ^ n = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    have e2 : ∀ y, χ.1 y ^ n = 1 := fun y => by
      have := DFunLike.congr_fun e1 y
      simpa [MonoidHom.pow_apply] using this
    exact e2 _
  · obtain ⟨y, hy⟩ := h2 w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))
    exact ⟨y, hy⟩

theorem mulSupport_finite {E : Type} [Field E] [NumberField E] (f : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → ℂˣ)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    (Function.mulSupport fun w => f w ^ FractionalIdeal.count E w 𝔞).Finite := by
  refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors 𝔞)).subset fun w hw => ?_
  intro h
  apply hw
  simp only [h, zpow_zero]

theorem idealVal_chs_base : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), ∃ b : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ b ^ n = 1) ∧
      ((idealVal (GlobalTheory.SqStep.chs G i j μ₀).ν 𝔞 : ℂˣ) : ℂ) = D.what₂.embLL b * ((idealVal (GlobalTheory.SqStep.chs G i j t).ν 𝔞 : ℂˣ) : ℂ) := by
  intro D T Lc sc G μ₀ hL W S hN i j t 𝔞
  have e : ∀ s, (GlobalTheory.SqStep.chs G i j s).ν = G.nu s i (j + 1) := fun s => by
    show (Lc.mu s (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  have hν : (GlobalTheory.SqStep.chs G i j μ₀).ν = (GlobalTheory.SqStep.chs G i j t).ν * ((Lc.xi t)⁻¹ * Lc.xi μ₀) := by
    rw [e, e]
    refine MonoidHom.ext fun x => ?_
    show Lc.mu0 (j + 1) x * Lc.xi μ₀ x / G.ch.chi (D.R.m - i) x =
      Lc.mu0 (j + 1) x * Lc.xi t x / G.ch.chi (D.R.m - i) x * ((Lc.xi t x)⁻¹ * Lc.xi μ₀ x)
    rw [div_mul_eq_mul_div, mul_assoc (Lc.mu0 (j + 1) x) (Lc.xi t x), mul_inv_cancel_left]
  obtain ⟨n, hn, hfin⟩ := hL.xi_fin t
  let c : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun w => ((Lc.xiH t).val w)⁻¹
  have hw : ∀ w, val (GlobalTheory.SqStep.chs G i j μ₀).ν w = val (GlobalTheory.SqStep.chs G i j t).ν w * c w := fun w => by
    rw [hν, val_mul, val_mul, val_inv, val_eq_of_chrEq (hL.xi t) w, val_eq_of_chrEq (hL.xi μ₀) w, hL.xi_base]
    rw [show (1 : HChar D.host.E).val w = 1 from rfl, mul_one]
  let H : Subgroup ℂˣ :=
    { carrier := {z | z ^ n = 1 ∧ (z : ℂ) ∈ D.what₂.embLL.fieldRange}
      mul_mem' := fun ha hb => ⟨by rw [mul_pow, ha.1, hb.1, one_mul], by rw [Units.val_mul]; exact mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_pow _, by rw [Units.val_one]; exact one_mem _⟩
      inv_mem' := fun ha => ⟨by rw [inv_pow, ha.1, inv_one], by rw [Units.val_inv_eq_inv_val]; exact inv_mem ha.2⟩ }
  have hc : ∀ w, c w ∈ H := fun w => H.inv_mem (val_mem hfin (hN.chars.xi t) w)
  have hprod : idealVal (GlobalTheory.SqStep.chs G i j μ₀).ν 𝔞 =
      idealVal (GlobalTheory.SqStep.chs G i j t).ν 𝔞 * ∏ᶠ w, c w ^ FractionalIdeal.count D.host.E w 𝔞 := by
    unfold idealVal
    simp_rw [hw, mul_zpow]
    exact finprod_mul_distrib (mulSupport_finite _ 𝔞) (mulSupport_finite _ 𝔞)
  have hz : ∏ᶠ w, c w ^ FractionalIdeal.count D.host.E w 𝔞 ∈ H := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := (mulSupport_finite c 𝔞).toFinset) (by simp)]
    exact H.prod_mem fun w _ => H.zpow_mem (hc w) _
  obtain ⟨hzn, hzr⟩ := hz
  obtain ⟨b, hb⟩ := RingHom.mem_fieldRange.1 hzr
  refine ⟨b, ⟨n, hn, ?_⟩, ?_⟩
  · apply D.what₂.embLL.injective
    rw [map_pow, hb, map_one, ← Units.val_pow_eq_pow_val, hzn, Units.val_one]
  · rw [hprod, Units.val_mul, hb, mul_comm]

end GlobalTheory.SqStepIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasureStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tamagawa_adelicHaar_eq_map_product_measure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (e : κ ≃ Fin N) (ν : Measure (AF F)), GlobalTheory.SWQ.IsCov1 ν → ∀ μ : Measure (κ → AF F), IsTamagawa F κ μ → μ = Measure.map (GlobalTheory.PoissonReindex.reidx (F := F) e) (GlobalTheory.SWQ.muV N ν) := by
  first | exact @GlobalTheory.SWLit.tamagawa_eq_map_pi | exact GlobalTheory.SWLit.tamagawa_eq_map_pi | (intros; apply GlobalTheory.SWLit.tamagawa_eq_map_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelContinuousFunctional
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaKernelCont

theorem theta_pureA_clm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ (g : UA σ X.J) (h : UA σ W.J),
    ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), theta om (pureA F f φ) g h = T f := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ g h
  obtain ⟨l, hl, hlθ⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  have hs := hP.weil.isUSplitting
  obtain ⟨T, hT⟩ := hs.adm (g, h) l hl φ hφ
  refine ⟨T, fun f => ?_⟩
  have hmem : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hmem' : om (g, h) (pureA F f φ) ∈ schA F (Fin n × Fin d) := hs.pres (g, h) _ hmem
  rw [← hT f, LinearMap.comp_apply, hlθ _ hmem']
  rfl

end GlobalTheory.ThetaKernelCont
end
end

