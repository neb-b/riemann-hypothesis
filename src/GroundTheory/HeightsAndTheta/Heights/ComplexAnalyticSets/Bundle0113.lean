module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0111
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0112
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.JacobianAtCurvePoint
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0110
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGradDensSheetBound
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets FieldNumbers

noncomputable section

theorem exists_finset_span_integral_of_div (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O Ω : Type}
    [CommRing O] [Field Ω] [Algebra O Ω] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f)
    (hΩ : ∀ x : Ω, ∃ a b : O, x = algebraMap O Ω a / algebraMap O Ω b) :
    ∃ t : Finset Ω, ∀ x : Ω, IsIntegral O x → x ∈ Submodule.span O (t : Set Ω) := by
  let ψ : MvPolynomial (Fin n) ℂ →+* Ω := (algebraMap O Ω).comp φ
  let _ : Algebra ℂ Ω := (ψ.comp C).toAlgebra
  let S : Set Ω := Set.range fun i ↦ ψ (X i)
  have hpoly : ∀ f, ψ f ∈ Algebra.adjoin ℂ S := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f i hf => rw [map_mul]; exact mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
  let A : Subalgebra ℂ Ω :=
    { toSubsemiring := (algebraMap O Ω).rangeS, algebraMap_mem' := fun c ↦ ⟨φ (C c), rfl⟩ }
  have hRA : Algebra.adjoin ℂ S ≤ A := Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact ⟨φ (X i), rfl⟩)
  have hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin ℂ S, ∃ d ∈ Algebra.adjoin ℂ S, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹ := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨f, s, hs, ho⟩ := hφ o
    refine ⟨ψ f, hpoly f, ψ s, hpoly s, (hs.map (algebraMap O Ω)).ne_zero, ⟨↑hs.unit⁻¹, ?_⟩, ?_⟩
    · change algebraMap O Ω ↑hs.unit⁻¹ = (algebraMap O Ω (φ s))⁻¹
      rw [map_units_inv, IsUnit.unit_spec]
    · refine (eq_mul_inv_iff_mul_eq₀ (hs.map (algebraMap O Ω)).ne_zero).2 ?_
      change algebraMap O Ω o * algebraMap O Ω (φ s) = algebraMap O Ω (φ f)
      rw [← map_mul, ho]
  have hE : ∀ x : Ω, x ∈ IntermediateField.adjoin ℂ S := by
    have hA : ∀ a ∈ A, a ∈ IntermediateField.adjoin ℂ S := by
      intro a ha
      obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
      exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hr)
        (inv_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hd))
    intro x
    obtain ⟨a, b, rfl⟩ := hΩ x
    exact div_mem (hA _ ⟨a, rfl⟩) (hA _ ⟨b, rfl⟩)
  have hfin : FiniteDimensional (IntermediateField.adjoin ℂ S)
      (IntermediateField.extendScalars (le_refl (IntermediateField.adjoin ℂ S))) := by
    rw [IntermediateField.extendScalars_self]; infer_instance
  obtain ⟨t, -, ht⟩ := exists_finset_integral_span hN (Set.finite_range _) A _ hRA hloc le_rfl hfin
  let _ : Algebra O A := ((algebraMap O Ω).codRestrict A fun o ↦ (⟨o, rfl⟩ : algebraMap O Ω o ∈ (algebraMap O Ω).rangeS)).toAlgebra
  have : IsScalarTower O A Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsur : Function.Surjective (algebraMap O A) := by rintro ⟨_, o, rfl⟩; exact ⟨o, rfl⟩
  refine ⟨t, fun x hx ↦ ?_⟩
  rw [← Submodule.restrictScalars_span O A hsur]
  exact ht x (hE x) hx.tower_top

theorem exists_algHom_span_of_mem_minimalPrimes (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ}
    {O : Type} [CommRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) {p : Ideal O} (hp : p ∈ minimalPrimes O) :
    ∃ g : FractionRing O →ₐ[O] FractionRing (O ⧸ p), ∃ t : Finset (FractionRing (O ⧸ p)),
      ∀ x : FractionRing O, IsIntegral O x → g x ∈ Submodule.span O (t : Set (FractionRing (O ⧸ p))) := by
  have := Ideal.IsMinimalPrime.isPrime hp
  have hu : ∀ y : nonZeroDivisors O, IsUnit (Algebra.ofId O (FractionRing (O ⧸ p)) y) := by
    intro y
    refine IsUnit.mk0 _ fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes ?_ hp y.2
    have h' : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p y) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by rw [map_zero]; exact h
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ h')
  obtain ⟨t, ht⟩ := exists_finset_span_integral_of_div hN φ hφ (Ω := FractionRing (O ⧸ p)) fun x ↦ by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O ⧸ p) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨a, b, rfl⟩
  exact ⟨IsLocalization.liftAlgHom (M := nonZeroDivisors O) hu, t, fun x hx ↦ ht _ (hx.map _)⟩

theorem finite_integralClosure_of_isReduced (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O : Type}
    [CommRing O] [IsReduced O] [IsNoetherianRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) :
    Module.Finite O (integralClosure O (FractionRing O)) := by
  have := (minimalPrimes.finite_of_isNoetherianRing O).to_subtype
  choose g t ht using fun p : minimalPrimes O ↦ exists_algHom_span_of_mem_minimalPrimes hN φ hφ p.2
  let F : integralClosure O (FractionRing O) →ₗ[O]
      ((p : minimalPrimes O) → Submodule.span O (t p : Set (FractionRing (O ⧸ (p : Ideal O))))) :=
    LinearMap.pi fun p ↦ LinearMap.codRestrict _
      ((g p).toLinearMap ∘ₗ (integralClosure O (FractionRing O)).val.toLinearMap) fun x ↦ ht p x x.2
  refine Module.Finite.of_injective F ((injective_iff_map_eq_zero F).2 fun x hx ↦ ?_)
  have h0 : ∀ p : minimalPrimes O, g p x = 0 := fun p ↦ congrArg Subtype.val (congr_fun hx p)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) (x : FractionRing O)
  have ha : a ∈ sInf (minimalPrimes O) := by
    refine Ideal.mem_sInf.2 fun p hp ↦ ?_
    have := Ideal.IsMinimalPrime.isPrime hp
    have e : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p a) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by
      rw [map_zero]
      change algebraMap O (FractionRing (O ⧸ p)) a = 0
      rw [← (g ⟨p, hp⟩).commutes, ← hab, map_mul, h0, zero_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ e)
  rw [Ideal.sInf_minimalPrimes, Ideal.mem_radical_iff] at ha
  obtain ⟨k, hk⟩ := ha
  have ha0 : a = 0 := IsNilpotent.eq_zero ⟨k, by simpa using hk⟩
  rw [ha0, map_zero, (IsLocalization.map_units (FractionRing O) b).mul_left_eq_zero] at hab
  exact Subtype.ext hab

theorem isReduced_curveLocalRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (h : IsRadicalAt I q) : IsReduced (curveLocalRing I q) := by
  refine (Ideal.isRadical_iff_quotient_reduced _).1 ?_
  rw [Ideal.IsRadical, ← IsLocalization.map_radical (RingHom.ker (eval q)).primeCompl]
  refine Ideal.map_le_iff_le_comap.2 fun f hf ↦ ?_
  obtain ⟨s, hs, hsf⟩ := h f hf
  have hu : IsUnit (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) s) :=
    IsLocalization.map_units _ (⟨s, fun h' ↦ hs (RingHom.mem_ker.1 h')⟩ : (RingHom.ker (eval q)).primeCompl)
  exact (Ideal.unit_mul_mem_iff_mem _ hu).1 (by rw [← map_mul]; exact Ideal.mem_map_of_mem _ hsf)

theorem curveLocalRing_eq_div {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (o : curveLocalRing I q) : ∃ f s, IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s) ∧
      o * algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s =
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
  obtain ⟨z, rfl⟩ : ∃ z, Ideal.Quotient.mk
      (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))) z = o :=
    Ideal.Quotient.mk_surjective o
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl z
  refine ⟨f, s, isUnit_algebraMap_curveLocalRing I q s fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have e := congrArg (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval q))) f s)
  rw [map_mul] at e
  exact e

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GoodPointBranchSlice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

namespace GoodPointBranch

def consZero (d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cons (α := fun _ => (Fin d → ℂ) →L[ℂ] ℂ) 0
    fun j => ContinuousLinearMap.proj j)

theorem consZero_apply {d : ℕ} (v : Fin d → ℂ) : consZero d v = Fin.cons 0 v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consZero]

theorem consZero_apply_zero {d : ℕ} (v : Fin d → ℂ) : consZero d v 0 = 0 := by
  rw [consZero_apply]
  rfl

theorem consZero_tail {d : ℕ} (t : Fin (d + 1) → ℂ) (ht : t 0 = 0) : consZero d (Fin.tail t) = t := by
  rw [consZero_apply, ← ht]
  exact Fin.cons_self_tail t

theorem consZero_injective {d : ℕ} : Function.Injective (consZero d) := fun a b h => by
  rw [consZero_apply, consZero_apply] at h
  exact Fin.cons_right_injective _ h

theorem consZero_mem_ball {d : ℕ} {s : ℝ} {v : Fin d → ℂ} (hv : v ∈ ball (0 : Fin d → ℂ) s) :
    consZero d v ∈ ball (0 : Fin (d + 1) → ℂ) s := by
  rw [mem_ball_zero_iff] at hv ⊢
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg _) hv
  rw [pi_norm_lt_iff hs]
  intro i
  rw [consZero_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hs
  · simpa using (norm_le_pi_norm v j).trans_lt hv

theorem tail_mem_ball {d : ℕ} {s : ℝ} {t : Fin (d + 1) → ℂ} (ht : t ∈ ball (0 : Fin (d + 1) → ℂ) s) :
    Fin.tail t ∈ ball (0 : Fin d → ℂ) s := by
  rw [mem_ball_zero_iff] at ht ⊢
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg _) ht
  rw [pi_norm_lt_iff hs]
  intro j
  exact (norm_le_pi_norm t j.succ).trans_lt ht

def consCLM (d : ℕ) : (ℂ × (Fin d → ℂ)) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cons (α := fun _ => (ℂ × (Fin d → ℂ)) →L[ℂ] ℂ)
    (ContinuousLinearMap.fst ℂ ℂ (Fin d → ℂ))
    fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin d → ℂ)))

theorem consCLM_apply {d : ℕ} (p : ℂ × (Fin d → ℂ)) : consCLM d p = vecCons p.1 p.2 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consCLM]

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn
    fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem slice_chart {d n : ℕ} {ψ : (Fin (d + 1) → ℂ) → Fin n → ℂ} {D : (Fin (d + 1) → ℂ) →L[ℂ] Fin n → ℂ}
    {q : Fin n → ℂ} {S : Set (Fin n → ℂ)} {A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)} {O : Set (Fin d → ℂ)}
    {V : Set (Fin n → ℂ)} {g : (Fin d → ℂ) → Fin n → ℂ}
    (hψ : HasStrictFDerivAt ψ D 0) (hψ0 : ψ 0 = q) (hD : ∀ v, v 0 = 0 → D v = 0 → v = 0)
    (hV : IsOpen V) (hqV : q ∈ V) (hg : AnalyticOnNhd ℂ g O) (hAg : ∀ y ∈ O, A (g y) = y)
    (hS : S ∩ V = g '' O) (hslice : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), ψ (consZero d v) ∈ S) :
    (∀ v, v 0 = 0 → A (D v) = 0 → v = 0) ∧
    ∃ W ∈ 𝓝 (0 : Fin d → ℂ), Set.InjOn (fun v => ψ (consZero d v)) W ∧
      ∀ W' ∈ 𝓝 (0 : Fin d → ℂ), W' ⊆ W → ∃ N ∈ 𝓝 q, S ∩ N ⊆ (fun v => ψ (consZero d v)) '' W' := by
  set σ : (Fin d → ℂ) → Fin n → ℂ := fun v => ψ (consZero d v) with hσdef
  have hσ : HasStrictFDerivAt σ (D.comp (consZero d)) 0 := by
    have h0 : HasStrictFDerivAt ψ D (consZero d 0) := by rw [map_zero]; exact hψ
    exact h0.comp 0 (consZero d).hasStrictFDerivAt
  have hσ0 : σ 0 = q := by simp [hσdef, hψ0]
  have hev : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), σ v ∈ S ∧ σ v ∈ V :=
    hslice.and (hσ.continuousAt.preimage_mem_nhds (by rw [hσ0]; exact hV.mem_nhds hqV))
  have hgA : ∀ x ∈ S, x ∈ V → g (A x) = x := by
    intro x hxS hxV
    have hx : x ∈ g '' O := by rw [← hS]; exact ⟨hxS, hxV⟩
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hAg y hy]
  have hqS : q ∈ S := hσ0 ▸ hev.self_of_nhds.1
  have hAqO : A q ∈ O := by
    have hq : q ∈ g '' O := by rw [← hS]; exact ⟨hqS, hqV⟩
    obtain ⟨y, hy, hyq⟩ := hq
    rw [← hyq, hAg y hy]
    exact hy
  have hcomp : σ =ᶠ[𝓝 0] fun v => g (A (σ v)) := hev.mono fun v hv => (hgA _ hv.1 hv.2).symm
  have hgd : HasFDerivAt g (fderiv ℂ g (A q)) (A (σ 0)) := by
    rw [hσ0]
    exact (hg _ hAqO).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun v => g (A (σ v))) ((fderiv ℂ g (A q)).comp (A.comp (D.comp (consZero d)))) 0 :=
    hgd.comp 0 (A.hasFDerivAt.comp 0 hσ.hasFDerivAt)
  have heq : D.comp (consZero d) = (fderiv ℂ g (A q)).comp (A.comp (D.comp (consZero d))) :=
    hσ.hasFDerivAt.unique (h2.congr_of_eventuallyEq hcomp)
  have ha : ∀ v, v 0 = 0 → A (D v) = 0 → v = 0 := by
    intro v hv0 hAv
    apply hD v hv0
    have h := congrArg (fun L : (Fin d → ℂ) →L[ℂ] Fin n → ℂ => L (Fin.tail v)) heq
    simp only [ContinuousLinearMap.comp_apply, consZero_tail v hv0, hAv, map_zero] at h
    exact h
  refine ⟨ha, ?_⟩
  have hinj : Function.Injective (A.comp (D.comp (consZero d))) := by
    intro a b hab
    simp only [ContinuousLinearMap.comp_apply] at hab
    have h0 : A (D (consZero d (a - b))) = 0 := by rw [map_sub, map_sub, map_sub, hab, sub_self]
    have h1 := ha _ (consZero_apply_zero _) h0
    exact sub_eq_zero.1 (consZero_injective (by rw [h1, map_zero]))
  let e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ) :=
    (LinearEquiv.ofInjectiveEndo ((A.comp (D.comp (consZero d))) : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
      hinj).toContinuousLinearEquiv
  have he : (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) = A.comp (D.comp (consZero d)) := by
    ext v
    rfl
  have hF : HasStrictFDerivAt (fun v => A (σ v)) (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0 := by
    rw [he]
    exact A.hasStrictFDerivAt.comp 0 hσ
  have hΦ : ⇑(hF.toOpenPartialHomeomorph (fun v => A (σ v))) = fun v => A (σ v) :=
    hF.toOpenPartialHomeomorph_coe
  refine ⟨(hF.toOpenPartialHomeomorph _).source ∩ {v | σ v ∈ S ∧ σ v ∈ V},
    inter_mem ((hF.toOpenPartialHomeomorph _).open_source.mem_nhds hF.mem_toOpenPartialHomeomorph_source) hev,
    ?_, ?_⟩
  · intro a ha' b hb' hab
    exact (hF.toOpenPartialHomeomorph _).injOn ha'.1 hb'.1 (by rw [hΦ]; exact congrArg A hab)
  · intro W' hW' hW'W
    have himg : (fun v => A (σ v)) '' W' ∈ 𝓝 (A q) := by
      have h1 : (fun v => A (σ v)) '' W' ∈ map (fun v => A (σ v)) (𝓝 0) := image_mem_map hW'
      rw [hF.map_nhds_eq_of_equiv] at h1
      simpa only [hσ0] using h1
    refine ⟨V ∩ A ⁻¹' ((fun v => A (σ v)) '' W'),
      inter_mem (hV.mem_nhds hqV) (A.continuous.continuousAt.preimage_mem_nhds himg), ?_⟩
    rintro x ⟨hxS, hxV, hxW⟩
    obtain ⟨v, hv, hvx⟩ := hxW
    have hvx' : A (σ v) = A x := hvx
    have hvW := hW'W hv
    refine ⟨v, hv, ?_⟩
    show σ v = x
    rw [← hgA _ hvW.2.1 hvW.2.2, hvx', hgA x hxS hxV]

end GoodPointBranch

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveJacobian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem NormalCurveJacobian.proof (hDVR : NormalCurvePointDVR.Statement) : NormalCurveJacobian.Statement := by
  intro σ _ I w hI hint hdim hw
  obtain ⟨hd, hdvr⟩ := hDVR σ I w hI hint hdim hw
  let : Algebra (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs (Algebra (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  have : IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs
      (IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  exact JacobianAtCurvePoint.exists_of_isDiscreteValuationRing I w hw (pointLocalRing I w)
    (by exact Ideal.Quotient.mk_surjective) (by exact Ideal.mk_ker)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveRegularPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalCurveRegularPoint

theorem fderiv_eval_single {σ : Type} [Fintype σ] [DecidableEq σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) (i : σ) :
    fderiv ℂ (fun x : σ → ℂ => eval x g) z (Pi.single i 1) = eval z (pderiv i g) := by
  induction g using MvPolynomial.induction_on generalizing z with
  | C a => simp
  | add p q hp hq =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hq' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) q z trivial).differentiableAt
    simp only [map_add (f := _)]
    rw [fderiv_fun_add hp' hq']
    simp [hp, hq]
  | mul_X p j hp =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hX : DifferentiableAt ℂ (fun x : σ → ℂ => x j) z := differentiableAt_apply j z
    simp only [eval_mul, eval_X]
    rw [fderiv_fun_mul hp' hX]
    simp [hp, Derivation.leibniz, pderiv_X, Pi.single_apply, fderiv_apply, mul_comm]
    split_ifs <;> simp

end NormalCurveRegularPoint

theorem NormalCurveRegularPoint.proof (hJ : NormalCurveJacobian.Statement) : NormalCurveRegularPoint.Statement := by
  classical
  intro σ _ I w hI hnorm hdim hw
  obtain ⟨k, f, D, hk, hfI, hlin, hD, hgen⟩ := hJ σ I w hI hnorm hdim hw
  set W : Set (σ → ℂ) := {z | eval z D ≠ 0}
  have hWo : IsOpen W := isOpen_ne_fun (continuous_eval D) continuous_const
  have hder : ∀ j, (fun i : σ => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w (Pi.single i 1)) =
      fun i => eval w (pderiv i (f j)) := fun j => funext fun i =>
    NormalCurveRegularPoint.fderiv_eval_single (f j) w i
  let Φ : ((σ → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (σ → ℂ) :=
    { toFun := fun L i => L (Pi.single i 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hlin' : LinearIndependent ℂ (fun j => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w) := by
    refine LinearIndependent.of_comp Φ ?_
    convert hlin using 1
    funext j
    exact hder j
  obtain ⟨d, A, O, V, g, hd, hO, hV, hwV, hVW, hg, hAg, hset⟩ :=
    IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.proof σ (Fin k) (fun j z => eval z (f j)) w W
      (fun j => AnalyticOnNhd.eval_mvPolynomial (f j) w trivial) (fun j => hw _ (hfI j)) hlin'
      (hWo.mem_nhds hD)
  simp only [Fintype.card_fin] at hd
  obtain rfl : d = 1 := by omega
  refine ⟨A, O, V, g, hO, hV, hwV, hg, hAg, ?_⟩
  rw [← hset]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨hzV, fun j => hz _ (hfI j)⟩
  · rintro ⟨hzV, hzf⟩
    refine ⟨fun q hq => ?_, hzV⟩
    have hspan : Ideal.span (Set.range f) ≤ RingHom.ker (eval z) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hzf j
    have h0 : eval z (D * q) = 0 := hspan (hgen q hq)
    rw [eval_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hVW hzV)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedDensityNonneg

theorem half_log_eq_phi (a : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    Real.log (‖a‖ ^ 2 + ε) / 2 = phi (![a, ((√ε : ℝ) : ℂ)] : Fin 2 → ℂ) := by
  simp only [phi, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε]
  ring

end RegularizedDensityNonneg

theorem RegDensNonneg.proof : RegDensNonneg.Statement := by
  intro n d J A u ε x s hε hs
  have han : AnalyticAt ℂ s (A *ᵥ x) := FormIntegralPositivity.analyticAt_sheet hs
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ x
    have hh : AnalyticAt ℂ (fun w => linEval u (s w)) y := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)
    let τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ) := fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]
    have hτ : AnalyticAt ℂ τ y := by
      refine analyticAt_pi_iff.2 fun i => ?_
      fin_cases i
      · simpa [τ] using hh
      · simpa [τ] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)
    have hS : sqSum (τ y) ≠ 0 := by
      have : sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε := by
        simp only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]
      rw [this]
      positivity
    have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
    have hfun : logReg u ε ∘ s = phi ∘ τ := by
      funext w
      exact RegularizedDensityNonneg.half_log_eq_phi _ hε.le
    rw [hfun]
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  · simp only [Matrix.cons_val_succ]
    have hE : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s (A *ᵥ x)) :=
      ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have e : (euclPot : (Fin n → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
      funext w; simp [euclPot, Complex.normSq_eq_norm_sq]
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ _ _ han hE, e, ReciprocityTheory.AnForm.A.hessC_sum_normSq]
    exact GradDensSheetBound.posSemidef_transpose_mul_mul_conj _ PosSemidef.one

end

end GroundTheory.Heights₂.Heights
end

