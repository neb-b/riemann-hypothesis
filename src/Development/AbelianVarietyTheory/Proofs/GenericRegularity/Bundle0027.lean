module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericFrameIntegralOffFinitelyManyFunctions
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import ReciprocityTheory.SemistableReduction.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericFrameIntegralOffFinitelyManyFunctionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFrame_integral_off_finitelyMany_functions : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (h : GenFrEx Xo c) (Z : Comp Xo c), ∃ S : Finset (Om Z), (∀ s ∈ S, s ≠ 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ ψ : Om Z →ₐ[c.F] T.Fr, (∀ s ∈ S, vV T.V (ψ s) = 0) → ∀ z : FrPt Xo c T.Fr, FrMap ψ (genFr h Z) z → Integral T io z := by
  first | exact @GlobalTheory.Reg.GenInt.genFr_integral | exact GlobalTheory.Reg.GenInt.genFr_integral | (intros; apply GlobalTheory.Reg.GenInt.genFr_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralElementsGenericLinearSectionGaussPoint
section
namespace GlobalTheory.GaussSection

open MvPolynomial

theorem eval_mem_closure {Ω U σ : Type} [Field Ω] [Field U] (f : Ω →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (t : σ → U) (S : Set U)
    (hS : ∀ s, t s ∈ S) (p : MvPolynomial σ Ω) (hp : ∀ α, v (f (p.coeff α)) ≤ 1) :
    eval₂ f t p ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ S) := by
  rw [MvPolynomial.eval₂_eq]
  apply sum_mem
  intro α _
  apply mul_mem
  · exact Subring.subset_closure (Or.inl ⟨Set.mem_range_self _, hp α⟩)
  · apply prod_mem
    intro i _
    exact pow_mem (Subring.subset_closure (Set.mem_union_right _ (hS i))) _

theorem exists_normalise {Ω U σ : Type} [Field Ω] [Field U] (f : Ω →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (p : MvPolynomial σ Ω) (hp : p ≠ 0) :
    ∃ (c : Ω) (q : MvPolynomial σ Ω), c ≠ 0 ∧ p = C c * q ∧ (∀ α, v (f (q.coeff α)) ≤ 1) ∧
      ∃ α, v (f (q.coeff α)) = 1 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hp
  obtain ⟨α₀, hα₀, hmax⟩ := p.support.exists_max_image (fun α => v (f (p.coeff α)))
    ⟨d, MvPolynomial.mem_support_iff.mpr hd⟩
  have hc : p.coeff α₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hα₀
  have hfc : 0 < v (f (p.coeff α₀)) := by
    rw [zero_lt_iff, Ne, Valuation.zero_iff, map_eq_zero]
    exact hc
  refine ⟨p.coeff α₀, C (p.coeff α₀)⁻¹ * p, hc, ?_, fun α => ?_, α₀, ?_⟩
  · rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  · rw [coeff_C_mul, map_mul, map_mul, map_inv₀, map_inv₀, inv_mul_le_iff₀ hfc, mul_one]
    by_cases hα : α ∈ p.support
    · exact hmax α hα
    · rw [MvPolynomial.notMem_support_iff.mp hα, map_zero, map_zero]
      exact zero_le
  · rw [coeff_C_mul, inv_mul_cancel₀ hc, map_one, map_one]

theorem quotient_of_gauss {Ω U σ : Type} [Field Ω] [Field U] (f : Ω →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (t : σ → U) (S : Set U)
    (hS : ∀ s, t s ∈ S) (hS' : ∀ u ∈ S, ∃ p : MvPolynomial σ Ω, eval₂ f t p = u)
    (hG : ∀ p : MvPolynomial σ Ω, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) →
      v (eval₂ f t p) = 1)
    (g : U) (hg : g ∈ Subfield.closure (Set.range f ∪ S)) (hv : v g ≤ 1) :
    ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ S),
      ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ S), v d = 1 ∧ g * d = a := by
  classical
  by_cases hg0 : g = 0
  · exact ⟨0, zero_mem _, 1, one_mem _, map_one v, by rw [hg0, zero_mul]⟩
  have hle : Subring.closure (Set.range f ∪ S) ≤ (MvPolynomial.eval₂Hom f t).range := by
    rw [Subring.closure_le]
    rintro u (⟨c, rfl⟩ | hu)
    · exact ⟨C c, by simp⟩
    · obtain ⟨p, hp⟩ := hS' u hu
      exact ⟨p, hp⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hg
  obtain ⟨P, rfl⟩ := hle hy
  obtain ⟨Q, rfl⟩ := hle hz
  simp only [MvPolynomial.coe_eval₂Hom] at hg0 hv ⊢
  have hz0 : eval₂ f t Q ≠ 0 := fun h => hg0 (by rw [h, div_zero])
  have hy0 : eval₂ f t P ≠ 0 := fun h => hg0 (by rw [h, zero_div])
  have hQ : Q ≠ 0 := by
    rintro rfl
    exact hz0 (eval₂_zero _ _)
  have hP : P ≠ 0 := by
    rintro rfl
    exact hy0 (eval₂_zero _ _)
  obtain ⟨c, Q', hc, rfl, hQi, hQu⟩ := exists_normalise f v Q hQ
  obtain ⟨c', P', -, rfl, hPi, hPu⟩ := exists_normalise f v P hP
  have hdQ := hG Q' hQi hQu
  have hdP := hG P' hPi hPu
  have hfc : f c ≠ 0 := (map_ne_zero f).mpr hc
  have hQ0 : eval₂ f t Q' ≠ 0 := by
    intro h
    rw [h, map_zero] at hdQ
    exact zero_ne_one hdQ
  simp only [eval₂_mul, eval₂_C] at hv ⊢
  refine ⟨f (c' / c) * eval₂ f t P',
    mul_mem (Subring.subset_closure (Or.inl ⟨Set.mem_range_self _, ?_⟩))
      (eval_mem_closure f v t S hS P' hPi),
    eval₂ f t Q', eval_mem_closure f v t S hS Q' hQi, hdQ, ?_⟩
  · have : v (f (c' / c)) = v (f c' * eval₂ f t P' / (f c * eval₂ f t Q')) := by
      rw [map_div₀, map_div₀, map_div₀, map_mul, map_mul, hdP, hdQ, mul_one, mul_one]
    rw [this]
    exact hv
  · rw [map_div₀]
    field_simp

private theorem algebraicIndependent_congr_algebra {ι R S : Type*} [CommRing R] [CommRing S] (x : ι → S)
    (A₁ A₂ : Algebra R S) (h : ∀ r, (letI := A₁; algebraMap R S r) = (letI := A₂; algebraMap R S r))
    (hx : letI := A₁; AlgebraicIndependent R x) : letI := A₂; AlgebraicIndependent R x := by
  obtain rfl := Algebra.algebra_ext A₁ A₂ h
  exact hx

theorem indep_comp {K Ω U τ : Type} [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U]
    (v : Valuation U (WithZero (Multiplicative ℤ))) (s : τ → U)
    (hs : ∀ j, s j ∈ v.valuationSubring)
    (hG : ∀ p : MvPolynomial τ K, (∀ α, v (algebraMap Ω U (algebraMap K Ω (p.coeff α))) ≤ 1) →
      (∃ α, v (algebraMap Ω U (algebraMap K Ω (p.coeff α))) = 1) →
      v (eval₂ ((algebraMap Ω U).comp (algebraMap K Ω)) s p) = 1) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (v.valuationSubring.comap (algebraMap Ω U))
      (algebraMap K Ω)
    letI : Algebra (IsLocalRing.ResidueField
        ((v.valuationSubring.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
        (IsLocalRing.ResidueField v.valuationSubring) :=
      ((algebraMap _ (IsLocalRing.ResidueField v.valuationSubring)).comp
        (algebraMap _ (IsLocalRing.ResidueField
          (v.valuationSubring.comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent
      (IsLocalRing.ResidueField
        ((v.valuationSubring.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => IsLocalRing.residue v.valuationSubring ⟨s j, hs j⟩) := by
  refine algebraicIndependent_congr_algebra _
    (ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring ((algebraMap Ω U).comp (algebraMap K Ω))) _ ?_
    ((GlobalTheory.algebraicIndependent_residue_iff_gauss K U _ v τ s hs).mpr hG)
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  rfl

theorem integral_elements (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω]
    (f : Ω →+* U) (D N : ℕ) (hD : Algebra.trdeg K Ω = D)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (s : Fin (D + 1) × Fin N → U)
    (a : Fin N → Ω) (ha : ∃ k, a k ≠ 0)
    (hrel : ∀ i : Fin D, ∑ k, s (i.succ, k) * f (a k) = 0) (hs : ∀ p, v (s p) ≤ 1)
    (hG : ∀ p : MvPolynomial (Fin (D + 1) × Fin N) K,
      (∀ α, v (f (algebraMap K Ω (p.coeff α))) ≤ 1) →
      (∃ α, v (f (algebraMap K Ω (p.coeff α))) = 1) →
      v (MvPolynomial.eval₂ (f.comp (algebraMap K Ω)) s p) = 1) :
    ∀ g ∈ Subfield.closure (Set.range f ∪ Set.range s), v g ≤ 1 →
      ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range s),
        ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range s),
          v d = 1 ∧ g * d = a := by
  intro g hg hv
  classical
  let _ : Algebra Ω U := f.toAlgebra
  obtain ⟨k₁, hk₁⟩ := ha
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ (fun k => v (f (a k)))
    ⟨k₁, Finset.mem_univ _⟩
  have ha₀ : a k₀ ≠ 0 := by
    intro h0
    have h := hk₀ k₁ (Finset.mem_univ _)
    rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff, map_eq_zero] at h
    exact hk₁ h
  have hfa : f (a k₀) ≠ 0 := (map_ne_zero f).mpr ha₀
  have hva : 0 < v (f (a k₀)) := by
    rw [zero_lt_iff, Ne, Valuation.zero_iff]
    exact hfa
  have hsV : ∀ j, s j ∈ v.valuationSubring := hs
  set t : Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀}) → U :=
    Sum.elim (fun k => s (0, k)) (fun q => s (q.1.succ, q.2.1)) with ht_def
  have ht : ∀ x, t x ∈ v.valuationSubring := by
    rintro (k | q)
    · exact hsV _
    · exact hsV _
  have hcoefX : ∀ (x : Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) α,
      (X x : MvPolynomial _ Ω).coeff α ∈ v.valuationSubring.comap (algebraMap Ω U) := by
    intro x α
    rw [coeff_X]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hex : ∀ j : Fin (D + 1) × Fin N, ∃ q : MvPolynomial (Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) Ω,
      (∀ α, q.coeff α ∈ v.valuationSubring.comap (algebraMap Ω U)) ∧ MvPolynomial.aeval t q = s j := by
    rintro ⟨i, k⟩
    obtain rfl | ⟨i', rfl⟩ := Fin.eq_zero_or_eq_succ i
    · exact ⟨X (Sum.inl k), hcoefX _, by rw [aeval_X]; rfl⟩
    by_cases hk : k = k₀
    · rw [hk]
      refine ⟨∑ q : {k : Fin N // k ≠ k₀}, C (-(a q / a k₀)) * X (Sum.inr (i', q)), fun α => ?_, ?_⟩
      · rw [coeff_sum]
        refine sum_mem fun q _ => ?_
        rw [coeff_C_mul]
        refine mul_mem (neg_mem ?_) (hcoefX _ _)
        rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
          RingHom.algebraMap_toAlgebra, map_div₀, map_div₀, div_le_one₀ hva]
        exact hk₀ q (Finset.mem_univ _)
      · have hr := hrel i'
        rw [Fintype.sum_eq_add_sum_subtype_ne _ k₀] at hr
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, aeval_C, aeval_X, RingHom.algebraMap_toAlgebra]
        have key : ∑ q : {k : Fin N // k ≠ k₀}, f (-(a q / a k₀)) * t (Sum.inr (i', q)) =
            -(∑ q : {k : Fin N // k ≠ k₀}, s (i'.succ, q.1) * f (a q)) / f (a k₀) := by
          rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_neg, map_div₀]
          simp only [ht_def, Sum.elim_inr]
          ring
        rw [key, div_eq_iff hfa]
        linear_combination -hr
    · exact ⟨X (Sum.inr (i', ⟨k, hk⟩)), hcoefX _, by rw [aeval_X]; rfl⟩
  choose P hPc hPe using hex
  have hcard : Fintype.card (Fin (D + 1) × Fin N) =
      Fintype.card (Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) + D := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by have := k₀.pos; omega⟩
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype_compl,
      Fintype.card_unique]
    simp only [Nat.add_sub_cancel]
    ring
  have hind := indep_comp (K := K) (Ω := Ω) (U := U) v s hsV hG
  obtain ⟨-, -, h3⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K Ω U D hD
    (Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) t v.valuationSubring ht
    (Fin (D + 1) × Fin N) (fun j => ⟨s j, hsV j⟩) P hPc hcard hPe hind
  have hGΩ := (GlobalTheory.algebraicIndependent_residue_iff_gauss Ω U f v _ t ht).mp h3
  refine quotient_of_gauss f v t (Set.range s) ?_ ?_ hGΩ g hg hv
  · rintro (k | q)
    · exact ⟨(0, k), rfl⟩
    · exact ⟨(q.1.succ, q.2.1), rfl⟩
  · rintro u ⟨j, rfl⟩
    exact ⟨P j, (MvPolynomial.aeval_def _ _).symm.trans (hPe j)⟩

end GlobalTheory.GaussSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SubalgebraEqIntegralClosureOfValuesResidues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.LocStructNak

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

theorem dvd_of_vL_le [∀ ζ : Pts O A, IsDVRAt ζ] (c b : ↥(As O A))
    (h : ∀ ζ : Pts O A, vL ζ c ≤ vL ζ b) : c ∣ b := by
  have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) b ∈
      Ideal.map (algebraMap ↥(As O A) (Loc ζ)) (Ideal.span {c}) := by
    intro ζ
    have h1 := h ζ
    rw [vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact h1
  exact Ideal.mem_span_singleton.1 (Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩))


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem exists_residue (C : Subalgebra O ↥(As O A)) (ζ : Pts O A) (b c d : ↥(As O A))
    (hc : c ∈ C) (hd : d ∈ C) (hd0 : d ∉ ζ.asIdeal) (h : d * b - c ∈ ζ.asIdeal) :
    ∃ c' ∈ C, b - c' ∈ ζ.asIdeal := by
  haveI : Algebra.IsIntegral ↥C ↥(As O A) := Algebra.IsIntegral.tower_top O
  haveI := ζ.isMaximal
  have hmax : (ζ.asIdeal.comap (algebraMap ↥C ↥(As O A))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal ζ.asIdeal
  obtain ⟨y, z, hz, hyz⟩ := hmax.exists_inv (x := ⟨d, hd⟩) (by simpa [Ideal.mem_comap] using hd0)
  have hz' : (z : ↥(As O A)) ∈ ζ.asIdeal := hz
  have hyz' : (y : ↥(As O A)) * d + z = 1 := congrArg Subtype.val hyz
  refine ⟨y * c, C.mul_mem y.2 hc, ?_⟩
  have e : b - y * c = y * (d * b - c) + b * z := by
    linear_combination (-b) * hyz'
  rw [e]
  exact ζ.asIdeal.add_mem (ζ.asIdeal.mul_mem_left _ h) (ζ.asIdeal.mul_mem_left _ hz')

theorem exists_approx [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)] (C : Subalgebra O ↥(As O A))
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, vL ζ c = (n ζ : ℕ∞))
    (hres : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C, b - c ∈ ζ.asIdeal)
    (n : Pts O A → ℕ) (b : ↥(As O A)) : ∃ c ∈ C, ∀ ζ, (n ζ : ℕ∞) ≤ vL ζ (b - c) := by
  classical
  letI := Fintype.ofFinite (Pts O A)
  obtain ⟨N, hN⟩ : ∃ N, ∑ ζ, n ζ = N := ⟨_, rfl⟩
  induction N generalizing n with
  | zero =>
    refine ⟨0, C.zero_mem, fun ζ => ?_⟩
    rw [(Finset.sum_eq_zero_iff.1 hN) ζ (Finset.mem_univ _)]
    simp
  | succ N ih =>
    obtain ⟨ζ₀, -, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := n)
      (by rw [hN]; omega)
    have hsum : ∑ ζ, Function.update n ζ₀ (n ζ₀ - 1) ζ = N := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ζ₀), ← Finset.sdiff_singleton_eq_erase] at hN
      omega
    obtain ⟨c₁, hc₁, h₁⟩ := ih _ hsum
    obtain ⟨c, hc, hv⟩ := hval (Function.update n ζ₀ (n ζ₀ - 1))
    obtain ⟨b', hb'⟩ := dvd_of_vL_le c (b - c₁) (fun ζ => by rw [hv]; exact h₁ ζ)
    obtain ⟨c', hc', hm⟩ := hres ζ₀ b'
    refine ⟨c₁ + c * c', C.add_mem hc₁ (C.mul_mem hc hc'), fun ζ => ?_⟩
    have e : b - (c₁ + c * c') = c * (b' - c') := by linear_combination hb'
    rw [e, vL_mul, hv]
    by_cases hζ : ζ = ζ₀
    · subst hζ
      have h1 : 1 ≤ vL ζ (b' - c') := by
        rw [Order.one_le_iff_ne_zero, Ne, vL_eq_zero_iff]
        exact not_not.2 hm
      rw [Function.update_self]
      calc (n ζ : ℕ∞) = ((n ζ - 1 : ℕ) : ℕ∞) + 1 := by
            have : n ζ = (n ζ - 1) + 1 := by omega
            conv_lhs => rw [this]
            push_cast
            rfl
        _ ≤ _ := add_le_add le_rfl h1
    · rw [Function.update_of_ne hζ]
      exact le_self_add

theorem as_le_of_val_of_residue (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ϖ : O) (hU : IsUnif A ϖ) [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)]
    [Module.Finite O ↥(As O A)] (C : Subalgebra O A) (hC : C ≤ As O A)
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, ord ϖ ζ c = (((n ζ : ℕ) : ℤ) : WithTop ℤ))
    (hres : ∀ (ζ : Pts O A), ∀ b ∈ As O A, ∃ c ∈ C, ∃ d ∈ C,
      ord ϖ ζ d = 0 ∧ 0 < ord ϖ ζ (d * b - c)) : As O A ≤ C := by
  set C' : Subalgebra O ↥(As O A) := C.comap (As O A).val with hC'
  have hinj : Function.Injective (ENat.map (Nat.cast : ℕ → ℤ)) :=
    (ENat.strictMono_map_iff.2 Nat.strictMono_cast).injective
  have hzero : ∀ (ζ : Pts O A) (a : ↥(As O A)), ord ϖ ζ (a : A) = 0 ↔ a ∉ ζ.asIdeal := by
    intro ζ a
    rw [ord_of_mem ζ hU a.2, ← vL_eq_zero_iff]
    constructor
    · intro h
      exact hinj h
    · intro h
      change (vL ζ a).map (Nat.cast : ℕ → ℤ) = 0
      rw [h]
      rfl
  have hval' : ∀ n : Pts O A → ℕ, ∃ c ∈ C', ∀ ζ, vL ζ c = (n ζ : ℕ∞) := by
    intro n
    obtain ⟨c, hc, h⟩ := hval n
    refine ⟨⟨c, hC hc⟩, hc, fun ζ => hinj ?_⟩
    rw [← ord_of_mem ζ hU (hC hc), h ζ, ENat.map_natCast]
  have hres' : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C', b - c ∈ ζ.asIdeal := by
    intro ζ b
    obtain ⟨c, hc, d, hd, hd0, h⟩ := hres ζ b b.2
    refine exists_residue C' ζ b ⟨c, hC hc⟩ ⟨d, hC hd⟩ hc hd ((hzero ζ ⟨d, hC hd⟩).1 hd0) ?_
    by_contra hn
    exact h.ne' ((hzero ζ _).2 hn)
  have key : (⊤ : Submodule O ↥(As O A)) ≤ Subalgebra.toSubmodule C' := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    intro b _
    obtain ⟨c, hc, h⟩ := exists_approx C' hval' hres' (ep ϖ) b
    obtain ⟨b', hb'⟩ := dvd_of_vL_le (algebraMap O ↥(As O A) ϖ) (b - c)
      (fun ζ => by rw [← coe_ep ζ hU]; exact h ζ)
    have e : b = c + ϖ • b' := by rw [Algebra.smul_def, ← hb']; ring
    rw [e]
    exact Submodule.add_mem_sup hc (Submodule.smul_mem_smul
      ((IsLocalRing.mem_maximalIdeal ϖ).2 hU.irreducible.not_isUnit) Submodule.mem_top)
  intro x hx
  exact key (Submodule.mem_top (x := (⟨x, hx⟩ : ↥(As O A))))

end GlobalTheory.LocStructNak
end

