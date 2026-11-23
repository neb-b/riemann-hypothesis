module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0076

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullSectionIntegral

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_scale_of_isMultiHomog (y : (Σ k, ι k) → Ω) (t : K → Ω) {f : MRing ι} {e : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f e) :
    aeval (fun p => t p.1 * y p) f = (∏ k, t k ^ e k) * aeval y f := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hpow : ∏ p : Σ k, ι k, t p.1 ^ d p = ∏ k, t k ^ e k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ d ⟨k, i⟩ = t k ^ e k
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  have hsplit : ∏ p, (t p.1 * y p) ^ d p = (∏ p : Σ k, ι k, t p.1 ^ d p) * ∏ p, y p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => mul_pow _ _ _
  rw [hsplit, hpow]
  ring


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_mConeMap (y : (Σ k, ι k) → Ω) (t : K → Ω) (f : MRing ι) :
    eval t (mConeMap y f) = aeval (fun p => t p.1 * y p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    simp [mConeMap, mul_comm]

theorem aeval_scale_eq_zero {y : (Σ k, ι k) → Ω} (t : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p => t p.1 * y p) f = 0 := by
  rw [← eval_mConeMap, show mConeMap y f = 0 from hf, map_zero]

theorem exists_sum_eq_one [CharZero Ω] (P : Ideal (MRing ι)) (y' : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y' ⟨k, c k⟩ = 1) (hP : ∀ f ∈ P, aeval y' f = 0) {n : ℕ} (L : Fin n → MRing ι)
    (hL : ∀ z ∈ mcPts P, ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ b : Fin n → MvPolynomial (Σ k, ι k) ℚ, ∑ i, aeval y' (b i) * aeval y' (L i) = 1 := by
  classical
  set φ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval y'
  let Lq : Fin n → MvPolynomial (Σ k, ι k) ℚ := fun i => map (algebraMap ℤ ℚ) (L i)
  have hLq : ∀ i, φ (Lq i) = aeval y' (L i) := fun i => aeval_map_algebraMap ℚ y' (L i)
  let J : Ideal (MvPolynomial (Σ k, ι k) ℚ) := RingHom.ker φ ⊔ Ideal.span (Set.range Lq)
  by_cases hJ : J = ⊤
  · have h1 : (1 : MvPolynomial (Σ k, ι k) ℚ) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨β, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hb
    refine ⟨β, ?_⟩
    have := congrArg φ hab
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), show φ a = 0 from ha, zero_add, map_sum, map_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hLq]
  · exfalso
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
    let := Ideal.Quotient.field m
    have : Algebra.FiniteType ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m)
        (Ideal.Quotient.mkₐ_surjective ℚ m)
    have := finite_of_finite_type_of_isJacobsonRing ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m)
    let ψ : (MvPolynomial (Σ k, ι k) ℚ ⧸ m) →ₐ[ℚ] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    let z : (Σ k, ι k) → ℂ := fun p => ψ (Ideal.Quotient.mk m (X p))
    have hz : ∀ g : MvPolynomial (Σ k, ι k) ℚ, ψ (Ideal.Quotient.mk m g) = aeval z g := by
      intro g
      have : (ψ.comp (Ideal.Quotient.mkₐ ℚ m)) = aeval z := by
        ext p; simp [z]
      exact congrArg (fun F => F g) this
    have hzZ : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) =
        ψ (Ideal.Quotient.mk m (map (algebraMap ℤ ℚ) f)) := by
      intro f
      rw [hz, aeval_map_algebraMap, eval_map, aeval_def, algebraMap_int_eq]
    have hker : ∀ g ∈ RingHom.ker φ, Ideal.Quotient.mk m g = 0 := fun g hg =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_left hg))
    have hzP : z ∈ mcPts P := by
      refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
      · have hX : (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker φ := by
          simp [RingHom.mem_ker, φ, hc k]
        have := hker _ hX
        rw [map_sub, map_one, sub_eq_zero] at this
        simp [z, this]
      · have hφf : φ (map (algebraMap ℤ ℚ) f) = 0 := by
          rw [show φ (map (algebraMap ℤ ℚ) f) = aeval y' f from aeval_map_algebraMap ℚ y' f]
          exact hP f hf
        rw [hzZ, hker _ (RingHom.mem_ker.mpr hφf), map_zero]
    obtain ⟨j, hj⟩ := hL z hzP
    apply hj
    rw [hzZ, Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_right
      (Ideal.subset_span ⟨j, rfl⟩))), map_zero]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_mem_of_forall [CharZero Ω] (V : Subring Ω) (hQ : ∀ r : ℚ, algebraMap ℚ Ω r ∈ V)
    (y' : (Σ k, ι k) → Ω) (hy : ∀ p, y' p ∈ V) (b : MvPolynomial (Σ k, ι k) ℚ) : aeval y' b ∈ V := by
  induction b using MvPolynomial.induction_on with
  | C a => simpa using hQ a
  | add p q hp hq => rw [map_add (f := _)]; exact V.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact V.mul_mem hp (hy i)

theorem proof : PullSectionIntegral.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hV _ he hL hzero τ s hs j hj
  classical
  set A := Algebra.adjoin ℚ (Set.range fun i => aeval y (L i) / aeval y (L j))
  set R := (integralClosure A Ω).toSubring
  have : IsIntegrallyClosedIn R Ω := inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  show s / aeval y (L j) ^ (q * τ) ∈ R
  by_contra hnot
  obtain ⟨V, hRV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hnot
  have hAV : ∀ x ∈ A, x ∈ V := fun x hx =>
    hRV (isIntegral_algebraMap (R := A) (A := Ω) (x := ⟨x, hx⟩))
  have hQ : ∀ r : ℚ, algebraMap ℚ Ω r ∈ V.toSubring := fun r => hAV _ (A.algebraMap_mem r)

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  have hmax : ∀ k, ∃ c : ι k, ∀ i, V.valuation (y ⟨k, i⟩) ≤ V.valuation (y ⟨k, c⟩) := by
    intro k
    obtain ⟨i0, -⟩ := hrel k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (y ⟨k, i⟩))
      ⟨i0, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    obtain ⟨i0, hi0⟩ := hrel k
    have := hc k i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  have hratio : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ V := by
    intro p
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hc p.1 p.2) zero_le

  set M : Ω := ∏ k, y ⟨k, c k⟩ ^ e k
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  have hchart : (chartRingZ y c : Set Ω) ⊆ V := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hratio p
    | algebraMap r => simp
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  have : IsIntegrallyClosedIn V.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn V Ω)
  have hxV : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) ∈ V.toSubring :=
    (Subring.integralClosure_le_iff (R := chartRingZ y c) (T := V.toSubring)).mpr
      (fun r => hchart r.2) (hs c hc0)
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) = (M ^ (q * τ))⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) = -((e k * (q * τ) : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, pow_mul]
  rw [hprod] at hxV

  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have hP' : ∀ f ∈ mCoordIdeal y, aeval (fun p => t p.1 * y p) f = 0 := fun f hf =>
    aeval_scale_eq_zero t hf
  obtain ⟨b, hb⟩ := exists_sum_eq_one (mCoordIdeal y) (fun p => t p.1 * y p) c
    (fun k => inv_mul_cancel₀ (hc0 k)) hP' L hzero
  have hLt : ∀ i, aeval (fun p => t p.1 * y p) (L i) = M⁻¹ * aeval y (L i) := by
    intro i
    rw [aeval_scale_of_isMultiHomog y t (hL i)]
    simp [t, M, Finset.prod_inv_distrib, inv_pow]
  have hratio' : ∀ p : Σ k, ι k, t p.1 * y p ∈ V := fun p => by
    simpa [t, div_eq_inv_mul] using hratio p
  have hMV : M / aeval y (L j) ∈ V := by
    have hsum : M / aeval y (L j) =
        ∑ i, aeval (fun p => t p.1 * y p) (b i) * (aeval y (L i) / aeval y (L j)) := by
      have := congrArg (fun w => w * (M / aeval y (L j))) hb
      simp only [one_mul, Finset.sum_mul, hLt] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [hsum]
    refine sum_mem fun i _ => mul_mem ?_ ?_
    · exact aeval_mem_of_forall V.toSubring hQ _ (fun p => hratio' p) (b i)
    · exact hAV _ (Algebra.subset_adjoin ⟨i, rfl⟩)
  apply htV
  have hMn : M ^ (q * τ) ≠ 0 := pow_ne_zero _ hM0
  have : s / aeval y (L j) ^ (q * τ) = s * (M ^ (q * τ))⁻¹ * (M / aeval y (L j)) ^ (q * τ) := by
    rw [div_pow, mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hMn, mul_one_div]
  rw [this]
  exact mul_mem hxV (pow_mem hMV _)

end PullSectionIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SecMRankBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem finite_secM (y : (Σ k, ι k) → Ω) (d : K → ℕ) : Module.Finite ℤ (secM y d) := by
  have h := SectionLatticeFinite.secM_fg y d
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (secM y d), ← Submodule.fg_iff_addSubgroup_fg] at h
  exact Module.Finite.iff_fg.mpr h


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Ω} {g : MRing ι} (hg : g ∈ mCoordIdeal y) :
    aeval y g = 0 := by
  have hext : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp (mConeMap y) = aeval y :=
    MvPolynomial.algHom_ext fun p => by simp [mConeMap]
  have h0 : mConeMap y g = 0 := hg
  rw [← hext, AlgHom.comp_apply, h0, map_zero]

variable [DecidableEq K]

theorem finrank_secM_le [CharZero Ω] (y : (Σ k, ι k) → Ω) (d : K → ℕ) :
    Module.finrank ℤ (secM y d) ≤
      Module.finrank ℚ (NumbersDVR.gradedPiece (KH.genIdeal y) d) := by
  have hI : ∀ f ∈ KH.genIdeal y, aeval y f = 0 := by
    have hle : KH.genIdeal y ≤ RingHom.ker (aeval y : MRingOver ℚ ι →ₐ[ℚ] Ω) := by
      unfold KH.genIdeal
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]
      change aeval y (map (algebraMap ℤ ℚ) g) = 0
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_mem hg
    exact fun f hf => hle hf
  let ψ : (MRingOver ℚ ι ⧸ KH.genIdeal y) →ₗ[ℚ] Ω :=
    (Ideal.Quotient.liftₐ (KH.genIdeal y) (aeval y) hI).toLinearMap
  let V := NumbersDVR.gradedPiece (KH.genIdeal y) d
  have : FiniteDimensional ℚ V := (FieldNumbers.GradedFinite.proof ℚ K ι (KH.genIdeal y) d).1
  let R : Submodule ℚ Ω := V.map ψ
  have : FiniteDimensional ℚ R := Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp inferInstance).map ψ)
  have hsub : ∀ s ∈ secM y d, s ∈ R := by
    intro s hs
    have hspan : Submodule.span ℤ {s | ∃ g : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ aeval y g = s} ≤
        R.restrictScalars ℤ := by
      rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨Ideal.Quotient.mk _ (map (Int.castRingHom ℚ) g), ⟨map (Int.castRingHom ℚ) g, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
        exact (Bridge.isMultiHomog_iff _ _).mpr fun m hm k => hg m (support_map_subset _ _ hm) k
      · change aeval y (map (Int.castRingHom ℚ) g) = aeval y g
        rw [← algebraMap_int_eq, aeval_map_algebraMap]
    exact hspan hs
  have := finite_secM y d
  have : Module.IsTorsionFree ℤ (secM y d) :=
    Function.Injective.moduleIsTorsionFree (secM y d).subtype Subtype.val_injective (fun _ _ => rfl)
  let bs := Module.Free.chooseBasis ℤ (secM y d)
  let v : Module.Free.ChooseBasisIndex ℤ (secM y d) → Ω := fun i => (bs i : Ω)
  have hliZ : LinearIndependent ℤ v :=
    bs.linearIndependent.map' (secM y d).subtype.toIntLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  rw [Module.finrank_eq_card_chooseBasisIndex, ← finrank_span_eq_card hliQ]
  calc Module.finrank ℚ (Submodule.span ℚ (Set.range v)) ≤ Module.finrank ℚ R :=
        Submodule.finrank_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => hsub _ (bs i).2))
    _ ≤ Module.finrank ℚ V := Submodule.finrank_map_le ψ V

theorem proof (h : GenericFibreVar.Statement) : SecMRankBound.Statement := by
  intro K _ ι _ Ω _ y D b hvar hb
  classical

  have hchar : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simp [mCoordIdeal, RingHom.mem_ker, mConeMap]
      rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hvar.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  refine ⟨fun m => finite_secM y _, ?_⟩

  obtain ⟨⟨hprime, hhom, -⟩, hdim⟩ := h K ι Ω y D hvar
  have hlt : ringKrullDim (MRingOver ℚ ι ⧸ KH.genIdeal y) <
      (((D + 1) + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (by omega : D + Fintype.card K < D + 1 + Fintype.card K)
  have hdeg := NumbersDVR.HilbDegBound.full ℚ K ι (D + 1) (KH.genIdeal y) hprime
    ((Bridge.isMultiHomogIdeal_iff _).mpr hhom) hlt
  obtain ⟨a₀, C, hC⟩ := DegLTGrowth.proof K (D + 1) _ hdeg
  have hexp : ((D + 1 : ℕ) : ℝ) - 1 = ((D : ℕ) : ℝ) := by push_cast; ring

  have hrank : ∀ m : ℕ, (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤
      |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := by
    intro m
    have e := (FieldNumbers.GradedFinite.proof ℚ K ι (KH.genIdeal y) (fun k => m * b k)).2
    have hle := finrank_secM_le y (fun k => m * b k)
    calc (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ)
        ≤ (Module.finrank ℚ (NumbersDVR.gradedPiece (KH.genIdeal y) (fun k => m * b k)) : ℝ) := by
          exact_mod_cast hle
      _ = |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := by
          rw [e]; simp
  set B : ℝ := ∑ k, (b k : ℝ) with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => by positivity
  set M0 : ℝ := ∑ j ∈ Finset.range a₀, (Module.finrank ℤ (secM y (fun k => j * b k)) : ℝ) with hM0def
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg fun j _ => by positivity
  have hC1 : 0 ≤ max C 0 * (B + 1) ^ D := by positivity
  refine ⟨max C 0 * (B + 1) ^ D + M0, by positivity, fun m => ?_⟩
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have hpow1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ D := one_le_pow₀ (by linarith)
  rcases lt_or_ge m a₀ with hm | hm
  ·
    have h1 : (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤ M0 :=
      Finset.single_le_sum (f := fun j => (Module.finrank ℤ (secM y (fun k => j * b k)) : ℝ))
        (fun j _ => by positivity) (Finset.mem_range.mpr hm)
    nlinarith
  ·
    have hg := hC (fun k => m * b k) (fun k => le_trans hm (Nat.le_mul_of_pos_right m (hb k)))
    rw [hexp, Real.rpow_natCast] at hg
    have hsum : (∑ k, (((m * b k : ℕ)) : ℝ)) = m * B := by
      rw [hBdef, Finset.mul_sum]; push_cast; rfl
    have hX : (m : ℝ) * B + 1 ≤ (B + 1) * ((m : ℝ) + 1) := by nlinarith
    have hXpow : ((m : ℝ) * B + 1) ^ D ≤ ((B + 1) * ((m : ℝ) + 1)) ^ D :=
      pow_le_pow_left₀ (by positivity) hX D
    calc (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ)
        ≤ |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := hrank m
      _ ≤ C * ((∑ k, (((m * b k : ℕ)) : ℝ)) + 1) ^ D := hg
      _ = C * ((m : ℝ) * B + 1) ^ D := by rw [hsum]
      _ ≤ max C 0 * ((m : ℝ) * B + 1) ^ D :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((B + 1) * ((m : ℝ) + 1)) ^ D :=
          mul_le_mul_of_nonneg_left hXpow (le_max_right _ _)
      _ = max C 0 * (B + 1) ^ D * ((m : ℝ) + 1) ^ D := by rw [mul_pow]; ring
      _ ≤ (max C 0 * (B + 1) ^ D + M0) * ((m : ℝ) + 1) ^ D := by nlinarith

theorem full : SecMRankBound.Statement := proof GenericFibreVar.proof

end SecMRankBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjFrameGraphChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameGraph

variable {κ : Type} {D : ℕ}

theorem linForm_projMat [Fintype κ] (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [ReciprocityTheory.ChartRestriction.G.AI.I4.linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem graphIdeal_isPrime {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) [P.IsPrime] (g : (Σ k, ι₂ k) → MRing ι) : (graphIdeal P g).IsPrime :=
  RingHom.ker_isPrime _

variable {Ω : Type} [Field Ω]

theorem frame_ne_zero {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hF : IsProjFrame x e) (k : Fin (D + 1)) :
    x (e k) ≠ 0 := by
  intro h
  have hX : (X k : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h]
  rw [hF.free, Ideal.mem_bot] at hX
  exact X_ne_zero k hX

theorem genFibre_x'_ne_zero {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    G.x' ⟨Sum.inl (), j⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl (), j⟩ : MRing (Sum.elim (GlobalTheory κ) ι₂)) ∈ graphIdeal (coordIdeal ℤ x) g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  have h2 : (X ⟨(), j⟩ : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact MvPolynomial.C_eq_zero.1 h1
  rw [coordIdeal, RingHom.mem_ker] at h2
  simp [coneMap] at h2
  exact hj h2

def fibreChart {K₂ : Type} {ι₂ : K₂ → Type} (j : κ) :
    (k : FibreBlock (Sum.inr : K₂ → Unit ⊕ K₂)) → fibreIdx (Sum.elim (GlobalTheory κ) ι₂) Sum.inr k
  | ⟨Sum.inl _, _⟩ => j
  | ⟨Sum.inr k, h⟩ => absurd ⟨k, rfl⟩ h

theorem isChart_fibreChart {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) (fibreChart (ι₂ := ι₂) j) := by
  rintro ⟨(u | k), h⟩
  · cases u
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact genFibre_x'_ne_zero G j hj
  · exact absurd ⟨k, rfl⟩ h

end ProjFrameGraph

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCharpolyRootLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def CharpolyRootLift.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω) (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ),
      l j ≠ 0 → c 0 = 1 → (∀ i ≤ Module.finrank P Ω, (c i).IsHomogeneous (i * m)) →
      (LinearMap.charpoly (Algebra.lmul P Ω (u / l j ^ m))).map (algebraMap P Ω) =
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
      ∀ (a : Fin (D + 1)) (hu : u / l a ^ m ∈
          integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω)
        (ζ : Fin (D + 1) → ℂ), ζ a ≠ 0 → ∀ w : ℂ,
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (Module.finrank P Ω - i) = 0 →
        ∃ ψ : integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω →+* ℂ,
          (∀ (k : Fin (D + 1)) (hk : l k / l a ∈
              integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω),
            ψ ⟨l k / l a, hk⟩ = ζ k / ζ a) ∧
          ψ ⟨u / l a ^ m, hu⟩ = w / ζ a ^ m

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

