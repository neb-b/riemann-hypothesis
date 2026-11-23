module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0098
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibrePt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0079
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0014
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonoNormSq

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtRel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section


open ProjFrameFibrePt in
theorem ProjFrameGenPtRel.proof : ProjFrameGenPtRel.Statement := by
  intro D Ω _ _ κ _ x e _ hF G
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro n hn
    have h1 : (C (n : ℤ) : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))) ∈ graphP x e := by
      rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_C, eq_intCast, Int.cast_natCast]
      exact hn
    rw [graphP, graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_C, eq_intCast, Int.cast_natCast,
      ← map_natCast (C : (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* MvPolynomial Unit _), C_eq_zero,
      ← map_natCast (Ideal.Quotient.mk (coordIdeal ℤ x)), Ideal.Quotient.eq_zero_iff_mem, coordIdeal,
      RingHom.mem_ker, map_natCast, ← map_natCast (Polynomial.C : Ω →+* Polynomial Ω), Polynomial.C_eq_zero] at h1
    exact_mod_cast h1
  ·
    have hker : ∀ h : MRing (GlobalTheory κ),
        aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) h = 0 ↔ h ∈ coordIdeal ℤ x := by
      intro h
      constructor
      · intro h0
        have h2 : rename (fun p : Ix κ => aV D p.2) h ∈ graphP x e := by
          rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_rename]
          exact h0
        rwa [graphP, graphIdeal, RingHom.mem_ker, graphMap_rename_inl, C_eq_zero,
          Ideal.Quotient.eq_zero_iff_mem] at h2
      · intro hh
        exact aeval_inl_eq_zero G hh
    ext f
    have hu : f ∈ coordIdeal ℤ (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) ↔
        ∀ d, homogeneousComponent d f ∈ coordIdeal ℤ x := by
      rw [coordIdeal, RingHom.mem_ker, Polynomial.ext_iff]
      simp only [coeff_coneMap, Polynomial.coeff_zero, hker]
    rw [hu]
    constructor
    · intro h
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => h d
    · intro h d
      exact coordIdeal_isHomogIdeal ℤ x f h d
  ·
    intro k
    have h := x'_frame_mul G (e := e) k
    change G.x' (bV κ k) * G.x' (aV D (e 0).2) = G.x' (bV κ 0) * G.x' (aV D (e k).2)
    linear_combination -h
  ·
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_fieldRange] at hy
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨f, g, _, rfl⟩ := G.gen c
      have key : ∀ h : MRing (GlobalTheory (Fin (D + 1))), algebraMap G.Φ G.Φ' (aeval G.x h) ∈
          Subfield.closure (Set.range fun k : Fin (D + 1) => G.x' ⟨Sum.inr (), k⟩) := by
        intro h
        induction h using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, eq_intCast, map_intCast]
          exact intCast_mem _ a
        | add p q hp hq =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hp hq
        | mul_X p i hp =>
          rw [map_mul, map_mul, aeval_X]
          exact mul_mem hp (Subfield.subset_closure ⟨i.2, G.compat i⟩)
      rw [map_div₀]
      exact div_mem (key f) (key g)
    · rw [Subfield.closure_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨G.x ⟨(), k⟩, (G.compat ⟨(), k⟩).symm⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtTransc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameGenPtTransc

open ProjFrameFibrePt

theorem proof : ProjFrameGenPtTransc.Statement := by
  intro D Ω _ _ κ _ x e _hA hF G
  classical
  have := coordIdeal_isPrime ℤ x
  rw [transcendental_iff]
  intro q hq
  have hc : ∀ n, ∃ g : MvPolynomial (Ix κ) ℤ,
      aeval (fun p : Ix κ => G.x' (aV D p.2)) g = ((q.coeff n : _) : G.Φ') := by
    intro n
    have h : ((q.coeff n : _) : G.Φ') ∈
        (aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) : MvPolynomial (Ix κ) ℤ →ₐ[ℤ] G.Φ').range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (q.coeff n).2
    obtain ⟨g, hg⟩ := h
    exact ⟨g, hg⟩
  choose g hg using hc
  have hFΓ : (∑ n ∈ q.support, rename (fun p : Ix κ => aV D p.2) (g n) * X (bV κ 0) ^ n) ∈ graphP x e := by
    have key : ∀ F, aeval G.x' F = 0 → F ∈ graphP x e := fun F h => by
      rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker]; exact h
    refine key _ ?_
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hq, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_pow, aeval_X, aeval_rename]
    exact congrArg (· * _) (hg n)
  replace hFΓ : graphMap (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
      (∑ n ∈ q.support, rename (fun p : Ix κ => aV D p.2) (g n) * X (bV κ 0) ^ n) = 0 := hFΓ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hFΓ
  simp only [map_mul, map_pow, graphMap_rename_inl, graphMap_inr, ProjFrameGraph.linForm_projMat] at hFΓ
  simp only [mul_pow, ← mul_assoc, ← C_pow, ← C_mul] at hFΓ
  have hX : Ideal.Quotient.mk (coordIdeal ℤ x) (X (e 0)) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, X_mem_coordIdeal_iff]
    exact ProjFrameGraph.frame_ne_zero hF 0
  have hcoef : ∀ m, q.coeff m = 0 := by
    intro m
    by_cases hm : m ∈ q.support
    · have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single () m)) hFΓ
      rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Finset.sum_eq_single m] at h1
      · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one] at h1
        have h2 := (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ hX)
        rw [Ideal.Quotient.eq_zero_iff_mem] at h2
        have h3 := aeval_inl_eq_zero G h2
        rw [hg m] at h3
        exact Subtype.ext h3
      · intro n _ hn
        rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
        intro h
        exact hn (Finsupp.single_injective () h)
      · intro h
        exact absurd hm h
    · exact Polynomial.notMem_support_iff.1 hm
  apply AddMonoidAlgebra.ext
  ext m
  simpa using congrArg Subtype.val (hcoef m)

end ProjFrameGenPtTransc

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegreeInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial BlockImageHilb

noncomputable section

namespace PullConeDegreeInt

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isWeightedHomogeneous_of_isMultiHomog {f : MRing ι} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a := by
  intro m hm
  funext k
  rw [weight_blockWeight_apply]
  exact hf m (mem_support_iff.mpr hm) k

theorem isMultiHomog_of_isWeightedHomogeneous {f : MRing ι} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a := by
  intro m hm k
  rw [← weight_blockWeight_apply, hf (mem_support_iff.mp hm)]

theorem mConeMap_eq (y : (Σ k, ι k) → Ω) {f : MRing ι} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    mConeMap y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hf (mem_support_iff.mp hμ)]
  simp only [mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem coeff_mConeMap (y : (Σ k, ι k) → Ω) (f : MRing ι) (n : K → ℕ) :
    AddMonoidAlgebra.coeff (mConeMap y f) (Finsupp.equivFunOnFinite.symm n) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) n f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m r rfl
    rw [mConeMap_eq y hm, PullConeDegree.prod_X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial,
      weightedHomogeneousComponent_of_mem (n := Finsupp.weight (NumbersDVR.blockWeight ι) m) hm]
    by_cases h : n = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm), map_zero]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, map_add (f := _), map_add (f := _)]


omit [DecidableEq K] in
theorem exists_dvd_monomial (N : ℕ) (hne : ∀ k, Nonempty (ι k)) (μ : (Σ k, ι k) →₀ ℕ)
    (hμ : ∀ k, N * Fintype.card (ι k) ≤ ∑ i, μ ⟨k, i⟩) (r : ℤ) :
    ∃ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∣ monomial μ r := by
  have hc : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := ι k)) (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at hlt
    exact absurd (hμ k) (not_le.mpr hlt)
  choose c hc using hc
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fintype.prod_sigma, ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans
    (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MRing ι) ^ μ ⟨k, i⟩) (Finset.mem_univ (c k)))

end Lemmas

theorem proof : PullConeDegreeInt.Statement := by
  classical
  intro K _ ι _ Ω _ y D e L N M hy hL hN d g hg hd
  have hne : ∀ k, Nonempty (ι k) := fun k => (hy k).elim fun i _ => ⟨i⟩
  have hg' := isWeightedHomogeneous_of_isMultiHomog hg

  have hgI : (M : MRing ι) * g ∈ coneNullIdealZ y L := by
    rw [g.as_sum, Finset.mul_sum]
    refine Ideal.sum_mem _ fun μ hμ => ?_
    obtain ⟨c, hc⟩ := exists_dvd_monomial N hne μ
      (fun k => by rw [hg μ hμ k]; have := hd k; omega) (AddMonoidAlgebra.coeff g μ)
    exact Ideal.mem_of_dvd _ (mul_dvd_mul_left _ hc) (hN c)
  have hI : coneNullIdealZ y L = RingHom.ker (mConeMap y) ⊔ Ideal.span (Set.range L) := by
    rw [coneNullIdealZ, Ideal.span_union, Ideal.span_eq]
    rfl
  rw [hI, Submodule.mem_sup] at hgI
  obtain ⟨u, hu, v, hv, huv⟩ := hgI
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv

  have hmapL : ∀ j, mConeMap y (L j) = monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    intro j
    rw [mConeMap_eq y (isWeightedHomogeneous_of_isMultiHomog (hL j)), PullConeDegree.prod_X_pow_eq_monomial,
      C_mul_monomial, mul_one]
  have hMg : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) ((M : MRing ι) * g) d := by
    have h := (isWeightedHomogeneous_C (NumbersDVR.blockWeight ι) (M : ℤ)).mul hg'
    rw [zero_add, map_natCast] at h
    exact h
  have hψg : mConeMap y ((M : MRing ι) * g) =
      ∑ j, mConeMap y (b j) * monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← huv, map_add (f := _), RingHom.mem_ker.mp hu, zero_add, ← hb, map_sum]
    simp only [map_mul, hmapL]

  refine ⟨fun j => weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (d - e) (b j),
    fun j => isMultiHomog_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm d)) hψg
  rw [mConeMap_eq y hMg, PullConeDegree.prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
    coeff_monomial, if_pos rfl, coeff_sum, map_mul, map_natCast] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle : Finsupp.equivFunOnFinite.symm e ≤ Finsupp.equivFunOnFinite.symm d :=
    Finsupp.le_def.mpr fun k => by simp only [Finsupp.coe_equivFunOnFinite_symm]; have := hd k; omega
  have hsub : Finsupp.equivFunOnFinite.symm d - Finsupp.equivFunOnFinite.symm e =
      Finsupp.equivFunOnFinite.symm (d - e) := by
    ext k
    simp
  rw [coeff_mul_monomial', if_pos hle, hsub, coeff_mConeMap]

end PullConeDegreeInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

namespace ResolutionDegree

theorem hessC_congr {n : ℕ} {φ ψ : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]

theorem maDens_congr {n : ℕ} {φ ψ : Fin n → (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : (fun k => ReciprocityTheory.AnForm.hessC (φ k) z) = fun k => ReciprocityTheory.AnForm.hessC (ψ k) z :=
    funext fun k => hessC_congr (h k)
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH]

theorem mInt_congr_of_locDens {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Ψ : Fin e → LocPot X} (h : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Ψ j y)
    (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [h j y hy]
  · rfl

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem smooth_logRatio_resPt (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) :
    d.R.A.Smooth (fun y => logRatio m₀ m₁ (resPt d y)) := fun j => by
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y),
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _), ⟨hy.1, d.R.mem_U _⟩, ?_⟩
  have hsm : ContDiffOn ℝ ∞
      (fun y' => logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y')))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y)) :=
    (gbamix_smooth_logRatio h₀ h₁).comp (resLift_contDiffOn d _ j)
      fun y' hy' => gaamix_ne_zero_of_mcPts (d.R.mem _ _ hy'.2)
  refine (hsm.mono Set.inter_subset_right).congr fun y' hy' => ?_
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2.2⟩
  change logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')) = _
  rw [hcy]
  exact gbamix_logRatio_deg (m₀ := m₀) (m₁ := m₁) c _ hc

theorem mInt_resPot_eq (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)} (g : d.R.X → ℝ) :
    mInt d.R.A (fun _ => resPot d m₁) g =
      mInt d.R.A (fun _ => resPot d m₀ + LocPot.ofFun (fun y => logRatio m₀ m₁ (resPt d y))) g := by
  refine mInt_congr_of_locDens _ (fun j y hy => ?_) g
  unfold locDens
  refine maDens_congr fun _ => ?_
  have hmem : (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y) ∈ 𝓝 y :=
    ((d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _)).mem_nhds ⟨hy, d.R.mem_U _⟩
  filter_upwards [hmem] with y' hy'
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2⟩
  have hz := gaamix_ne_zero_of_mcPts (d.R.mem ((d.R.A.chart j).symm y) _ hy'.2)
  have h₀ := m₀.pos _ hz
  have h₁ := m₁.pos _ hz
  change Real.log (m₁.ρ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) =
    Real.log (m₀.ρ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) +
      logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y'))
  rw [hcy, gbamix_logRatio_deg (m₀ := m₀) (m₁ := m₁) c
    (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y')) hc,
    logRatio, Real.log_div h₁.ne' h₀.ne']
  ring

theorem mass_eq (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) :
    mInt d.R.A (fun _ => resPot d m₁) (fun _ => 1) = mInt d.R.A (fun _ => resPot d m₀) (fun _ => 1) := by
  rw [mInt_resPot_eq d (m₀ := m₀)]
  exact massIndep d.R.A (fun _ => resPot d m₀) (fun _ y => logRatio m₀ m₁ (resPt d y))
    (fun _ => isPotential_resPot d h₀) (fun _ => smooth_logRatio_resPt d h₀ h₁)

theorem mass_pullFS (hPM : ProjFSMass.Statement) (d : HSMDatum D Ω κ) {e : Fin (D + 1) → Ix κ}
    {m₀ : ConeMetric ℂ (Ix κ)} (hfr : IsProjFrame d.x e) (h₀ : IsSmoothMetric m₀) (hFS : IsPullFS d.x e m₀) :
    mInt d.R.A (fun _ => resPot d m₀) (fun _ => 1) = (projDeg d.x e : ℝ) := by
  obtain ⟨Ψ, hΨ, hmass⟩ := hPM D Ω κ d.x e m₀ hfr hFS
  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory κ) := HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  have hA : IsSmoothHerm A := contDiffOn_const
  have hlog : logNorm A 1 = fun _ => (1 : ℝ) := by
    funext z
    simp [A, logNorm, HermLine.ofWeight]
  have hsec : IsSectionOn (coordIdeal ℤ d.x) A 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro a ha k
      rw [support_one] at ha
      simp only [Finset.mem_singleton] at ha
      simp [ha]
    · exact (Ideal.ne_top_iff_one _).1 d.arith.2.1.1.ne_top
  have key := AnResBridge.bridge d.R Ψ (fun _ => HermLine.ofCone m₀) A 1 d.arith hΨ
    (fun _ => gbamix_smoothHerm_ofCone h₀) hA hsec
  rw [hlog] at key
  rw [← hmass]
  exact key.symm

end ResolutionDegree

theorem ResolutionDegree.proof (hPF : PullFSExtension.Statement) (hPM : ProjFSMass.Statement) :
    ResolutionDegree.Statement := by
  intro D Ω _ _ κ _ d e m hfr hm
  obtain ⟨m₀, h₀, -, -, hFS⟩ := hPF D Ω κ d.x e hfr
  rw [ResolutionDegree.mass_eq d h₀ hm]
  exact ResolutionDegree.mass_pullFS hPM d hfr h₀ hFS

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsVeroneseChiParts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

open Veronese

def VeroneseMonoBasis.Statement : Prop :=
  ∀ D n : ℕ, ∃ b : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → MvPolynomial (Ix (Idx D)) ℚ,
    IsSecBasis (Veronese.x D) n b ∧
      ∀ k, aeval (Veronese.x D) (b k) = ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i

def VeroneseGramMono.Statement : Prop :=
  ∀ (D n r : ℕ) (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ)
    (A : Matrix (Fin r) (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ),
    (∀ k, aeval (Veronese.x D) (b k) =
      ∑ l, (A k l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D (2 * n) l i) →
    Veronese.gram D n b = A.map (Int.cast : ℤ → ℝ) *
      Matrix.diagonal (fun l => monoNormSq (adtEnum D (2 * n) l)) * (A.map (Int.cast : ℤ → ℝ)).transpose

theorem adtEnum_zero_eq (D : ℕ) (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) 0).card) :
    adtEnum D 0 l = 0 := by
  have h := Finset.Nat.mem_antidiagonalTuple.mp
    (((Finset.Nat.antidiagonalTuple (D + 1) 0).equivFin.symm l).2)
  funext i
  exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

