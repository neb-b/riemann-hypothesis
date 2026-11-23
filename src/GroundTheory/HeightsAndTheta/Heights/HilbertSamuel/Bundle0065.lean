module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameBasePtFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameBasePtFree

theorem linForm_projMat {κ : Type} [Fintype κ] {D : ℕ} (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [ReciprocityTheory.ChartRestriction.G.AI.I4.linForm, projMat]
  generalize e k = q
  obtain ⟨⟨⟩, j⟩ := q
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem rename_mem_span {κ : Type} {D : ℕ} (e : Fin (D + 1) → Ix κ) {h : MvPolynomial (Fin (D + 1)) ℤ} {n : ℕ}
    (hh : h.IsHomogeneous n) (hn : 0 < n) :
    rename e h ∈ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  have h1 : h ∈ Ideal.span ((X : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hm0 : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    have := hh (mem_support_iff.mp hm)
    rw [hm0, map_zero] at this
    omega
  have h2 := Ideal.mem_map_of_mem (rename e : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Ix κ) ℤ) h1
  rw [Ideal.map_span, Set.image_image, Set.image_univ] at h2
  simpa [rename_X] using h2

theorem pow_mem (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) (x : Ix κ → Ω)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame x e) (p : Ix κ) :
    ∃ N : ℕ, (X p : MvPolynomial (Ix κ) ℤ) ^ N ∈
      coordIdeal ℤ x ⊔ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  obtain ⟨q, hmon, hq⟩ := hfr.integral p
  set N := q.natDegree with hNdef
  have hcoef : ∀ j, ∃ f : MvPolynomial (Fin (D + 1)) ℤ,
      coneMap ℤ (x ∘ e) f = ((q.coeff j : coneRing ℤ (x ∘ e)) : Polynomial Ω) :=
    fun j => (q.coeff j).2
  choose f hf using hcoef
  set F : MvPolynomial (Ix κ) ℤ := X p ^ N +
      ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j with hFdef
  have hFh : F.IsHomogeneous N := by
    refine (isHomogeneous_X_pow p N).add (IsHomogeneous.sum _ _ _ fun j hj => ?_)
    have hj' : N - j + j = N := Nat.sub_add_cancel (Finset.mem_range.mp hj).le
    have := ((homogeneousComponent_isHomogeneous (N - j) (f j)).rename_isHomogeneous (f := e)).mul
      (isHomogeneous_X_pow p j)
    rwa [hj'] at this
  have hFx : aeval x F = 0 := by
    have h0 := congrArg (fun r : Polynomial Ω => r.coeff N) hq
    simp only [Polynomial.coeff_zero] at h0
    rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.coeff_add,
      Polynomial.finsetSum_coeff] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h0, hFdef, map_add (f := _), map_sum]
    congr 1
    · rw [Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul_X_pow, if_pos rfl,
        map_pow, aeval_X]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : j ≤ N := (Finset.mem_range.mp hj).le
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow,
        ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hjN, Polynomial.coeff_mul_C]
      rw [map_mul, map_pow, aeval_X, aeval_rename]
      have : algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω) (q.coeff j) = coneMap ℤ (x ∘ e) (f j) := (hf j).symm
      rw [this, coeff_coneMap]
  have hFP : F ∈ coordIdeal ℤ x := mem_coordIdeal_of_isHomogeneous ℤ x hFh hFx
  refine ⟨N, ?_⟩
  have hsum : (∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j) ∈
      Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    have hjN : j < N := Finset.mem_range.mp hj
    exact rename_mem_span e (homogeneousComponent_isHomogeneous (N - j) (f j)) (by omega)
  have : (X p : MvPolynomial (Ix κ) ℤ) ^ N =
      F - ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j := by
    rw [hFdef]; ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hsum)

end ProjFrameBasePtFree


open ProjFrameBasePtFree in
theorem ProjFrameBasePtFree.proof : ProjFrameBasePtFree.Statement := by
  intro D Ω _ _ κ _ x e hfr k₂ i
  obtain ⟨N, hN⟩ := pow_mem D Ω κ x e hfr ⟨(), i ()⟩
  refine ⟨N, ?_⟩
  have hspan : (Set.range fun j : GlobalTheory (Fin (D + 1)) k₂ =>
      ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨k₂, j⟩) =
      Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ) := by
    cases k₂
    ext
    simp [linForm_projMat]
  rw [hspan, Fintype.prod_unique]
  exact hN

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace QuotPartGraded

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def blockWeight (ι : K → Type) : (Σ k, ι k) → (K → ℤ) := fun x => Pi.single x.1 1

theorem blockWeight_apply (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = ∑ i, (d ⟨k, i⟩ : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • blockWeight ι i) (by intro i; simp),
    Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem isMultiHomog_iff (p : MRingOver S ι) (a : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a ↔ IsWeightedHomogeneous (blockWeight ι) p (fun k => (a k : ℤ)) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog
  constructor
  · intro h d hd
    funext k
    rw [blockWeight_apply]
    have := h d (mem_support_iff.2 hd) k
    exact_mod_cast this
  · intro h m hm k
    have := congrFun (h (mem_support_iff.1 hm)) k
    rw [blockWeight_apply] at this
    exact_mod_cast this

theorem nonneg_of_isWeightedHomogeneous {p : MRingOver S ι} {c : K → ℤ}
    (hp : IsWeightedHomogeneous (blockWeight ι) p c) (h0 : p ≠ 0) : ∀ k, 0 ≤ c k := by
  obtain ⟨d, hd⟩ := ne_zero_iff.1 h0
  intro k
  rw [← hp hd, blockWeight_apply]
  positivity

theorem span_eq (c : K → ℤ) :
    Submodule.span S {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p (fun k => (c k).toNat)} =
      weightedHomogeneousSubmodule S (blockWeight ι) c := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro p ⟨hc, hp⟩
    rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
    have h' := (isMultiHomog_iff p _).1 hp
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h'
  · intro p hp
    by_cases h0 : p = 0
    · rw [h0]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      have hc := nonneg_of_isWeightedHomogeneous hp h0
      refine ⟨hc, (isMultiHomog_iff p _).2 ?_⟩
      have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
      rw [hcc]
      exact hp

theorem quotPart_eq (V : Ideal (MRingOver S ι)) (c : K → ℤ) :
    KH.quotPart S V c =
      (weightedHomogeneousSubmodule S (blockWeight ι) c).map (Ideal.Quotient.mkₐ S V).toLinearMap := by
  rw [KH.quotPart, ← span_eq, Submodule.map_span]
  rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous {V : Ideal (MRingOver S ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  obtain ⟨T, hT, rfl⟩ := hV
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨fun k => (a k : ℤ), (isMultiHomog_iff f a).1 ha⟩

end QuotPartGraded

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem QuotPartGraded.proof : QuotPartGraded.Statement := by
  intro S _ K _ ι _ V hV
  have hq := QuotPartGraded.quotPart_eq (S := S) (ι := ι) V
  refine ⟨?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum
      have hlift : ∀ c, ∃ p : MRingOver S ι, c ∈ s →
          (p ∈ weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c ∧
            Ideal.Quotient.mk V p = v c) := by
        intro c
        by_cases hc : c ∈ s
        · have h1 := hv c hc
          rw [hq] at h1
          obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 h1
          exact ⟨y, fun _ => ⟨hy, hyv⟩⟩
        · exact ⟨0, fun h => absurd h hc⟩
      choose p hp using hlift
      have hsumV : ∑ c ∈ s, p c ∈ V := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hsum]
        exact Finset.sum_congr rfl fun c hc => (hp c hc).2
      intro c hc
      have hcomp := weightedHomogeneousComponent_mem_of_mem S (QuotPartGraded.blockWeight ι)
        (QuotPartGraded.isHomogeneous hV) hsumV c
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single c] at hcomp
      · rw [← (hp c hc).2, Ideal.Quotient.eq_zero_iff_mem]
        rwa [weightedHomogeneousComponent_eq_self (hp c hc).1] at hcomp
      · intro d hd hdc
        exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne c (hp d hd).1 (Ne.symm hdc)
      · intro h
        exact absurd hc h
    · have htop := (DirectSum.Decomposition.isInternal
        (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι))).submodule_iSup_eq_top
      rw [show KH.quotPart S V = fun c => (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c).map
          (Ideal.Quotient.mkₐ S V).toLinearMap from funext hq]
      rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective S V
  · intro a c p m hp hm
    rw [hq] at hm ⊢
    obtain ⟨q, hq', rfl⟩ := Submodule.mem_map.1 hm
    refine Submodule.mem_map.2 ⟨p * q, ?_, ?_⟩
    · have := ((QuotPartGraded.isMultiHomog_iff p a).1 hp).mul hq'
      rw [mem_weightedHomogeneousSubmodule, add_comm]
      exact this
    · simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
      rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RealFormsOnPoints.proof (hN : ComplexFormsOnPoints.Statement)
    (hB : IndependentModBaseChange.Statement) : RealFormsOnPoints.Statement := by
  intro K _ ι _ Ω _ y d e r g hP hg hli c hc
  obtain ⟨_, ⟨hprime, -, hrel⟩, -, -⟩ := hP

  have hZ : LinearIndependent ℤ (fun i => Ideal.Quotient.mk (mCoordIdeal y) (g i)) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have hmem : ∑ i, n i • g i ∈ mCoordIdeal y := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_zsmul] using hn
    have h0 : mConeMap y (∑ i, n i • g i) = 0 := hmem
    have hsum : mConeMap y (∑ i, n i • g i) =
        MvPolynomial.C (∑ i, n i • aeval y (g i)) * ∏ k, MvPolynomial.X k ^ e k := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ProjLine.mConeMap_eq_of_isMultiHomog y (hg i), map_zsmul, smul_mul_assoc]
    rw [hsum] at h0
    have hX : (∏ k, MvPolynomial.X k ^ e k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact (MvPolynomial.C_eq_zero).mp ((mul_eq_zero.mp h0).resolve_right hX)

  have hC := hB _ (mCoordIdeal y) r g hZ
  set I := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℂ)) with hI

  have hF : (∑ i, (c i : ℂ) • MvPolynomial.map (Int.castRingHom ℂ) (g i)) ∈ I := by
    refine hN K ι _ hprime hrel _ fun z hz => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simpa only [smul_eval] using hc z hz
  rw [Fintype.linearIndependent_iff] at hC
  funext i
  have h := hC (fun i => (c i : ℂ)) (by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hF
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hF, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]) i
  exact_mod_cast h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace ResolutionMixedIntegral

theorem proof (hB : ResolutionMixedBridge.Statement) (hI : ResolutionInterpIntegral.Statement) :
    ResolutionMixedIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  rw [hI D Ω κ d m₁ hm₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hM : ∀ j : Fin D, IsSmoothMetric (if j.val < i then m₁ else d.m) := fun j => by
    split_ifs
    · exact hm₁
    · exact d.smooth
  have hpot : mixPot d.m m₁ D i = fun j z => Real.log ((if j.val < i then m₁ else d.m).ρ z) := by
    funext j z
    unfold mixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => resPot d (if j.val < i then m₁ else d.m)) =
      fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D Ω κ d (fun j => if j.val < i then m₁ else d.m) m₁ hM hm₁, hres]

end ResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreArith
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SegreArithmetic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]


omit [DecidableEq K] in
theorem segreCoords_div (y : (Σ k, ι k) → Ω) (f c : (k : K) → ι k) :
    segreCoords y ⟨(), f⟩ / segreCoords y ⟨(), c⟩ = ∏ k, y ⟨k, f k⟩ / y ⟨k, c k⟩ := by
  simp only [segreCoords, Finset.prod_div_distrib]

theorem ratio_eq_segre (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, c k⟩ =
      segreCoords y ⟨(), Function.update c k i⟩ / segreCoords y ⟨(), c⟩ := by
  rw [segreCoords_div, Finset.prod_eq_single k]
  · rw [Function.update_self]
  · intro j _ hj
    rw [Function.update_of_ne hj]
    exact div_self (hc j)
  · intro h
    exact absurd (Finset.mem_univ k) h


omit [Fintype K] [DecidableEq K] in
theorem charZero_of_horizontal (y : (Σ k, ι k) → Ω)
    (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_injective_algebraMap (R := ℤ) (A := Ω) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro n hn
  have hmem : n ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, ← algebraMap_eq, AlgHom.commutes,
      MvPolynomial.algebraMap_apply, C_eq_zero]
    exact hn
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from h] at hmem
  exact (Ideal.mem_bot).mp hmem

end SegreArithmetic


open SegreArithmetic BlockImageArithmetic in
theorem SegreArith.proof : SegreArith.Statement := by
  intro K _ _ ι _ Ω _ y D hY
  classical
  obtain ⟨hK, ⟨_, _, hrel⟩, hhor, hdim⟩ := hY
  have : CharZero Ω := charZero_of_horizontal y hhor
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hnz
  set x := segreCoords y with hx
  let c' : ∀ u, GlobalTheory ((k : K) → ι k) u := fun _ ↦ c
  have hx0 : x ⟨(), c⟩ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
  have hc' : ∀ u, x ⟨u, c' u⟩ ≠ 0 := fun _ ↦ hx0
  set Fy := CoordinateConeArithVar.ratioField y c with hFy
  set Fx := CoordinateConeArithVar.ratioField (ι := GlobalTheory ((k : K) → ι k)) x c' with hFx
  have hLx : Fx ≤ Fy := by
    rw [hFx, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨u, f⟩, rfl⟩
    show x ⟨u, f⟩ / x ⟨u, c⟩ ∈ Fy
    rw [hx, segreCoords_div]
    exact prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, f k⟩, rfl⟩
  have hLy : Fy ≤ Fx := by
    rw [hFy, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    show y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ Fx
    rw [ratio_eq_segre y c hc k i]
    exact IntermediateField.subset_adjoin _ _ ⟨⟨(), Function.update c k i⟩, rfl⟩
  have hLeq : Fy = Fx := le_antisymm hLy hLx
  have hdy := ringKrullDim_eq y c hc
  rw [hdim] at hdy
  rw [coordIdeal_eq_mCoordIdeal]
  refine ⟨⟨()⟩, ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal x,
    CoordinateConeArithVar.relevant x c' hc'⟩, CoordinateConeArithVar.horizontal x, ?_⟩
  rw [ringKrullDim_eq x c' hc']
  rw [← hFy, hLeq] at hdy
  generalize (Algebra.trdeg ℤ Fx).toENat = t at hdy ⊢
  have h1 : ((D + 1 + Fintype.card K : ℕ) : ℕ∞) = t + Fintype.card K + 1 := by exact_mod_cast hdy
  induction t using ENat.recTopCoe with
  | top => simp at h1
  | coe t =>
    have h2 : D + 1 + Fintype.card K = t + Fintype.card K + 1 := by exact_mod_cast h1
    have h3 : t = D := by omega
    subst h3
    rw [Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNonzeroSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def GeneratedNonzeroSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (n : K → ℤ),
    KH.GeneratedV ℚ (KH.genIdeal y) n → ∃ s ∈ chartLat y n 1, s ≠ 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

