module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import GroundTheory.PAdicHodge.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariant
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {R : Type} [CommRing R] {N : ℕ}

theorem minorIJ_eq_det (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) (k : ℕ) (hI : I.card = k)
    (hJ : J.card = k) : minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dite_eq_left hI]

theorem minorIJ_of_card_ne (h : Matrix (Fin N) (Fin N) R) {I J : Finset (Fin N)} (e : I.card ≠ J.card) :
    minorIJ h I J = 0 := by
  unfold minorIJ
  rw [dite_eq_right e]

theorem minorIJ_mul_of_card (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) (k : ℕ) (hI : I.card = k)
    (hJ : J.card = k) :
    minorIJ (T * h) I J = ∑ s : GroundTheory.PAdicHodge.KSubset N k, minorIJ T I s.1 * minorIJ h s.1 J := by
  rw [minorIJ_eq_det _ _ _ k hI hJ]
  have e : (T * h).submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ) =
      T.submatrix (I.orderEmbOfFin hI) id * h.submatrix id (J.orderEmbOfFin hJ) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [e, GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [minorIJ_eq_det T I s.1 k hI s.2, minorIJ_eq_det h s.1 J k s.2 hJ]
  rfl

theorem minorIJ_mul (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  by_cases e : I.card = J.card
  · rw [minorIJ_mul_of_card T h I J I.card rfl e.symm]
    have h1 : ∑ I' : Finset (Fin N), minorIJ T I I' * minorIJ h I' J =
        ∑ I' ∈ Finset.univ.filter (fun I' : Finset (Fin N) => I'.card = I.card),
          minorIJ T I I' * minorIJ h I' J := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_
      have hc : s.card ≠ I.card := fun hc => hs (by simp [hc])
      rw [minorIJ_of_card_ne T (Ne.symm hc), zero_mul]
    rw [h1]
    exact (Finset.sum_subtype (Finset.univ.filter fun I' : Finset (Fin N) => I'.card = I.card)
      (p := fun s : Finset (Fin N) => s.card = I.card) (fun s => by simp)
      (fun I' => minorIJ T I I' * minorIJ h I' J)).symm
  · rw [minorIJ_of_card_ne _ e]
    symm
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : I.card = s.card
    · rw [minorIJ_of_card_ne h (fun h' => e (hs.trans h')), mul_zero]
    · rw [minorIJ_of_card_ne T hs, zero_mul]

theorem minorIJ_eq_zero_of_row (h : Matrix (Fin N) (Fin N) R) {I C : Finset (Fin N)} {a : Fin N} (ha : a ∈ I)
    (hz : ∀ c ∈ C, h a c = 0) : minorIJ h I C = 0 := by
  by_cases e : I.card = C.card
  · rw [minorIJ_eq_det h I C _ e rfl]
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨x, rfl⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero x fun y => ?_
    simp only [Matrix.submatrix_apply]
    refine hz _ ?_
    exact Finset.orderEmbOfFin_mem _ _ _
  · exact minorIJ_of_card_ne h e

theorem sum_mem_eq_sum_enum (C : Finset (Fin N)) (f : Fin N → R) :
    ∑ k ∈ C, f k = ∑ z, f (C.orderEmbOfFin rfl z) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ C rfl]
  rw [Finset.sum_map]
  rfl

theorem prod_mem_eq_prod_enum (C : Finset (Fin N)) (f : Fin N → R) :
    ∏ k ∈ C, f k = ∏ z, f (C.orderEmbOfFin rfl z) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ C rfl]
  rw [Finset.prod_map]
  rfl

theorem minorIJ_mul_of_support (A B : Matrix (Fin N) (Fin N) R) (I C : Finset (Fin N))
    (hz : ∀ k c, c ∈ C → k ∉ C → B k c = 0) :
    minorIJ (A * B) I C = minorIJ A I C * minorIJ B C C := by
  by_cases e : I.card = C.card
  · rw [minorIJ_eq_det _ I C _ e rfl, minorIJ_eq_det A I C _ e rfl, minorIJ_eq_det B C C _ rfl rfl, ← Matrix.det_mul]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    have hy : C.orderEmbOfFin rfl y ∈ C := Finset.orderEmbOfFin_mem _ _ _
    have h1 : ∑ k, A (I.orderEmbOfFin e x) k * B k (C.orderEmbOfFin rfl y) =
        ∑ k ∈ C, A (I.orderEmbOfFin e x) k * B k (C.orderEmbOfFin rfl y) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
      rw [hz k _ hy hk, mul_zero]
    rw [h1, sum_mem_eq_sum_enum C]
  · rw [minorIJ_of_card_ne _ e, minorIJ_of_card_ne _ e, zero_mul]

theorem minorIJ_self_of_triangular (B : Matrix (Fin N) (Fin N) R) (hB : B.BlockTriangular id) (C : Finset (Fin N)) :
    minorIJ B C C = ∏ c ∈ C, B c c := by
  rw [minorIJ_eq_det B C C _ rfl rfl]
  have ht : (B.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)).BlockTriangular id := by
    intro x y hxy
    exact hB ((C.orderEmbOfFin rfl).strictMono hxy)
  rw [Matrix.det_of_upperTriangular ht, prod_mem_eq_prod_enum C (fun c => B c c)]
  rfl

theorem mem_stepCols_block {N j : ℕ} {i c : Fin N} (hj : j ≤ N) (hc : c ∈ stepCols N j i) :
    if (i : ℕ) + 1 ≤ j then N - j ≤ (c : ℕ) else (c : ℕ) < N - j := by
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  split_ifs at hc ⊢ with h
  · exact hc.1
  · omega

theorem support_stepCols {N j : ℕ} {i : Fin N} (hj : j ≤ N) (bb : Matrix (Fin N) (Fin N) R)
    (hd : IsBlockDiag j bb) (ht : bb.BlockTriangular id) (k c : Fin N) (hc : c ∈ stepCols N j i)
    (hk : k ∉ stepCols N j i) : bb k c = 0 := by
  by_cases hkc : c < k
  · exact ht hkc
  have hkc' : (k : ℕ) ≤ c := by simpa using not_lt.mp hkc
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  split_ifs at hc hk with h
  · refine hd k c fun hiff => ?_
    have : ¬ (k : ℕ) < N - j → False := fun h' => hk ⟨by omega, by omega⟩
    have h3 : (k : ℕ) < N - j := by omega
    have := hiff.mp h3
    omega
  · exact absurd (by omega) hk

theorem isBlockDiag_mul {j : ℕ} {T h : Matrix (Fin N) (Fin N) R} (hT : IsBlockDiag j T) (hh : IsBlockDiag j h) :
    IsBlockDiag j (T * h) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((a : ℕ) < N - j ↔ (k : ℕ) < N - j)
  · rw [hh k b (fun h' => hab (hk.trans h')), mul_zero]
  · rw [hT a k hk, zero_mul]

theorem support_wIdx {j : ℕ} {h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) (k c : Fin N)
    (hc : c ∈ wIdx N j) (hk : k ∉ wIdx N j) : h k c = 0 := by
  simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  refine hh k c fun hiff => ?_
  have := hiff.mp (not_le.mp hk)
  omega

theorem support_omIdx {j : ℕ} {h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) (k c : Fin N)
    (hc : c ∈ omIdx N j) (hk : k ∉ omIdx N j) : h k c = 0 := by
  simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  refine hh k c fun hiff => hk (hiff.mpr hc)

theorem detFac_mul {j : ℕ} (i : Fin N) {T h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) :
    detFac j i (T * h) = detFac j i T * detFac j i h := by
  unfold detFac
  rw [minorIJ_mul_of_support T h _ _ (support_wIdx hh), minorIJ_mul_of_support T h _ _ (support_omIdx hh)]
  split_ifs <;> ring

theorem minor_stepCols_eq_zero {N j : ℕ} {i : Fin N} (hj : j ≤ N) (h : Matrix (Fin N) (Fin N) R)
    (I : Finset (Fin N)) (hd : IsBlockDiag j h) (hI : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  by_cases e : I.card = (stepCols N j i).card
  · have hs : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hI ⟨e, hs⟩
    obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
    refine minorIJ_eq_zero_of_row h ha fun c hc => hd a c fun hiff => ?_
    have hb := mem_stepCols_block hj hc
    split_ifs at has hb with h1
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at has
      have := hiff.mp (not_le.mp has)
      omega
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at has
      exact has (hiff.mpr hb)
  · exact minorIJ_of_card_ne h e

theorem minors_main : ∀ (R : Type) [CommRing R] (N j : ℕ) (i : Fin N), j ≤ N →
    (∀ (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)),
      minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J) ∧
    (∀ (h : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j h → ¬ IsStepRows N j i I →
      minorIJ h I (stepCols N j i) = 0 ∨ stepCols N j i = ∅) ∧
    (∀ (h bb : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j bb → bb.BlockTriangular id →
      minorIJ (h * bb) I (stepCols N j i) = minorIJ h I (stepCols N j i) * ∏ c ∈ stepCols N j i, bb c c) ∧
    ∀ T h : Matrix (Fin N) (Fin N) R, IsBlockDiag j T → IsBlockDiag j h →
      IsBlockDiag j (T * h) ∧ detFac j i (T * h) = detFac j i T * detFac j i h := by
  intro R _ N j i hj
  refine ⟨minorIJ_mul, fun h I hd hI => Or.inl (minor_stepCols_eq_zero hj h I hd hI), ?_, ?_⟩
  · intro h bb I hd ht
    rw [minorIJ_mul_of_support h bb I _ (support_stepCols hj bb hd ht),
      minorIJ_self_of_triangular bb ht]
  · intro T h hT hh
    exact ⟨isBlockDiag_mul hT hh, detFac_mul i hh⟩

end GlobalTheory.CompanionTheory.Ar.PB.MinorCalc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousCuspNormFamilyStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_cusp_norm_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ I hP hH
  by_cases h : ∃ r v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsNzFamily I r v
  · have hcont : Continuous fun x => (R x).nzOf σ I h.choose_spec.choose :=
      GlobalTheory.CompanionTheory.Ar.Cusp.NzCont.continuous_nzOf R hP hH σ I _
    simpa only [RiemLat.nz, dite_eq_left h] using hcont
  · simpa only [RiemLat.nz, dite_eq_right h] using
      (continuous_const : Continuous fun _ : X => (1 : ℝ))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

abbrev cxIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Ideal (MRingOver ℂ ι) :=
  P.map (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)

def cxPosDens {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) : ℝ :=
  ∑ᶠ w ∈ setFibre S Ψ y, max (setSheetDensity S Ψ φ g y w) 0

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsDescendedRingHomOnQuotientStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_ringHom_on_quotient : ∀ (O : Type) [Ring O] (g g' : ℕ) (B : O →+* Module.End ℂ (Fin g → ℂ)) (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q → (∀ (a : O) z, q z = 0 → q (B a z) = 0) → ∃ B' : O →+* Module.End ℂ (Fin g' → ℂ), ∀ a z, B' a (q z) = q (B a z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUniv.ringAction_descends_along_surjection | exact GlobalTheory.CompanionTheory.Ar.QuotUniv.ringAction_descends_along_surjection | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUniv.ringAction_descends_along_surjection <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHermLineOfLocalSmooth
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace CExt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth Topology Filter Set
open scoped Manifold

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def colMap (p : (k : K) → ι k) (m : (Σ k, ι k × ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => m ⟨q.1, (q.2, p q.1)⟩

theorem colMap_contDiff (p : (k : K) → ι k) {n : WithTop ℕ∞} : ContDiff ℝ n (colMap p) :=
  contDiff_pi.2 fun q => contDiff_apply ℝ (fun _ => ℂ) (⟨q.1, (q.2, p q.1)⟩ : Σ k, ι k × ι k)

theorem sameOrbit_colMap {p : (k : K) → ι k} {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι)
    (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) : SameOrbit (colMap p (prMap z)) z := by
  refine ⟨fun k => (starRingEnd ℂ) (z ⟨k, p k⟩) / (blockSq z k : ℂ), fun k =>
    div_ne_zero ((map_ne_zero _).2 (hp k)) (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne'), ?_⟩
  funext q
  simp only [colMap, prMap]
  ring

theorem prMap_diag_ne_zero {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι) {k : K} {i : ι k}
    (hi : z ⟨k, i⟩ ≠ 0) : prMap z ⟨k, (i, i)⟩ ≠ 0 :=
  div_ne_zero (mul_ne_zero hi ((map_ne_zero _).2 hi))
    (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne')

theorem ne_zero_of_prMap_diag {z : (Σ k, ι k) → ℂ} {k : K} {i : ι k}
    (h : prMap z ⟨k, (i, i)⟩ ≠ 0) : z ⟨k, i⟩ ≠ 0 := by
  intro h0
  apply h
  simp [prMap, h0]

theorem isClosed_prMap_image {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsClosed (prMap '' mcPts P) := by
  have hA : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hC := (isCompact_unitBlocks (K := K) (ι := ι)).inter_right hA
  have hcont : ContinuousOn (prMap (K := K) (ι := ι)) (unitBlocks K ι ∩
      {z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}) := fun z hz =>
    (prMap_continuousAt (unitBlocks_subset hz.1)).continuousWithinAt
  convert (hC.image_of_continuousOn hcont).isClosed using 1
  ext m
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, hc, hu⟩ := exists_normalize (K := K) (ι := ι) hz.1
    exact ⟨_, ⟨hu, (mcPts_smul hP c hc hz).2⟩, prMap_smul c z hc⟩
  · rintro ⟨z, ⟨hu, hz⟩, rfl⟩
    exact ⟨z, ⟨unitBlocks_subset hu, hz⟩, rfl⟩

theorem exists_smooth_on_matrices {P : Ideal (MRing ι)} {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hP : IsMultiHomogIdeal P) (hinv : ∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') :
    ∃ g : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ z ∈ mcPts P, g (prMap z) = u z := by
  have ht : ∀ m : (Σ k, ι k × ι k) → ℂ,
      Convex ℝ {r : ℝ | ∀ z ∈ mcPts P, prMap z = m → r = u z} := by
    intro m x hx y hy a b _ _ hab z hz hzm
    rw [smul_eq_mul, smul_eq_mul, hx z hz hzm, hy z hz hzm, ← add_mul, hab, one_mul]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := (⊤ : ℕ∞))
    (M := (Σ k, ι k × ι k) → ℂ) (F := ℝ) 𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) ht (fun x => by
    by_cases hx : x ∈ prMap '' mcPts P
    · obtain ⟨z₀, hz₀, rfl⟩ := hx
      choose p hp using hz₀.1
      obtain ⟨V, w, hV, hmem, hw, hwu⟩ := hloc (colMap p (prMap z₀))
        (mem_mcPts_of_sameOrbit hP (sameOrbit_colMap hz₀.1 hp) hz₀)
      have hO : IsOpen (colMap p ⁻¹' V ∩ {m | ∀ k, m ⟨k, (p k, p k)⟩ ≠ 0}) := by
        refine (hV.preimage (colMap_contDiff p (n := 0)).continuous).inter ?_
        simp only [setOf_forall]
        exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
      refine ⟨_, hO.mem_nhds ⟨hmem, fun k => prMap_diag_ne_zero hz₀.1 (hp k)⟩, w ∘ colMap p, ?_, ?_⟩
      · exact contMDiffOn_iff_contDiffOn.2
          (hw.comp (colMap_contDiff p).contDiffOn fun y hy => hy.1)
      · rintro y ⟨hy1, hy2⟩ z hz rfl
        have ho := sameOrbit_colMap hz.1 fun k => ne_zero_of_prMap_diag (hy2 k)
        show w (colMap p (prMap z)) = u z
        rw [hwu _ ⟨hy1, mem_mcPts_of_sameOrbit hP ho hz⟩]
        exact hinv z hz _ ho
    · refine ⟨_, (isClosed_prMap_image hP).isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy z hz hzy
      exact absurd ⟨z, hz, hzy⟩ hy)
  exact ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z hz => hg _ z hz rfl⟩


variable (ι) in
def expLine (g : ((Σ k, ι k × ι k) → ℂ) → ℝ) : HermLine ι where
  a := 0
  h z := by
    classical
    exact if z ∈ nzBlocks K ι then Real.exp (g (prMap z)) else 1
  pos z hz := by
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  smul c z hc := by
    classical
    have hiff : (fun p : Σ k, ι k => c p.1 * z p) ∈ nzBlocks K ι ↔ z ∈ nzBlocks K ι := by
      refine forall_congr' fun k => exists_congr fun i => ?_
      simp [hc k]
    simp only [hiff, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul, prMap_smul c z hc]

end CExt

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem exists_hermLine_of_local_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (u : ((Σ k, ι k) → ℂ) → ℝ), IsMultiHomogIdeal P → (∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') → ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ z ∈ mcPts P, Real.log (B.h z) = u z := by
  intro K _ ι _ P u hP hinv hloc
  obtain ⟨g, hg, hgu⟩ := CExt.exists_smooth_on_matrices hP hinv hloc
  refine ⟨CExt.expLine ι g, rfl, ?_, fun z hz => ?_⟩
  · have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)))
        (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.nzBlocks K ι) :=
      Real.contDiff_exp.comp_contDiffOn
        (hg.comp_contDiffOn GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap_contDiffOn)
    refine h1.congr fun z hz => ?_
    exact if_pos hz
  · have h2 : (CExt.expLine ι g).h z = Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)) :=
      if_pos hz.1
    rw [h2, Real.log_exp, hgu z hz]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

def grMat (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (I₀ : Finset (Fin N)) (w : Finset (Fin N) → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  C + ∑ I, (w I / w I₀) • B I

def IsGrChart (N j : ℕ) (i : Fin N) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ)
    (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (w : Finset (Fin N) → ℂ), IsBlockDiag j h → h.det ≠ 0 → a ≠ 0 →
    (∀ I, IsStepRows N j i I → w I = a * minorIJ h I (stepCols N j i)) → w I₀ ≠ 0 →
      IsBlockDiag j (grMat C B I₀ w) ∧ (grMat C B I₀ w).det ≠ 0 ∧
        ∀ I, minorIJ (grMat C B I₀ w) I (stepCols N j i) * w I₀ = a * minorIJ h I (stepCols N j i)

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (k₀ : K) (z : (Σ k, ι k) → ℂ)
    (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) (basePart M.blk z) * z ⟨k₀, m⟩

def baseMono (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℂ :=
  ∏ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, F.c k⟩ ^ M.dy p k.1

def stepGap (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((BM.hom p).h z) - Real.log ((fsHerm ι (M.dy p)).h z)

def stepPh (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x : R.X) : ℝ :=
  if h : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x then stepGap M BM p h.2.choose else 0

def IsStepHyp (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  IsBlockMap κ v ∧ (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) ∧
    HoloMap R.A BM.Rb.A pr ∧
    ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))

def IsStepChart (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x y₀ : R.X) (W : Set R.X) (l : Fin BM.q)
    (H : R.X → Matrix (Fin N) (Fin N) ℂ) (D : R.X → ℂ) : Prop :=
  IsOpen W ∧ y₀ ∈ W ∧ W ⊆ R.U x ∧ (∀ y' ∈ W, pr y' ∈ BM.O l) ∧
    (∀ a b, R.A.HoloOn W fun y' => H y' a b) ∧ (∀ y' ∈ W, IsBlockDiag j (H y') ∧ (H y').det ≠ 0) ∧
    R.A.HoloOn W D ∧ (∀ y' ∈ W, D y' ≠ 0) ∧
    ∀ y' ∈ W, pr y' ∉ bdry BM.s →
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' =
        blockPot j p.2 (BM.G l p.1 (pr y')) (H y') + Real.log ‖D y'‖

def HasStepCharts (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  ∀ x y₀, y₀ ∈ R.U x → ∃ W l H D, IsStepChart M BM p κ v R pr x y₀ W l H D

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianRestrictionOrthonormalCoordsStatement
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_restriction_orthonormal_coords : ∀ (g m : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ W : Submodule ℂ (Fin g → ℂ), Module.finrank ℂ W = m → ∃ c : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ z ∈ W, ∀ z' ∈ W, z' ⬝ᵥ Hm *ᵥ star z = ∑ i, starRingEnd ℂ (c z i) * c z' i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords | exact GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords <;> assumption)
end

