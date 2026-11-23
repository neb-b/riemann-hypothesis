module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GramDetSandwich
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.SplitModelToPlaceModel
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.UpdateEraseSubset
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GraphEquiv
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DoubleSumEqZero
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DegreeOneCellEqChartUpdate
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GramAtLocalLog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open scoped Matrix ComplexOrder

namespace MuFrameNormLocal

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem valAt_eq_complexPoint_reading {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    LowerBoundFree.valAt y s z = IndefiniteRowSideFullHecke.LowerBoundFree.valAt y s z := by
  classical
  by_cases h : ∃ v, IsValueAt y s z v
  · obtain ⟨v, hv⟩ := h
    rw [LowerBoundFree.valAt_eq hz hv,
      IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq hz (HermMetricEq.isValueAt_iff.1 hv)]
  · have h' : ¬ IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y s z := fun ⟨v, hv⟩ =>
      h ⟨v, HermMetricEq.isValueAt_iff.2 hv⟩
    rw [LowerBoundFree.valAt, dite_eq_right h, IndefiniteRowSideFullHecke.LowerBoundFree.valAt, dite_eq_right h']

theorem regularAt_of_isUnitOn {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k} {f u : Ω}
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hd : InFrameDomain y c f z)
    (hu : IsUnitOn y c f u) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y u z ∧ IndefiniteRowSideFullHecke.LowerBoundFree.valAt y u z ≠ 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv, hv0⟩ := hd.2
    exact hv0 (isValueAt_unique hz hv
      (HermMetricEq.isValueAt_iff.2 IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_zero))
  have hfi := HermMetricEq.regularAt_inv hf0 hd.2
  have hloc : ∀ s : Ω, (∃ n : ℕ, f ^ n * s ∈ chartRing ℤ (segreCoord y) c) →
      IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y s z := by
    rintro s ⟨n, hn⟩
    have h1 := (HermMetricEq.regularAt_pow hfi n).mul
      (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hd.1 hn)
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_mul] at h1
  have h1 := hloc u hu.2.1
  have h2 := hloc u⁻¹ hu.2.2
  refine ⟨h1, fun h0 => ?_⟩
  have hm := (h1.isValueAt hz).mul (h2.isValueAt hz)
  rw [mul_inv_cancel₀ hu.1, h0, zero_mul] at hm
  exact one_ne_zero (IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hz IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one hm)

end Values

section Gram

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ} {y : (Σ k, ι k) → Ω}
  {W : ChartBundle ℤ (segreCoord y) N E} {Xo : Set ((Σ k, ι k) → ℂ)}
  {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} {χ : Fin nc → SncChart P n Bd}

theorem gramAt_eq_of_frame (hA : HermMetric y W Xo χ) (hXo : Xo ⊆ mcPts (mCoordIdeal y))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ Xo) {l : Fin hA.m}
    (hd : InFrameDomain y (hA.chart l) (hA.fr l) z) {b : Fin N → E}
    {S : Matrix (Fin N) (Fin N) Ω} (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z)
    (hb : ∀ q, b q = ∑ p, S p q • hA.b l p) :
    LowerBoundFree.gramAt hA b z = (HermMetricEq.valM y S z)ᴴ * hA.gram l z * HermMetricEq.valM y S z := by
  rw [← hA.gramMatrix_change_of_frame hXo hz hd hS hb]
  have hv : ∀ s : Ω, LowerBoundFree.valAt y s z = IndefiniteRowSideFullHecke.LowerBoundFree.valAt y s z :=
    fun s => valAt_eq_complexPoint_reading (hXo hz)
  unfold LowerBoundFree.gramAt HermMetric.gramMatrixInFamily HermMetricEq.valM
  simp only [hv]

end Gram

section LogBounds

variable {X : Type*} {F : Filter X} {Q : X → Prop} {L : X → ℝ}

end LogBounds

section Local

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

end Local

end MuFrameNormLocal

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagonalFibreFubini

def wordCoef (i : ℕ) : ℕ → Fin 2 → ℝ := fun n =>
  if n = 0 then ![1, -1] else if n = 1 then ![0, 1] else if n < 2 + 2 * i then ![1, 0] else ![0, 1]

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem linProd_word (k i : ℕ) (hik : i < k) :
    wwLinProd k (wordCoef i) = (X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * k = 2 + 2 * i + r := ⟨2 * k - 2 - 2 * i, by omega⟩
  rw [wwLinProd, hr, Finset.prod_range_add, Finset.prod_range_add]
  have h1 : ∏ x ∈ Finset.range 2, (C (wordCoef i x 0) * X 0 + C (wordCoef i x 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
      (X 0 - X 1) * X 1 := by
    simp [Finset.prod_range_succ, wordCoef]
    ring
  have h2 : ∏ x ∈ Finset.range (2 * i),
      (C (wordCoef i (2 + x) 0) * X 0 + C (wordCoef i (2 + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) = X 0 ^ (2 * i) := by
    rw [← Finset.card_range (2 * i), ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x hx => ?_
    have hx' : x < 2 * i := Finset.mem_range.1 hx
    simp [wordCoef, show 2 + x ≠ 1 by omega, show 2 + x < 2 + 2 * i by omega]
  have h3 : ∏ x ∈ Finset.range r,
      (C (wordCoef i (2 + 2 * i + x) 0) * X 0 + C (wordCoef i (2 + 2 * i + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
        X 1 ^ r := by
    rw [← Finset.card_range r, ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x _ => ?_
    simp [wordCoef, show 2 + 2 * i + x ≠ 1 by omega,
      show ¬ 2 + 2 * i + x < 2 + 2 * i by omega]
  rw [h1, h2, h3, show 2 + 2 * i + r - 1 - 2 * i = r + 1 by omega, pow_succ]
  ring

end DiagonalFibreFubini


end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDoubleCechX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem DoubleCech.proof : GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DoubleCech.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DoubleCech.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq.proof

end GroundTheory.Heights₂.Heights.Swarm
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGeneratedCechTieX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cechD locPart cechCc cechZc mIdealOver chartRingOver quotPart
  secOver GeneratedV)

noncomputable section

namespace GeneratedCechTie

open HZeroRowPlaceData

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω}

theorem evMap_mul {I : ∀ k, Finset (ι k)} (hI : Good y I)
    (x x' : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) :
    evMap y I (x * x') = evMap y I x * evMap y I x' := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction x' using LocalizedModule.induction_on with
    | h m' t' =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
      obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective m'
      rw [LocalizedModule.mk_mul_mk, ← map_mul, evMap_mk y hI, evMap_mk y hI, evMap_mk y hI,
        Submonoid.coe_mul, map_mul, map_mul, mul_div_mul_comm]

theorem evMap_one {I : ∀ k, Finset (ι k)} (hI : Good y I) :
    evMap y I (1 : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) = 1 := by
  have h1 : (1 : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) =
      LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1 := by
    rw [map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : cellMon S I)),
      LocalizedModule.mk_pow, one_pow, one_pow]
  rw [h1, evMap_mk y hI]
  simp

theorem one_mem_locPart (T : Submonoid (MRingOver S ι)) :
    (1 : LocalizedModule T (MRingOver S ι ⧸ mIdealOver S y)) ∈
      locPart ι (quotPart S (mIdealOver S y)) T 0 := by
  have h1 : (1 : LocalizedModule T (MRingOver S ι ⧸ mIdealOver S y)) =
      LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1 := by
    rw [map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : T)),
      LocalizedModule.mk_pow, one_pow, one_pow]
  rw [h1]
  refine GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.mk_mem_locPart _ 1 0
    (GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun _ => rfl) ?_
  refine Submodule.subset_span ⟨1, ⟨fun k => by simp, ?_⟩, rfl⟩
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun k => by simp

theorem exists_cocycle {n : K → ℤ} {s : Ω} (hs : s ∈ secOver S y n) :
    ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) n 0,
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → evMap y (chart c) (z (cell0 c)) = s := by
  have hs' : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver S y c := by
    intro c hc
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs c) hc
  have hlift : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, Good y I.1 → ∃ w ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n,
      evMap y I.1 w = s := fun I hI =>
    exists_lift hI (fun k => Finset.min'_mem _ (I.2.1 k)) n
      (hs' _ fun k => hI k _ (Finset.min'_mem _ (I.2.1 k)))
  classical
  let z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0 := fun I =>
    if hI : Good y I.1 then (hlift I hI).choose else 0
  have hzC : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, z I ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n := by
    intro I
    by_cases hI : Good y I.1
    · simp only [z, dif_pos hI]; exact (hlift I hI).choose_spec.1
    · simp only [z, dif_neg hI]; exact Submodule.zero_mem _
  have hzv : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, Good y I.1 → evMap y I.1 (z I) = s := by
    intro I hI
    simp only [z, dif_pos hI]
    exact (hlift I hI).choose_spec.2
  have hzCc : z ∈ cechCc ι (quotPart S (mIdealOver S y)) n 0 :=
    Submodule.mem_pi.mpr fun I _ => hzC I
  have hzD : cechD S ι _ 0 z = 0 := by
    funext J
    by_cases hJ : Good y J.1
    · refine evMap_injOn y hJ n (cechD_mem_locPart n 0 hzCc J) (Submodule.zero_mem _) ?_
      have hconst : constD K ι Ω 0 (fun I => evMap y I.1 (z I)) J = constD K ι Ω 0 (fun _ => s) J :=
        CechPointVanish.constD_congr J.1 0 (fun I hIJ => hzv I fun k i hi => hJ k i (hIJ k hi)) J
          fun k => subset_refl _
      rw [evMap_cechD z J hJ, hconst, constD_const, Pi.zero_apply, map_zero]
    · unfold Good at hJ
      push Not at hJ
      obtain ⟨k, i, hi, hy0⟩ := hJ
      have := subsingleton_of_bad (S := S) hi hy0
      exact @Subsingleton.elim _ this _ _
  exact ⟨z, Submodule.mem_inf.mpr ⟨hzCc, hzD⟩, fun c hc => hzv (cell0 c) (good_chart hc)⟩

end GeneratedCechTie


open GeneratedCechTie HZeroRowPlaceData in
theorem GeneratedCechTie.proof : GeneratedCechTie.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y β _ hgen I
  obtain ⟨n, s, hs, hgen⟩ := hgen
  obtain ⟨c, rfl⟩ := degree_zero_cell_eq_chart I
  by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
  · choose z hz hzv using fun j => exists_cocycle (hs j)
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    have hcI : ∀ k, c k ∈ chart c k := fun k => Finset.mem_singleton_self _
    have hval : ∀ j, u j * (∏ k, y ⟨k, c k⟩ ^ (-β k)) * ∏ k, y ⟨k, c k⟩ ^ (-(-β) k) = u j := by
      intro j
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [Pi.neg_apply, neg_neg]
      rw [Finset.prod_congr rfl fun k _ => zpow_neg_mul_zpow_self (β k) (hc k), Finset.prod_const_one,
        mul_one]
    choose U hU hUv using fun j => exists_lift (good_chart hc) hcI (-β)
      (s := u j * ∏ k, y ⟨k, c k⟩ ^ (-β k)) (by rw [hval j]; exact hu j)
    refine ⟨n, z, U, hz, hU, ?_⟩
    let Z : Fin n → LocalizedModule (cellMon S (chart c)) (MRingOver S ι ⧸ mIdealOver S y) := fun j => z j (cell0 c)
    show ∑ j, U j * Z j = 1
    have hmem : ∑ j, U j * Z j ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S (chart c)) 0 := by
      refine Submodule.sum_mem _ fun j _ => ?_
      have h := GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.locPart_mul (hU j)
        (Submodule.mem_pi.mp (Submodule.mem_inf.mp (hz j)).1 (cell0 c) (Set.mem_univ _))
      rwa [neg_add_cancel] at h
    refine evMap_injOn y (good_chart hc) 0 hmem (one_mem_locPart _) ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [evMap_one (good_chart hc), map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evMap_mul (good_chart hc), hUv j, show evMap y (chart c) (Z j) = s j from hzv j c hc]
    ring
  · push Not at hc
    obtain ⟨k, hk⟩ := hc
    have := subsingleton_of_bad (S := S) (I := chart c) (Finset.mem_singleton_self (c k)) hk
    exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, @Subsingleton.elim _ this _ _⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNefAddBlock
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

namespace NefAddBlock

section Reduction

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]


theorem map_red {W : Ideal (Geo.MRing ι)} (hW : Geo.IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : Geo.MRing ι) ∈ W) (n : ℕ)
    (hdim : ringKrullDim (Geo.MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) ∧
      FieldNumbers.relDim (W.map (Bridge.GeoNum.red p)) = ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have hker : RingHom.ker (Bridge.GeoNum.red (ι := ι) p) ≤ W := by
    rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p (W.map (Bridge.GeoNum.red p)))
    rw [hcm] at this
    exact this.symm

end Reduction

end NefAddBlock

end GroundTheory.Heights₂.Heights
end
end

