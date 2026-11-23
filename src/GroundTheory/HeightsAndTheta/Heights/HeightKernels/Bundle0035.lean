module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExc
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPointLineDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualPointLineDegreeAlt

theorem sum_log_norm {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  classical
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ => ‖φ x‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real,
    Real.norm_eq_abs]

theorem isMultiHomog_X {T : Type} [Fintype T] (t : T) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨⟩ := k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single t]
  · simp
  · intro c _ hc
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hc (sigma_mk_injective h).symm
  · simp

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} {K' : Type} [Field K'] [NumberField K'] [Algebra K K']

theorem dualNormSq_point (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (v : Fin i → K') (σ' : K' →+* ℂ) :
    dualNormSq b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) =
      (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
  classical
  set σ := σ'.comp (algebraMap K K') with hσ
  let w : (K →+* ℂ) × Fin i → ℂ := fun q => if q.1 = σ then σ' (v q.2) else 0
  have hw : dualRecover b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) = w := by
    rw [dualRecover, LinearEquiv.symm_apply_eq]
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      dualEmbMatrix, w, Fintype.sum_prod_type, mul_ite, mul_zero, dualPointCoord, map_sum, map_mul]
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [hτ]) (by simp)]
    simp [hσ]
  rw [dualNormSq, hw, Finset.sum_eq_single σ, Matrix.det_unique]
  · simp only [w, if_true, gramAt]
    rfl
  · intro τ _ hτ
    have h0 : (fun j => w (τ, j)) = 0 := by
      funext j
      simp [w, hτ]
    rw [h0]
    simp
  · simp

end DualPointLineDegreeAlt


open DualPointLineDegreeAlt in
theorem DualPointLineDegree.proof (hPt : DualCurvePoint.Statement) (hPos : PointDegCPos.Statement)
    (hAr : PointArInt.Statement) (hVert : PointVertR.Statement) (hIdx : DualLineIndex.Statement)
    (hSemi : DualLineSemipositive.Statement) : DualPointLineDegree.Statement := by
  intro K _ _ i F T _ _ b hb II hII W hW hbW
  obtain ⟨K', _, _, _, v, hv, rfl⟩ := hPt K i F T b W hW hbW
  set y := dualPointCoord b v with hy
  set A := dualLine F b hb with hA
  refine ⟨hPos T K' y hW, K', inferInstance, inferInstance, inferInstance, v, hv, ?_⟩
  obtain ⟨t₀, ht₀⟩ := hW.2.1.2.2 ()
  set s : MRing (dualBlocks T) := X ⟨(), t₀⟩ with hs
  have hs1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1) := isMultiHomog_X t₀
  have hsec : IsSectionOn (mCoordIdeal y) A s := ⟨fun _ => 1, fun _ => rfl, hs1, ht₀⟩
  have hsm : IsSmoothHerm A := (hSemi K i F T b hb).1
  have hy0 : y ⟨(), t₀⟩ ≠ 0 := by
    intro h
    apply ht₀
    change mConeMap y (X ⟨(), t₀⟩) = 0
    simp [mConeMap, h]

  have hR := (hII Unit (dualBlocks T)).2.2 (mCoordIdeal y) 0 Fin.elim0 A s (fun _ => 1) hW
    (fun j => j.elim0) hsm (fun _ => rfl) hs1 ht₀
  have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) A : Fin 1 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) =
      ![A] := by
    funext j
    fin_cases j
    rfl
  rw [hsnoc, Inter.SpecIntHeightFormula.proof Inter.arithVarZero Unit (dualBlocks T) _ _ A s hW hsm hsec] at hR

  have hV := hVert T K' y s hW hs1 ht₀
  have hI := hAr T K' y A s hW hsec
  have hL := hIdx K i F T b K' v hv
  have hys : aeval y s = y ⟨(), t₀⟩ := by simp [hs]
  have hlog : ∀ σ' : K' →+* ℂ, logNorm A s (fun p => σ' (y p)) =
      Real.log ‖σ' (y ⟨(), t₀⟩)‖ -
        1 / 2 * Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
    intro σ'
    have hq : dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) =
        (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re :=
      dualNormSq_point b hb v σ'
    have hpos : 0 < dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) := by
      have := A.pos (fun p => σ' (y p)) (fun _ => ⟨t₀, (map_ne_zero σ').mpr hy0⟩)
      simpa [hA, dualLine] using this
    have hne : ‖σ' (y ⟨(), t₀⟩)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hy0)
    simp only [logNorm, hs, map_X, eval_X, hA, dualLine]
    rw [Real.log_div hne (Real.sqrt_pos.mpr hpos).ne', Real.log_sqrt hpos.le, ← hq]
    ring
  rw [Finset.sum_congr rfl fun σ' _ => hlog σ', Finset.sum_sub_distrib,
    sum_log_norm hy0, ← Finset.mul_sum] at hI
  rw [hys] at hV
  have hn : (0 : ℝ) < Module.finrank ℚ K' := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < degC (mCoordIdeal y) := by exact_mod_cast hPos T K' y hW
  rw [← hy] at hL
  have hdeg : F.lineDegree K' v = (-Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
      (1 : Submodule (𝓞 K') K').toAddSubgroup) - 1 / 2 * ∑ σ' : K' →+* ℂ,
        Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) /
      Module.finrank ℚ K' := by
    unfold HermLattice.lineDegree subDegree normalise
    rw [eq_inv_of_mul_eq_one_left hL, Real.log_inv]
  have hR' : II Unit (dualBlocks T) (mCoordIdeal y) 1 ![A] =
      vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0 := hR
  have key : (vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0) *
      Module.finrank ℚ K' = degC (mCoordIdeal y) * (Real.log (genIndex
        (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup) +
        1 / 2 * ∑ σ' : K' →+* ℂ,
          Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) := by
    linear_combination hV - hI
  rw [hdeg, hR', neg_div, ← neg_div, div_eq_div_iff hn.ne' hd.ne']
  linear_combination key

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedGraphFibre

variable {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]


open Classical in
def vertWeight {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then 0 else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

theorem vertR_eq_finsum (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    vertR P L s = ∑ᶠ W, (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℝ) * vertWeight L W := by
  classical
  rw [vertR, finsum_mem_def]
  refine finsum_congr fun W => ?_
  simp only [Set.indicator, ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, vertWeight]
  by_cases hW : W ∈ divSupp P s
  · rw [if_pos hW, if_pos hW]
  · rw [if_neg hW, if_neg hW, Nat.cast_zero, zero_mul]

theorem finite_support (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    (Function.support fun W => (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℝ) * vertWeight L W).Finite :=
  (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s).support.finite_toSet.subset fun W hW =>
    Finsupp.mem_support_iff.mpr fun h0 => hW (by simp [h0])

theorem vertR_sub (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s₁ s₂ : MRing ι)
    (E : Ideal (MRing ι)) (hhor : ¬ IsHorizontal E)
    (hE : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₂ E : ℤ) = ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₁ E + 1)
    (hW : ∀ W, ¬ IsHorizontal W → W ≠ E → ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₂ W = ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₁ W) :
    vertR P L s₁ - vertR P L s₂ = -((geoNum n E (fun j => (L j).a) : ℝ) * Real.log (charOf E)) := by
  classical
  rw [vertR_eq_finsum, vertR_eq_finsum, ← finsum_sub_distrib (finite_support P L s₁) (finite_support P L s₂)]
  have hpt : ∀ W, (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₁ W : ℝ) * vertWeight L W - (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₂ W : ℝ) * vertWeight L W =
      if W = E then -vertWeight L E else 0 := by
    intro W
    by_cases hWh : IsHorizontal W
    · have hne : W ≠ E := fun h => hhor (h ▸ hWh)
      simp [vertWeight, hWh, hne]
    · by_cases hWE : W = E
      · subst hWE
        have hR : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₂ W : ℝ) = ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₁ W + 1 := by exact_mod_cast hE
        rw [if_pos rfl, hR]
        ring
      · rw [if_neg hWE, hW W hWh hWE, sub_self]
  rw [finsum_congr hpt, finsum_eq_single _ E (fun W hW => if_neg hW), if_pos rfl]
  simp [vertWeight, hhor]

end StackedGraphFibre


open StackedGraphFibre in
theorem DualStackedGraphFibre.proof (hCyc : DualStackedExcCycle.Statement)
    (hSec : DualStackedExcGeoSecond.Statement) (hFir : DualStackedExcGeoFirst.Statement) :
    DualStackedGraphFibre.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab t L hL
  obtain ⟨E, hE, hhor, hEt⟩ := hCyc K i F F' T b b' a hi hlt hcov hab
  have key := vertR_sub (stackedGraph b' a) L (graphSecond t) (C (a t) * graphFirst t) E hhor (hEt t).1
    (hEt t).2
  have ha : ∀ s, a s ≠ 0 := fun s hs =>
    b.ne_zero s (Subtype.ext (by rw [hab s, hs, zero_smul]; rfl))
  refine ⟨fun hall => ?_, fun ⟨j, hj⟩ => ?_⟩
  · have hd : (fun j => (L j).a) = fun _ => degSecond := funext hall
    rw [key, hd, hSec K i F F' T b b' a hi hlt hcov hab E hE, ← DualLatticeIndex.proof K i F F' hlt.le,
      DualStackedDegreeAlt.relIndex_stacked hlt.le b b' a hab,
      Real.log_prod (fun s _ => abs_ne_zero.mpr (Int.cast_ne_zero.mpr (ha s)))]
  · rw [key, hFir K i F F' T b b' a hi hlt hcov hab E hE (fun j => (L j).a) hL ⟨j, hj⟩]
    simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassFibreDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

namespace GrassmannianFibreDegree

variable (n p : ℕ) [Fact p.Prime]

theorem span_eq_ker :
    (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) =
      RingHom.ker (Bridge.GeoNum.red (ι := plBlocks 1 1 n) p) :=
  (Bridge.GeoNum.ker_red p).symm

theorem isPrime : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).IsPrime := by
  rw [span_eq_ker]
  exact RingHom.ker_isPrime _

theorem isRelevant : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) := by
  intro k
  refine ⟨plAnchor 1 n, ?_⟩
  rw [span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]
  exact X_ne_zero _

theorem divSupp_eq :
    divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) = {Ideal.span {C (p : ℤ)}} := by
  have := isPrime n p
  ext W
  simp only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, isRelevant n p⟩

theorem ringKrullDim_quot :
    ringKrullDim (MRing (plBlocks 1 1 n) ⧸ (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))) =
      ((n + Fintype.card (Fin 1) : ℕ) : WithBot ℕ∞) := by
  rw [span_eq_ker, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  have hc : Nat.card ((_ : Fin 1) × PlIdx 1 n) = n + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
    omega
  rw [ENat.card_eq_coe_natCard, hc, Fintype.card_fin]
  simp

def coordEquiv : (Σ _ : Unit, Fin (n + 1)) ≃ (Σ _ : Fin 1, PlIdx 1 n) :=
  Equiv.ofBijective (GrassmannianLinesProjective.coordMap n)
    ⟨(GrassmannianLinesProjective.isBlockMap n).2.1, GrassmannianLinesProjective.coordMap_surjective n⟩

theorem intNum_bot :
    NumbersDVR.intNum (ZMod p) (⊥ : Ideal (NumbersDVR.MRing (plBlocks 1 1 n) (ZMod p)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have h := FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (Equiv.ofUnique Unit (Fin 1))
    (coordEquiv n) (fun _ => Subsingleton.elim _ _)
    (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p)))
    (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ))
  rw [Ideal.map_bot] at h
  rw [h]
  exact FieldNumbers.intNum_projectiveSpace (ZMod p) n

theorem geoNum_span :
    geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have := isPrime n p
  have hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) :=
    ⟨isPrime n p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by
      rw [Set.mem_singleton_iff.mp hf]
      exact Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant n p⟩
  rw [← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_quot n p)]
  have hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).map
      (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker n p).le
  rw [hb]
  exact intNum_bot n p

end GrassmannianFibreDegree


open GrassmannianFibreDegree in
theorem GrassFibreDegree.proof : GrassFibreDegree.Statement := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have := isPrime n p
  have hW : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) ∈
      divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) := by
    rw [divSupp_eq]
    rfl
  have hg : geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun j => ((fun _ : Fin n => fsMulti (plBlocks 1 1 n)) j).a) = 1 :=
    geoNum_span n p
  rw [GrassmannianLinesProjective.grassIdeal_eq_bot]
  unfold vertR
  rw [divSupp_eq, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal hp hW),
    Inter.Conservation.charOf_eq hp hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]
  simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace VerticalPointLength

theorem maximal_and_mult_eq (hCh : VertPointChart.Statement) (hMC : VertPointMultChart.Statement)
    (hSQ : SectionQuotLocal.Statement) {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} {s : MRing (fun _ : Unit => T)} (hP : IsArithVar (mCoordIdeal y) 1)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) {W : Ideal (MRing (fun _ : Unit => T))}
    (hW : W ∈ divSupp (mCoordIdeal y) s) :
    (curvePtIdeal y W).IsMaximal ∧
      multAt (mCoordIdeal y ⊔ Ideal.span {s}) W = locLen (curvePtIdeal y W) (sectionQuot y (aeval y s)) := by
  obtain ⟨t, ht⟩ := hW.2 ()
  obtain ⟨hmax, hrat, hmem⟩ := hCh T K' y s hP hs hsP W hW t ht
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨a, b, -, hb, hab⟩ := (hmem 1 s hs).mp hsW
  rw [pow_one] at hab
  refine ⟨hmax, ?_⟩
  rw [hMC T K' y s hP hs hsP W hW t ht a b hb hab,
    hSQ T K' y s hP hs hsP _ t hmax.isPrime hrat a b hb hab]

end VerticalPointLength

theorem VertPointLength.proof (hCh : VertPointChart.Statement)
    (hInj : VertPointInj.Statement) (hSurj : VertPointSurj.Statement)
    (hMC : VertPointMultChart.Statement) (hSQ : SectionQuotLocal.Statement) :
    VertPointLength.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  refine ⟨⟨fun W hW => ?_, hInj T K' y s hP hs hsP,
      fun m hm => hSurj T K' y s hP hs hsP m hm.1 hm.2⟩,
    fun W hW => (VerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW).2⟩
  obtain ⟨hmax, hmult⟩ := VerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW
  exact ⟨hmax, hmult ▸ (IndefiniteRowSideFullHecke.Inter.multAt_pos_of_mem_divSupp hW).ne'⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLinear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def linPointMap {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    MRing (stackedBlocks T) →+* MvPolynomial (Option (Fin n)) k :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl _, t⟩ => C (α t) * X none
    | ⟨.inr _, t⟩ => ∑ j, C (M t j) * X (some j)

def linPrime {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    Ideal (MRing (stackedBlocks T)) :=
  RingHom.ker (linPointMap α M)

def LinFormsIndep {T : Type} {k : Type} [Field k] {n : ℕ} (M : T → Fin n → k) : Prop :=
  ∀ w : Fin n → k, (∀ t, ∑ j, M t j * w j = 0) → w = 0

def DualStackedExcLinear.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      ∃ (k : Type) (_ : Field k) (_ : Fintype k) (α : T → k) (M : T → Fin i → k),
        Submodule.span ℤ (Set.range α) = ⊤ ∧ LinFormsIndep M ∧ E = linPrime α M ∧
          Fintype.card k = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

def LinPrimeCut.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (n : ℕ) (α : T → k) (M : T → Fin (n + 2) → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : T, graphSecond c ∉ linPrime α M →
      ∃ M' : T → Fin (n + 1) → k, LinFormsIndep M' ∧
        divSupp (linPrime α M) (graphSecond c) = {linPrime α M'} ∧
        multAt (linPrime α M ⊔ Ideal.span {graphSecond c}) (linPrime α M') = 1

def LinPrimeBase.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (α : T → k) (M : T → Fin 1 → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : (κ : Unit ⊕ Unit) → stackedBlocks T κ,
      (∀ κ, (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) ∉ linPrime α M) →
      Nonempty ((MRing (stackedBlocks T) ⧸ (linPrime α M ⊔
        Ideal.span (Set.range fun κ => (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) - 1))) ≃+* k)

namespace LinPrimeExample

theorem linPointMap_first {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphFirst t) = C (α t) * X none := by
  simp [linPointMap, graphFirst]

theorem linPointMap_second {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphSecond t) = ∑ j, C (M t j) * X (some j) := by
  simp [linPointMap, graphSecond]

end LinPrimeExample

end

end GroundTheory.Heights₂.Heights
end

