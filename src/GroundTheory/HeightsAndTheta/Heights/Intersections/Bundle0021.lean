module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.SpanSingletonEqRangeLsmul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem geoNum_zero_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (b : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 W b := by
  unfold geoNum
  split_ifs <;> positivity

theorem span_singleton_eq_range_lsmul {A : Type*} [CommRing A] (x : A) :
    Ideal.span {x} = LinearMap.range (LinearMap.lsmul A A x) := by
  ext z
  simp [Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]

theorem regularityLocalCardinality_holds.proof (hD : regularityLocalDimension_holds.Statement) (hR : regularityLocalResidue_holds.Statement) : regularityLocalCardinality_holds.Statement := by
  intro K _ ι _ P s a W b y hP hs hsP hW hy hy0
  obtain ⟨hloc, hnoeth, hdim⟩ := hD K ι P s a W hP hs hsP hW
  have := hloc
  have := hnoeth
  have : P.IsPrime := hP.2.1.1
  have : IsDomain (locRing P W) := inferInstance
  have : Ring.KrullDimLE 1 (locRing P W) := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim
  obtain ⟨-, hcard⟩ := hR K ι P s a W b hP hs hsP hW
  have hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤ := by
    rw [locIdeal_eq_span hy, span_singleton_eq_range_lsmul]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'
  rw [card_eq_card_residueField_pow_length _ hfin, hcard]
  have hg : (geoNum 0 W b : ℝ) = ((geoNum 0 W b).toNat : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (geoNum_zero_nonneg W b)).symm
  rw [hg]
  push_cast
  rw [Real.log_pow, Real.log_pow]

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsMeasurable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsAbsMeasurable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    AEStronglyMeasurable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w|)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsMonoSemiPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsMonoSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E D : HermLine ι) (t : MRing ι),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → (∀ j, IsSemiPosHerm (M j)) →
    IsSmoothHerm E → IsSectionOn Q E t → IsSmoothHerm D → D.a = 0 →
    (∀ z ∈ mcPts Q, eval z (map (Int.castRingHom ℂ) t) ≠ 0 → logNorm E t z ≤ Real.log (D.h z)) →
    ptsIntegral Q (pot M) (logNorm E t) ≤ ptsIntegral Q (pot M) (fun z => Real.log (D.h z))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsRegLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsRegLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → IsSmoothHerm E → t ∉ Q →
    Filter.Tendsto (fun ε => ptsIntegral Q (pot M) (fun z => Real.log ((regLine E t ht ε).h z)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ptsIntegral Q (pot M) (logNorm E t)))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StRegCurvBound
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def RegCurvBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsSmoothHerm E → ∃ C : ℕ, ∀ ε : ℝ, 0 < ε →
      IsSemiPosHerm ((E.tensor (regLine E t ht ε)).tensor
        (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (C : ℤ))))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFAt (I : AllFam) (r : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    I K' ι' P' (d + r) (Fin.append L' N) =
      (J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

def PFStep.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ r : ℕ, PFAt I r → PFAt I (r + 1)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemRegRingSpecZ
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Subring (funField P) where
  carrier := {x | ∀ W, IsClosedPt W → P ≤ W → (x : FractionRing (MRing ι ⧸ P)) ∈ locRing P W}
  mul_mem' ha hb W h1 h2 := mul_mem (ha W h1 h2) (hb W h1 h2)
  one_mem' _ _ _ := one_mem _
  add_mem' ha hb W h1 h2 := add_mem (ha W h1 h2) (hb W h1 h2)
  zero_mem' _ _ _ := zero_mem _
  neg_mem' ha W h1 h2 := neg_mem (ha W h1 h2)

def RegularityOrder.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → Module.Free ℤ (regRing P) ∧ Module.Finite ℤ (regRing P) ∧
      ∀ hF : IsField (funField P), letI := hF.toField; ∀ [NumberField (funField P)],
        Module.finrank ℤ (regRing P) = Module.finrank ℚ (funField P)

end

end GroundTheory.Heights₂.Heights.Inter
end

