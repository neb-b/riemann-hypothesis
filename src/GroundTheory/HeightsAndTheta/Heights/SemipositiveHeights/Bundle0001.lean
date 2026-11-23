module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.BigLineBundleMoriwaki
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem BigLineBundleMoriwaki.of_moriwakiBig (hM : MoriwakiBigStatement) : ArithmeticVolumeLowerBound :=
  HilbertSamuel.ArithmeticVolumeBig.arithmeticVolumeBig_smoothFibre (HilbertSamuel.ArithmeticVolumeBig.of_moriwakiBig_only hM)

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.MetricLocalB
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace MetricLocalB

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem induct (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) :
    ∀ (n : ℕ) (P : Ideal (MRing ι)) (L L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
      IsArithVar P n → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (L j)) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (L' j)) →
      (∀ j, (L j).a = (L' j).a) → (∀ j, ∀ z ∈ mcPts P, (L j).h z = (L' j).h z) →
      I P n L = I P n L'
  | 0, P, L, L', _, _, _, _, _ => by rw [Subsingleton.elim L L']
  | n + 1, P, L, L', hP, hL, hL', ha, hh => by

    have key : ∀ (C C' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (b : K → ℕ), (∀ k, C.a k = b k) → (∀ k, C'.a k = b k) →
        ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm C → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm C' → (∀ z ∈ mcPts P, C.h z = C'.h z) →
        I P (n + 1) (Fin.snoc (Fin.init L) C) = I P (n + 1) (Fin.snoc (Fin.init L') C') := by
      intro C C' b hC hC' hCs hC's hCC'
      have hPp : P.IsPrime := hP.2.1.1
      choose i hi using hP.2.1.2.2
      have hs := isMultiHomog_secOf i b
      have hsP := secOf_not_mem hPp hi b
      rw [hI.2.2 P n (Fin.init L) C (secOf i b) b hP (fun j => hL j.castSucc) hCs hC hs hsP,
        hI.2.2 P n (Fin.init L') C' (secOf i b) b hP (fun j => hL' j.castSucc) hC's hC' hs hsP]
      unfold recR
      congr 1
      · refine finsum_mem_congr rfl fun W hW => ?_
        by_cases hWh : IsHorizontal W
        · have hWa : IsArithVar W n := by
            have hWmin := hW.1
            have hWmh := isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1.2.1 hs hWmin
            refine ⟨hP.1, ⟨hWmin.1.1, hWmh, hW.2⟩, hWh, ?_⟩
            have := hPp
            have hdim := dim_quot_minimal_add_one P W (secOf i b) hsP hWmin
            rw [hP.2.2.2, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega] at hdim
            exact withBot_eq_of_add_one hdim
          have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
          have e := induct I hI n W (Fin.init L) (Fin.init L') hWa (fun j => hL j.castSucc)
            (fun j => hL' j.castSucc) (fun j => ha j.castSucc)
            (fun j z hz => hh j.castSucc z ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩)
          simp only [ite_eq_left hWh, e]
        · have e : (fun j => (Fin.init L j).a) = fun j => (Fin.init L' j).a :=
            funext fun j => ha j.castSucc
          simp only [ite_eq_right hWh, e]
      · unfold arInt
        exact (ptsLocal K ι P n 0 _ _ _ _
          (fun j z hz => congrArg Real.log (hh j.castSucc z hz))
          (fun z hz => by unfold logNorm; rw [hCC' z hz])).2

    set A := L (Fin.last n) with hA
    set A' := L' (Fin.last n) with hA'
    let b : K → ℕ := fun k => (A.a k).natAbs
    let B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := HermLine.sqMetric b
    have hB : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm B := isSmoothHerm_sqMetric b
    let c : K → ℕ := fun k => (A.a k + (A.a k).natAbs).toNat
    have hBa : ∀ k, B.a k = b k := fun k => rfl
    have hc : ∀ k, (A.tensor B).a k = c k := by
      intro k
      show A.a k + ((A.a k).natAbs : ℤ) = ((A.a k + (A.a k).natAbs).toNat : ℤ)
      rw [Int.toNat_of_nonneg (by omega)]
    have hc' : ∀ k, (A'.tensor B).a k = c k := by
      intro k
      rw [← hc k]
      show A'.a k + B.a k = A.a k + B.a k
      rw [hA, hA', ha (Fin.last n)]
    have hAs : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A := hL _
    have hA's : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' := hL' _
    have e1 := hI.2.1 P n (Fin.init L) A B hP (fun j => hL j.castSucc) hAs hB
    have e1' := hI.2.1 P n (Fin.init L') A' B hP (fun j => hL' j.castSucc) hA's hB
    have k1 := key (A.tensor B) (A'.tensor B) c hc hc' (isSmoothHerm_tensor hAs hB)
      (isSmoothHerm_tensor hA's hB) (fun z hz => by
        show A.h z * B.h z = A'.h z * B.h z
        rw [hA, hA', hh (Fin.last n) z hz])
    have k2 := key B B b hBa hBa hB hB (fun _ _ => rfl)
    rw [e1, e1', k2] at k1
    simpa only [hA, hA', Fin.snoc_init_self] using add_right_cancel k1

end MetricLocalB

theorem MetricLocalB.full : MetricLocalStatement := by
  intro K _ ι _ I hI P n L L' hP hL hL' ha hh
  exact MetricLocalB.induct I hI n P L L' hP hL hL' ha hh

end GroundTheory.Heights₂.Heights
end
end

