module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0009
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0005
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldLeLocRing
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)

abbrev HLine {K : Type} [Fintype K] (ι : K → Type) := ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι

section Objects

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev MCone (ι : K → Type) := (Σ k, ι k) → ℂ

def logH (L : HLine ι) : MCone ι → ℝ := fun z => Real.log (L.h z)


variable (ι) in
structure Res (P : Ideal (MRing ι ℂ)) (e : ℕ) where

  D : Ideal (MRing ι ℂ)
  homog : IsMultiHomogIdeal D
  not_le : ¬ D ≤ P

  R : ReciprocityTheory.AnForm.R.AlgRes ι P D e

namespace Res

variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)

end Res


def IsProjVarQ (P0 : Ideal (MRing ι ℚ)) (e : ℕ) : Prop :=
  IsMultiProjPrime P0 ∧ ringKrullDim (MRing ι ℚ ⧸ P0) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)

end Objects

section Ring

variable {K : Type} {ι : K → Type}

end Ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.CardLeRingKrullDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace RegularityRelativeClosedPoint

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq K]

def killBlocks (S : Finset K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p

theorem killBlocks_form (S : Finset K) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) :
    killBlocks S g = (∏ k, (if k ∈ S then (0 : MRing ι) else 1) ^ a k) * g := by
  have e : (fun p : (Σ k, ι k) => if p.1 ∈ S then (0 : MRing ι) else X p) =
      fun p => (if p.1 ∈ S then (0 : MRing ι) else 1) * X p := by
    funext p
    split_ifs <;> simp
  have h := regularityLocalResidue_holds.aeval_blockScale_int hg (fun k => if k ∈ S then (0 : MRing ι) else 1) X
  rw [aeval_X_left_apply] at h
  rw [killBlocks, e]
  exact h

theorem le_comap_killBlocks (S : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W) :
    W ≤ W.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hW
  rw [Ideal.span_le]
  intro g hg
  obtain ⟨a, ha⟩ := hT g hg
  rw [SetLike.mem_coe, Ideal.mem_comap, killBlocks_form S ha]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span hg)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_comp {S T : Finset K} (hST : S ⊆ T) :
    (killBlocks T).comp (killBlocks S) = (killBlocks T : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [AlgHom.comp_apply, killBlocks, aeval_X]
  by_cases h : p.1 ∈ S
  · simp [h, hST h]
  · simp [h]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_empty : (killBlocks ∅ : MRing ι →ₐ[ℤ] MRing ι) = AlgHom.id ℤ (MRing ι) :=
  MvPolynomial.algHom_ext fun p => by simp [killBlocks]

theorem card_le_ringKrullDim (W : Ideal (MRing ι)) [W.IsPrime] (hWh : IsMultiHomogIdeal W)
    (hWr : IsRelevant W) : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ W) := by
  choose j hj using hWr
  let Q : Finset K → Ideal (MRing ι) := fun S => W.comap (killBlocks S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => Ideal.comap_isPrime _ _
  have hstep : ∀ S k, k ∉ S → Q S < Q (insert k S) := by
    intro S k hk
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, X ⟨k, j k⟩, ?_, ?_⟩
    · have h1 := Ideal.mem_comap.mp (le_comap_killBlocks (insert k S) hWh (Ideal.mem_comap.mp hg))
      rw [← AlgHom.comp_apply, killBlocks_comp (Finset.subset_insert k S)] at h1
      exact Ideal.mem_comap.mpr h1
    · rw [Ideal.mem_comap]
      simp [killBlocks]
    · intro h
      rw [Ideal.mem_comap] at h
      simp only [killBlocks, aeval_X, if_neg hk] at h
      exact hj k h
  have chain : ∀ S : Finset K, (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) ≤
      ringKrullDim (MRing ι ⧸ Q ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have : (Q (insert k S)).IsPrime := hQp _
      have h1 := HorizNotMem.ringKrullDim_quotient_add_one_le (hstep S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + (ringKrullDim (MRing ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) := by gcongr
        _ ≤ _ := ih
  have hQ0 : Q ∅ = W := by
    ext g
    simp [Q, killBlocks_empty]
  have : (Q Finset.univ).IsPrime := hQp _
  have : IsDomain (MRing ι ⧸ Q Finset.univ) := Ideal.Quotient.isDomain _
  have h3 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ Q Finset.univ) := ringKrullDim_nonneg_of_nontrivial
  have hc := chain Finset.univ
  rw [Finset.card_univ, hQ0] at hc
  calc ((Fintype.card K : ℕ) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + 0 := (add_zero _).symm
    _ ≤ (Fintype.card K : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q Finset.univ) := by gcongr
    _ ≤ _ := hc

end RegularityRelativeClosedPoint

theorem RegularityRelativeClosedPoint.proof : RegularityRelativeClosedPoint.Statement := by
  intro K _ ι _ P W hP hW hPW hne
  classical
  refine ⟨hW, ?_⟩
  obtain ⟨-, ⟨hPp, -, -⟩, -, hPdim⟩ := hP
  obtain ⟨hWp, hWh, hWr⟩ := hW
  have := hPp
  have := hWp
  have e := mvPolynomialInt_dimFormula P W hPW
  rw [hPdim] at e
  have hh : (W.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
    hne (le_antisymm (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0) hPW)
  have hlow := RegularityRelativeClosedPoint.card_le_ringKrullDim W hWh hWr
  generalize ringKrullDim (MRing ι ⧸ W) = m at e hlow ⊢
  generalize (W.map (Ideal.Quotient.mk P)).height = h at e hh
  induction m using WithBot.recBotCoe with
  | bot => exact absurd hlow (by simp)
  | coe m =>
    have e' : m + h = ((1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast e
    have hlow' : ((Fintype.card K : ℕ) : ℕ∞) ≤ m := by exact_mod_cast hlow
    induction m using ENat.recTopCoe with
    | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
    | coe m =>
      induction h using ENat.recTopCoe with
      | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
      | coe h =>
        have h1 : m + h = 1 + Fintype.card K := by exact_mod_cast e'
        have h2 : Fintype.card K ≤ m := by exact_mod_cast hlow'
        have h3 : h ≠ 0 := by exact_mod_cast hh
        have h4 : m = Fintype.card K := by omega
        rw [h4]
        rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIntValuationLtOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityValuationCentre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsMultiProjPrime P → ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ] (v : Valuation (funField P) Γ) (n : ℤ),
    v (n : funField P) < 1 →
    ∃ W : Ideal (MRing ι), IsMultiProjPrime W ∧ P ≤ W ∧ C n ∈ W ∧
      ∀ z : funField P, (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W → v z ≤ 1

theorem RegularityValuationCentre.exists_int_valuation_lt_one {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ n : ℤ, n ≠ 0 ∧ v.valuation F (n : F) < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hc : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxv (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨n, hn0, ?_⟩
  have e : (n : F) = algebraMap (NumberField.RingOfIntegers F) F (algebraMap ℤ _ n) := by simp
  rw [e, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact hn

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IdDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionDivisorPushforward.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (E : Ideal (MRing ι') → ℤ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ W' ∈ divSupp P' (rename v s), imageZ v W' = W →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (fibreIdeal κ G') 0 Fin.elim0) →
    ∑ᶠ W' ∈ {W' | W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W},
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' =
      J (fibreIdeal κ G) 0 Fin.elim0 * multAt (imageZ v P' ⊔ Ideal.span {s}) W

section Inhabitants


end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalPrime.proof (h₁ : RegularityOrder.Statement) : RegularityLocalPrime.Statement := by
  intro K _ ι _ P p y hP hp hy
  have hPp : P.IsPrime := hP.2.1.1
  obtain ⟨c, hc0, hc⟩ := RegularityDenominator.proof RegularityDivisorSupportClosed.proof LocRingPow.proof K ι P y hP
  have hcR : c ∈ regRing P := fun W h1 h2 => (hc W h1 h2).1
  have : Module.Finite ℤ (regRing P) := (h₁ K ι P hP).2.1
  have hci : IsIntegral ℤ (⟨c, hcR⟩ : regRing P) := Algebra.IsIntegral.isIntegral _
  have hne := Ideal.comap_ne_bot_of_integral_mem (I := Ideal.span {(⟨c, hcR⟩ : regRing P)})
    (fun h => hc0 (congrArg Subtype.val h)) (Ideal.mem_span_singleton_self _) hci
  obtain ⟨N, hN, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hN)
  have hNF : ((N : funField P) : FractionRing (MRing ι ⧸ P)) =
      ((d : funField P) : FractionRing (MRing ι ⧸ P)) * (c : FractionRing (MRing ι ⧸ P)) := by
    have h := congrArg (fun z : regRing P => ((z : funField P) : FractionRing (MRing ι ⧸ P))) hd
    simp only [Subring.coe_mul, algebraMap_int_eq, eq_intCast, SubringClass.coe_intCast] at h
    simp only [SubringClass.coe_intCast]
    exact h.symm
  have hpu : p.natAbs ≠ 1 := fun h => hp.not_isUnit (Int.isUnit_iff_natAbs_eq.mpr h)
  obtain ⟨m, hNm, hpm⟩ := (Int.finiteMultiplicity_iff.mpr ⟨hpu, hN0⟩).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity p N = e at hNm
  refine ⟨m, hpm, fun W h1 h2 => ?_⟩
  rw [Subring.coe_mul, SubringClass.coe_intCast]
  by_cases hpW : C p ∈ W
  · exact mul_mem (intCast_mem _ m) (hy W h1 h2 hpW)
  have hCp : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C p)) = (p : _) := by
    rw [eq_intCast C p, map_intCast, map_intCast]
  have hp0 : (p : FractionRing (MRing ι ⧸ P)) ≠ 0 := by
    intro h
    apply hpW
    apply h2
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← IsFractionRing.to_map_eq_zero_iff (K := FractionRing (MRing ι ⧸ P)),
      hCp, h]
  have hq : (p : FractionRing (MRing ι ⧸ P))⁻¹ ∈ locRing P W :=
    frac_mem_locRing h2 (RegularityDenominator.isMultiHomog_C 1) (RegularityDenominator.isMultiHomog_C p) hpW
      (by rw [hCp, map_one, map_one, map_one, inv_mul_cancel₀ hp0])
  have hyc : (y : FractionRing (MRing ι ⧸ P)) * (c : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by
    have := (hc W h1 h2).2
    rwa [Subring.coe_mul] at this
  have hdW : ((d : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := d.2 W h1 h2
  have key : (m : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) =
      (p : FractionRing (MRing ι ⧸ P))⁻¹ ^ e *
        (((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c)) := by
    have hN' : ((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c) =
        (p : FractionRing (MRing ι ⧸ P)) ^ e * m * y := by
      rw [show ((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c) =
        ((N : funField P) : FractionRing (MRing ι ⧸ P)) * y by rw [hNF]; ring, SubringClass.coe_intCast,
        hNm, Int.cast_mul, Int.cast_pow]
    rw [hN', inv_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  rw [key]
  exact mul_mem (pow_mem hq _) (mul_mem hdW hyc)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherExtra
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

open ReciprocityTheory.ChartRestriction.G in
def pullbackDensity_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (L : Fin n → Geo.HermLine ι) (L' : Fin n → Geo.HermLine ι')
    (A : Geo.HermLine ι) (A' : Geo.HermLine ι') (s : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsGoodProj (imageZ v P') Ψ →
    (∀ j, Geo.IsSmoothHerm (L j)) → (∀ j, AI.I4.IsPullHerm κ v (L j) (L' j)) →
    Geo.IsSmoothHerm A → AI.I4.IsPullHerm κ v A A' → Geo.IsSectionOn (imageZ v P') A s →
    ∀ᵐ y : Fin n → ℂ, ∀ x ∈ pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ,
      Geo.logNorm A' (rename v s) (R.lift x x) * pushDens R.A (fun j => Geo.potOf R (L' j)) (pullQ R v Ψ) x =
        sheetDensity (imageZ v P') Ψ (Geo.pot L) (Geo.logNorm A s) y (pullW R v Ψ x)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherFurther
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

def PullbackDegreeCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    IsGoodProj (imageZ v P') Ψ →
    ∀ᵐ y : Fin n → ℂ, ∀ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ y,
      (({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ).ncard : ℤ) =
        J (fibreIdeal κ G) 0 Fin.elim0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalSpanTwo
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (a : Fin n → K → ℤ) (s : MRing ι) (α : K → ℕ) (W' : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsMultiHomog s α → s ∉ imageZ v P' → W' ∈ divSupp P' (rename v s) → ¬ IsHorizontal W' →
    (imageZ v W' ∈ divSupp (imageZ v P') s ∧
        ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
          geoNum n W' (fun j => pullDeg κ (a j)) =
            J' (fibreIdeal κ G') 0 Fin.elim0 * geoNum n (imageZ v W') a) ∨
      (imageZ v W' ∉ divSupp (imageZ v P') s ∧ geoNum n W' (fun j => pullDeg κ (a j)) = 0)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockGenFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGenFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    ∃ (f₀ : MRing ι') (a : K' → ℕ), IsMultiHomog f₀ a ∧ f₀ ∉ P' ∧
      ∀ u : (Σ k, ι k) → ℂ, ∃ T : Finset ((Σ k', ι' k') → ℂ),
        ∀ z' ∈ mcPts P', eval z' (map (Int.castRingHom ℂ) f₀) ≠ 0 →
          SameOrbit (fun p => z' (v p)) u → ∃ t ∈ T, SameOrbit z' t

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

