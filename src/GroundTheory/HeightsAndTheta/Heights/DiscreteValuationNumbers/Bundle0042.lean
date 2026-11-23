module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0040

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem LeftSideAdditiveInDegree.proof
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (d : ℕ) (hP : IsModelOver P (d + 1))
    (b : K → ℤ) (f g : MRing ι O) (hD : IsVerticalDivisor P ϖ b f g)
    (c₁ c₂ : K → ℕ) (L : Fin d → K → ℤ) :
    cutIdentityLeftSide P f g (c₁ + c₂) L =
      cutIdentityLeftSide P f g c₁ L + cutIdentityLeftSide P f g c₂ L := by
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    intro h e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P h e hPmh he) hW'.1,
        hW'.1.1.1, le_sup_left.trans hW'.1.1.2⟩
    · exact absurd rfl hW

  have hadd : ∀ W, ratDiv P f g W ≠ 0 →
      vNum W (Matrix.vecCons (fun k => ((c₁ + c₂) k : ℤ)) L) =
        vNum W (Matrix.vecCons (fun k => (c₁ k : ℤ)) L) +
          vNum W (Matrix.vecCons (fun k => (c₂ k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    obtain ⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · exact hmh g bg hbg W fun hWg => hW (by simp [ratDiv, hWf, hWg])
      · exact hmh f bf hbf W hWf
    have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
    have hdrop := DimStrictDrop.full (MRing ι O) P W hlt
    rw [hP.dim] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [SpecialQuotDim.full O ϖ hϖ K ι W hϖW]
      have e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [e] at hdrop
      exact lt_natCast_of_add_one_le hdrop
    have key := IntNumAddFirst.full (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWm)
      hdim (fun k => (c₁ k : ℤ)) (fun k => (c₂ k : ℤ)) L
    have hsum : (fun k => ((c₁ + c₂) k : ℤ)) = (fun k => (c₁ k : ℤ)) + (fun k => (c₂ k : ℤ)) := by
      funext k; simp
    unfold vNum
    rw [hsum, key]
  have hZfin := ratDiv_support_finite DivCycleFiniteSupport.full P f g
  unfold cutIdentityLeftSide cycEval
  rw [← finsum_add_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
    (hZfin.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  · beta_reduce
    rw [hadd W hW, mul_add]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagPairValueIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
      (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
        (f l) (g l)) →
    ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
      Q.IsHomogeneous (d + 1 - c) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                (Fin.append φ₁.deg y) (Fin.append φ₁.deg' y') (Fin.append φ₁.f f) (Fin.append φ₁.g g)
                                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
          (Fin.append φ₂.deg y) (Fin.append φ₂.deg' y') (Fin.append φ₂.f f) (Fin.append φ₂.g g)
          (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ResidualContraction.proof (hle : BlowUpOrderLe.Statement.{u})
    (hcomp : ResidualContractionComponent.Statement.{u}) :
    ResidualContraction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
    x hxP
  have hGmin := hcomp O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'

  have hG'supp : G' ∈ (blowUpOf P (blowUpGens s g f m e) ⊔ Ideal.span {liftForm s}).minimalPrimes ∧
      IsRelevant G' := by
    by_contra h
    unfold divCycle at hsG'
    rw [dite_eq_right h] at hsG'
    exact lt_irrefl _ hsG'

  have hsP' : liftForm (J := BlowUpIdx ι) s ∉ blowUpOf P (blowUpGens s g f m e) := by
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hsP
  exact hle O K ι (BlowUpIdx ι) P hP.multiProj.isPrime (blowUpGens s g f m e) G' (liftForm s) hsP'
    hG'supp.1 hG'supp.2 s hsP hGmin x hxP

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField assocDeg assocVar)

def PairNumberJoinLeft.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord z w))) d →
    fnField O (joinCoord x (joinCoord z w)) = fnField O (joinCoord x z) →
    ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim ι' ι₂)))
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι ι')),
      IsFieldIntersection I → IsFieldIntersection I₁ →
    ∀ (n : ℕ) (a a' : Fin n → K ⊕ K' → ℤ)
      (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
      (∀ i, IsVertDiv O (mcIdeal O (joinCoord x z)) (a i - a' i) (f i) (g i)) →
    ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I₁ (mcIdeal O (joinCoord x z)) d a a' f g H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O (joinCoord x (joinCoord z w))) d
          (fun i => assocDeg (K₂ := K₂) (a i)) (fun i => assocDeg (K₂ := K₂) (a' i))
          (fun i => rename (assocVar ι₂) (f i)) (fun i => rename (assocVar ι₂) (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField midDeg midVar)

def PairNumberJoinRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord w z))) d →
    fnField O (joinCoord x (joinCoord w z)) = fnField O (joinCoord x z) →
    ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim ι₂ ι')))
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι ι')),
      IsFieldIntersection I → IsFieldIntersection I₁ →
    ∀ (n : ℕ) (a a' : Fin n → K ⊕ K' → ℤ)
      (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
      (∀ i, IsVertDiv O (mcIdeal O (joinCoord x z)) (a i - a' i) (f i) (g i)) →
    ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I₁ (mcIdeal O (joinCoord x z)) d a a' f g H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O (joinCoord x (joinCoord w z))) d
          (fun i => midDeg (K₂ := K₂) (a i)) (fun i => midDeg (K₂ := K₂) (a' i))
          (fun i => rename (midVar ι₂) (f i)) (fun i => rename (midVar ι₂) (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagPlainValueIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (L : Fin r → K → ℤ) (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 →
      G.IsHomogeneous c → Q.IsHomogeneous (d + 1 - c) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                (Fin.append φ₁.deg L) (Fin.append φ₁.deg' L) (Fin.append φ₁.f fun _ => 1)
                                (Fin.append φ₁.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
          (Fin.append φ₂.deg L) (Fin.append φ₂.deg' L) (Fin.append φ₂.f fun _ => 1)
          (Fin.append φ₂.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagModelRootIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (F₁ F₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O x d N E E')
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₁.ι'))
      (I₂ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₂.ι')),
      IsFieldIntersection I₁ → IsFieldIntersection I₂ →
    ∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d →
    ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) →
    ∀ a : O, a ≠ 0 →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I₁ W d
                                (Fin.append F₁.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₁.K') (L l))
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x F₁.z)) (C a))) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I₂ W d
                                (Fin.append F₂.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₂.K') (L l))
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x F₂.z)) (C a)))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagModelValueIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (F₁ F₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O x d N E E')
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₁.ι'))
      (I₂ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₂.ι')),
      IsFieldIntersection I₁ → IsFieldIntersection I₂ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
      (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
        (f l) (g l)) →
    ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
      Q.IsHomogeneous (d + 1 - c) →
      F₁.value O I₁ G y y' f g Q = F₂.value O I₂ G y y' f g Q

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordCompMidSwapVars
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type}

def midSwapBlocks : K ⊕ (K₂ ⊕ K') ≃ K ⊕ (K' ⊕ K₂) :=
  Equiv.sumCongr (Equiv.refl K) (Equiv.sumComm K₂ K')

def midSwapVars (ι : K → Type) (ι' : K' → Type) (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) ≃
      (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) where
  toFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  invFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  left_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl
  right_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl

theorem midSwapVars_fst {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
    (v : Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) :
    (midSwapVars ι ι' ι₂ v).1 = midSwapBlocks v.1 := by
  obtain ⟨k | k | k, i⟩ := v <;> rfl

theorem joinCoord_comp_midSwapVars {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type} {Ω : Type*}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω) :
    joinCoord x (joinCoord z w) ∘ midSwapVars ι ι' ι₂ = joinCoord x (joinCoord w z) := by
  funext v
  obtain ⟨k | k | k, i⟩ := v <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField pairNum midSwapBlocks midSwapVars
  ptCoord ptIdx unif)

def PairNumberRelabelAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ (y : (Σ k, ι₂ k) → Ω) (d : ℕ),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (y ∘ σ)) d →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d ∧ fnField O y = fnField O (y ∘ σ) ∧
        (∀ (b : K₂ → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          IsVertDiv O (mcIdeal O (y ∘ σ)) (b ∘ e) f g →
            IsVertDiv O (mcIdeal O y) b (rename σ f) (rename σ g)) ∧
        ∀ (I₁ : IFamily (IsLocalRing.ResidueField O) ι₁) (I : IFamily (IsLocalRing.ResidueField O) ι₂),
          IsFieldIntersection I₁ → IsFieldIntersection I →
        ∀ (n : ℕ) (a a' : Fin n → K₂ → ℤ) (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          (∀ i, IsVertDiv O (mcIdeal O (y ∘ σ)) (a i ∘ e - a' i ∘ e) (f i) (g i)) →
        ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
          GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I₁ (mcIdeal O (y ∘ σ)) d (fun i => a i ∘ e) (fun i => a' i ∘ e) f g H =
            GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O y) d a a' (fun i => rename σ (f i)) (fun i => rename σ (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem GenericProjClosureModel.proof (h₁ : TwistedDualGensExist.Statement)
    (h₂ : GenericProjClosureDim.Statement) (h₃ : GenericProjClosureDivisor.Statement) :
    GenericProjClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB Φ _ _ _ _ e t ht
  obtain ⟨a₁, ha₁⟩ := h₁ O Ω K ι y N E B
  obtain ⟨M, φ, hφ⟩ := ha₁ a₁ le_rfl
  obtain ⟨a₁', ha₁'⟩ := h₁ O Ω K ι y N E B'
  obtain ⟨M', φ', hφ'⟩ := ha₁' a₁' le_rfl
  have hZ := h₂ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht
  obtain ⟨f₀, g₀, hD, hfg⟩ :=
    h₃ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht hZ
  exact ⟨M, M', a₁, a₁', φ, φ', hφ, hφ', hZ, f₀, g₀, hD, hfg⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

