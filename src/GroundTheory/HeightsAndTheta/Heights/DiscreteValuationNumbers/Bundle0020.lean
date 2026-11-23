module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IdealCycleSupportFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem idealCycle_support_finite {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    [IsNoetherianRing (MRing ι R)] (J : Ideal (MRing ι R)) :
    (Function.support (idealCycle J)).Finite := by
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J)
  intro W hW
  by_contra hmin
  apply hW
  unfold idealCycle
  rw [dite_eq_right]
  exact fun h => hmin h.1

theorem finsum_mul_finsum_comm {α β : Type*} (a : α → ℤ) (c : α → β → ℤ) (n : β → ℤ)
    (ha : (Function.support a).Finite) (hc : ∀ W, (Function.support (c W)).Finite) :
    ∑ᶠ W, a W * ∑ᶠ U, c W U * n U = ∑ᶠ U, (∑ᶠ W, a W * c W U) * n U := by
  classical
  set S := ha.toFinset
  set T := S.biUnion (fun W => (hc W).toFinset)
  have hcT : ∀ W ∈ S, Function.support (c W) ⊆ ↑T := by
    intro W hW U hU
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨W, hW, (hc W).mem_toFinset.mpr hU⟩
  have hin : ∀ U, ∑ᶠ W, a W * c W U = ∑ W ∈ S, a W * c W U := by
    intro U
    apply finsum_eq_sum_of_support_subset
    intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW
  simp_rw [hin]
  rw [finsum_eq_sum_of_support_subset (s := S), finsum_eq_sum_of_support_subset (s := T)]
  · rw [Finset.sum_congr rfl (g := fun W => a W * ∑ U ∈ T, c W U * n U)]
    · simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    · intro W hW
      congr 1
      apply finsum_eq_sum_of_support_subset
      intro U hU
      exact hcT W hW (left_ne_zero_of_mul hU)
  · intro U hU
    obtain ⟨W, hW, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hU)
    exact hcT W hW (right_ne_zero_of_mul hne)
  · intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW

theorem RightExpansion.proof (hV : VertCutEff.Statement.{u})
    (hD : DivisorIdealCycle.Statement.{u}) : RightExpansion.Statement.{u} := by
  classical
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hmodel b f g heff c s hs hsP hhor hnc L
  have hPmh : IsMultiHomogIdeal (P ⊔ Ideal.span {s}) :=
    SupSpanMultiHomog.proof O K ι P s c hmodel.multiProj.multiHomog hs
  have key : ∀ W : Ideal (MRing ι O),
      divCycle P s W * (if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) =
        divCycle P s W * cycEval (fun U => vNum U L) (idealCycle (W ⊔ divisorIdeal P f g)) := by
    intro W
    by_cases hW : divCycle P s W = 0
    · rw [hW, zero_mul, zero_mul]
    congr 1
    obtain ⟨hWp, hPW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
    have hWmin : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
      unfold divCycle at hW
      split_ifs at hW with h
      · exact h.1
      · exact absurd rfl hW
    split_ifs with hϖW
    · exact hV O ϖ hϖ K ι P d hmodel b f g heff W s hsP hWmin hWrel
        (MinimalPrimeMultiHomog.proof O K ι _ W hPmh hWmin) hϖW (hnc W hϖW hW) L
    · have hv := hhor W hW hϖW
      have hP : P.IsPrime := hmodel.multiProj.isPrime
      rw [hD O K ι P W f g g f hP hWp hPW heff.1.den_not_mem
        (fun U hU hWU hUrel => heff.2 U hU (hPW.trans hWU) hUrel)
        hv.den_not_mem hv.num_not_mem (by rw [mul_comm, sub_self]; exact P.zero_mem)]
  exact (finsum_congr key).trans <| finsum_mul_finsum_comm _ (fun W U => idealCycle (W ⊔ divisorIdeal P f g) U) _
    (DivCycleFiniteSupport.proof O K ι P s) (fun W => idealCycle_support_finite _)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem CommonFactorInduction.proof (hpos : ExcessPositive.Statement.{u}) (havoid : AvoidingFormExists.Statement.{u})
    (hhor : HorizontalAvoidingForm.Statement.{u}) (hpieces : BlowUpDecomposition.Statement.{u})
    (hdrop : BlowUpExcessDecreases.Statement.{u}) (hred : BlowUpReduction.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hmul : DivCycleMul.Statement.{u}) : CommonFactorInduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH hcommon IH L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hε := hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon

  obtain ⟨e, h, hh, hhP, hle, hhH, hhG, hh0, hmulε⟩ :=
    havoid O ϖ hϖ K ι P d hP b f g hD (fun k => (b k).toNat)
  have hdiv : ∀ W, divCycle P (s * h) W = divCycle P s W + divCycle P h W :=
    fun W => congrFun (hmul O K ι P s h hPp hsP hhP) W
  have hshP : s * h ∉ P := fun hm => (hPp.mem_or_mem hm).elim hsP hhP
  have hshH : ∀ H, divCycle P (s * h) H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g := by
    intro H hH hϖH
    rw [hdiv] at hH
    by_cases h1 : divCycle P s H = 0
    · exact hhH H (by rwa [h1, zero_add] at hH) hϖH
    · exact hsH H h1 hϖH
  have hcommon' : ∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P (s * h) G ≠ 0 ∧ ratDiv P f g G ≠ 0 := by
    obtain ⟨G, hG, hsG, hDG⟩ := hcommon
    exact ⟨G, hG, by rwa [hdiv, hhG G hG hDG, add_zero], hDG⟩

  set e₂ : K → ℕ := fun k => (((c + e) k : ℕ) - b k : ℤ).toNat with he₂def
  have he₂ : ∀ k, (((c + e) k : ℕ) : ℤ) = b k + e₂ k := by
    intro k
    have h1 : (b k).toNat ≤ e k := hle k
    have h2 : b k ≤ ((b k).toNat : ℤ) := Int.self_le_toNat (b k)
    simp only [he₂def, Pi.add_apply, Nat.cast_add]
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  obtain ⟨m, hm, hmP, hmH⟩ := hhor O ϖ hϖ K ι P d hP (s * h) hshP e₂
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, hH₀⟩ := hpieces O ϖ hϖ K ι P d hP b f g hD (c + e)
    (s * h) (hs.mul hh) hshP hshH e₂ he₂ m hm hmP hmH
  obtain ⟨hdrop₁, hdrop₀⟩ := hdrop O ϖ hϖ K ι P d hP b f g hD (c + e) (s * h) (hs.mul hh) hshP
    hshH e₂ he₂ m hm hmP hmH hcommon'
  rw [hmulε s hsP] at hdrop₁ hdrop₀

  have hId₁ := IH (Option K) (extIdx ι (BlowUpIdx ι)) _ d hmodel _ _ _ hD₁ _ _ hsl hslP
    (fun H hH hϖH => (hH₁ H hH hϖH).1) hdrop₁ (liftDegs L)
  have hId₀ := IH (Option K) (extIdx ι (BlowUpIdx ι)) _ d hmodel _ _ _ hE (Pi.single none 1)
    (newVar none) (isWeightedHomogeneous_X _ _ _) hY₀P hH₀ hdrop₀ (liftDegs L)

  have hIdsh := hred O ϖ hϖ K ι P d hP b f g hD (c + e) (s * h) (hs.mul hh) hshP hshH e₂ he₂ m hm
    hmP hmH L hId₁ hId₀
  have hIdh := IH K ι P d hP b f g hD e h hh hhP hhH (by rw [hh0]; exact hε) L

  rw [cutIdentity_iff] at hIdsh hIdh ⊢
  have h1 := hlhs O ϖ hϖ K ι P d hP b f g hD.1 c e L
  have h2 := hrhs O ϖ hϖ K ι P d hP b f g s h hsP hhP L
  linarith

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull FlagPair midDeg midVar)

def FlagPairJoinRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (EF E'F : ChartBundle O (mseg (joinCoord x z)) N V),
    IsPull O x z E EF → IsPull O x z E' E'F → ∀ φ : FlagPair O (joinCoord x z) EF E'F,
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord w z))) N V,
      IsPull O x (joinCoord w z) E EB → IsPull O x (joinCoord w z) E' E'B →
    ∃ ψ : FlagPair O (joinCoord x (joinCoord w z)) EB E'B,
      ψ.Vs = φ.Vs ∧ ψ.gen = φ.gen ∧ ψ.gen' = φ.gen' ∧
      ψ.deg = (fun i => midDeg (K₂ := K₂) (φ.deg i)) ∧
      ψ.deg' = (fun i => midDeg (K₂ := K₂) (φ.deg' i)) ∧
      ψ.f = (fun i => rename (midVar ι₂) (φ.f i)) ∧ ψ.g = (fun i => rename (midVar ι₂) (φ.g i))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem NoCommonComponentCase.proof (h₁ : LeftExpansion.Statement.{u}) (h₂ : RightExpansion.Statement.{u})
    (h₃ : LocalCoefficient.Statement.{u}) (h₄ : IntNumVanish.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno L
  unfold cutIdentity
  rw [h₁ O ϖ hϖ K ι P d hP b f g hD.1 c s hs hsP hno L,
    h₂ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno L]
  unfold cycEval
  refine finsum_congr fun U => ?_
  beta_reduce
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧
      ¬ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ U)
  ·
    obtain ⟨hUp, hUm, -, hϖU, hdim⟩ := hU
    have hv : vNum U L = 0 := by
      refine h₄ _ K ι d (specialIdeal U) (SpecialIdealCorresp.proof O ϖ hϖ K ι ⊥ U hUp hϖU).1
        (SpecialIdealMultiHomog.proof O K ι U hUm) (Or.inr ?_) L
      rw [SpecialQuotDim.proof O ϖ hϖ K ι U hϖU]
      exact lt_of_not_ge hdim
    rw [hv, mul_zero, mul_zero]
  ·
    have e := h₃ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno U fun hp hm hr hϖU => by
      by_contra h
      exact hU ⟨hp, hm, hr, hϖU, h⟩
    unfold cycEval at e
    rw [e]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord midDeg midVar)

def JoinVerticalDivisorRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (b : K ⊕ K' → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
    IsVertDiv O (mcIdeal O (joinCoord x z)) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x (joinCoord w z))) (midDeg (K₂ := K₂) b)
      (rename (midVar ι₂) f) (rename (midVar ι₂) g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointVerticalDivisor.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) b f g →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) b)
      (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f)
      (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointNumbers.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (r : ℕ) (deg : Fin r → K → ℤ) (H : MvPolynomial (Fin r) ℤ),
    (∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor (pointIdeal O y) ϖ b f g →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                                (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f)
          (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g)) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (pointIdeal O y) f g)) ∧
    (∀ a : O, a ≠ 0 →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                                (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (C a))) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H)
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
          (ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) (C a))))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord assocDeg assocVar)

def JoinVerticalDivisorLeft.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (b : K ⊕ K' → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
    IsVertDiv O (mcIdeal O (joinCoord x z)) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x (joinCoord z w))) (assocDeg (K₂ := K₂) b)
      (rename (assocVar ι₂) f) (rename (assocVar ι₂) g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull SameGeneric)

def JoinPullbackAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' →
    ∃ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V,
      IsPull O x z E EB ∧ IsPull O x z E' E'B ∧ SameGeneric O (joinCoord x z) EB E'B

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointFlagModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∃ (EB E'B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) N E)
      (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))
          EB E'B),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d ∧
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))) =
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O y ∧
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O y (ptCoord (Ω := Ω)) B EB ∧
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O y (ptCoord (Ω := Ω)) B' E'B ∧
        φ.deg = (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i)) ∧
        φ.deg' = (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i)) ∧
        φ.f = (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i)) ∧
        φ.g = (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RatDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem CommonFactorRemoval.proof (hmul : DivCycleMul.Statement.{u}) : CommonFactorRemoval.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g q s hf hg hq _ hH c L

  have hrat : ∀ W : Ideal (MRing ι O), W.IsPrime → f ∉ W → g ∉ W → q ∉ W →
      ratDiv W (f * q) (g * q) = ratDiv W f g := by
    intro W hW hfW hgW hqW
    funext G
    simp only [ratDiv, hmul O K ι W f q hW hfW hqW, hmul O K ι W g q hW hgW hqW, Pi.add_apply]
    ring
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [hrat P hP.multiProj.isPrime hf hg hq]
  · unfold cutIdentityRightSide cycEval
    congr 1
    funext W
    by_cases hW : divCycle P s W = 0
    · simp [hW]
    · dsimp only
      split_ifs with hϖ
      · rfl
      · obtain ⟨h1, h2, h3⟩ := hH W hW hϖ
        rw [hrat W (isPrime_of_divCycle_ne_zero hW) h1 h2 h3]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

