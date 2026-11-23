module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

theorem PolynomialDimensionInequality.full : PolynomialDimensionInequality.Statement.{u} :=
  PolynomialDimensionInequality.proof PolynomialPrimeOverZeroHeight.proof.{u}

theorem DimensionInequalityOneGenerator.full : DimensionInequalityOneGenerator.Statement.{u, v} :=
  DimensionInequalityOneGenerator.proof PolynomialDimensionInequality.full.{u}
    QuotientHeightAddOne.proof.{u}

theorem DimensionInequality.full : DimensionInequality.Statement.{u, v} :=
  DimensionInequality.proof DimensionInequalityOneGenerator.full.{u, v}
    DimensionInequalityOneGenerator.full.{v, v}

theorem ReesAlgebraDim.full : ReesAlgebraDim.Statement.{u} :=
  ReesAlgebraDim.proof DimensionInequality.full.{u, u}

theorem BlowUpModel.full : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof ReesAlgebraDim.full.{u}

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ComapLiftFormConstChartPrimeExample
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOrderLe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (P : Ideal (MRing ι R)), P.IsPrime →
    ∀ (u : J → MRing ι R) (G' : Ideal (MRing (extIdx ι J) R)) (y : MRing (extIdx ι J) R),
      y ∉ blowUpOf P u → G' ∈ (blowUpOf P u ⊔ Ideal.span {y}).minimalPrimes → IsRelevant G' →
    ∀ x : MRing ι R, x ∉ P → G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
    ∀ z : MRing ι R, z ∉ P →
      divCycle (blowUpOf P u) (liftForm z) G' ≤ divCycle P z (G'.comap (liftForm (J := J)))

def ExceptionalContraction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) G' →
      G'.comap (liftForm (J := BlowUpIdx ι)) ∈ (P ⊔ Ideal.span {s}).minimalPrimes

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalCongrOnSupport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Helpers

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]

theorem powMonomial_isMultiHomog (e : K → ℕ) (i : ∀ k, ι k) :
    IsMultiHomog (powMonomial (R := R) e i) e := by
  have h := IsWeightedHomogeneous.prod (R := R) Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ e k)
    (fun k => e k • blockWeight ι ⟨k, i k⟩) (fun k _ => (isWeightedHomogeneous_X R _ _).pow (e k))
  have key : (∑ k, e k • blockWeight ι ⟨k, i k⟩) = e := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [key] at h
  exact h


omit [Fintype K] [DecidableEq K] in
theorem liftForm_C_eq {J : Type} (a : R) : liftForm (ι := ι) (J := J) (C a : MRing ι R) = C a := by
  simp [liftForm]


omit [Fintype K] [DecidableEq K] in
theorem cycEval_congr_on_support {n n' : Ideal (MRing ι R) → ℤ} (Z : Ideal (MRing ι R) → ℤ)
    (h : ∀ W, Z W ≠ 0 → n W = n' W) : cycEval n Z = cycEval n' Z := by
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · rw [hW, zero_mul, zero_mul]
  · rw [h W hW]


open scoped Classical in
omit [Fintype K] [DecidableEq K] in
open Classical in
theorem cycEval_ite (p : Ideal (MRing ι R) → Prop) (A B : Ideal (MRing ι R) → ℤ)
    (Z : Ideal (MRing ι R) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => if p W then A W else B W) Z =
      cycEval (fun W => if p W then A W else 0) Z + cycEval (fun W => if p W then 0 else B W) Z := by
  unfold cycEval
  rw [← finsum_add_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  dsimp only
  split_ifs <;> ring


omit [Fintype K] [DecidableEq K] in
theorem vecCons_liftMDeg {d : ℕ} (c : K → ℕ) (L : Fin d → K → ℤ) :
    Matrix.vecCons (fun k => ((liftMDeg c k : ℕ) : ℤ)) (liftDegs L) =
      liftDegs (Matrix.vecCons (fun k => (c k : ℤ)) L) := by
  funext i o
  refine Fin.cases ?_ (fun i => ?_) i <;> cases o <;> simp [liftDegs, liftDeg, liftMDeg]

end Helpers

theorem BlowUpInvariance.proof (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u}) :
    BlowUpInvariance.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e hce m hm hmP hmH L
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.1.degrees
  have hPp := hP.multiProj.isPrime

  have hdeg : bf + e = c + bg := by
    funext k
    have h1 := hce k
    have h2 := congrFun hb k
    simp only [Pi.add_apply] at h1 h2 ⊢
    omega
  have hN : ∀ j, IsMultiHomog (blowUpGens s g f m e j) (c + bg) := by
    rintro (_ | _ | i)
    · exact hs.mul hg
    · exact hdeg ▸ hf.mul hm
    · exact hdeg ▸ hf.mul (powMonomial_isMultiHomog e i)
  have hfm : f * m ∉ P := fun h => (hPp.mem_or_mem h).elim hD.1.num_not_mem hmP
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [vecCons_liftMDeg]
    exact hdiv O ϖ hϖ K ι _ P (d + 1) hP b f g hD.1 _ _ hN ⟨some none, hfm⟩ _

  have hinv : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧
        v * blowUpGens s g f m e j' - w * blowUpGens s g f m e j ∈ P := by
    intro W hW hPW hrel hϖW
    choose i hi using hrel
    have hμ : powMonomial e i ∉ W := by
      rw [powMonomial, hW.prod_mem_iff]
      rintro ⟨k, -, hk⟩
      exact hi k (hW.mem_of_pow_mem _ hk)
    obtain ⟨u', v', hu', hv', h⟩ := hD.1.unit_off_special W hW hPW (fun k => ⟨i k, hi k⟩) hϖW
    refine ⟨some (some i), ?_⟩
    rintro (_ | _ | i')
    · refine ⟨v' * powMonomial e i, s * u', fun h' => (hW.mem_or_mem h').elim hv' hμ, ?_⟩
      have e1 : v' * powMonomial e i * (s * g) - s * u' * (f * powMonomial e i) =
          -(s * powMonomial e i) * (u' * f - v' * g) := by ring
      simpa only [blowUpGens, e1] using P.mul_mem_left _ h
    · exact ⟨powMonomial e i, m, hμ, by simp only [blowUpGens]; rw [show powMonomial e i * (f * m) -
        m * (f * powMonomial e i) = 0 by ring]; exact P.zero_mem⟩
    · exact ⟨powMonomial e i, powMonomial e i', hμ, by simp only [blowUpGens]; rw [show powMonomial e i *
        (f * powMonomial e i') - powMonomial e i' * (f * powMonomial e i) = 0 by ring]; exact P.zero_mem⟩

  obtain ⟨htrans, hpt⟩ := hhor O ϖ hϖ K ι _ P (d + 1) hP _ _ hN ⟨some none, hfm⟩ hinv c s hs hsP
  unfold cutIdentityRightSide
  rw [cycEval_ite _ _ _ _ (hfin O (Option K) (extIdx ι (BlowUpIdx ι)) (blowUpOf P (blowUpGens s g f m e))
    (liftForm s)), cycEval_ite _ _ _ _ (hfin O K ι P s)]
  congr 1
  · have hdegrees : Matrix.vecCons (liftDeg b) (liftDegs L) = liftDegs (Matrix.vecCons b L) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hdegrees]
    exact hvert O ϖ hϖ K ι _ P (d + 1) hP _ _ hN ⟨some none, hfm⟩ c s hs hsP (Matrix.vecCons b L)
  rw [← htrans (fun W => cycEval (fun G => vNum G L) (ratDiv W f g))]
  refine cycEval_congr_on_support _ fun W hW => ?_
  by_cases hϖ' : (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ W
  · simp only [ite_eq_left hϖ']
  rw [ite_eq_right hϖ', ite_eq_right hϖ']
  obtain ⟨hWs, hWeq⟩ := hpt W hW hϖ'
  have hϖW : (C ϖ : MRing ι O) ∉ W.comap (liftForm (ι := ι) (J := BlowUpIdx ι) (R := O)) := by
    rwa [Ideal.mem_comap, liftForm_C_eq]
  generalize W.comap (liftForm (ι := ι) (J := BlowUpIdx ι) (R := O)) = V at hWs hWeq hϖW ⊢
  have hWm := hcomp O ϖ hϖ K ι P d hP c s hs hsP _ hWs hϖW
  have hWv := hsH _ hWs hϖW
  have hfmW : blowUpGens s g f m e (some none) ∉ V :=
    fun h => (hWm.multiProj.isPrime.mem_or_mem h).elim hWv.num_not_mem (hmH _ hWs hϖW)
  rw [hWeq ⟨_, hfmW⟩]
  exact hdiv O ϖ hϖ K ι _ _ d hWm b f g hWv _ _ hN ⟨_, hfmW⟩ L

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleNeZeroFacts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem divCycle_ne_zero_facts {O : Type u} [CommRing O] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {P : Ideal (MRing ι O)} (hP : IsMultiHomogIdeal P) {f : MRing ι O} {e : K → ℕ}
    (hf : IsMultiHomog f e) {W : Ideal (MRing ι O)} (h : divCycle P f W ≠ 0) :
    W.IsPrime ∧ IsRelevant W ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
  unfold divCycle at h
  split_ifs at h with hW
  · obtain ⟨hmin, hrel⟩ := hW
    refine ⟨hmin.1.1, hrel, le_trans le_sup_left hmin.1.2, ?_⟩
    exact MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P f e hP hf) hmin
  · exact absurd rfl h

theorem LeftTermSupport.proof : LeftTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs G U hU
  by_contra hne
  apply hU
  have hG : ratDiv P f g G ≠ 0 := left_ne_zero_of_mul hne
  have hU' : divCycle G s U ≠ 0 := right_ne_zero_of_mul hne
  have hϖG : (C ϖ : MRing ι O) ∈ G := hD.vertical G hG
  obtain ⟨bf, bg, hf, hg, -⟩ := hD.degrees
  have hGfacts : P ≤ G ∧ IsMultiHomogIdeal G := by
    have : divCycle P f G ≠ 0 ∨ divCycle P g G ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hG (by unfold ratDiv; rw [h.1, h.2, sub_zero])
    rcases this with h | h
    · exact (divCycle_ne_zero_facts hP hf h).2.2
    · exact (divCycle_ne_zero_facts hP hg h).2.2
  obtain ⟨hUp, hUr, hGU, hUm⟩ := divCycle_ne_zero_facts hGfacts.2 hs hU'
  exact ⟨hUp, hUm, hUr, hGU hϖG, le_trans hGfacts.1 hGU⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagModelCommonModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ F₁ F₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O x d N E E',
    ∃ (K'' : Type) (_ : Fintype K'') (ι'' : K'' → Type) (_ : ∀ k, Fintype (ι'' k))
      (z : (Σ k, ι'' k) → Ω)
      (EB E'B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) N V)
      (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) EB E'B),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) d ∧
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) =
                                IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O x ∧
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O x z E EB ∧ IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O x z E' E'B ∧
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) EB E'B ∧
      (∀ (b : K → ℤ) (f g : MRing ι O),
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) b f g →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') b)
          (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') f) (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') g)) ∧
      ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι ι'')) (I₁ : IFamily
          (IsLocalRing.ResidueField O) (Sum.elim ι F₁.ι'))
        (I₂ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₂.ι')),
        IsFieldIntersection I → IsFieldIntersection I₁ → IsFieldIntersection I₂ →
      ∀ (G : MvPolynomial (Fin N) ℤ) (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
        (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
          (f l) (g l)) →
      ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
        Q.IsHomogeneous (d + 1 - c) →
        F₁.value O I₁ G y y' f g Q =
            IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) d
              (Fin.append φ₁.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y l))
              (Fin.append φ₁.deg' fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y' l))
              (Fin.append φ₁.f fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
              (Fin.append φ₁.g fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l))
              (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) ∧
          F₂.value O I₂ G y y' f g Q =
            IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) d
              (Fin.append φ₂.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y l))
              (Fin.append φ₂.deg' fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y' l))
              (Fin.append φ₂.f fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
              (Fin.append φ₂.g fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l))
              (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsProjVarF)

def VerticalDivisorSupportFibre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRingOver O ι)) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d →
    ∀ (b : K → ℤ) (f g : MRingOver O ι), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g →
    ∀ W : Ideal (MRingOver O ι), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g W ≠ 0 →
      IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem IsMultiHomogIdeal.sup {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
    {I J : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) (hJ : IsMultiHomogIdeal J) :
    IsMultiHomogIdeal (I ⊔ J) := by
  intro f hf b
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hI x hx b) (hJ y hy b)

theorem RightTermSupport.proof : RightTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs hH W U hU
  by_contra hne
  have hW : divCycle P s W ≠ 0 := left_ne_zero_of_mul hne
  have hWU : idealCycle (W ⊔ divisorIdeal P f g) U ≠ 0 := right_ne_zero_of_mul hne
  have hWm : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h
    · exact absurd rfl hW
  have hUm : U ∈ (W ⊔ divisorIdeal P f g).minimalPrimes ∧ IsRelevant U := by
    unfold idealCycle at hWU
    split_ifs at hWU with h
    · exact h
    · exact absurd rfl hWU
  have hWp : W.IsPrime := hWm.1.1.1
  have hUp : U.IsPrime := hUm.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hWm.1.1.2
  have hWU' : W ≤ U := le_sup_left.trans hUm.1.1.2
  have hDU : divisorIdeal P f g ≤ U := le_sup_right.trans hUm.1.1.2
  have hWmh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P s c hP hs) hWm.1
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.1.degrees
  have hDm : IsMultiHomogIdeal (divisorIdeal P f g) :=
    ColonMultiHomog.proof O K ι _ g bg (SupSpanMultiHomog.proof O K ι P f bf hP hbf) hbg
  have hUmh : IsMultiHomogIdeal U :=
    MinimalPrimeMultiHomog.proof O K ι _ U (hWmh.sup hDm) hUm.1
  apply hU
  refine ⟨hUp, hUmh, hUm.2, ?_, hPW.trans hWU'⟩
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · exact hWU' hϖW
  by_contra hϖU
  have hV := hH W hW hϖW
  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_special U hUp hWU' hUm.2 hϖU
  obtain ⟨u', v', hu', huv'⟩ := hD.2 U hUp (hPW.trans hWU') hUm.2
  have hv'D : v' ∈ divisorIdeal P f g := by
    unfold divisorIdeal
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have e : v' * g = u' * f - (u' * f - v' * g) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
      (Ideal.mem_sup_left huv')
  have hmem : g * (u * v' - u' * v) ∈ W := by
    have e : g * (u * v' - u' * v) = u' * (u * f - v * g) - u * (u' * f - v' * g) := by ring
    rw [e]
    exact W.sub_mem (W.mul_mem_left _ huv) (W.mul_mem_left _ (hPW huv'))
  have hdiff : u * v' - u' * v ∈ U :=
    hWU' ((hWp.mem_or_mem hmem).resolve_left hV.den_not_mem)
  have hv'U : v' ∈ U := hDU hv'D
  have hu'v : u' * v ∈ U := by
    have e : u' * v = u * v' - (u * v' - u' * v) := by ring
    rw [e]
    exact U.sub_mem (U.mul_mem_left _ hv'U) hdiff
  exact (hUp.mem_or_mem hu'v).elim hu' hv

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d

end GroundTheory.Heights₂.Heights.NumbersDVR
end

