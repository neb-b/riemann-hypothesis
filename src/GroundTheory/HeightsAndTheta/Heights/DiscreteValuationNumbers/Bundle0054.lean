module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionKoszul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0040

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinLeft
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord pullDeg liftVar assocDeg assocVar FlagModel)

namespace FlagModelJoinLeftAlt

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocDeg_pullDeg (a : K → ℤ) :
    assocDeg (K₂ := K₂) (pullDeg (K' := K') a) = pullDeg (K' := K' ⊕ K₂) a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem assocVar_comp_liftVar :
    assocVar (ι := ι) (ι' := ι') ι₂ ∘ liftVar ι' = liftVar (Sum.elim ι' ι₂) :=
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := K') a - pullDeg (K' := K') b = pullDeg (K' := K') (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end FlagModelJoinLeftAlt


open FlagModelJoinLeftAlt in
theorem FlagModelJoinLeftAlt.proof (hVert : JoinVerticalDivisor.Statement)
    (hFlag : FlagPairJoinLeft.Statement) (hNum : PairNumberJoinLeft.Statement) :
    FlagModelJoinLeftAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' _ _ F K₂ _ ι₂ _ w hZ hfn EB E'B hp hp'
  obtain ⟨ψ, -, -, -, hdeg, hdeg', hf, hg⟩ :=
    hFlag O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w N V E E' F.EB F.E'B F.pull F.pull' F.flag EB E'B hp hp'
  refine ⟨ψ, fun I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ => ?_⟩
  have hvert : ∀ i, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (joinCoord x F.z))
      (Fin.append F.flag.deg (fun l => pullDeg (K' := F.K') (y l)) i -
        Fin.append F.flag.deg' (fun l => pullDeg (K' := F.K') (y' l)) i)
      (Fin.append F.flag.f (fun l => rename (liftVar F.ι') (f l)) i)
      (Fin.append F.flag.g (fun l => rename (liftVar F.ι') (g l)) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact F.flag.vert j
    · simp only [Fin.append_right, pullDeg_sub]
      exact hVert O Ω K ι x F.K' F.ι' F.z _ _ _ (hv j)
  have hH : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (d + 1) := by
    have h : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (c + (d + 1 - c)) :=
      hG.rename_isHomogeneous.mul hQ.rename_isHomogeneous
    rwa [show c + (d + 1 - c) = d + 1 by omega] at h
  unfold FlagModel.value
  refine (hNum O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w d F.model hZ
    (hfn.trans F.birat.symm) I I₁ hI hI₁ (N + r) _ _ _ _ hvert _ hH).trans ?_
  congr 1 <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [hdeg, hdeg', hf, hg, assocDeg_pullDeg, assocVar_comp_liftVar]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinRight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord pullDeg liftVar midDeg midVar FlagModel)

namespace FlagModelJoinRightAlt

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem midDeg_pullDeg (a : K → ℤ) :
    midDeg (K₂ := K₂) (pullDeg (K' := K') a) = pullDeg (K' := K₂ ⊕ K') a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midVar_comp_liftVar :
    midVar (ι := ι) (ι' := ι') ι₂ ∘ liftVar ι' = liftVar (Sum.elim ι₂ ι') :=
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := K') a - pullDeg (K' := K') b = pullDeg (K' := K') (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end FlagModelJoinRightAlt


open FlagModelJoinRightAlt in
theorem FlagModelJoinRightAlt.proof (hVert : JoinVerticalDivisor.Statement)
    (hFlag : FlagPairJoinRight.Statement) (hNum : PairNumberJoinRight.Statement) :
    FlagModelJoinRightAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' _ _ F K₂ _ ι₂ _ w hZ hfn EB E'B hp hp'
  obtain ⟨ψ, -, -, -, hdeg, hdeg', hf, hg⟩ :=
    hFlag O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w N V E E' F.EB F.E'B F.pull F.pull' F.flag EB E'B hp hp'
  refine ⟨ψ, fun I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ => ?_⟩
  have hvert : ∀ i, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (joinCoord x F.z))
      (Fin.append F.flag.deg (fun l => pullDeg (K' := F.K') (y l)) i -
        Fin.append F.flag.deg' (fun l => pullDeg (K' := F.K') (y' l)) i)
      (Fin.append F.flag.f (fun l => rename (liftVar F.ι') (f l)) i)
      (Fin.append F.flag.g (fun l => rename (liftVar F.ι') (g l)) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact F.flag.vert j
    · simp only [Fin.append_right, pullDeg_sub]
      exact hVert O Ω K ι x F.K' F.ι' F.z _ _ _ (hv j)
  have hH : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (d + 1) := by
    have h : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (c + (d + 1 - c)) :=
      hG.rename_isHomogeneous.mul hQ.rename_isHomogeneous
    rwa [show c + (d + 1 - c) = d + 1 by omega] at h
  unfold FlagModel.value
  rw [hNum O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w d F.model hZ (hfn.trans F.birat.symm) I I₁ hI hI₁ (N + r)
    _ _ _ _ hvert _ hH]
  congr 1 <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [hdeg, hdeg', hf, hg, midDeg_pullDeg, midVar_comp_liftVar]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPlainValueIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace FlagPlainValueIndependence

theorem vEval_intNum {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (d : ℕ) {m : ℕ} (deg : Fin m → K → ℤ)
    (H : MvPolynomial (Fin m) ℤ) (Z : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) →₀ ℤ)
    (hZ : ∀ W, Z W ≠ 0 → ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d deg H) Z =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
        (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          W d deg H) Z := by
  classical
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hV := hZ W (Finsupp.mem_support_iff.mp hW)
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs with h
  · rw [Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hV]
  · rfl

theorem pairNum_intNum (hSupp : VerticalDivisorSupportFibre.Statement)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {d N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V}
    (hM : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d)
    (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
    (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (r : ℕ) (L : Fin r → K → ℤ)
    (H : MvPolynomial (Fin (N + r)) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                              (Fin.append φ.deg L) (Fin.append φ.deg' L) (Fin.append φ.f fun _ => 1)
                              (Fin.append φ.g fun _ => 1) H =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
        (Fin.append φ.deg L) (Fin.append φ.deg' L) (Fin.append φ.f fun _ => 1)
        (Fin.append φ.g fun _ => 1) H := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  induction l using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact vEval_intNum I hI d _ _ _ fun W hW => hSupp O K ι _ d hM _ _ _ (φ.vert i) W hW
  | right j =>
    simp only [Fin.append_right]
    have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) 1 1 = 0 := sub_self _
    exact vEval_intNum I hI d _ _ _ fun W hW => absurd (by rw [h0]; rfl) hW

theorem exists_isFlagPair (hF : FlagPairCharacterisation.Statement.{0, 0, 0})
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {d N : ℕ} (hN : 0 < N) {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V} {ϖ : O}
    (hϖ : Irreducible ϖ) (hM : IsModelOver (pointIdeal O x) d)
    (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E') :
    ∃ w w' : Module.Basis (Fin N) Ω V, IsFlagPair ϖ x E E' w w' φ.deg φ.deg' φ.f φ.g := by
  have hne : ∀ k, ∃ j, x ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hM.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : ∃ c, segreVec x c ≠ 0 := ⟨c, Finset.prod_ne_zero_iff.mpr fun k _ => hc k⟩
  have hiff := hF O Ω K ι x N V E E' ϖ hϖ hM.multiProj
  obtain ⟨hl, hl'⟩ := hiff.2 hyc φ
  have hrank : Fintype.card (Fin N) = Module.finrank Ω V := by
    rw [Fintype.card_fin, ← finrank_top Ω V, ← φ.top, φ.dim]
    rfl
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hl hrank,
    basisOfLinearIndependentOfCardEqFinrank hl' hrank, (hiff.1 _ _ _ _ _ _).mpr ⟨φ, ?_, ?_, rfl, rfl, rfl, rfl⟩⟩
  · exact (coe_basisOfLinearIndependentOfCardEqFinrank hl hrank).symm
  · exact (coe_basisOfLinearIndependentOfCardEqFinrank hl' hrank).symm

theorem proof (hFlag : FlagIndependence.Statement) (hF : FlagPairCharacterisation.Statement.{0, 0, 0})
    (hSupp : VerticalDivisorSupportFibre.Statement) : FlagPlainValueIndependence.Statement := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM hS φ₁ φ₂ I hI G hG r L c Q hc hGc hQ
  rw [pairNum_intNum hSupp hM φ₁ I hI r L, pairNum_intNum hSupp hM φ₂ I hI r L,
    plainPolynomialPairNumber.proof O K ι _ d N _ _ _ _ c G hGc hc r L Q hQ,
    plainPolynomialPairNumber.proof O K ι _ d N _ _ _ _ c G hGc hc r L Q hQ]
  refine Finset.sum_congr rfl fun μ hμ => congrArg (Q.coeff μ * ·) ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : φ₁.deg = φ₂.deg := Subsingleton.elim _ _
    have h2 : φ₁.deg' = φ₂.deg' := Subsingleton.elim _ _
    have h3 : φ₁.f = φ₂.f := Subsingleton.elim _ _
    have h4 : φ₁.g = φ₂.g := Subsingleton.elim _ _
    rw [h1, h2, h3, h4]
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨-, hM'⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
    have hS' := (BundleExamples.sameGeneric_iff hϖ x E E').mp hS
    obtain ⟨w₁, w₁', h₁⟩ := exists_isFlagPair hF hN hϖ hM' φ₁
    obtain ⟨w₂, w₂', h₂⟩ := exists_isFlagPair hF hN hϖ hM' φ₂
    have hE := dividedDifferenceExpansion.proof N c G hGc
    exact hFlag O ϖ hϖ Ω K ι x d hM' N V E E' hS' w₁ w₁' w₂ w₂' _ _ _ _ _ _ _ _ h₁ h₂ c G hGc hG _ _ hE hE
      (classList L μ) (by rw [classList_length_of_mem_support L hQ hμ]; omega)

end FlagPlainValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinRight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord midDeg midVar assocDeg assocVar midSwapBlocks midSwapVars
  midSwapVars_fst joinCoord_comp_midSwapVars)

namespace PairNumberJoinRight

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocDeg_comp_midSwapBlocks (a : K ⊕ K' → ℤ) :
    assocDeg (K₂ := K₂) a ∘ midSwapBlocks = midDeg (K₂ := K₂) a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midSwapVars_comp_midVar :
    ⇑(midSwapVars ι ι' ι₂) ∘ midVar (ι := ι) (ι' := ι') ι₂ = assocVar ι₂ := by
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem midDeg_sub (a b : K ⊕ K' → ℤ) :
    midDeg (K₂ := K₂) a - midDeg (K₂ := K₂) b = midDeg (K₂ := K₂) (a - b) := by
  funext k
  rcases k with k | k | k <;> simp [midDeg]

end PairNumberJoinRight


open PairNumberJoinRight in
theorem PairNumberJoinRight.proof (hLeft : PairNumberJoinLeft.Statement)
    (hVert : JoinVerticalDivisorRight.Statement) (hRel : PairNumberRelabelAlt.Statement) :
    PairNumberJoinRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w d hF hZ hfn I I₁ hI hI₁ n a a' f g hv H hH
  classical
  have hy := joinCoord_comp_midSwapVars x z w
  obtain ⟨hZL, hfnL, -, hnum⟩ := hRel O Ω (K ⊕ (K₂ ⊕ K')) (Sum.elim ι (Sum.elim ι₂ ι'))
    (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) midSwapBlocks (midSwapVars ι ι' ι₂) midSwapVars_fst
    (joinCoord x (joinCoord z w)) d (by rw [hy]; exact hZ)
  have hIL : IsFieldIntersection (F := IsLocalRing.ResidueField O) (ι := Sum.elim ι (Sum.elim ι' ι₂))
      (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) :=
    IntNumIsFieldIntersection.full _ _ _
  rw [hLeft O Ω K ι x K' ι' z K₂ ι₂ w d hF hZL (hfnL.trans (by rw [hy]; exact hfn)) _ I₁ hIL hI₁ n a a'
    f g hv H hH]
  have key := hnum I _ hI hIL n (fun i => assocDeg (K₂ := K₂) (a i)) (fun i => assocDeg (K₂ := K₂) (a' i))
    (fun i => rename (midVar ι₂) (f i)) (fun i => rename (midVar ι₂) (g i)) (fun i => by
      rw [hy, assocDeg_comp_midSwapBlocks, assocDeg_comp_midSwapBlocks, midDeg_sub]
      exact hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (hv i)) H hH
  simp only [hy, assocDeg_comp_midSwapBlocks, rename_rename, midSwapVars_comp_midVar] at key
  exact key.symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHomLocRingLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def HomLocRingMem.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], W.IsPrime → P ≤ W →
    ∀ z : FractionRing (MRing ι R ⧸ P), z ∈ homLocRing P W ↔
      ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
        z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g)

def HomLocRingIsLocal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], W.IsPrime → P ≤ W →
    IsLocalRing (homLocRing P W) ∧
      ∀ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
        ∀ hz : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ∈
              homLocRing P W,
          IsUnit (⟨_, hz⟩ : homLocRing P W) ↔ f ∉ W

def HomLocRingNoetherian.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      IsNoetherianRing (homLocRing P W)

def HomLocRingDimLe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      ringKrullDim (homLocRing P W) ≤ ((W.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagConeAlg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagConeAlg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, 1 ≤ k → ∀ hkN : k ≤ N,
    ∃ (l : Fin k → Fin M) (m' : Fin M'),
      LinearIndependent Ω (fun i : Fin k => fun j : Fin k => φ (l i) (w (Fin.castLE hkN j))) ∧
      flagClosurePt y w e φ φ' t k ⟨none, m'⟩ ≠ 0 ∧
      ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
        IsAlgebraic
          (Algebra.adjoin O
            (Set.range (fun q : Σ k, ι k =>
                (C (algebraMap Ω Φ (y q)) * X (some (some q.1)) : MvPolynomial (Option (Option K)) Φ)) ∪
              Set.range (Sum.elim
                (fun i : Fin k => C (flagClosurePt y w e φ φ' t k ⟨some none, l i⟩) * X (some none))
                (fun _ : Unit => C (flagClosurePt y w e φ φ' t k ⟨none, m'⟩) * X none))))
          (C (flagClosurePt y w e φ φ' t k p) * X p.1)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutForms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutForms.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (S : Finset (Ideal (MRing (bundleIdx (bundleIdx ι M) M') O))),
      (∀ Q ∈ S, Q.IsPrime ∧ IsRelevant Q ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ Q ∧
        (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q) →
      ∃ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs ∧ IsMultiHomog h ch ∧
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧ h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h ∧
        ∀ Q ∈ S, h ∉ Q

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

