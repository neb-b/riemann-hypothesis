module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0054

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairValueIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace FlagPairValueIndependence

theorem polyNum_congr {F : Type*} [Field F] {K : Type} [Fintype K] {κ : K → Type} [∀ k, Fintype (κ k)]
    (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ) (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F κ)) (n : ℕ)
    {m : ℕ} {deg₁ deg₂ : Fin m → K → ℤ} (P : MvPolynomial (Fin m) ℤ)
    (h : ∀ s ∈ P.vars, deg₁ s = deg₂ s) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n deg₁ P = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n deg₂ P := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hm : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₁ μ = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₂ μ := by
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
    congr 1
    funext s
    by_cases hs : μ s = 0
    · simp [hs]
    · rw [h s ((mem_vars_iff_mem_support s).mpr ⟨μ, hμ, Finsupp.mem_support_iff.mpr hs⟩)]
  exact congrArg (fun l : List (K → ℤ) => P.coeff μ * if h : l.length = n then
    I W n (fun j => l.get (Fin.cast h.symm j)) else 0) hm

theorem not_mem_vars_divDiff_castAdd {N r : ℕ} (i : Fin N) (j : Fin r) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin r) ℤ) :
    Fin.natAdd (N + r) (Fin.natAdd N j) ∉ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
      (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)).vars := by
  classical
  intro hs
  obtain ⟨μ, hμ, hsμ⟩ := (mem_vars_iff_mem_support _).mp hs
  have he : Function.Injective
      (finSumFinEquiv.symm : Fin ((N + r) + (N + r)) → Fin (N + r) ⊕ Fin (N + r)) :=
    finSumFinEquiv.symm.injective
  have h1 : Finsupp.mapDomain finSumFinEquiv.symm μ ∈ (rename finSumFinEquiv.symm
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).support := by
    rw [support_rename_of_injective he]
    exact Finset.mem_image_of_mem _ hμ
  have h2 : finSumFinEquiv.symm (Fin.natAdd (N + r) (Fin.natAdd N j)) ∈ (rename finSumFinEquiv.symm
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).vars := by
    refine (mem_vars_iff_mem_support _).mpr ⟨_, h1, ?_⟩
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply_of_injective he]
    exact Finsupp.mem_support_iff.mp hsμ
  rw [finSumFinEquiv_symm_apply_natAdd, plainPolynomialPairNumber.rename_divDiff_castAdd_mul] at h2
  rcases Finset.mem_union.mp (vars_mul _ _ h2) with h3 | h3
  · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (vars_rename _ _ h3)
    rcases t with t | t
    · exact Sum.inl_ne_inr ht
    · simp only [Sum.map_inr, Sum.inr.injEq] at ht
      have := congrArg Fin.val ht
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
  · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (vars_rename _ _ h3)
    exact Sum.inl_ne_inr ht

theorem proof (hPlain : FlagPlainValueIndependence.Statement)
    (hFur : flagFurtherTerm_independent.Statement) : FlagPairValueIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ
  classical
  have hz : ∀ J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (IsLocalRing.ResidueField O) ι) → ℤ,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J 0 = 0 := fun J => Finsupp.sum_zero_index
  have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) 1 1 = 0 :=
    sub_self _
  have split : ∀ φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E',
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                (Fin.append φ.deg y) (Fin.append φ.deg' y') (Fin.append φ.f f) (Fin.append φ.g g)
                                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                  (Fin.append φ.deg y) (Fin.append φ.deg' y) (Fin.append φ.f fun _ => 1)
                                  (Fin.append φ.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) +
          ∑ l : Fin r, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
            (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
              (Fin.append (Fin.append φ.deg y) (Fin.append φ.deg' y'))
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
            (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l)) := by
    intro φ
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, h0, hz, Finset.sum_const_zero, add_zero]
    refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
    refine congrArg (fun J => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J _) (funext fun W => ?_)
    refine polyNum_congr I W d _ fun s hs => ?_
    induction s using Fin.addCases with
    | left a => simp only [Fin.append_left]
    | right b =>
      induction b using Fin.addCases with
      | left a => simp only [Fin.append_right, Fin.append_left]
      | right j => exact absurd hs (not_mem_vars_divDiff_castAdd i j G Q)
  rw [split φ₁, split φ₂, hPlain O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y c Q hc hGc hQ]
  congr 1
  exact Finset.sum_congr rfl fun l _ =>
    hFur O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ l

end FlagPairValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointModel
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)

namespace JoinPointModel

section Split

variable {K : Type} {ι : K → Type}

def varEquiv : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Option (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  invFun
    | some p => ⟨.inl p.1, p.2⟩
    | none => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨k | u, i⟩
    · rfl
    · cases u
      change Fin 1 at i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rfl
  right_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl

variable (K) (Ω : Type*) [CommRing Ω]

def tgtEquiv : MvPolynomial (K ⊕ Unit) Ω ≃ₐ[Ω] Polynomial (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.optionEquivSumPUnit.{0, 0} K).symm).trans (optionEquivLeft Ω K)

variable {K} (O : Type*) [CommRing O]

def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O ≃ₐ[O]
    Polynomial (MvPolynomial (Σ k, ι k) O) :=
  (renameEquiv O varEquiv).trans (optionEquivLeft O _)

end Split

section Cone

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem tgtEquiv_mcMap (y : (Σ k, ι k) → Ω) (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    tgtEquiv K Ω (mcMap O (joinCoord y (ptCoord (Ω := Ω))) p) =
      Polynomial.map (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω) (srcEquiv O p) := by
  have h : ((tgtEquiv K Ω : MvPolynomial (K ⊕ Unit) Ω →+* Polynomial (MvPolynomial K Ω)).comp
      (mcMap O (joinCoord y (ptCoord (Ω := Ω))) : _ →+* MvPolynomial (K ⊕ Unit) Ω)) =
      (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)).comp
        (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tgtEquiv, srcEquiv, mcMap, optionEquivLeft_C]
    · rintro ⟨k | u, i⟩
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, optionEquivLeft_X_some, optionEquivLeft_C]
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, ptCoord, optionEquivLeft_X_none]
  exact RingHom.congr_fun h p

theorem mem_pointIdeal_join_iff (y : (Σ k, ι k) → Ω)
    (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    p ∈ pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) ↔
      srcEquiv O p ∈ RingHom.ker
        (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)) := by
  rw [← BundleExamples.mcIdeal_eq_pointIdeal, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, RingHom.mem_ker, RingHom.mem_ker,
    Polynomial.coe_mapRingHom, ← tgtEquiv_mcMap, map_eq_zero_iff _ (tgtEquiv K Ω).injective]

theorem ringKrullDim_join [IsNoetherianRing O] (y : (Σ k, ι k) → Ω) :
    ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ pointIdeal O (joinCoord y (ptCoord (Ω := Ω)))) =
      ringKrullDim (MRing ι O ⧸ pointIdeal O y) + 1 := by
  let J := RingHom.ker (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω))
  let Φ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O →+* Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J :=
    (Ideal.Quotient.mk J).comp (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom
  have hΦ : Function.Surjective Φ := Ideal.Quotient.mk_surjective.comp (srcEquiv O).surjective
  have hker : pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) = RingHom.ker Φ := by
    ext p
    rw [mem_pointIdeal_join_iff, RingHom.mem_ker (f := Φ)]
    change _ ↔ Ideal.Quotient.mk J (srcEquiv O p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
  have hJ : J = (pointIdeal O y).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) := by
    simp only [J]
    rw [Polynomial.ker_mapRingHom]
    rfl
  have hq : ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ RingHom.ker Φ) =
      ringKrullDim (Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hΦ)
  have hp : ringKrullDim (Polynomial (MRing ι O ⧸ pointIdeal O y)) =
      ringKrullDim (Polynomial (MRing ι O) ⧸ (pointIdeal O y).map (Polynomial.C : MRing ι O →+* _)) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.polynomialQuotientEquivQuotientPolynomial (pointIdeal O y))
  rw [hker, hq, hJ, ← hp, Polynomial.ringKrullDim_of_isNoetherianRing]

end Cone

end JoinPointModel


open JoinPointModel in
theorem JoinPointModel.proof : JoinPointModel.Statement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y d hW
  rw [BundleExamples.isModelOver_iff]
  refine ⟨inferInstance, ⟨?_, ?_, ?_⟩⟩
  · apply GenericProjClosureDim.isMultiProjPrime_pointIdeal
    rintro (k | u)
    · obtain ⟨j, hj⟩ := hW.multiProj.relevant k
      refine ⟨j, fun h0 => hj ?_⟩
      change y ⟨k, j⟩ = 0 at h0
      rw [pointIdeal, RingHom.mem_ker]
      simp [pointConeMap, h0]
    · exact ⟨(0 : Fin 1), by simp [joinCoord, ptCoord]⟩
  · rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, pointIdeal, RingHom.mem_ker,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  · rw [BundleExamples.mcIdeal_eq_pointIdeal, ringKrullDim_join, hW.dim, Fintype.card_sum, Fintype.card_unit,
      show d + 1 + (Fintype.card K + 1) = (d + 1 + Fintype.card K) + 1 by omega]
    norm_cast

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinTwoModels
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal joinCoord fnField)

namespace JoinTwoModels

section Field

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem ratio_mem {K' : Type} {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : fnField O (joinCoord x z) = fnField O x) (k : K') (i j : ι' k) :
    z ⟨k, i⟩ / z ⟨k, j⟩ ∈ fnField O x := by
  rw [← h]
  exact Subfield.subset_closure (Or.inr ⟨⟨.inr k, (i, j)⟩, rfl⟩)

theorem fnField_join_two {K₁ : Type} {ι₁ : K₁ → Type} {K₂ : Type} {ι₂ : K₂ → Type} (x : (Σ k, ι k) → Ω)
    (z₁ : (Σ k, ι₁ k) → Ω) (z₂ : (Σ k, ι₂ k) → Ω) (h₁ : fnField O (joinCoord x z₁) = fnField O x)
    (h₂ : fnField O (joinCoord x z₂) = fnField O x) :
    fnField O (joinCoord x (joinCoord z₁ z₂)) = fnField O x := by
  apply le_antisymm
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨kk, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    · rcases kk with k | k | k
      · exact Subfield.subset_closure (Or.inr ⟨⟨k, (i, j)⟩, rfl⟩)
      · exact ratio_mem x z₁ h₁ k i j
      · exact ratio_mem x z₂ h₂ k i j
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, (i, j)⟩, rfl⟩)

end Field

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem exists_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    {d : ℕ} (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  classical
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at h
  obtain ⟨j, hj⟩ := h.2.multiProj.relevant k
  refine ⟨j, fun h0 => hj ?_⟩
  rw [pointIdeal, RingHom.mem_ker]
  simp [pointConeMap, h0]

end Model

end JoinTwoModels


open JoinTwoModels in
theorem JoinTwoModels.proof (hC : ConeTrdegFnField.Statement) : JoinTwoModels.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d hx K₁ _ ι₁ _ z₁ K₂ _ ι₂ _ z₂ h₁ hf₁ h₂ hf₂
  classical
  have hf := fnField_join_two x z₁ z₂ hf₁ hf₂
  refine ⟨?_, hf⟩
  have hy : ∀ k, ∃ i, joinCoord x (joinCoord z₁ z₂) ⟨k, i⟩ ≠ 0 := by
    rintro (k | k | k)
    · exact exists_ne_zero x hx k
    · exact exists_ne_zero _ h₁ (.inr k)
    · exact exists_ne_zero _ h₂ (.inr k)
  have hx' : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := exists_ne_zero x hx
  have hxW := hx
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at hxW
  obtain ⟨hK, hW⟩ := hxW
  have hinj : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O x).comap (C : O →+* MRing ι O) := by
      simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
        MvPolynomial.algebraMap_apply, ha, map_zero]
    rw [hW.noTorsion] at hmem
    exact hmem
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff]
  have hP := GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy
  have hPC : (pointIdeal O (joinCoord x (joinCoord z₁ z₂))).comap
      (C : O →+* MRing (Sum.elim ι (Sum.elim ι₁ ι₂)) O) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
      MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  refine ⟨inferInstance, ⟨hP, hPC, ?_⟩⟩

  have hdW := DvrConeDimTrdeg.proof O K ι (pointIdeal O x) hW.multiProj hW.noTorsion
  have hdJ := DvrConeDimTrdeg.proof O (K ⊕ (K₁ ⊕ K₂)) (Sum.elim ι (Sum.elim ι₁ ι₂)) _ hP hPC
  have htW := hC O Ω hinj K ι x hx'
  have htJ := hC O Ω hinj (K ⊕ (K₁ ⊕ K₂)) (Sum.elim ι (Sum.elim ι₁ ι₂)) _ hy
  rw [hf] at htJ
  rw [BundleExamples.mcIdeal_eq_pointIdeal] at htW htJ
  set T := Algebra.trdeg O (Algebra.adjoin O (fnField O x : Set Ω))
  rw [hW.dim] at hdW
  erw [htW] at hdW
  erw [hdJ, htJ]
  rw [map_add (f := _), map_natCast] at hdW ⊢
  have hT : Cardinal.toENat T = d := by
    have h1 : ((Cardinal.toENat T + (Fintype.card K : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) =
        ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdW.symm
    have h2 : Cardinal.toENat T + ((Fintype.card K + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
      have := WithBot.coe_injective h1
      push_cast at this ⊢
      rw [← add_assoc, this]; ring
    exact (WithTop.add_right_cancel (ENat.natCast_ne_top _) h2)
  rw [hT, Fintype.card_sum, Fintype.card_sum]
  have e : ((d : ℕ∞) + ((Fintype.card K + (Fintype.card K₁ + Fintype.card K₂) : ℕ) : ℕ∞) + 1) =
      ((d + 1 + (Fintype.card K + (Fintype.card K₁ + Fintype.card K₂)) : ℕ) : ℕ∞) := by
    push_cast; ring
  rw [e]
  norm_cast

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivSupportFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorSupportFibre.fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.proof (GenericDimBound.proof MaximalIdealHeightFG.proof)
    GenericDimGe.proof SpecialIdealCorresp.proof SpecialIdealMultiHomog.proof SupSpanMultiHomog.proof
    MinimalPrimeMultiHomog.proof SpecialQuotDim.proof ComponentDim.proof

theorem VerticalDivisorSupportFibre.proof : VerticalDivisorSupportFibre.Statement := by
  classical
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hP1⟩ := (BundleExamples.isModelOver_iff O P d).mp hP
  have hV1 := (VerticalDivisorCharacterisation.proof O K ι P ϖ b f g hϖ hP1.multiProj).mp hV
  rw [BundleExamples.ratCyc_eq] at hW
  have hϖW := hV1.vertical W hW
  rw [BundleExamples.redIdeal_eq]

  have key : ∀ (h : MRing ι O) (bh : K → ℕ), IsMultiHomog h bh → h ∉ P → divCycle P h W ≠ 0 →
      ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d := by
    intro h bh hh hhP hne
    unfold divCycle at hne
    split_ifs at hne with hc
    · obtain ⟨hmp, hdim⟩ := VerticalComponentFibre.proof VerticalDivisorSupportFibre.fibreVarieties O ϖ hϖ
        K ι P d hP1 h bh hh hhP W hc.1 hc.2 hϖW
      obtain ⟨hpr, hho, hre⟩ := hmp
      exact ⟨⟨hpr, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof _ K ι _).2 hho, hre⟩, hdim⟩
    · exact absurd rfl hne
  obtain ⟨bf, bg, hf, hg, -⟩ := hV1.degrees
  by_cases hfW : divCycle P f W = 0
  · refine key g bg hg hV1.den_not_mem fun hgW => hW ?_
    simp [ratDiv, hfW, hgW]
  · exact key f bf hf hV1.num_not_mem hfW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutChart.Statement : Prop :=
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
    ∀ (k : ℕ) (hk : k < N) (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      W.IsPrime → IsRelevant W → pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W →
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
      ∃ (cl cm : Option (Option K) → ℕ) (l μ u : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog l cl ∧ IsMultiHomog μ cm ∧
        (fun o => (cl o : ℤ) - cm o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        μ ∉ W ∧ u ∉ W ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) l =
          flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) μ ∧
        (k = 0 → l ∉ W) ∧
        (0 < k → ∀ q ∈ pointIdeal O (flagClosurePt y w e φ φ' t k), ∃ n : ℕ,
          u ^ n * q ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l})

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

