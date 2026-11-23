module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutLiesOver
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0061

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutProjection

theorem relDim_anti {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} {I J : Ideal (MRing ι F)}
    (hIJ : I ≤ J) : FieldNumbers.relDim J ≤ FieldNumbers.relDim I := by
  have hmono : Monotone (fun x : WithBot ℕ∞ =>
      WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) x) :=
    WithBot.monotone_map_iff.2 (WithTop.monotone_map_iff.2 (fun a b h =>
      Int.sub_le_sub_right (by exact_mod_cast h) _))
  exact hmono (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJ) (Ideal.Quotient.factor_surjective hIJ))

theorem specialIdeal_le_contractPrime {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K K' : Type*} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type*}
    {I : Ideal (MRing (fun k => ι' (j k)) O)} {W : Ideal (MRing ι' O)}
    (h : I ≤ W.comap (rename (FieldNumbers.blockIncl j ι'))) :
    specialIdeal I ≤ FieldNumbers.contractPrime j (specialIdeal W) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  simp only [Ideal.mem_comap, FieldNumbers.contractPrime, specialIdeal]
  rw [← map_rename]
  exact Ideal.mem_map_of_mem _ (h hf)

end SegreFlagCutProjection

open SegreFlagCutProjection in
theorem SegreFlagCutProjection.proof (hLies : SegreFlagCutLiesOver.Statement)
    (hDim : SegreFlagProjSpecialDim.Statement) : SegreFlagCutProjection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  obtain ⟨hl1, hl2⟩ := hLies O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  obtain ⟨hd1, hd2⟩ := hDim O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  refine ⟨fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_,
    fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_⟩
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl1 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd1
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl2 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection IsProjVarF)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField assocDeg assocVar)

namespace PairNumberJoinLeft

theorem verticalComponentFibre : VerticalComponentFibre.Statement :=
  VerticalComponentFibre.proof (FibreVarieties.proof GenericFibProps.full GenericDimBound.full
    GenericDimGe.proof SpecialIdealCorresp.full SpecialIdealMultiHomog.full SupSpanMultiHomog.full
    MinimalPrimeMultiHomog.full SpecialQuotDim.full ComponentDim.proof)

theorem pairNum_fieldNum {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ)
    (hP : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d) (I : IFamily (IsLocalRing.ResidueField O) ι)
    (hI : IsFieldIntersection I) {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    (hv : ∀ l, IsVertDiv O P (y l - y' l) (f l) (g l)) (G : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I P d y y' f g G =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
        y y' f g G := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hM⟩ := (BundleExamples.isModelOver_iff O P d).mp hP
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  have hdiv : IsVerticalDivisor P ϖ (y l - y' l) (f l) (g l) :=
    (VerticalDivisorCharacterisation.proof O K ι P ϖ _ _ _ hϖ hM.multiProj).mp (hv l)
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hW' : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P (f l) (g l) W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hvert : (C ϖ : MRing ι O) ∈ W := hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
  obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
  have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (f l) W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (g l) W ≠ 0 := by
    by_contra hc
    simp only [not_or, ne_eq, not_not] at hc
    apply hW'
    simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
  have hVar : IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d := by
    rcases hor with h | h
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := verticalComponentFibre O ϖ hϖ K ι P d hM (f l) bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := verticalComponentFibre O ϖ hϖ K ι P d hM (g l) bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  split_ifs with h
  · exact Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hVar
  · rfl

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

def assocSigma (ι : K → Type) (ι' : K' → Type) (ι₂ : K₂ → Type) :
    (Σ k : (K ⊕ K') ⊕ K₂, Sum.elim (Sum.elim ι ι') ι₂ k) ≃
      (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) where
  toFun
    | ⟨.inl (.inl k), i⟩ => ⟨.inl k, i⟩
    | ⟨.inl (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
    | ⟨.inr k, i⟩ => ⟨.inr (.inr k), i⟩
  invFun
    | ⟨.inl k, i⟩ => ⟨.inl (.inl k), i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inl (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr k, i⟩
  left_inv := by rintro ⟨(k | k) | k, i⟩ <;> rfl
  right_inv := by rintro ⟨k | k | k, i⟩ <;> rfl

theorem assocSigma_fst (v : Σ k : (K ⊕ K') ⊕ K₂, Sum.elim (Sum.elim ι ι') ι₂ k) :
    (assocSigma ι ι' ι₂ v).1 = Equiv.sumAssoc K K' K₂ v.1 := by
  obtain ⟨(k | k) | k, i⟩ := v <;> rfl

theorem assocSigma_symm_fst (v : Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) :
    ((assocSigma ι ι' ι₂).symm v).1 = (Equiv.sumAssoc K K' K₂).symm v.1 := by
  obtain ⟨k | k | k, i⟩ := v <;> rfl

theorem pointIdeal_map_rename {K₁ K₃ : Type} {κ₁ : K₁ → Type} {κ₃ : K₃ → Type} (R : Type) [CommRing R]
    {Ω : Type} [Field Ω] [Algebra R Ω] (e : K₁ ≃ K₃) (σ : (Σ k, κ₁ k) ≃ (Σ k, κ₃ k))
    (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, κ₁ k) → Ω) :
    (pointIdeal R y).map (rename σ) = pointIdeal R (y ∘ σ.symm) := by
  have hp : ∀ p, (σ.symm p).1 = e.symm p.1 := fun p => by
    rw [Equiv.eq_symm_apply, ← hσ, Equiv.apply_symm_apply]
  have key : (pointConeMap R y).comp (rename σ.symm) =
      ((rename e.symm).restrictScalars R).comp (pointConeMap R (y ∘ σ.symm)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, hp]
  have hmap : (pointIdeal R y).map (rename σ) = (pointIdeal R y).comap (rename σ.symm) := by
    have h := Ideal.map_comap_of_equiv (I := pointIdeal R y) (renameEquiv R σ).toRingEquiv
    exact h
  rw [hmap]
  ext f
  rw [Ideal.mem_comap]
  unfold pointIdeal
  rw [RingHom.mem_ker, RingHom.mem_ker]
  have hf := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at hf
  change (pointConeMap R y) (rename σ.symm f) = 0 ↔ _
  rw [hf, AlgHom.restrictScalars_apply]
  exact map_eq_zero_iff _ (rename_injective _ e.symm.injective)

theorem assocDeg_comp (b : K ⊕ K' → ℤ) :
    assocDeg (K₂ := K₂) b ∘ Equiv.sumAssoc K K' K₂ = joinDeg (K' := K₂) b := by
  funext k
  rcases k with (k | k) | k <;> rfl

theorem rename_assocVar {R : Type} [CommRing R] (f : MRing (Sum.elim ι ι') R) :
    rename (assocVar ι₂) f = rename (assocSigma ι ι' ι₂) (joinForm (ι' := ι₂) f) := by
  rw [joinForm, rename_rename]
  refine congrArg (fun φ => rename φ f) ?_
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem fnField_assoc (O : Type) [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] (x : (Σ k, ι k) → Ω)
    (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (hfn : fnField O (joinCoord x (joinCoord z w)) = fnField O (joinCoord x z)) :
    fnField O (joinCoord (joinCoord x z) w) = fnField O (joinCoord x z) := by
  apply le_antisymm
  · refine Subfield.closure_le.mpr ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨(k | k) | k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inr k, i, j⟩, rfl⟩)
    · rw [← hfn]
      exact Subfield.subset_closure (Or.inr ⟨⟨.inr (.inr k), i, j⟩, rfl⟩)
  · refine Subfield.closure_le.mpr ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, i, j⟩, rfl⟩)

end PairNumberJoinLeft


open PairNumberJoinLeft in
theorem PairNumberJoinLeft.proof (hPull : PairNumberPullback.Statement)
    (hVert : JoinVerticalDivisorLeft.Statement) (hBir : BirationalJoin.Statement) :
    PairNumberJoinLeft.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w d hF hZ hfn I I₁ hI hI₁ n a a' f g hv H hH
  let _ := Classical.decEq K
  let _ := Classical.decEq K'
  let _ := Classical.decEq K₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hvZ : ∀ i, IsVertDiv O (mcIdeal O (joinCoord x (joinCoord z w)))
      (assocDeg (K₂ := K₂) (a i) - assocDeg (K₂ := K₂) (a' i))
      (rename (assocVar ι₂) (f i)) (rename (assocVar ι₂) (g i)) := by
    intro i
    have h := hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (hv i)
    convert h using 1
    funext k
    rcases k with k | k | k <;> simp [assocDeg]
  rw [pairNum_fieldNum _ d hF I₁ hI₁ _ _ _ _ hv, pairNum_fieldNum _ d hZ I hI _ _ _ _ hvZ,
    BundleExamples.pairNum_eq _ d _ _ _ _ hH, BundleExamples.pairNum_eq _ d _ _ _ _ hH]
  set Gs := fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l H) with hGs
  have hσ := assocSigma_fst (ι := ι) (ι' := ι') (ι₂ := ι₂)
  have hσ' := assocSigma_symm_fst (ι := ι) (ι' := ι') (ι₂ := ι₂)
  have hPZ : (pointIdeal O (joinCoords (joinCoords x z) w)).map (rename (assocSigma ι ι' ι₂)) =
      mcIdeal O (joinCoord x (joinCoord z w)) := by
    rw [pointIdeal_map_rename O (Equiv.sumAssoc K K' K₂) _ hσ]
    change pointIdeal O _ = pointIdeal O _
    congr 1
    funext p
    obtain ⟨k | k | k, i⟩ := p <;> rfl
  have hZP : (mcIdeal O (joinCoord x (joinCoord z w))).map (rename (assocSigma ι ι' ι₂).symm) =
      pointIdeal O (joinCoords (joinCoords x z) w) := by
    rw [BundleExamples.mcIdeal_eq_pointIdeal,
      pointIdeal_map_rename O (Equiv.sumAssoc K K' K₂).symm _ hσ']
    congr 1
    funext p
    obtain ⟨(k | k) | k, i⟩ := p <;> rfl
  have hrel := (PairNumberRelabel.proof O ϖ ((K ⊕ K') ⊕ K₂) (Sum.elim (Sum.elim ι ι') ι₂)
    (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) (Equiv.sumAssoc K K' K₂) (assocSigma ι ι' ι₂) hσ
    (pointIdeal O (joinCoords (joinCoords x z) w))).2.2 n (fun i => assocDeg (a i))
    (fun i => assocDeg (a' i)) (fun i => joinForm (f i)) (fun i => joinForm (g i)) Gs []
  rw [hPZ] at hrel
  simp only [← rename_assocVar, assocDeg_comp, List.map_nil] at hrel
  rw [hrel]
  have hmodF : IsModelOver (pointIdeal O (joinCoords x z)) d := by
    rw [BundleExamples.joinCoords_eq]
    exact ((BundleExamples.isModelOver_iff O _ d).mp hF).2
  have hmodZ : IsModelOver (pointIdeal O (joinCoords (joinCoords x z) w)) (d + 0) := by
    rw [← hZP]
    exact (PairNumberRelabel.proof O ϖ (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) ((K ⊕ K') ⊕ K₂)
      (Sum.elim (Sum.elim ι ι') ι₂) (Equiv.sumAssoc K K' K₂).symm (assocSigma ι ι' ι₂).symm hσ'
      (mcIdeal O (joinCoord x (joinCoord z w)))).1 d ((BundleExamples.isModelOver_iff O _ d).mp hZ).2
  have hbir : IsBirationalJoin O (joinCoords x z) w := by
    rw [BundleExamples.joinCoords_eq]
    exact hBir O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) K₂ ι₂ w (fnField_assoc O x z w hfn)
  have hvF : ∀ i, IsVerticalDivisor (pointIdeal O (joinCoords x z)) ϖ (a i - a' i) (f i) (g i) := by
    intro i
    rw [BundleExamples.joinCoords_eq]
    exact (VerticalDivisorCharacterisation.proof O (K ⊕ K') (Sum.elim ι ι') _ ϖ _ _ _ hϖ
      ((BundleExamples.isModelOver_iff O _ d).mp hF).2.multiProj).mp (hv i)
  have hexp := dividedDifferenceExpansion.proof n (d + 1) H hH
  have key := (hPull O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') K₂ ι₂ (joinCoords x z) w d 0 hmodF hmodZ n a a' f g
    hvF (d + 1) H hH Gs hexp [] (by simp)).2 hbir
  rw [BundleExamples.mcIdeal_eq_pointIdeal, ← BundleExamples.joinCoords_eq]
  exact key.symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumRelabel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

namespace PairNumberRelabelAlt

theorem mcIdeal_map_rename {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
    [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] (O : Type) [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (y ∘ σ)).map (rename σ) = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y :=
  pointIdeal_map_rename e σ hσ y

theorem mem_ratios {Ω₁ : Type*} [Field Ω₁] {K₀ : Type} {κ : K₀ → Type} (y : (Σ k, κ k) → Ω₁) (z : Ω₁) :
    z ∈ Set.range (fun q : (Σ k, κ k × κ k) => y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) ↔
      ∃ a b : Σ k, κ k, a.1 = b.1 ∧ y a / y b = z := by
  constructor
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    exact ⟨⟨k, i⟩, ⟨k, j⟩, rfl, rfl⟩
  · rintro ⟨⟨k, i⟩, ⟨k', j⟩, h, rfl⟩
    dsimp only at h
    subst h
    exact ⟨⟨k, i, j⟩, rfl⟩

theorem fnField_comp {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} (O : Type) [CommRing O] {Ω : Type}
    [Field Ω] [Algebra O Ω] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (y : (Σ k, ι₂ k) → Ω) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O y = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (y ∘ σ) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField
  congr 1
  ext z
  simp only [Set.mem_union]
  refine or_congr_right ?_
  rw [mem_ratios, mem_ratios]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨σ.symm a, σ.symm b, ?_, by simp only [Function.comp_apply, Equiv.apply_symm_apply]⟩
    apply e.injective
    rw [← hσ, ← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hab]
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨σ a, σ b, by rw [hσ, hσ, hab], rfl⟩

theorem pairNum_eq_intNum (hF : VerticalComponentFibre.Statement)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : IFamily (IsLocalRing.ResidueField O) ι) (hI : IsFieldIntersection I)
    (P : Ideal (MRing ι O)) (d : ℕ) (hP : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d)
    {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    (hv : ∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P (y l - y' l) (f l) (g l))
    (G : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I P d y y' f g G =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
        y y' f g G := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hM := ((BundleExamples.isModelOver_iff O P d).1 hP).2
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  have hdiv := (VerticalDivisorCharacterisation.proof O K ι P ϖ (y l - y' l) (f l) (g l) hϖ hM.multiProj).1 (hv l)
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hW0 := Finsupp.mem_support_iff.mp hW
  have hvert : (C ϖ : MRing ι O) ∈ W := hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
  obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
  have hvar : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d := by
    have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (f l) W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (g l) W ≠ 0 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      apply hW0
      simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
    rcases hor with h | h
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι P d hM (f l) bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι P d hM (g l) bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  split_ifs with h
  · exact Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hvar
  · rfl

end PairNumberRelabelAlt


open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal) in
theorem PairNumberRelabelAlt.proof (hF : VerticalComponentFibre.Statement) : PairNumberRelabelAlt.Statement := by
  classical
  intro O _ _ _ Ω _ _ K₁ _ ι₁ _ K₂ _ ι₂ _ e σ hσ y d hM
  have hmap := PairNumberRelabelAlt.mcIdeal_map_rename O e σ hσ y
  have hM₁ := (BundleExamples.isModelOver_iff O (mcIdeal O (y ∘ σ)) d).1 hM
  have hM₂' : IsModelOver ((mcIdeal O (y ∘ σ)).map (rename σ)) d := by
    rw [PairNumberRelabel.map_rename_eq σ]
    exact PairNumberRelabel.isModelOver_map e σ hσ _ d hM₁.2
  have hM₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d := by
    rw [← hmap]
    exact (BundleExamples.isModelOver_iff O _ d).2 ⟨⟨e hM₁.1.some⟩, hM₂'⟩
  have hvd : ∀ (b : K₂ → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
      IsVertDiv O (mcIdeal O (y ∘ σ)) (b ∘ e) f g → IsVertDiv O (mcIdeal O y) b (rename σ f) (rename σ g) := by
    intro b f g h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have h1 := (VerticalDivisorCharacterisation.proof O K₁ ι₁ _ ϖ (b ∘ e) f g hϖ hM₁.2.multiProj).1 h
    have h2 := PairNumberRelabel.isVerticalDivisor_map e σ hσ _ ϖ b f g h1
    rw [← PairNumberRelabel.map_rename_eq σ] at h2
    rw [← hmap]
    exact (VerticalDivisorCharacterisation.proof O K₂ ι₂ _ ϖ b _ _ hϖ hM₂'.multiProj).2 h2
  refine ⟨hM₂, PairNumberRelabelAlt.fnField_comp O e σ hσ y, hvd, ?_⟩
  intro I₁ I hI₁ hI n a a' f g hfg H hH
  have hfg' : ∀ i, IsVertDiv O (mcIdeal O y) (a i - a' i) (rename σ (f i)) (rename σ (g i)) :=
    fun i => hvd (a i - a' i) (f i) (g i) (hfg i)
  rw [PairNumberRelabelAlt.pairNum_eq_intNum hF I₁ hI₁ _ d hM (fun i => a i ∘ e) (fun i => a' i ∘ e) f g hfg H,
    PairNumberRelabelAlt.pairNum_eq_intNum hF I hI _ d hM₂ a a' _ _ hfg' H,
    BundleExamples.pairNum_eq _ d _ _ f g hH, BundleExamples.pairNum_eq _ d a a' _ _ hH, ← hmap,
    PairNumberRelabel.map_rename_eq σ, PairNumberRelabel.pairNum_map e σ hσ _ a a' f g]
  rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFrac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpLocRingFrac.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∀ z ∈ blowUpLocRing P u W', ∃ b ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
          (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧ z * s = b

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

