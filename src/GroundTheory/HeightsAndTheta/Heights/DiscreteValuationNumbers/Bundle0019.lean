module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem IntNumIsFieldIntersection.of_intNumBase_cutRational
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) :
    IntNumIsFieldIntersection.Statement.{u} :=
  IntNumIsFieldIntersection.proof VocabMultiHomog.proof
    (VocabMultiHomogIdeal.proof VocabMultiHomog.proof) VocabDivCycle.proof
    (IntNumPoint.proof hBase) (IntNumRatSection.proof hCut)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpVerticalPush.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ a : Fin n → K → ℤ,
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing (extIdx ι J) O) ∈ W then vNum W (liftDegs a) else 0)
          (divCycle (blowUpOf P u) (liftForm x))) =
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W a else 0) (divCycle P x))

def BlowUpDivisorPush.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ a : Fin n → K → ℤ,
      cycEval (fun G => vNum G (liftDegs a)) (ratDiv (blowUpOf P u) (liftForm (J := J) f) (liftForm g)) =
        cycEval (fun G => vNum G a) (ratDiv P f g)

def BlowUpHorizontalCorresp.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    (∀ h : Ideal (MRing ι O) → ℤ,
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing (extIdx ι J) O) ∈ W then 0
            else h (W.comap (liftForm (ι := ι) (J := J) (R := O))))
          (divCycle (blowUpOf P u) (liftForm x))) =
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then 0 else h W) (divCycle P x))) ∧
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      divCycle P x (W.comap (liftForm (ι := ι) (J := J) (R := O))) ≠ 0 ∧
      ((∃ j, u j ∉ W.comap (liftForm (ι := ι) (J := J) (R := O))) →
        W = blowUpOf (W.comap (liftForm (ι := ι) (J := J) (R := O))) u)

def HorizontalComponentModel.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), divCycle P x W ≠ 0 → (C ϖ : MRing ι O) ∉ W → IsModelOver W d

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalAddOfFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem cycEval_add_of_finite {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (φ : Ideal (MRing ι R) → ℤ) {Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite) :
    cycEval φ (Z₁ + Z₂) = cycEval φ Z₁ + cycEval φ Z₂ := by
  unfold cycEval
  have f₁ : (Function.support fun W => Z₁ W * φ W).Finite :=
    h₁.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => Z₂ W * φ W).Finite :=
    h₂.subset fun W hW h0 => hW (by simp [h0])
  rw [← finsum_add_distrib f₁ f₂]
  refine finsum_congr fun W => ?_
  simp only [Pi.add_apply]
  ring

theorem RightSideMultiplicativeInForm.proof (h₁ : DivCycleMul.Statement.{u})
    (h₂ : DivCycleFiniteSupport.Statement.{u}) : RightSideMultiplicativeInForm.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g s₁ s₂ hs₁ hs₂ L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold cutIdentityRightSide
  rw [h₁ O K ι P s₁ s₂ hPp hs₁ hs₂]
  exact cycEval_add_of_finite _ (h₂ O K ι P s₁) (h₂ O K ι P s₂)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleEqZeroOfFormNotMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_nonneg (P : Ideal (MRing ι R)) (x : MRing ι R) (W : Ideal (MRing ι R)) :
    0 ≤ divCycle P x W := by
  unfold divCycle
  split_ifs <;> simp

theorem divCycle_eq_zero_of_form_not_mem (P : Ideal (MRing ι R)) {x : MRing ι R} {W : Ideal (MRing ι R)}
    (hx : x ∉ W) : divCycle P x W = 0 := by
  unfold divCycle
  rw [dite_eq_right]
  exact fun h => hx (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end

theorem ExcessPositive.proof : ExcessPositive.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP ⟨G, hϖG, hsG, hDG⟩
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hGdef : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant G := by
    by_contra h
    exact hsG (by unfold divCycle; rw [dite_eq_right h])
  have hGp : G.IsPrime := hGdef.1.1.1
  have hPG : P ≤ G := le_sup_left.trans hGdef.1.1.2
  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGp hPG hGdef.2
  have huP : u ∉ P := fun h => huG (hPG h)
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have hvP : v ∉ P := by
    intro hv
    have h1 : u * f ∈ P := by
      have h2 := P.add_mem huv (P.mul_mem_right g hv)
      rwa [sub_add_cancel] at h2
    exact (hPp.mem_or_mem h1).elim huP hfP
  have hcyc : divCycle P (u * f) G = divCycle P (v * g) G :=
    congrFun (divCycle_congr_of_sub_mem huv) G
  have huf := congrFun (DivCycleMul.proof O K ι P u f hPp huP hfP) G
  have hvg := congrFun (DivCycleMul.proof O K ι P v g hPp hvP hgP) G
  simp only [Pi.add_apply] at huf hvg
  have hu0 := divCycle_eq_zero_of_form_not_mem P huG
  have hv0 := divCycle_nonneg P v G
  have hs0 := divCycle_nonneg P s G
  have hDpos : 0 < ratDiv P f g G := by
    unfold ratDiv at hDG ⊢
    omega
  have hprod : 0 < (divCycle P s G * ratDiv P f g G).toNat := by
    have : 0 < divCycle P s G * ratDiv P f g G := mul_pos (lt_of_le_of_ne hs0 (Ne.symm hsG)) hDpos
    omega

  have hfin := DivCycleFiniteSupport.proof.{u} O K ι P s
  have hbdd : BddAbove (Set.range fun G' : {G' : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G'} =>
      (divCycle P s G'.1 * ratDiv P f g G'.1).toNat) := by
    apply Set.Finite.bddAbove
    apply ((hfin.image fun G' => (divCycle P s G' * ratDiv P f g G').toNat).insert 0).subset
    rintro _ ⟨G', rfl⟩
    by_cases h : divCycle P s G'.1 = 0
    · left
      simp [h]
    · right
      exact ⟨G'.1, h, rfl⟩
  exact lt_of_lt_of_le hprod (le_ciSup hbdd ⟨G, hϖG⟩)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExceptionalDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem BlowUpReduction.proof (hpieces : BlowUpDecomposition.Statement.{u})
    (hinv : BlowUpInvariance.Statement.{u}) (hcf : CommonFactorRemoval.Statement.{u})
    (hadd : AdditivityInDivisor.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (htaut : TautologicalCase.Statement.{u}) :
    BlowUpReduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L hId₁ hId₀
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  obtain ⟨hinvl, hinvr⟩ := hinv O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L
  set Q := blowUpOf P (blowUpGens s g f m e)
  set Y₀ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar none
  set Y₁ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar (some none)
  have hQ : Q.IsPrime := hmodel.multiProj.isPrime
  have hfmQ := hE.1.num_not_mem
  have hgYQ := hE.1.den_not_mem
  rw [map_mul] at hfmQ
  have hfQ : liftForm f ∉ Q := fun h => hfmQ (Q.mul_mem_right _ h)
  have hgQ : liftForm g ∉ Q := fun h => hgYQ (Q.mul_mem_right _ h)
  have hqQ : liftForm m * Y₁ ∉ Q := fun h =>
    (hQ.mem_or_mem h).elim hD₁.1.den_not_mem hD₁.1.num_not_mem

  have hcfq := hcf O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel (liftDeg b) (liftForm f)
    (liftForm g) (liftForm m * Y₁) (liftForm s) hfQ hgQ hqQ hslP (fun H hH hϖH => by
      obtain ⟨h₁, h₂⟩ := hH₁ H hH hϖH
      have hHp := isPrime_of_divCycle_ne_zero hH
      refine ⟨fun h => h₂.num_not_mem ?_, fun h => h₂.den_not_mem (H.mul_mem_right _ h),
        fun h => (hHp.mem_or_mem h).elim h₁.den_not_mem h₁.num_not_mem⟩
      rw [map_mul]; exact H.mul_mem_right _ h) (liftMDeg c) (liftDegs L)
  obtain ⟨haddl, haddr⟩ := hadd O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ _
    hD₁.1 hE.1 (liftMDeg c) (liftForm s) hsl hslP hH₁ (liftDegs L)
  have hnum : Y₁ * liftForm (f * m) = liftForm f * (liftForm m * Y₁) := by rw [map_mul]; ring
  have hden : liftForm m * (liftForm g * Y₁) = liftForm g * (liftForm m * Y₁) := by ring
  have hdeg : residualDeg e + exceptionalDeg b e = liftDeg b := by
    funext o; cases o <;> simp [residualDeg, exceptionalDeg, liftDeg]
  rw [hnum, hden, hcfq.1] at haddl
  rw [hnum, hden, hdeg, hcfq.2] at haddr

  obtain ⟨bf, bg, hbf, hbg, hb⟩ := hE.1.degrees
  have ht := htaut O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf bg hbf hbg hb
    (liftDegs L)
  have hdegs : liftMDeg c + bg = bf + Pi.single none 1 := by
    funext o
    have h := congrFun hb o
    cases o with
    | none => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; omega
    | some k => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; have := he k; omega
  have hl₁ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 (liftMDeg c) bg
    (liftDegs L)
  have hl₂ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf
    (Pi.single none 1) (liftDegs L)
  rw [hdegs] at hl₁
  have hrel := cutIdentityRightSide_congr_of_sub_mem ϖ Q (exceptionalDeg b e) (liftForm (f * m))
    (liftForm g * Y₁) (blowUp_relation P s g f m e) (liftDegs L)
  have hsg : liftForm (s * g) * Y₁ = liftForm s * (liftForm g * Y₁) := by rw [map_mul]; ring
  rw [hsg, hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hslP hE.1.den_not_mem,
    hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hE.1.num_not_mem hY₀P] at hrel
  rw [cutIdentity_iff] at hId₁ hId₀ ⊢
  rw [← hinvl, ← hinvr]
  linarith

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExistsMultiHomogNotMemOfIsRelevant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Avoid

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem exists_multiHomog_not_mem_of_isRelevant {H : Ideal (MRing ι R)} (hH : H.IsPrime)
    (hrel : IsRelevant H) (c : K → ℕ) : ∃ m : MRing ι R, IsMultiHomog m c ∧ m ∉ H := by
  choose i hi using hrel
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k) (fun k => c k • blockWeight ι ⟨k, i k⟩)
      (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)
    have hc : (∑ k, c k • blockWeight ι ⟨k, i k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hc] at hprod
    exact hprod
  · intro hm
    obtain ⟨k, -, hk⟩ := hH.prod_mem_iff.mp hm
    exact hi k (hH.mem_of_pow_mem _ hk)

theorem exists_multiHomog_not_mem_finset [Infinite R] (c : K → ℕ) (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ Q ∈ S, Q.IsPrime ∧ IsRelevant Q ∧ ∀ a : R, C a ∈ Q → a = 0) :
    ∃ m : MRing ι R, IsMultiHomog m c ∧ ∀ Q ∈ S, m ∉ Q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, isWeightedHomogeneous_zero _ _ _, by simp⟩
  | @insert Q₀ S _ ih =>
    obtain ⟨x, hx, hxS⟩ := ih fun Q h => hS Q (Finset.mem_insert_of_mem h)
    obtain ⟨hQ₀, hrel₀, hC₀⟩ := hS Q₀ (Finset.mem_insert_self _ _)
    obtain ⟨y, hy, hyQ₀⟩ := exists_multiHomog_not_mem_of_isRelevant hQ₀ hrel₀ c

    have hsub : ∀ Q ∈ S, {t : R | x + C t * y ∈ Q}.Subsingleton := by
      intro Q hQS t ht t' ht'
      obtain ⟨hQ, -, hCQ⟩ := hS Q (Finset.mem_insert_of_mem hQS)
      have hd : C (t - t') * y ∈ Q := by
        have h := Q.sub_mem ht ht'
        rw [map_sub]
        convert h using 1
        ring
      rcases hQ.mem_or_mem hd with h | h
      · exact sub_eq_zero.mp (hCQ _ h)
      · exact absurd (by simpa using Q.sub_mem ht (Q.mul_mem_left (C t) h)) (hxS Q hQS)
    have hfin : (insert 0 (⋃ Q ∈ S, {t : R | x + C t * y ∈ Q})).Finite :=
      (S.finite_toSet.biUnion fun Q hQ => (hsub Q hQ).finite).insert 0
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset hfin.toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      not_or, not_exists] at ht
    obtain ⟨ht0, htS⟩ := ht
    by_cases hxQ₀ : x ∈ Q₀
    · refine ⟨x + C t * y, hx.add (by simpa using (isWeightedHomogeneous_C _ t).mul hy), ?_⟩
      intro Q hQ
      rcases Finset.mem_insert.mp hQ with rfl | hQS
      · intro h
        have h' : C t * y ∈ Q := by simpa using Q.sub_mem h hxQ₀
        rcases hQ₀.mem_or_mem h' with h'' | h''
        · exact ht0 (hC₀ _ h'')
        · exact hyQ₀ h''
      · exact htS Q hQS
    · refine ⟨x, hx, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQS
      · exact hxQ₀
      · exact hxS Q hQS

end Avoid

theorem HorizontalAvoidingForm.proof : HorizontalAvoidingForm.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP s hs e
  classical
  have : Infinite O :=
    Infinite.of_injective _ (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)

  have hfin : (Function.support (divCycle P s)).Finite := by
    apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s}))
    intro W hW
    by_contra hmin
    apply hW
    unfold divCycle
    rw [dite_eq_right]
    exact fun h => hmin h.1

  have hT : ∀ Q ∈ insert P (hfin.toFinset.filter fun H => (C ϖ : MRing ι O) ∉ H),
      Q.IsPrime ∧ IsRelevant Q ∧ ∀ a : O, C a ∈ Q → a = 0 := by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · refine ⟨hP.multiProj.isPrime, hP.multiProj.relevant, fun a ha => ?_⟩
      have h : a ∈ Q.comap (C : O →+* MRing ι O) := ha
      rw [hP.noTorsion] at h
      exact (Submodule.mem_bot O).mp h
    · obtain ⟨hQs, hϖQ⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hQp, -, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero
        (Function.mem_support.mp (hfin.mem_toFinset.mp hQs))
      refine ⟨hQp, hrel, fun a ha => ?_⟩
      by_contra ha0
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
      rw [map_mul, map_pow] at ha
      rcases hQp.mem_or_mem ha with h | h
      · exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ h (u.isUnit.map C))
      · exact hϖQ (hQp.mem_of_pow_mem _ h)
  obtain ⟨m, hm, hmT⟩ := exists_multiHomog_not_mem_finset e _ hT
  refine ⟨m, hm, hmT P (Finset.mem_insert_self _ _), fun H hH hϖH => hmT H ?_⟩
  exact Finset.mem_insert_of_mem
    (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr (Function.mem_support.mpr hH), hϖH⟩)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def BlowUpStrictTransform.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ s : MRing ι O, s ∉ P → ∀ (e : K → ℕ) (m : MRing ι O),
    ∀ H : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ H →
      (divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) H ≠ 0 ∨
        divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) H ≠ 0) →
      divCycle P s (H.comap (liftForm (J := BlowUpIdx ι))) ≠ 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull FlagPair assocDeg assocVar)

def FlagPairJoinLeft.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (EF E'F : ChartBundle O (mseg (joinCoord x z)) N V),
    IsPull O x z E EF → IsPull O x z E' E'F → ∀ φ : FlagPair O (joinCoord x z) EF E'F,
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord z w))) N V,
      IsPull O x (joinCoord z w) E EB → IsPull O x (joinCoord z w) E' E'B →
    ∃ ψ : FlagPair O (joinCoord x (joinCoord z w)) EB E'B,
      ψ.Vs = φ.Vs ∧ ψ.gen = φ.gen ∧ ψ.gen' = φ.gen' ∧
      ψ.deg = (fun i => assocDeg (K₂ := K₂) (φ.deg i)) ∧
      ψ.deg' = (fun i => assocDeg (K₂ := K₂) (φ.deg' i)) ∧
      ψ.f = (fun i => rename (assocVar ι₂) (φ.f i)) ∧ ψ.g = (fun i => rename (assocVar ι₂) (φ.g i))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

