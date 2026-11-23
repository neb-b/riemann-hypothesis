module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemLin
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePos
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FirstWeightLeConductor
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0011
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OpBound

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemRed
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

def Lemma5aAt (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ b, MemAtG 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)
      (symP p O hk hrk F (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b))

def WordConditionAt (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ Fp : MvPolynomial (TV n' (m + 1)) (KK O),
      MemAtG 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x)
        (cPrime n' r TT.card c0 cpp cStar) Fp →
      ∀ l : List (Fin n' × (Fin (m + 1) × Fin (m + 1))), (∀ z ∈ l, z.1 ∈ TT) →
        (∀ s, (l.filter fun z => z.1 = s).length ≤ c0) →
        MemAtG (1 / 8) (3 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x)
          (cPrime n' r TT.card c0 cpp cStar) (opWord l Fp)

theorem memAt_of_wordConditionAt (C CLa : ℝ) (h5 : Lemma5aAt C CLa) (hW : WordConditionAt C CLa) : MemStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD G hG
  rw [memAt_iff]
  have hM : ∀ f ∈ Submodule.span (KK O) (Set.range fun b =>
      symP p O hk hrk F (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)),
      MemAtG 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x)
        (cPrime n' r TT.card c0 cpp cStar) f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact h5 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD b
    | zero => exact memAtG_zero _ _ _ _ _ _ _ _ _ _ _
    | add y z _ _ hy hz => exact memAtG_add _ _ _ _ _ _ _ _ _ _ _ hy hz
    | smul c y _ hy => exact memAtG_smul _ _ _ _ _ _ _ _ _ _ _ c hy
  unfold OpCl at hG
  induction hG using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, l, h1, h2, rfl⟩ := hy
    exact hW p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD f (hM f hf)
      l h1 h2
  | zero => exact memAtG_zero _ _ _ _ _ _ _ _ _ _ _
  | add y z _ _ hy hz => exact memAtG_add _ _ _ _ _ _ _ _ _ _ _ hy hz
  | smul c y _ hy => exact memAtG_smul _ _ _ _ _ _ _ _ _ _ _ c hy

def Lemma5aTheoremII (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → Lemma5aAt C CLa

def RestWord (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → WordConditionAt C CLa

theorem memCondition_of_theoremII (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h5 : Lemma5aTheoremII D CLa Ck Crk Cdeg)
    (hW : RestWord D CLa Ck Crk Cdeg) : RestMEM D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨C₁, h1, h5'⟩ := h5 hA
  obtain ⟨C₂, _, hW'⟩ := hW hA
  refine ⟨max C₁ C₂, lt_max_of_lt_left h1, fun C hC => ?_⟩
  exact memAt_of_wordConditionAt C CLa (h5' C (le_trans (le_max_left _ _) hC)) (hW' C (le_trans (le_max_right _ _) hC))

end Formalism.MainNotions.TestSideWords
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.OperatorWeightBoundHolds
section
noncomputable section

namespace Formalism.MainNotions.TestSideWords

open Formalism.GradedWeylDivisibility

private theorem initMinor_comp_perm_eq_sign_mul {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (σ : Equiv.Perm (Fin s)) :
    PI.RW.initMinor R (I ∘ σ) hs =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Fin r × Fin n) R)) * PI.RW.initMinor R I hs := by
  unfold PI.RW.initMinor
  rw [← Matrix.det_permute σ]
  rfl

private theorem initMinor_eq_zero_of_not_injective {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (hI : ¬ Function.Injective I) : PI.RW.initMinor R I hs = 0 := by
  unfold PI.RW.initMinor
  simp only [Function.Injective, not_forall] at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  exact Matrix.det_zero_of_row_eq (Ne.symm (Ne.symm hne)) (by
    funext q
    simp [hij])

private theorem initMinor_eq_sign_sort_mul {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (hI : Function.Injective I) :
    PI.RW.initMinor R I hs =
      ((((Equiv.Perm.sign (Tuple.sort I) : ℤˣ) : ℤ) : MvPolynomial (Fin r × Fin n) R)) *
        PI.RW.initMinor R (I ∘ Tuple.sort I) hs := by
  rw [initMinor_comp_perm_eq_sign_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem bideterminant_span_holds : PI.RW.BideterminantSpan := by
  intro R _ _ k n ν
  rw [show PI.RW.dualWeyl R k n ν = Formalism.GradedWeylDivisibility.dualWeyl R k n ν from rfl,
    Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R k n ν]
  refine Submodule.span_le.mpr ?_
  rintro f ⟨K, sz, hsz, I, hν, rfl⟩
  by_cases hinj : ∀ i, Function.Injective (I i)
  · have hb : Formalism.GradedWeylDivisibility.bideterminant R sz hsz I =
        (∏ i, ((((Equiv.Perm.sign (Tuple.sort (I i)) : ℤˣ) : ℤ) : MvPolynomial (Fin k × Fin n) R))) *
          PI.RW.bideterminant R sz hsz (fun i => I i ∘ Tuple.sort (I i)) := by
      show (∏ i, PI.RW.initMinor R (I i) (hsz i)) = _
      unfold PI.RW.bideterminant
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => initMinor_eq_sign_sort_mul (I i) (hsz i) (hinj i))
    rw [hb, ← Int.cast_prod, ← zsmul_eq_mul]
    have hJ : ∀ i, StrictMono (I i ∘ Tuple.sort (I i)) := fun i =>
      (Tuple.monotone_sort (I i)).strictMono_of_injective ((hinj i).comp (Equiv.injective _))
    refine zsmul_mem (Submodule.subset_span ?_) _
    exact ⟨K, sz, hsz, fun i => I i ∘ Tuple.sort (I i), hν, hJ, rfl⟩
  · push_neg at hinj
    obtain ⟨i, hi⟩ := hinj
    have h0 : Formalism.GradedWeylDivisibility.bideterminant R sz hsz I = 0 := by
      show (∏ i, PI.RW.initMinor R (I i) (hsz i)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (initMinor_eq_zero_of_not_injective (I i) (hsz i) hi)
    rw [h0]
    exact Submodule.zero_mem _

theorem dual_weyl_weights_bounded : Formalism.MainNotions.TestSideCounting.RestWt := rowWtSpan_of bidetMem bideterminant_span_holds

theorem letter_operators_holds : Formalism.MainNotions.TestSideCounting.RestTheta := row_letter_rule

theorem onePos_of_OB (hOB : Formalism.MainNotions.TestSideCounting.OpBound) : Formalism.MainNotions.TestSideCounting.OnePos :=
  Formalism.MainNotions.TestSideCounting.onePos_of_opBound hOB letter_operators_holds dual_weyl_weights_bounded

theorem tensor_operators_of_one_position (h : Formalism.MainNotions.TestSideCounting.OnePos) : Formalism.MainNotions.TestSideCounting.TenOp :=
  adjointTensorOfSingle_valid Formalism.L2.G.Model.TS.Top.fockRBlock h

theorem tenOp_of_OB (hOB : Formalism.MainNotions.TestSideCounting.OpBound) : Formalism.MainNotions.TestSideCounting.TenOp := tensor_operators_of_one_position (onePos_of_OB hOB)

theorem operator_weight_bound_holds : Formalism.MainNotions.TestSideCounting.OpBound := operator_words_bound

theorem tensor_operators_holds : Formalism.MainNotions.TestSideCounting.TenOp := tenOp_of_OB operator_weight_bound_holds

end Formalism.MainNotions.TestSideWords
end
end

