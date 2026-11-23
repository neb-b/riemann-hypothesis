module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedStaircaseTensorPeriodicUniformizerPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stairElt_diag (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (e : ℕ) (J : G.Level) (X : ℕ × ℕ) :
    ∃ n : Fin (G.rank X) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X =
        diagGL fun a => ϖ ^ n a := by
  have h1 : ∀ Y : ℕ × ℕ, ∃ n : Fin (G.rank Y) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (1 : GL (Fin (G.rank Y)) k) = diagGL fun a => ϖ ^ n a := fun Y =>
    ⟨fun _ => 0, fun _ => Nat.zero_le _, Units.ext (by simp)⟩
  have h2 : ∀ j : ℕ, ∃ n : Fin (G.rank (G.m, j)) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      stair G ϖ e j = diagGL fun a => ϖ ^ n a := fun j =>
    ⟨fun a => e * (a.val + 1 - topRank G j), fun a => Nat.mul_le_mul_left _ (by
      have := topRank_add hs j; have := a.2; omega), rfl⟩
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]; exact h2 j
    · rw [Reps.elt, onColumn_apply]
      cases j with
      | zero => exact h2 0
      | succ j =>
        have : ¬ j < G.m - 2 := by omega
        simp only [dif_neg this]
        exact h1 _
  · rw [Reps.elt, onColumn, dif_neg hi]
    exact h1 _

theorem valuation_fill_sub_le (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (n : ℕ) (x : ColArgs G) (y : RowArgs G)
    (v l : Vars G) (hl : l ∈ varLat G ϖ n) (b : Edge) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    valuation k ((fill hs x y (v + l) - fill hs x y v) b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ <;> simp only [Pi.sub_apply, Matrix.sub_apply, fill] <;> split_ifs
  · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, downMap]
    split_ifs with h
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, stepPt, Matrix.add_apply, Matrix.of_apply,
        add_sub_add_left_eq_sub]
      split_ifs
      · simp only [Pi.add_apply, add_sub_cancel_left]
        exact hl ⟨j, h⟩ _
      · simp
    · simp
    · simp
  all_goals simp

end

theorem moved_stair_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s)
    (ϖ : kˣ), IsUnif ϖ → ∀ (e : ℕ) (T : G.Args → ℂ), G.IsTensor ϖ e (oppositePath G.m) T → ∀ (J : G.Level) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (v l : Vars G), l ∈ varLat G ϖ (G.m * e) →
    moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y (v + l)) =
      moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y v) := by
  intro k _ _ _ _ G hs ϖ hϖ e T hT J keep x y v l hl
  rcases Nat.eq_zero_or_pos G.m with hm | hm
  · have : l = 0 := funext fun j => absurd j.2 (by omega)
    rw [this, add_zero]
  have hd := stairElt_diag G hs ϖ e J
  generalize (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) = g at hd ⊢
  have hf := valuation_fill_sub_le G hs ϖ _ x y v l hl
  have hsum : G.moveArgs .one g (fill hs x y (v + l)) =
      G.moveArgs .one g (fill hs x y v) + G.moveArgs .one g (fill hs x y (v + l) - fill hs x y v) := by
    funext b
    simp only [Grid.moveArgs, Pi.add_apply, Pi.sub_apply, Matrix.mul_sub, Matrix.sub_mul, add_sub_cancel]
  simp only [moved, Grid.pathAct]
  rw [hsum, hT.2.2]
  intro b r
  generalize fill hs x y (v + l) - fill hs x y v = d at hf
  obtain ⟨n, -, hn⟩ := hd b.tgt
  obtain ⟨n', hn1, hn'⟩ := hd b.src
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  rw [SplitFlip.stdLat, smul_diagLat, mem_diagLat]
  intro s
  have hv : (G.moveArgs .one g d b).row r s = (ϖ : k) ^ n r * d b r s * ((ϖ : k) ^ n' s)⁻¹ := by
    have hinv : ((diagGL fun a => ϖ ^ n' a : GL (Fin (G.rank b.src)) k)⁻¹).val =
        Matrix.diagonal fun a => ((ϖ : k) ^ n' a)⁻¹ := by
      rw [Matrix.coe_units_inv]
      refine Matrix.inv_eq_right_inv ?_
      simp [Matrix.diagonal_mul_diagonal]
    simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val, hn, hn', hinv, diagGL_val,
      Matrix.diagonal_transpose, Matrix.row, Matrix.mul_diagonal, Matrix.diagonal_mul, Units.val_pow_eq_pow_val]
  have h2 := hf b r s
  rw [hv]
  simp only [map_mul, map_inv₀, map_pow, Units.val_pow_eq_pow_val, Pi.one_apply, mul_one] at h2 ⊢
  rw [mul_inv_le_iff₀ (pow_pos h0 _), ← pow_add]
  refine (mul_le_of_le_one_left' (pow_le_one' h1 _)).trans (h2.trans (pow_le_pow_right_of_le_one' h1 ?_))
  have := hn1 s
  obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le' hm
  rw [hm'] at this ⊢
  simp only [Nat.succ_eq_add_one, zero_add, Nat.add_sub_cancel] at this ⊢
  nlinarith

end GlobalTheory.UnfoldLoss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorChosenPlaceCoeffValuationLossLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.UnfoldLoss.MovedChosen

section Local

variable {k : Type} [Field k] {G : Grid k}

theorem gdet_stair (hs : 1 ≤ G.s) (ϖ : kˣ) (e j : ℕ) :
    ∃ a : ℕ, gdet (stair G ϖ e j) = ϖ ^ a ∧ a ≤ G.rank (G.m, j) * (e * G.m) := by
  refine ⟨∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j), ?_, ?_⟩
  · rw [stair, gdet, det_diagGL, Finset.prod_pow_eq_pow_sum]
  · calc ∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j) ≤ ∑ _a : Fin (G.rank (G.m, j)), e * G.m :=
          Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (by have := topRank_add hs j; have := a.2; omega)
      _ = _ := by simp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gdet_elt (hs : 1 ≤ G.s) (J : G.Level) (ϖ : kˣ) (e : ℕ) (X : ℕ × ℕ) :
    ∃ a : ℕ, gdet ((Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X) = ϖ ^ a ∧
      a ≤ G.rank X * (e * G.m) := by
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]
      exact gdet_stair hs ϖ e j
    · cases j with
      | zero =>
        rw [Reps.elt, onColumn_apply]
        exact gdet_stair hs ϖ e 0
      | succ i =>
        refine ⟨0, ?_, Nat.zero_le _⟩
        rw [Reps.elt, onColumn_apply]
        simp [show ¬ i < G.m - 2 by omega]
  · refine ⟨0, ?_, Nat.zero_le _⟩
    simp [Reps.elt, onColumn, hi]

theorem apow_half {ϖ : kˣ} (hϖ : IsUnif ϖ) (a n : ℕ) :
    apow (ϖ ^ a)⁻¹ ((n : ℂ) / 2) = ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (a * n) := by
  rw [apow_inv, apow_pow, hϖ.apow_eq, neg_neg, mul_comm a n, pow_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_mul_nat]
  push_cast
  congr 1
  ring

end Local

section Val

variable {D : D7}

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  refine Or.inr ?_
  have h1 := hy.resolve_left h0
  have h2 := hy'.resolve_left h0'
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

theorem lossLe_list_prod {w : PlL D} {ι : Type} (f : ι → ℂ) (a : ℝ) (l : List ι) (h : ∀ b ∈ l, LossLe w (f b) a) :
    LossLe w (l.map f).prod (l.length * a) := by
  induction l with
  | nil => exact ⟨1, by simp, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (lossLe_mul (h b (by simp)) (ih fun c hc => h c (by simp [hc]))).mono (le_of_eq ?_)
    simp only [List.length_cons]
    push_cast
    ring

theorem lossLe_sqrt {w : PlL D} {q : ℕ} (hq : q ≠ 0) (hs : ((Real.sqrt q : ℝ) : ℂ) ∈ Set.range D.what₂.embLL) (n n' : ℕ) :
    LossLe w (((Real.sqrt q : ℝ) : ℂ) ^ n * (((Real.sqrt q : ℝ) : ℂ) ^ n')⁻¹) (n' * (vw w (q : D.what₂.LL) : ℝ) / 2) := by
  obtain ⟨y, hy⟩ := hs
  have h2 : y ^ 2 = (q : D.what₂.LL) := D.what₂.embLL.injective (by
    rw [map_pow, hy, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast])
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (q : D.what₂.LL) = 0 := by rw [← h2]; simp
    exact hq (by exact_mod_cast this)
  have hv : (vw w (q : D.what₂.LL) : ℝ) = 2 * vw w y := by
    rw [← h2, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0]
    push_cast
    ring
  have hv0 : (0 : ℝ) ≤ (vw w (q : D.what₂.LL) : ℝ) := by exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w q
  refine ⟨y ^ n * (y ^ n')⁻¹, by rw [map_mul, map_inv₀, map_pow, map_pow, hy], Or.inr ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hy0) (inv_ne_zero (pow_ne_zero _ hy0)), Formalism.DivisionValues.ValuationRepresentative.vw_inv,
    ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, hv]
  rw [hv] at hv0
  have : (0 : ℝ) ≤ (n : ℝ) * vw w y := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  push_cast
  linarith

theorem rank_le {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (P : Pl D.host.E) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (locGrid G t P).rank (i, j) ≤ bigN D := by
  have h1 := Nat.mul_le_mul_right D.R.t hj
  have h2 := Nat.mul_le_mul_right (sLen D) hi
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
  nlinarith

end Val

theorem moved_loss : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∈ ch.G.pl.W0 → ∀ (w : PlL D) (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z)
      (c + (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) * (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β hβ P hW w c _ hT z
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := Test.pde_ne_q hS
  have hc' : ∀ Q ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal :=
    GlobalTheory.RowTest.guard_of_qGuard hS.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hTT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc' P.2
  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc').1 P.1 P.2).square 0 hm 0 hm).cond
  haveI := (isUnitVol_unitVol P.1).1
  set e := cosExp ch.G P with he
  have hdep : depthAt ch.G P = e := by
    obtain ⟨v, hv, hvP⟩ := Finset.mem_image.1 hW
    have := depthAt_w ch.G hv
    rw [he, ← hvP, this.1, this.2]
  rw [hdep] at hTT
  have hkeep : keepAt ch.G P = false := by simp [keepAt, hW]
  have hO := oneCoset one_le_sLen (psiAt ch.W P.1) (unitVol P.1) (givenLevel ch.G t P) (Tflip ch.W ch.S.B t Φ P) (unifAt P.1) e
    D.R.m_even (isUnif_unifAt P.1) hcond hTT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO ch.G t P hj)
  have hb : β P ∈ unfSupport (psiAt ch.W P.1) (unitVol P.1) false
      (Reps.through one_le_sLen (givenLevel ch.G t P) (stair (locGrid ch.G t P) (unifAt P.1) e)) (Tflip ch.W ch.S.B t Φ P) := by
    have := hβ P
    rw [hkeep] at this
    exact this
  have hβ' := funext (hO _ hb)
  have hdet : ∀ X, ∃ a : ℕ, gdet ((repsAt ch.G t P).elt (β P) X) = unifAt P.1 ^ a ∧
      a ≤ (locGrid ch.G t P).rank X * (e * D.R.m) := fun X => by
    rw [hβ']
    exact gdet_elt (G := locGrid ch.G t P) one_le_sLen _ _ _ X
  generalize (repsAt ch.G t P).elt (β P) = g at hdet ⊢
  have hq := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P.1
  have hsq : ((Real.sqrt (resCard (Kw (P : Pl D.host.E)) : ℕ) : ℝ) : ℂ) ∈ Set.range D.what₂.embLL := by
    rw [ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
    exact hF.sqrt P.1 (Or.inr ⟨t, P.2⟩)
  set v : ℝ := (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hv
  have hv0 : 0 ≤ v := by rw [hv]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
  rw [hkeep, moved_false]
  have hP := lossLe_list_prod (w := w) (fun b : Edge => apow (gdet (g b.src))⁻¹ (((locGrid ch.G t P).rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-((locGrid ch.G t P).rank b.src : ℂ) / 2))
      ((bigN D * (e * D.R.m) * bigN D : ℕ) * v / 2) (oppositePath (locGrid ch.G t P).m) (fun b hb => by
    have hr : (locGrid ch.G t P).rank b.src ≤ bigN D ∧ (locGrid ch.G t P).rank b.tgt ≤ bigN D := by
      change b ∈ oppositePath D.R.m at hb
      simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
      rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
      · exact ⟨rank_le _ _ _ hi.le le_rfl, rank_le _ _ _ hi le_rfl⟩
      · exact ⟨rank_le _ _ _ le_rfl hj, rank_le _ _ _ le_rfl hj.le⟩
    obtain ⟨a, ha, -⟩ := hdet b.src
    obtain ⟨a', ha', hle⟩ := hdet b.tgt
    rw [ha, ha', neg_div, apow_neg, apow_half (isUnif_unifAt P.1), apow_half (isUnif_unifAt P.1)]
    refine (lossLe_sqrt hq hsq _ _).mono ?_
    have h1 : a' * (locGrid ch.G t P).rank b.src ≤ bigN D * (e * D.R.m) * bigN D :=
      Nat.mul_le_mul (hle.trans (Nat.mul_le_mul_right _ hr.2)) hr.1
    have h2 : ((a' * (locGrid ch.G t P).rank b.src : ℕ) : ℝ) ≤ (bigN D * (e * D.R.m) * bigN D : ℕ) := by exact_mod_cast h1
    have h3 := mul_le_mul_of_nonneg_right h2 hv0
    rw [← hv]
    linarith)
  refine (lossLe_mul hP (hT _)).mono (le_of_eq ?_)
  have hlen : (oppositePath (locGrid ch.G t P).m).length = 2 * D.R.m := by
    change (oppositePath D.R.m).length = _
    simp [oppositePath]; ring
  rw [hlen]
  push_cast
  ring

end GlobalTheory.UnfoldLoss.MovedChosen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuaScalarMultiplesReferenceTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.BotScal

open GlobalTheory.KappaArith (AwayIm)

variable {D : D7} {T : Type} {Lc : LevCh D T}

theorem xi_awayIm_of_infPart {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ) (u : (AE D)ˣ)
    (hu : infPart D (u : AE D) = 1) : AwayIm D m ((Lc.xi t u : Circle) : ℂ) := by
  obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2 (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3)
    (Lc.xi t) (Lc.xiH t) (hL.xi t)
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom u)
  rw [hprod u hu S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact AwayIm.prod _ _ fun P _ => GlobalTheory.KappaArith.awayIm_val hL hx m P (Formalism.L2.Host.atFin P (k P))

theorem xi_awayIm {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ) (u : (AE D)ˣ) :
    AwayIm D m ((Lc.xi t u : Circle) : ℂ) := by
  obtain ⟨v, hv1, hv2, hv3⟩ := GlobalTheory.TameFinitePart.exists_lift D (Units.map (finPart D).toMonoidHom u)
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  have h1 : Lc.xi t (u * v⁻¹) = 1 := GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (by
    rw [Units.val_mul, map_mul, hv3]
    exact Units.mul_inv (Units.map (finPart D).toMonoidHom u))
  have h2 : Lc.xi t u = Lc.xi t v := by
    have := congrArg (· * Lc.xi t v) h1
    simpa [map_mul, map_inv] using this
  rw [h2]
  exact xi_awayIm_of_infPart hL hx m v hv1

end GlobalTheory.BotScal

namespace GlobalTheory.BotScal

theorem moved_vacua_scal : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (Y : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    ∃ r r' : T → ℂ, (∀ t, r t ≠ 0 ∧ r' t ≠ 0) ∧ (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω μ₀ (g, h) Y.vac) ∧
      (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' μ₀ (g', h) Y.vac') ∧
      ∀ t, ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ r' t / r t = D.what₂.embLL ζ * (r' μ₀ / r μ₀) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW Y hY g hg g' hg' h hh
  have hI := hY.2.2.2.2.2.2.2
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (GlobalTheory.Grid.neg A) ((GlobalTheory.Grid.ofSgn true A).symm g)
  obtain ⟨x', hx'⟩ := GlobalTheory.RecDict.exists_isDetRoot D A' g'
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D WW h
  have hvac : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW Y.vac := hI.isVac.2.theta
  have hvac' : IsThetaFunO W.ψ A' WW Y.vac' := hI.isVac'.2.theta
  have e := fun t => GlobalTheory.WeilChange.weilData_differ_by_splitFac D W.ψ (GlobalTheory.Grid.neg A) WW _ _ _ _ _ _ (hI.weil μ₀) (hI.weil t) _ h x y hx hy _ hvac
  have e' := fun t => GlobalTheory.WeilChange.weilData_differ_by_splitFac D W.ψ A' WW _ _ _ _ _ _ (hI.weil' μ₀) (hI.weil' t) g' h x' y hx' hy _ hvac'
  let a : T → (AE D)ˣ →* Circle := fun t => Lc.mu t (↑j + 1) * Lc.eta ^ (rankV D ↑i ↑j % 2)
  let b : (AE D)ˣ →* Circle := G.ch.chi (D.R.m - ↑i) * Lc.eta ^ (rankV D ↑i ↑j % 2)
  refine ⟨fun t => ((splitFacO b (b / a t) x y : Circle) : ℂ) * ((splitFacO b (b / a μ₀) x y : Circle) : ℂ)⁻¹,
    fun t => ((splitFacO (a t) (a t / b) x' y : Circle) : ℂ) * ((splitFacO (a μ₀) (a μ₀ / b) x' y : Circle) : ℂ)⁻¹,
    fun t => ⟨?_, ?_⟩, fun t => ?_, fun t => ?_, ?_⟩
  rotate_left 2
  · have := e t
    simp only [GlobalTheory.Grid.WRep.toSgn, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MonoidHom.id_apply] at this
    exact this
  · exact e' t
  · intro t
    have hb : Lc.xi μ₀ = 1 := MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi μ₀))
    obtain ⟨ζ, hζ, hζe⟩ := xi_awayIm hL (hN.chars.xi t) (Qn G t) (x'⁻¹ * y * x⁻¹)
    refine ⟨ζ, hζ, ?_⟩
    rw [hζe]
    simp only [splitFacO, a, b, LevCh.mu, Formalism.IndefR.Lift.tup, hb, Circle.coe_mul, Circle.coe_inv, MonoidHom.div_apply,
      MonoidHom.mul_apply, MonoidHom.one_apply, map_mul, map_inv, Circle.coe_div, mul_one]
    field_simp [Circle.coe_ne_zero]
  · exact mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))
  · exact mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))

end GlobalTheory.BotScal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogeny
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu WithConv

namespace GlobalTheory.Dieu

theorem hom_eq_zero_of_pow_smul_eq_zero {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k]
    {G H : PDivGroup p k} (m : ℕ) {f : G ⟶ H} (e : (p : ℤ_[p]) ^ m • f = 0) : f = 0 := by
  induction m generalizing f with
  | zero => simpa using e
  | succ m ih =>
    refine ih ?_
    refine eq_zero_of_prime_smul_eq_zero ?_
    rw [← mul_smul, ← pow_succ']
    exact e

theorem exists_comp_eq_of_kerIdeal_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q H : PDivGroup p k) (m : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (f : G ⟶ H),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → q' ≫ q = (p : ℤ_[p]) ^ m • 𝟙 Q →
    kerIdeal (f.app m) ≤ kerIdeal (q.app m) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ k _ _ G Q H m q q' f h1 h2 hk

  have hq : kerIdeal (q.app m) ≤ RingHom.ker (q'.app m : G.A m →ₐ[k] Q.A m) := by
    refine (kerIdeal_le_ker_iff (q.app m) _).2 fun c => ?_
    have e := congrArg (fun x => Hom.conv x m) h2
    simp only [pow_smul_conv] at e
    have e2 := DFunLike.congr_fun (congrArg ofConv (congrArg toPts e)) c
    rw [map_one] at e2
    refine e2.trans ?_
    rfl
  have hf := (kerIdeal_le_ker_iff (f.app m) _).1 (hk.trans hq)
  have hc : Hom.conv (q' ≫ f) m = 1 := by
    refine toPts_injective (ofConv_injective (AlgHom.ext fun c => ?_))
    rw [map_one]
    refine (hf c).trans ?_
    rfl
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one p k Q H m (q' ≫ f) hc
  refine ⟨g, sub_eq_zero.1 (hom_eq_zero_of_pow_smul_eq_zero m ?_)⟩
  rw [smul_sub, ← Linear.comp_smul, ← hg, ← Category.assoc, h1, Linear.smul_comp,
    Category.id_comp, sub_self]

end GlobalTheory.Dieu
end

