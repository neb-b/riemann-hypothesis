module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnisotropicCoreWittFrame
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrameOfDec

theorem form_mulVec {D : D7} {n m : ℕ} (A : Matrix (Fin n) (Fin m) D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E)
    (w : Fin m → D.host.E) : star (A *ᵥ w) ⬝ᵥ (G *ᵥ (A *ᵥ w)) = star w ⬝ᵥ ((Aᴴ * G * A) *ᵥ w) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem isWittFrame_of_hypDec (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (h : IsAniso T₀) :
    IsWittFrame D.sp.cm.sig T.gram d.e d.e' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cT_sig]; exact d.ee
  · rw [cT_sig]; exact d.e'e'
  · rw [cT_sig]
    have h1 := congrArg Matrix.conjTranspose d.e'e
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h1
    exact h1
  · intro z hX hY hz
    rw [cT_sig] at hX hY
    have hqY : d.qY *ᵥ z = 0 := hX
    have hqX : d.qX *ᵥ z = 0 := hY
    have hz0 : z = d.i₀ *ᵥ (d.q0 *ᵥ z) := by
      have := congrArg (fun M => M *ᵥ z) d.sum_eq_one_rat
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hqX, hqY,
        Matrix.mulVec_zero, zero_add, add_zero] at this
      exact this.symm
    obtain ⟨z₀, hz₀⟩ : ∃ w, w = d.q0 *ᵥ z := ⟨_, rfl⟩
    rw [← hz₀] at hz0
    by_cases h0 : z₀ = 0
    · rw [hz0, h0, Matrix.mulVec_zero]
    exfalso
    have e1 : hE D.sp.cm.sig T.gram z z = star z ⬝ᵥ (T.gram *ᵥ z) := by
      simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc]; rfl
    have hzz : star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) = 0 := by
      rw [← d.iso, ← form_mulVec, ← hz0, ← e1, hz]
    let C : Matrix (Fin T₀.rank) (Fin 1) D.host.E := Matrix.of fun i _ => z₀ i
    apply h 1 C
    refine ⟨Nat.one_pos, ?_, ?_⟩
    · change LinearIndependent D.host.E (fun _ : Fin 1 => z₀)
      exact linearIndependent_unique_iff.2 h0
    · rw [cT_sig]
      ext a b
      fin_cases a; fin_cases b
      have : (Cᴴ * T₀.gram * C) 0 0 = star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, Matrix.of_apply, dotProduct, Matrix.mulVec,
          Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      simpa using this.trans hzz

end GlobalTheory.WittFrameOfDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AntiOfStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.HdNc

theorem anti_of_step {r : ℕ} (f : Fin r → ℝ) (h : ∀ (i : Fin r) (hi : i.1 + 1 < r), f ⟨i.1 + 1, hi⟩ < f i) :
    ∀ a b : Fin r, a ≤ b → f b ≤ f a := by
  have key : ∀ (d a : ℕ) (ha : a + d < r), f ⟨a + d, ha⟩ ≤ f ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => intro a ha; exact le_rfl
    | succ d ih =>
      intro a ha
      have h1 := h ⟨a + d, by omega⟩ (by simp only []; omega)
      have h2 := ih a (by omega)
      have e : (⟨(⟨a + d, by omega⟩ : Fin r).1 + 1, by simp only []; omega⟩ : Fin r) = ⟨a + (d + 1), ha⟩ := by
        ext; simp only []; omega
      rw [e] at h1
      linarith
  intro a b hab
  have hd := key (b.1 - a.1) a.1 (by omega)
  have e1 : (⟨a.1 + (b.1 - a.1), by omega⟩ : Fin r) = b := by ext; simp only []; omega
  rw [e1] at hd
  exact hd

theorem lamS_node (R : Ranks) (P : HCParam R) (j : ℕ) (hj : j < R.m) (hi : R.k - 1 + j < R.r) :
    lamS R P ⟨R.k - 1 + j, hi⟩ = -(((P.b ⟨j, hj⟩ : ℚ)) : ℝ) := by
  unfold lamS
  rw [dite_eq_right (by simp only []; omega)]
  have e : R.k - 1 + j - (R.k - 1) = j := by omega
  simp only [e, dif_pos hj]

theorem node_of_sign (R : Ranks) (a b : Fin R.r) (hab : a < b) (hne : epsS R a ≠ epsS R b) : R.k ≤ b.1 := by
  by_contra hb
  push_neg at hb
  apply hne
  have ha : a.1 < R.k - 1 := by
    have : a.1 < b.1 := hab
    omega
  unfold epsS
  rw [if_pos ha]
  by_cases h1 : b.1 < R.k - 1
  · rw [if_pos h1]
  · rw [if_neg h1]
    have : b.1 - (R.k - 1) = 0 := by omega
    simp [this]

theorem gap_lt {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (a b : Fin D.R.r) (hab : a < b) (hne : epsS D.R a ≠ epsS D.R b) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤ lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b := by
  have hkb := node_of_sign D.R a b hab hne
  have hbr : b.1 < D.R.r := b.2
  have hm2 := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hgap := GlobalTheory.Core.Rk.HdGap.gap_of H τ (b.1 - D.R.k) (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlam, -, -, hCl⟩ := H
  have hstep : ∀ (i : Fin D.R.r) (hi : i.1 + 1 < D.R.r),
      lamS D.R (D.hc τ) ⟨i.1 + 1, hi⟩ < lamS D.R (D.hc τ) i := by
    intro i hi
    have := hlam τ i hi
    have h0 : (0 : ℝ) ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
    linarith
  set j := b.1 - D.R.k with hj
  have hj1 : j + 1 < D.R.m := by omega
  have e1 : b = ⟨D.R.k - 1 + (j + 1), by omega⟩ := by ext; simp only []; omega
  have hc : (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) ≤ b := by
    rw [Fin.le_def]; simp only []; omega
  have hac : a ≤ (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) := by
    rw [Fin.le_def]; simp only []; have : a.1 < b.1 := hab; omega
  have h1 := anti_of_step _ hstep _ _ hac
  have h2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj1⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := hgap
  rw [lamS_node D.R (D.hc τ) j (by omega) (by omega)] at h1
  rw [e1, lamS_node D.R (D.hc τ) (j + 1) hj1 (by omega)]
  linarith

theorem hd_nc : ∃ Cl₀ : ℝ, ∀ (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ), Cl₀ ≤ Cl → HD D L C' Cl Cg cb Cu cT CT →
    ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  refine ⟨1801, fun D L C' Cl Cg cb Cu cT CT hCl H X => ?_⟩
  have HL := H.2.2.1
  obtain ⟨hS, hr⟩ := GlobalTheory.Core.Rk.HdGap.scale_of hCl HL
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast (show 1 ≤ D.R.r by omega)
  have h4 : 100 * (D.R.r : ℝ) ^ 4 ≤ 1801 * (D.R.r : ℝ) ^ 19 := by
    have : (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hr1 (by norm_num)
    have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4 := by positivity
    linarith
  have key : ∀ (τ : D.what₂.Tau) (a b : Fin D.R.r), epsS D.R a ≠ epsS D.R b →
      100 * (D.R.r : ℝ) ^ 4 ≤ |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b| := by
    intro τ a b hne
    have hp : (0 : ℝ) ≤ 100 * (D.R.r : ℝ) ^ 4 := by positivity
    rcases lt_trichotomy a b with h | h | h
    · have := gap_lt HL τ a b h hne
      rw [abs_of_nonneg (by linarith)]
      linarith
    · exact absurd (by rw [h]) hne
    · have := gap_lt HL τ b a h (Ne.symm hne)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  intro v a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq]
  exact key _ _ _ hab

end GlobalTheory.Core.Rk.HdNc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanMajorantStabilisersConjugate
section
noncomputable section

namespace GlobalTheory.MajorantConj

section General

open scoped Matrix

abbrev sgnDiag (A : Type) [CommRing A] {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) A :=
  Matrix.diagonal fun i => if ε i then 1 else -1

theorem re_form {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (sgnDiag ℂ ε *ᵥ x)).re = ∑ i, (if ε i then 1 else -1) * Complex.normSq (x i) := by
  simp only [sgnDiag, Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Complex.mul_re, Complex.normSq_apply] <;> ring

theorem card_neg_le {n : ℕ} (ε ε' : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * sgnDiag ℂ ε * M = sgnDiag ℂ ε') :
    Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false} := by
  have key : ∀ x : Fin n → ℂ,
      star x ⬝ᵥ (sgnDiag ℂ ε' *ᵥ x) = star (M *ᵥ x) ⬝ᵥ (sgnDiag ℂ ε *ᵥ (M *ᵥ x)) := by
    intro x
    rw [← h, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  let T := (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // ε i = false} → Fin n)) ∘ₗ M.mulVecLin ∘ₗ
    (Function.ExtendByZero.linearMap ℂ ℂ (Subtype.val : {i // ε' i = false} → Fin n))
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨x, hx⟩ : ∃ x : Fin n → ℂ, x = Function.extend Subtype.val y 0 := ⟨_, rfl⟩
    have hxt : ∀ i, ε' i = true → x i = 0 := by
      intro i hi
      rw [hx, Function.extend_apply']
      · rfl
      · rintro ⟨j, rfl⟩
        rw [j.2] at hi
        exact Bool.false_ne_true hi
    have hxf : ∀ j : {i // ε' i = false}, x j.1 = y j := fun j => by
      rw [hx]
      exact Subtype.val_injective.extend_apply _ _ _
    have hv : ∀ j : {i // ε i = false}, (M *ᵥ x) j.1 = 0 := fun j => by
      have := congrFun hy j
      rw [hx]
      exact this
    have h1 := congrArg Complex.re (key x)
    rw [re_form, re_form] at h1
    have hL : ∀ i, (if ε' i then (1 : ℝ) else -1) * Complex.normSq (x i) = -Complex.normSq (x i) := by
      intro i
      cases hi : ε' i
      · simp
      · simp [hxt i hi]
    have hR : 0 ≤ ∑ i, (if ε i then (1 : ℝ) else -1) * Complex.normSq ((M *ᵥ x) i) := by
      apply Finset.sum_nonneg
      intro i _
      cases hi : ε i
      · simp [hv ⟨i, hi⟩]
      · simp [Complex.normSq_nonneg]
    simp only [hL, Finset.sum_neg_distrib] at h1
    have hz : ∑ i, Complex.normSq (x i) = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)] at hz
    funext j
    rw [← hxf j]
    exact Complex.normSq_eq_zero.mp (hz j.1 (Finset.mem_univ _))
  have := LinearMap.finrank_le_finrank_of_injective hT
  simpa [Module.finrank_fintype_fun_eq_card] using this

theorem exists_perm {n : ℕ} (ε ε' : Fin n → Bool)
    (h : Fintype.card {i // ε' i = false} = Fintype.card {i // ε i = false}) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, ε' (π i) = ε i := by
  classical
  have e0 : {i // ε i = false} ≃ {i // ε' i = false} := Fintype.equivOfCardEq h.symm
  have e1 : {i // ¬ε i = false} ≃ {i // ¬ε' i = false} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h])
  refine ⟨(Equiv.sumCompl fun i => ε i = false).symm.trans
    ((e0.sumCongr e1).trans (Equiv.sumCompl fun i => ε' i = false)), fun i => ?_⟩
  by_cases hi : ε i = false
  · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun j => ε j = false) hi, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    rw [hi]
    exact (e0 ⟨i, hi⟩).2
  · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun j => ε j = false) hi, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    have := (e1 ⟨i, hi⟩).2
    simp only [Bool.not_eq_false] at hi this
    rw [hi, this]

variable {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}

theorem cT_mul (M N : Matrix (Fin n) (Fin n) A) : Formalism.UG.cT s (M * N) = Formalism.UG.cT s N * Formalism.UG.cT s M := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one : Formalism.UG.cT s (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  unfold Formalism.UG.cT
  rw [Matrix.map_one s (map_zero s) (map_one s), Matrix.transpose_one]

theorem congr_inv {J D : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (h : Formalism.UG.cT s b.1 * J * b.1 = D) :
    Formalism.UG.cT s (b⁻¹).1 * D * (b⁻¹).1 = J := by
  rw [← h]
  have h1 : Formalism.UG.cT s (b⁻¹).1 * Formalism.UG.cT s b.1 = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  calc Formalism.UG.cT s (b⁻¹).1 * (Formalism.UG.cT s b.1 * J * b.1) * (b⁻¹).1
      = (Formalism.UG.cT s (b⁻¹).1 * Formalism.UG.cT s b.1) * J * (b.1 * (b⁻¹).1) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem congr_mul {J D D' : Matrix (Fin n) (Fin n) A} (b c : GL (Fin n) A) (h : Formalism.UG.cT s b.1 * J * b.1 = D)
    (h' : Formalism.UG.cT s c.1 * D * c.1 = D') : Formalism.UG.cT s (b * c).1 * J * (b * c).1 = D' := by
  rw [← h', ← h, Units.val_mul, cT_mul]
  simp only [Matrix.mul_assoc]

theorem card_neg_le' (φ : A →+* ℂ) (hφ : ∀ y, starRingEnd ℂ (φ y) = φ (s y)) (ε ε' : Fin n → Bool)
    (M : Matrix (Fin n) (Fin n) A) (h : Formalism.UG.cT s M * sgnDiag A ε * M = sgnDiag A ε') :
    Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false} := by
  have hc : (Formalism.UG.cT s M).map φ = (M.map φ)ᴴ := by
    ext i j
    show φ (s (M j i)) = star (φ (M j i))
    rw [← hφ]
    rfl
  have hd : ∀ e : Fin n → Bool, (sgnDiag A e).map φ = sgnDiag ℂ e := by
    intro e
    rw [sgnDiag, Matrix.diagonal_map (map_zero φ)]
    congr 1
    funext i
    split_ifs <;> simp
  have h2 := congrArg (fun X => X.map φ) h
  simp only [Matrix.map_mul, hc, hd] at h2
  exact card_neg_le ε ε' (M.map φ) h2

def permGL (π : Equiv.Perm (Fin n)) : GL (Fin n) A where
  val := (1 : Matrix (Fin n) (Fin n) A).submatrix id π
  inv := (1 : Matrix (Fin n) (Fin n) A).submatrix π id
  val_inv := by
    rw [Matrix.submatrix_mul_equiv]
    simp
  inv_val := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]

theorem permGL_diagonal (π : Equiv.Perm (Fin n)) (d : Fin n → A) :
    Formalism.UG.cT s (permGL (A := A) π).1 * Matrix.diagonal d * (permGL (A := A) π).1 = Matrix.diagonal fun i => d (π i) := by
  have hP : ((permGL (A := A) π).1).map s = (permGL (A := A) π).1 := by
    show ((1 : Matrix (Fin n) (Fin n) A).submatrix id π).map s = (1 : Matrix (Fin n) (Fin n) A).submatrix id π
    rw [← Matrix.submatrix_map, Matrix.map_one s (map_zero s) (map_one s)]
  unfold Formalism.UG.cT
  rw [hP]
  show ((1 : Matrix (Fin n) (Fin n) A).submatrix id π)ᵀ * Matrix.diagonal d *
    (1 : Matrix (Fin n) (Fin n) A).submatrix id π = _
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  split_ifs with hij
  · rw [hij]
  · rfl

theorem exists_unitary (φ : A →+* ℂ) (hφ : ∀ y, starRingEnd ℂ (φ y) = φ (s y)) {J : Matrix (Fin n) (Fin n) A}
    {ε ε' : Fin n → Bool} (b b' : GL (Fin n) A) (h : Formalism.UG.cT s b.1 * J * b.1 = sgnDiag A ε)
    (h' : Formalism.UG.cT s b'.1 * J * b'.1 = sgnDiag A ε') :
    ∃ P ∈ Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) A), b' * P * b⁻¹ ∈ Formalism.UG.UJ s J := by
  have hle : Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false} :=
    card_neg_le' s φ hφ ε ε' (b⁻¹ * b').1 (congr_mul s b⁻¹ b' (congr_inv s b h) h')
  have hge : Fintype.card {i // ε i = false} ≤ Fintype.card {i // ε' i = false} :=
    card_neg_le' s φ hφ ε' ε (b'⁻¹ * b).1 (congr_mul s b'⁻¹ b (congr_inv s b' h') h)
  obtain ⟨π, hπ⟩ := exists_perm ε ε' (le_antisymm hle hge)
  refine ⟨permGL π, ?_, ?_⟩
  · show Formalism.UG.cT s (permGL (A := A) π).1 * 1 * (permGL (A := A) π).1 = 1
    have := permGL_diagonal s π (fun _ => (1 : A))
    simpa [Matrix.diagonal_one] using this
  · show Formalism.UG.cT s (b' * permGL π * b⁻¹).1 * J * (b' * permGL π * b⁻¹).1 = J
    have h1 : Formalism.UG.cT s (b' * permGL π).1 * J * (b' * permGL π).1 = sgnDiag A ε := by
      have := congr_mul s b' (permGL π) h' (permGL_diagonal s π (fun i => if ε' i then (1 : A) else -1))
      simpa [sgnDiag, hπ] using this
    exact congr_mul s (b' * permGL π) b⁻¹ h1 (congr_inv s b h)

end General

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stabArch_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (a a' : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → IsMajorantFrame σ J a' → ∀ w : InfinitePlace F, ∃ g : GArch σ J w, ∀ k : GArch σ J w, k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a') ↔ g⁻¹ * k * g ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a) := by
  intro F E _ _ _ _ _ σ hcm n J hJ a a' ha ha' w
  obtain ⟨ε, hε⟩ := ha w
  obtain ⟨ε', hε'⟩ := ha' w
  generalize Formalism.UG.bc (compInf F E w) a = b at hε ⊢
  generalize Formalism.UG.bc (compInf F E w) a' = b' at hε' ⊢
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨P, hP, hg⟩ := exists_unitary (sigR w.Completion σ) (infEmb τ) (fun y => infEmb_sigR hcm τ y) b b' hε hε'
  have key : ∀ m : GL (Fin n) (w.Completion ⊗[F] E),
      b⁻¹ * ((b' * P * b⁻¹)⁻¹ * m * (b' * P * b⁻¹)) * b = P⁻¹ * (b'⁻¹ * m * b') * P := fun m => by group
  refine ⟨(⟨b' * P * b⁻¹, hg⟩ : HR w.Completion σ J), fun k => ?_⟩
  unfold stabArch
  first
  | (show b'⁻¹ * AdelicU.matHom w.Completion σ J k * b'⁻¹⁻¹ ∈ Formalism.UG.UJ (sigR w.Completion σ) 1 ↔
        b⁻¹ * ((b' * P * b⁻¹)⁻¹ * AdelicU.matHom w.Completion σ J k * (b' * P * b⁻¹)) * b⁻¹⁻¹ ∈
          Formalism.UG.UJ (sigR w.Completion σ) 1
     rw [inv_inv, inv_inv, key, mul_mem_cancel_right hP, mul_mem_cancel_left (inv_mem hP)])
  | (simp only [Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
     simp only [map_mul, map_inv, inv_inv]
     exact (mul_mem_cancel_right hP).symm.trans ((mul_mem_cancel_left (inv_mem hP)).symm.trans
       (by rw [← key]; exact Iff.rfl)))

end GlobalTheory.MajorantConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFunctionContinuousOnBesselGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.PhCont

variable {D : D7}

theorem psiBes_mul_embA (ψ : AddChar (AF D.host.F) ℂ) {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (o : OrthDec S₀ A L) (θ : D.host.E) (ζ : Fin L.rank → D.host.E) (n : GA D S) (a : GA D A) :
    psiBes ψ d θ (vecB o ζ) (n * embA d o a) = psiBes ψ d θ (vecB o ζ) n := by
  have hX : blockX d (n * embA d o a) = blockX d n := by
    rw [blockX, blockX, mt_mul, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclX]
  have hC : coefX d (vecB o ζ) (n * embA d o a) = coefX d (vecB o ζ) n := by
    rw [coefX, coefX, mt_mul, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, GlobalTheory.CharLaws.emb_vecB]
    simp only [Matrix.mul_assoc]
  rw [psiBes, psiBes, simpleSum, simpleSum, hX, hC]

theorem ph_continuousOn : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK)
    (y : X.B.I.Ginf), IsCharAF D.host.F ψ →
      ContinuousOn (fun g => Ph X u hK T (iotaX X h g * (y, X.xu u))) (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := by
  intro D X h u ψ A B hK T y hψ
  obtain ⟨p, hp, hpv⟩ := GlobalTheory.BesProj.exists_continuous_proj D _ _ A _ _ B.d B.o
  obtain ⟨hcont, hval⟩ := GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T
  refine continuousOn_iff_continuous_restrict.2 ?_
  show Continuous fun g : (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) => Ph X u hK T (iotaX X h g.1 * (y, X.xu u))
  have e : (fun g : (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) => Ph X u hK T (iotaX X h g.1 * (y, X.xu u))) =
      fun g => star (psiBes ψ B.d 1 (vecB B.o B.ζ) g.1) * B.colForm T.1 (X.Wu u y) (p g) := by
    funext g
    obtain ⟨g, hg⟩ := g
    obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o _).1 hg
    have hpa : p ⟨n * embA B.d B.o a, hg⟩ = a := hpv a ⟨n, hn⟩
    show Ph X u hK T (iotaX X h (n * embA B.d B.o a) * (y, X.xu u)) = _
    rw [hval n hn a y]
    show _ = star (psiBes ψ B.d 1 (vecB B.o B.ζ) (n * embA B.d B.o a)) * B.colForm T.1 (X.Wu u y) (p ⟨n * embA B.d B.o a, hg⟩)
    rw [psiBes_mul_embA]
    exact congrArg (fun a' => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) * B.colForm T.1 (X.Wu u y) a') hpa.symm
  rw [e]
  have hps : Continuous (psiBes ψ B.d 1 (vecB B.o B.ζ)) :=
    GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1 1 _
  exact (continuous_star.comp (hps.comp continuous_subtype_val)).mul ((hcont (X.Wu u y)).2.comp hp)

end GlobalTheory.Core.Mi.PhCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesTestDataOfNoncompactGapsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  first | exact @GlobalTheory.Core.Mi.seeData_of_gap | exact GlobalTheory.Core.Mi.seeData_of_gap | (intros; apply GlobalTheory.Core.Mi.seeData_of_gap <;> assumption)
end

