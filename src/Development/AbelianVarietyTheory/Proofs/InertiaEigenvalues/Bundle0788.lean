module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

noncomputable section
open MvPolynomial

namespace GlobalTheory.FockSubstComm

variable {D : D7} {m n : ℕ}

def rowMat (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  if (i : ℕ) < p τ then ((g τ)⁻¹).val else ((g τ).val)ᵀ

theorem fockSubst_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (v : FVar D m n) :
    fockSubst p g (X v) = ∑ b, C (rowMat p g v.1 v.2.1 v.2.2 b) * X (v.1, v.2.1, b) := by
  rw [fockSubst, aeval_X, rowMat]
  split_ifs <;> simp

open Classical in
theorem pderiv_fockSubst_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (b : Fin n)
    (u : FVar D m n) :
    pderiv (τ, i, b) (fockSubst p g (X u)) = if u.1 = τ ∧ u.2.1 = i then C (rowMat p g τ i u.2.2 b) else 0 := by
  rw [fockSubst_X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Derivation.leibniz, pderiv_C, smul_zero, add_zero, pderiv_X, smul_eq_mul]
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [Finset.sum_eq_single b]
    · simp [Pi.single_apply]
    · intro c _ hc; simp [Pi.single_apply, Prod.ext_iff, hc]
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    have : (u.1, u.2.1, c) ≠ (τ, i, b) := by
      intro e; simp [Prod.ext_iff] at e; exact h ⟨e.1, e.2.1⟩
    simp [Pi.single_apply, this]

theorem chain_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n)
    (C' : Matrix (Fin n) (Fin n) ℂ) (hC : rowMat p g τ i * C' = 1) (u : FVar D m n) :
    fockSubst p g (pderiv (τ, i, c) (X u)) = ∑ b, C' b c • pderiv (τ, i, b) (fockSubst p g (X u)) := by
  classical
  simp only [pderiv_fockSubst_X]
  rw [pderiv_X]
  by_cases h : u.1 = τ ∧ u.2.1 = i
  · simp only [if_pos h]
    have e : (∑ b, C' b c • C (rowMat p g τ i u.2.2 b) : PolF D m n) = C ((rowMat p g τ i * C') u.2.2 c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_eq_C_mul, ← map_mul, mul_comm]
    rw [e, hC]
    obtain ⟨u1, u2, u3⟩ := u
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1; subst h2
    by_cases h3 : u3 = c
    · subst h3; simp
    · have : ((u1, u2, u3) : FVar D m n) ≠ (u1, u2, c) := by simp [h3]
      simp [Pi.single_apply, this, Matrix.one_apply, h3]
  · simp only [if_neg h, smul_zero, Finset.sum_const_zero]
    have : u ≠ (τ, i, c) := by
      rintro rfl; exact h ⟨rfl, rfl⟩
    simp [Pi.single_apply, this]

theorem chain (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n)
    (C' : Matrix (Fin n) (Fin n) ℂ) (hC : rowMat p g τ i * C' = 1) (P : PolF D m n) :
    fockSubst p g (pderiv (τ, i, c) P) = ∑ b, C' b c • pderiv (τ, i, b) (fockSubst p g P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [pderiv_C]
  | add P Q hP hQ =>
    simp only [map_add (f := _), hP, hQ, smul_add, Finset.sum_add_distrib]
  | mul_X P u ih =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib]
    rw [ih, chain_X p g τ i c C' hC u, Finset.mul_sum, Finset.mul_sum]
    simp only [mul_smul_comm]

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem rai_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n) :
    (fockSubst p g).toLinearMap * raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i c =
      ∑ b, ((g τ)⁻¹).val c b • (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i b *
        (fockSubst p g).toLinearMap) := by
  refine LinearMap.ext fun P => ?_
  by_cases h : (i : ℕ) < p τ
  · simp only [raiO, sgn, h, decide_true, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [fockSubst_X, Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rowMat, h, smul_eq_C_mul, mul_assoc]
  · have hC : rowMat p g τ i * (((g τ)⁻¹).val)ᵀ = 1 := by
      rw [rowMat, if_neg h, ← Matrix.transpose_mul]
      simp
    simp only [raiO, sgn, h, decide_false, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.neg_apply, map_neg, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Derivation.coeFn_coe, Bool.false_eq_true, if_false]
    rw [chain p g τ i c _ hC, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [smul_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem low_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (l : Fin m) (c : Fin n) :
    (fockSubst p g).toLinearMap * lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l c =
      ∑ b, (g τ).val b c • (lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l b *
        (fockSubst p g).toLinearMap) := by
  refine LinearMap.ext fun P => ?_
  by_cases h : (l : ℕ) < p τ
  · have hC : rowMat p g τ l * (g τ).val = 1 := by
      rw [rowMat, if_pos h]
      simp
    simp only [lowO, sgn, h, decide_true, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe]
    rw [chain p g τ l c _ hC]
  · simp only [lowO, sgn, h, decide_false, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Bool.false_eq_true, if_false]
    rw [fockSubst_X, Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rowMat, h, smul_eq_C_mul, mul_assoc]

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem pair_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i l : Fin m) :
    Commute (fockSubst p g).toLinearMap
      (∑ j, raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i j *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l j) := by
  set σ := (fockSubst p g).toLinearMap
  set R := raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i
  set L := lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l
  have hR : ∀ c, σ * R c = ∑ b, ((g τ)⁻¹).val c b • (R b * σ) := rai_comm p g τ i
  have hL : ∀ c, σ * L c = ∑ b, (g τ).val b c • (L b * σ) := low_comm p g τ l
  have hGG : ∀ c b, ∑ j, (g τ).val c j * ((g τ)⁻¹).val j b = (1 : Matrix (Fin n) (Fin n) ℂ) c b := by
    intro c b
    rw [← Matrix.mul_apply]
    simp
  unfold Commute SemiconjBy
  calc σ * ∑ j, R j * L j
      = ∑ j, ∑ b, ∑ c, (((g τ)⁻¹).val j b * (g τ).val c j) • (R b * L c * σ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, hR, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [smul_mul_assoc, mul_assoc, hL, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [mul_smul_comm, smul_smul, ← mul_assoc]
    _ = ∑ b, ∑ c, (∑ j, (g τ).val c j * ((g τ)⁻¹).val j b) • (R b * L c * σ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = (∑ j, R j * L j) * σ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hGG, Matrix.one_apply, ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq']
        simp


open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem fockSubst_fockT (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau)
    (Y : Matrix (Fin m) (Fin m) ℂ) (P : PolF D m n) :
    fockSubst p g (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y P) =
      fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y (fockSubst p g P) := by
  have hc : Commute (fockSubst p g).toLinearMap
      (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y) := by
    unfold fockT
    refine Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun l _ => Commute.smul_right ?_ _
    rw [Finset.sum_add_distrib]
    refine Commute.add_right (pair_comm p g τ i l) (Commute.sum_right _ _ _ fun j _ => ?_)
    split_ifs
    · exact Commute.smul_right (Commute.one_right _) _
    · exact Commute.zero_right _
  have := LinearMap.congr_fun hc.eq P
  simpa only [Module.End.mul_apply, AlgHom.toLinearMap_apply] using this

end GlobalTheory.FockSubstComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonics
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.CompactHarm

open MvPolynomial

theorem pd_comm {σ : Type*} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0 := by
      intro a b
      rw [pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, hp, h]
    ring

theorem pd_X_mul {σ : Type*} [DecidableEq σ] (x u : σ) (Q : MvPolynomial σ ℂ) :
    pderiv x (X u * Q) = (if u = x then Q else 0) + X u * pderiv x Q := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : u = x
  · subst h; simp only [Pi.single_eq_same, mul_one, if_true]; ring
  · simp only [Pi.single_apply, h, if_false, mul_zero, add_zero, zero_add]

theorem dd_X_mul {σ : Type*} [DecidableEq σ] (x y u : σ) (R : MvPolynomial σ ℂ) :
    pderiv x (pderiv y (X u * R)) = (if u = y then pderiv x R else 0) + (if u = x then pderiv y R else 0) +
      X u * pderiv x (pderiv y R) := by
  rw [pd_X_mul, map_add (f := _), pd_X_mul]
  split_ifs <;> (try simp only [map_zero]) <;> ring

theorem gen {σ : Type*} [DecidableEq σ] {n : ℕ} (x y u w : Fin n → σ) (P : MvPolynomial σ ℂ)
    (hxy : ∑ j, pderiv (x j) (pderiv (y j) P) = 0)
    (hA1 : ∑ j, ∑ k, (if u k = y j then pderiv (x j) (pderiv (w k) P) else 0) = 0)
    (hA2 : ∑ j, ∑ k, (if u k = x j then pderiv (y j) (pderiv (w k) P) else 0) = 0) :
    ∑ j, pderiv (x j) (pderiv (y j) (∑ k, X (u k) * pderiv (w k) P)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, dd_X_mul]
  simp only [Finset.sum_add_distrib]
  rw [hA1, hA2, zero_add, zero_add, Finset.sum_comm]
  have : ∀ k, ∑ j, X (u k) * pderiv (x j) (pderiv (y j) (pderiv (w k) P)) = 0 := by
    intro k
    rw [← Finset.mul_sum]
    simp only [pd_comm (y _) (w k), pd_comm (x _) (w k)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hxy, map_zero, mul_zero]
  simp [this]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem fockT_single {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      ∑ j, (raiO τ (fun _ : Fin n => true) ε' i j * lowO τ (fun _ : Fin n => true) ε' l j) Q +
        (if i = l then ((n : ℂ) / 2) • Q else 0) := by
  classical
  unfold fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp only [Matrix.single_apply_same, one_smul, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
    congr 1
    split_ifs with h
    · simp only [LinearMap.smul_apply, Module.End.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_smul]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      ring
    · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk
    rw [Finset.sum_eq_zero]
    intro l' _
    simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem low_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (hi : ε' i = false)
    (hl : ε' l = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      -∑ j, pderiv (τ, i, j) (pderiv (τ, l, j) Q) := by
  have hil : i ≠ l := fun e => by rw [e, hl] at hi; exact Bool.noConfusion hi
  rw [fockT_single, if_neg hil, add_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, hi, hl]

theorem up_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = true)
    (hb : ε' b = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      ∑ j, X (τ, a, j) * pderiv (τ, b, j) Q + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

theorem dn_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = false)
    (hb : ε' b = false) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      -∑ j, pderiv (τ, a, j) (X (τ, b, j) * Q) + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem fockT_compact_harm : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (P : PolF D m n), (∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (P) = 0) → ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < p τ ↔ (b : ℕ) < p τ) → ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single a b (1 : ℂ)) P) = 0 := by
  classical
  intro D n m p P hP τ a b hab τ' i l hi hl
  have hL : ∀ (σ : D.what₂.Tau) (i l : Fin m), p σ ≤ (i : ℕ) → (l : ℕ) < p σ →
      ∑ j, pderiv (σ, i, j) (pderiv (σ, l, j) P) = 0 := by
    intro σ i l hi hl
    have := hP σ i l hi hl
    rw [low_eq σ _ i l (by simpa using hi) (by simpa using hl)] at this
    exact neg_eq_zero.1 this
  rw [low_eq τ' _ i l (by simpa using hi) (by simpa using hl), neg_eq_zero]
  let Lop : PolF D m n →ₗ[ℂ] PolF D m n :=
    ∑ j, (pderiv (τ', i, j)).toLinearMap ∘ₗ (pderiv (τ', l, j)).toLinearMap
  have hLop : ∀ Q, Lop Q = ∑ j, pderiv (τ', i, j) (pderiv (τ', l, j) Q) := by
    intro Q; simp [Lop, LinearMap.sum_apply]
  have hP0 : Lop P = 0 := by rw [hLop]; exact hL τ' i l hi hl
  have hite : ∀ (c : Prop) [Decidable c] (z : ℂ), Lop (if c then z • P else 0) = 0 := by
    intro c _ z; split_ifs <;> simp [hP0]
  rw [← hLop]
  by_cases ha : (a : ℕ) < p τ
  · have hb : (b : ℕ) < p τ := hab.1 ha
    rw [up_eq τ _ a b (by simpa using ha) (by simpa using hb), map_add (f := _), hite, add_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, a, k)) (fun k => (τ, b, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · by_cases h : τ = τ' ∧ a = l
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hL τ i b hi hb
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
  · have hb : ¬ (b : ℕ) < p τ := fun h => ha (hab.2 h)
    rw [dn_eq τ _ a b (by simpa using ha) (by simpa using hb)]
    have e : ∑ k, pderiv (τ, a, k) (X (τ, b, k) * P) =
        (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) + ∑ k, X (τ, b, k) * pderiv (τ, a, k) P := by
      simp only [pd_X_mul, Finset.sum_add_distrib]
    have hS1 : Lop (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs <;> simp [hP0]
    rw [e, map_add (f := _), map_neg, map_add (f := _), hS1, zero_add, hite, add_zero, neg_eq_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, b, k)) (fun k => (τ, a, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
    · by_cases h : τ = τ' ∧ b = i
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        simp only [pd_comm (τ, l, _) (τ, a, _)]
        exact hL τ a l (not_lt.1 ha) hl
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩

end GlobalTheory.CompactHarm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

def flipIdx (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) : ℕ :=
  ∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((m : ℕ) : 𝓞 D.host.E)})) ^ (V.rank * W.rank)

def flipScal (χW : (AE D)ˣ →* Circle) (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (x : (AE D)ˣ) : ℂ :=
  ((χW x : Circle) : ℂ)⁻¹ * ((Real.sqrt (flipIdx V W T m : ℝ) : ℝ) : ℂ)⁻¹

def IsFlipDet (V : HSp D) (e : AE D) (m : ℕ) (x : (AE D)ˣ) : Prop :=
  (x : AE D) * (e * (m : AE D) ^ V.rank + (1 - e)) = 1

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleOfAnisotropicFormHighestWeightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducible_of_anisotropic_form_highestWeight : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V), FiniteDimensional ℂ U → ∀ (J : Type) (E : J → Module.End ℂ V) (st : J → J) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (Hw : V → Prop), (∀ j, ∀ x ∈ U, E j x ∈ U) → (∀ x ∈ U, B x x = 0 → x = 0) → (∀ j x y, B (E j x) y = B x (E (st j) y)) → (∀ j, st (st j) = j) → (∀ T : Submodule ℂ V, T ≤ U → T ≠ ⊥ → (∀ j, ∀ x ∈ T, E j x ∈ T) → ∃ x ∈ T, x ≠ 0 ∧ Hw x) → (∀ x y, x ∈ U → y ∈ U → Hw x → Hw y → x ≠ 0 → ∃ c : ℂ, y = c • x) → ∀ S : Submodule ℂ V, S ≤ U → S ≠ ⊥ → (∀ j, ∀ x ∈ S, E j x ∈ S) → S = U := by
  first | exact @GlobalTheory.DownLift.abstract_irreducible_of_highestWeight | exact GlobalTheory.DownLift.abstract_irreducible_of_highestWeight | (intros; apply GlobalTheory.DownLift.abstract_irreducible_of_highestWeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpwardVectorLiftMemRangeCoefficientExtensionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardVectorLift_mem_range_coefficientExtension : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H), ∃ u : (R.HV i t).H, R.extV i t u = upVec R i t v b y := by
  first | exact @GlobalTheory.AdjRange.upVec_mem_range | exact GlobalTheory.AdjRange.upVec_mem_range | (intros; apply GlobalTheory.AdjRange.upVec_mem_range <;> assumption)
end

