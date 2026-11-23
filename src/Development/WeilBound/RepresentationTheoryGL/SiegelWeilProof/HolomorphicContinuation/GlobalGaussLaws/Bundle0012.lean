module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0009

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoB
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem compFin_eq_finPart (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v z =
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem reidx_conjTranspose_mul (y : M2 n) : (reidx y)ᴴ * reidx y = reidx (yᴴ * y) := by
  simp only [reidx, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

theorem reidx_one : reidx (1 : M2 n) = 1 := by
  simp [reidx]

theorem compAt_cT_mul {θ : InfFam D} (hθ : IsInfFam θ) {m : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (τ' : D.what₂.Tau) :
    compAt θ τ' (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * M) =
      (compAt θ τ' M)ᴴ * compAt θ τ' M := by
  obtain ⟨-, hcA, -, -⟩ := _root_.GlobalTheory.StdUnn.RealComp.real_components D θ hθ
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.conjTranspose_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact hcA (M l i) τ'

theorem cT_one {m : ℕ} : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (1 : Matrix (Fin m) (Fin m) (AE D)) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT]
  · simp [Formalism.UG.cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem iota_mem_K {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι)
    (k : GR n) (hk : InK (mR k)) : ι k ∈ K D n := by
  obtain ⟨hinf0, hcA, -, -⟩ := _root_.GlobalTheory.StdUnn.RealComp.real_components D θ hθ
  obtain ⟨-, hcomp⟩ := hι
  obtain ⟨hτ, hτ', hfin⟩ := hcomp k
  rw [K, GlobalTheory.RegSch.EmbLevel.mem_levelAll_iff]
  set M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (ι k)).1 with hM
  have hMm : M = mat (ι k) := rfl
  refine ⟨fun v y => ?_, fun w => ?_⟩
  · have h1 : M.map (compFin D.host.F D.host.E v) = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      rw [compFin_eq_finPart]
      have := congrFun (congrFun hfin i) j
      simp only [Matrix.map_apply] at this
      rw [← hMm] at this
      rw [this]
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [h1, Matrix.one_mulVec]
  ·
    have key : ∀ i j, compInf D.host.F D.host.E w
        ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig) M * M) i j - (1 : Matrix (Fin (n + n)) (Fin (n + n)) (AE D)) i j) = 0 := by
      intro i j
      refine ((hinf0 _).2 ?_) w
      intro τ'
      have hc := compAt_cT_mul hθ M τ'
      have hrow : θ τ' (infPart D ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * M) i j)) =
          ((compAt θ τ' M)ᴴ * compAt θ τ' M) i j := congrFun (congrFun hc i) j
      rw [map_sub, map_sub, hrow]
      by_cases hττ : τ' = τ
      · subst hττ
        have e : compAt θ τ' M = reidx (mR k) := hτ
        rw [e, reidx_conjTranspose_mul, hk.2, reidx_one]
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.one_apply_ne h]
      · have e : compAt θ τ' M = 1 := hτ' τ' hττ
        rw [e, Matrix.conjTranspose_one, Matrix.one_mul]
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.one_apply_ne h]
    simp only [inv_one, Units.val_one, cT_one, Matrix.mul_one]
    ext i j
    have := key i j
    rw [map_sub, sub_eq_zero] at this
    simpa only [Matrix.map_apply] using this

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacD
section
noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {m n : ℕ}

def sR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem gramX_eq (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (j i : Fin n) :
    gramX ε x j i = ∑ a, (sR ε a : ℂ) * (star (x a j) * x a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, sR, map_sub, map_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases ε a <;> simp

theorem trace_eq (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, (sR ε a : ℂ) * ∑ i, ∑ j, b i j * star (x a j) * x a i := by
  have h1 : (b * gramX ε x).trace = ∑ i, ∑ j, ∑ a, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h1]
  calc ∑ i, ∑ j, ∑ a, (sR ε a : ℂ) * (b i j * star (x a j) * x a i)
      = ∑ i, ∑ a, ∑ j, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) := Finset.sum_comm
    _ = ∑ a, (sR ε a : ℂ) * ∑ i, ∑ j, b i j * star (x a j) * x a i := by
        simp only [Finset.mul_sum]

theorem secN_one (ε : Fin m → Bool) (c t : ℝ) (hc : 0 < c) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    secN ε c t (1 : PX m n) b =
      ∏ a : Fin m, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det := by
  have hpt : ∀ x : Fin m → Fin n → ℂ,
      evX (1 : PX m n) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
        = ∏ a, rowF c (t * sR ε a) b (x a) := by
    intro x
    simp only [evX, map_one, one_mul, gs, rowF, trace_eq, Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    · congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    · congr 1
      rw [Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
  unfold secN
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun a v => rowF c (t * sR ε a) b v)]
  exact Finset.prod_congr rfl fun a _ => row_int c _ hc b hb

theorem detpm (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) :
    (c : ℂ) • 1 - (Complex.I * ((c * s : ℝ) : ℂ)) • b = (c : ℂ) • (1 - (Complex.I * (s : ℂ)) • b) := by
  rw [smul_sub, smul_smul]; push_cast; congr 2; ring

theorem fac_eq (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) :
    (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((c * s : ℝ) : ℂ)) • b).det =
      ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) * ((1 - (Complex.I * (s : ℂ)) • b).det)⁻¹ := by
  rw [detpm, det_smul, Fintype.card_fin, div_mul_eq_div_div, div_eq_mul_inv]

theorem one_sub_neg (b : Matrix (Fin n) (Fin n) ℂ) : (1 - (Complex.I * ((-1 : ℝ) : ℂ)) • b) = 1 + Complex.I • b := by
  push_cast; rw [mul_neg_one, neg_smul, sub_neg_eq_add]

theorem one_sub_pos (b : Matrix (Fin n) (Fin n) ℂ) : (1 - (Complex.I * ((1 : ℝ) : ℂ)) • b) = 1 - Complex.I • b := by
  push_cast; rw [mul_one]

private theorem prod_bool_fun_eq_pow_cnt_mul_pow_cnt (ε : Fin m → Bool) (F : Bool → ℂ) :
    ∏ a, F (ε a) = F true ^ cnt ε true * F false ^ cnt ε false := by
  have h : ∀ a, F (ε a) = if ε a = true then F true else F false := by
    intro a
    cases ε a <;> simp
  rw [Finset.prod_congr rfl fun a _ => h a, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp [cnt]

theorem secN_eval (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (hc : 0 < c)
    (hsign : (t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true))
    (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    secN ε c t (1 : PX m n) b = ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) *
      (1 - Complex.I • b).det ^ (-(p : ℤ)) * (1 + Complex.I • b).det ^ (-(q : ℤ)) := by
  rw [secN_one ε c t hc b hb]
  rcases hsign with ⟨ht, hp, hq⟩ | ⟨ht, hp, hq⟩
  · subst hp hq
    let F : Bool → ℂ := fun β => ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) *
      ((1 - (Complex.I * ((if β = true then 1 else -1 : ℝ) : ℂ)) • b).det)⁻¹
    have hf : ∀ a, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det
        = F (ε a) := by
      intro a
      rw [ht, fac_eq]
      rfl
    rw [Finset.prod_congr rfl fun a _ => hf a, prod_bool_fun_eq_pow_cnt_mul_pow_cnt ε F]
    simp only [F, ↓reduceIte, Bool.false_eq_true, one_sub_pos, one_sub_neg]
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, _root_.mul_pow, _root_.mul_pow,
      _root_.inv_pow, _root_.inv_pow, pow_add]
    ring
  · subst hp hq
    let F : Bool → ℂ := fun β => ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) *
      ((1 - (Complex.I * ((if β = true then -1 else 1 : ℝ) : ℂ)) • b).det)⁻¹
    have hf : ∀ a, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det
        = F (ε a) := by
      intro a
      have hs : t * sR ε a = c * (if ε a = true then -1 else 1) := by
        rw [ht]
        unfold sR
        split_ifs <;> ring
      rw [hs, fac_eq]
    rw [Finset.prod_congr rfl fun a _ => hf a, prod_bool_fun_eq_pow_cnt_mul_pow_cnt ε F]
    simp only [F, ↓reduceIte, Bool.false_eq_true, one_sub_pos, one_sub_neg]
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, _root_.mul_pow, _root_.mul_pow,
      _root_.inv_pow, _root_.inv_pow, pow_add]
    ring

end PositivityTheory.Rg.Sw.Glob.Vac
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SmulOneConj
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DRealH

variable {n : ℕ}

theorem blocks_of_inG {g : M2 n} (hg : InG g) :
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₁ = (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁ ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₂ = (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂ ∧
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₂ - (g.toBlocks₂₁)ᴴ * g.toBlocks₁₂ = 1 ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₁ - (g.toBlocks₂₂)ᴴ * g.toBlocks₁₁ = -1 := by
  have h := hg
  unfold InG JJ at h
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero,
    Matrix.fromBlocks_inj] at h
  obtain ⟨h11, h12, h21, h22⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (· + (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁) h11
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · have := congrArg (· + (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂) h22
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h12
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h21

variable {A B C D : Matrix (Fin n) (Fin n) ℂ}

theorem smul_one_conj (w : ℂ) : ((w • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (star w) • 1 := by
  rw [conjTranspose_smul, conjTranspose_one]

theorem cross_self (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B) = (star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h3]; abel
  have e4 : Bᴴ * C = -1 + Dᴴ * A := by rw [← h4]; abel
  simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, e3, e4, h1, h2]
  module

theorem cross_conj (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * ((star w) • C + D) = (w • C + D)ᴴ * ((star w) • A + B) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := eq_add_of_sub_eq h3
  have e4 : Bᴴ * C = -1 + Dᴴ * A := eq_add_of_sub_eq h4
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [h1, h2, e3, e4]
  module

theorem det_ne_zero (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) : (w • C + D).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have key := cross_self h1 h2 h3 h4 w
  have e := congrArg (fun M => star v ⬝ᵥ (M *ᵥ v)) key
  have l1 : ((w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B)) *ᵥ v
      = -((w • C + D)ᴴ *ᵥ ((w • A + B) *ᵥ v)) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, zero_sub]
  have l2 : ((star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v = (star w - w) • v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  simp only [l1, l2] at e
  rw [dotProduct_neg, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hv, star_zero, zero_dotProduct, neg_zero,
    dotProduct_smul, smul_eq_mul] at e
  have hne : star w - w ≠ 0 := sub_ne_zero.mpr hw
  have : star v ⬝ᵥ v = 0 := (mul_eq_zero.mp e.symm).resolve_left hne
  exact hv0 (dotProduct_star_self_eq_zero.mp this)

theorem conj_frac (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) :
    ((w • A + B) * (w • C + D)⁻¹)ᴴ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
  have hw' : star (star w) ≠ star w := by
    rw [star_star]
    exact fun h => hw h.symm
  have d1 := det_ne_zero h1 h2 h3 h4 w hw
  have d2 := det_ne_zero h1 h2 h3 h4 (star w) hw'
  have u1 : IsUnit (w • C + D)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact (star_ne_zero.mpr d1).isUnit
  have u2 : IsUnit ((star w) • C + D).det := d2.isUnit
  have cc := cross_conj h1 h2 h3 h4 w
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc ((w • C + D)ᴴ)⁻¹ * (w • A + B)ᴴ
      = ((w • C + D)ᴴ)⁻¹ * ((w • A + B)ᴴ * ((star w) • C + D)) * ((star w) • C + D)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u2]
    _ = ((w • C + D)ᴴ)⁻¹ * ((w • C + D)ᴴ * ((star w) • A + B)) * ((star w) • C + D)⁻¹ := by rw [cc]
    _ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ u1]

end DRealH

open DRealH in
theorem dReal : DReal := by
  intro m n ε t c e y X a ha s
  funext u
  have hA : aC X (s : ℂ) = mR (a s) := by
    rw [ha s]
    unfold aC
    congr 1
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_mul]
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  have hmul : mR y * aC X (s : ℂ) = mR (y * a s) := by
    rw [hA]
    rfl
  have hG : InG (mR (y * a s)) := (y * a s).2
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG hG
  have hIs : star Complex.I ≠ Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    simp at this
    norm_num at this
  have key := conj_frac h1 h2 h3 h4 Complex.I hIs
  have sI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  rw [sI] at key
  have cI : ((Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (-Complex.I) • 1 := by
    rw [smul_one_conj, sI]
  unfold famC jF gZf gC jC ptZ actZ
  simp only [hmul, cI, Matrix.mul_smul, Matrix.mul_one]
  rw [key]

end PositivityTheory.Rg.Sw.Glob
end
end

