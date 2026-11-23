module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0218

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvCov
section
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal Formalism.FourierDecayAlt.P.FourTermExpansion
  Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_right (X S x : Mat k r) (f : Mat k r → E) (h1 : S * S⁻¹ = 1) (h2 : S⁻¹ * S = 1) :
    RdV X (fun y => f (y * S)) x = RdV (S⁻¹ * X * S) f (x * S) := by
  unfold RdV
  congr 1
  funext t
  have e1 : ((t : ℂ) • (S⁻¹ * X * S)) = S⁻¹ * ((t : ℂ) • X) * S := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, Formalism.QuantumDeterminants.ioh_exp_conj S⁻¹ S _ h1 h2]
  show f (x * NormedSpace.exp ((t : ℂ) • X) * S) = f (x * S * (S⁻¹ * NormedSpace.exp ((t : ℂ) • X) * S))
  congr 1
  calc x * NormedSpace.exp ((t : ℂ) • X) * S
      = x * (S * S⁻¹) * NormedSpace.exp ((t : ℂ) • X) * S := by rw [h1, Matrix.mul_one]
    _ = x * S * (S⁻¹ * NormedSpace.exp ((t : ℂ) • X) * S) := by simp only [Matrix.mul_assoc]

theorem rdV_left (X A x : Mat k r) (f : Mat k r → E) :
    RdV X (fun y => f (A * y)) x = RdV X f (A * x) := by
  unfold RdV
  simp only [Matrix.mul_assoc]

theorem EZ_right (S : Mat k r) (hS : S ∈ GV k r) (f : Mat k r → E) (a b : Fin (2 * r + k + 1)) (x : Mat k r) :
    EZ (Msg k r a b) (fun y => f (y * S)) x = EZ (Mc S a b) f (x * S) := by
  have h := congrFun (congrFun (congrFun (congrFun (EHc_eq_LT (E := E) S hS) a) b) f) (x * S)
  refine Eq.trans ?_ h
  obtain ⟨h1, h2⟩ := gv_inv hS
  show RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) (fun y => f (y * S)) x +
      Complex.I • RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) (fun y => f (y * S)) x = _
  rw [rdV_right _ _ _ _ h1 h2, rdV_right _ _ _ _ h1 h2]
  rfl

theorem EZ_left (A : Mat k r) (Z : Mat k r) (f : Mat k r → E) (x : Mat k r) :
    EZ Z (fun y => f (A * y)) x = EZ Z f (A * x) := by
  unfold EZ
  rw [rdV_left, rdV_left]

theorem fold_right (S : Mat k r) (hS : S ∈ GV k r) (f : Mat k r → E) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      fold (Msg k r) ts (fun y => f (y * S)) = fun x => fold (Mc S) ts f (x * S)
  | [] => rfl
  | t :: ts => by
    funext x
    rw [fold_cons, fold_cons, fold_right S hS f ts, top_apply'', top_apply'']
    congr 1
    exact EZ_right S hS (fold (Mc S) ts f) t.2.1 t.2.2 x

theorem fold_left (A : Mat k r) (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) (f : Mat k r → E) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      fold M ts (fun y => f (A * y)) = fun x => fold M ts f (A * x)
  | [] => rfl
  | t :: ts => by
    funext x
    rw [fold_cons, fold_cons, fold_left A M f ts, top_apply'', top_apply'']
    congr 1
    exact EZ_left A (M t.2.1 t.2.2) (fold M ts f) x

theorem qminor_left {t : ℕ} (A : Mat k r) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E)
    (x : Mat k r) :
    qminorOp (Q.EH k r) a b u (fun y => f (A * y)) x = qminorOp (Q.EH k r) a b u f (A * x) := by
  rw [qm_eq, qm_eq]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [PP]
  rw [fold_left]

theorem qminor_right_all (S : Mat k r) (hS : S ∈ GV k r) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (x : Mat k r) (hx : x * S ∈ GV k r) (hloc : Loc (t : ℕ∞) f (x * S)) :
    qminorOp (Q.EH k r) a b u (fun y => f (y * S)) x =
      ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
        ((∏ j, (S⁻¹) (c j) (a j)) * ∏ j, S (b j) (d j)) • qminorOp (Q.EH k r) c d u f (x * S) := by
  set P := S⁻¹
  set A : (Fin t → Fin (2 * r + k + 1)) → ℂ := fun c => ∏ j, P (c j) (a j) with hA
  set B : (Fin t → Fin (2 * r + k + 1)) → ℂ := fun d => ∏ j, S (b j) (d j) with hB
  have step : ∀ σ : Equiv.Perm (Fin t),
      fold (Mc S) (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) f (x * S) =
        ∑ c, ∑ d, (A c * B d) • PP c d u σ f (x * S) := by
    intro σ
    rw [expandM S hS t _ f (x * S) hx hloc]
    refine (Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ (fun c => ?_)).symm
    simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    congr 1
    · simp only [Function.comp_apply, hA, hB]
      rw [Finset.prod_mul_distrib]
      congr 1
      exact (Equiv.prod_comp σ (fun j => P (c j) (a j))).symm
  rw [qm_eq]
  simp only [PP]
  simp_rw [fold_right S hS f]
  rw [show (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      fold (Mc S) (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) f (x * S)) =
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∑ c, ∑ d, (A c * B d) • PP c d u σ f (x * S) from
    Finset.sum_congr rfl (fun σ _ => by rw [step σ])]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [qm_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal Formalism.FourierDecayAlt.P.FourTermExpansion
  Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open Classical in
theorem sum_sortM {M : Type*} [AddCommGroup M] [Module ℂ M] {t N : ℕ} (F : (Fin t → Fin N) → M)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)), F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
      (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C := by
  rw [Formalism.FourierDecayAlt.P.CutMP.CapInv.groupingM (fun i : Fin N => (i : ℕ)) Fin.val_injective F hF hF0 W,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  by_cases h : StrictMono C
  · rw [if_pos h, if_pos (show StrictMono fun l => ((C l : Fin N) : ℕ) from h)]
  · rw [if_neg h, if_neg (show ¬ StrictMono fun l => ((C l : Fin N) : ℕ) from h)]


open Classical in
theorem collapse2 {M : Type*} [AddCommGroup M] [Module ℂ M] {t N : ℕ}
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (A B : (Fin t → Fin N) → ℂ)
    (hr : ∀ c d (τ : Equiv.Perm (Fin t)), D (c ∘ τ) d = ((Equiv.Perm.sign τ : ℤ) : ℂ) • D c d)
    (hr0 : ∀ c d, ¬ Function.Injective c → D c d = 0)
    (hc : ∀ c d (τ : Equiv.Perm (Fin t)), D c (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • D c d)
    (hc0 : ∀ c d, ¬ Function.Injective d → D c d = 0) :
    ∑ c, ∑ d, (A c * B d) • D c d =
      ∑ c ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
        ∑ d ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
          ((∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * A (c ∘ σ)) *
            (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * B (d ∘ σ))) • D c d := by
  set S := Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C)
  set Y : (Fin t → Fin N) → M := fun c =>
    ∑ d ∈ S, (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * B (d ∘ σ)) • D c d with hY
  have inner : ∀ c, ∑ d, (A c * B d) • D c d = A c • Y c := by
    intro c
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, sum_sortM (D c) (hc c) (hc0 c) B]
  simp_rw [inner]
  rw [sum_sortM Y (fun c τ => by simp only [hY, hr, smul_comm _ (((Equiv.Perm.sign τ : ℤ) : ℂ)), Finset.smul_sum])
    (fun c hcn => by simp [hY, hr0 c _ hcn]) A]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [hY, Finset.smul_sum, smul_smul]

theorem det_rows {t N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (c a : Fin t → Fin N) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, P ((c ∘ σ) j) (a j) = (P.submatrix c a).det := by
  rw [Matrix.det_apply']
  rfl

theorem det_cols {t N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (b d : Fin t → Fin N) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, S (b j) ((d ∘ σ) j) = (S.submatrix b d).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]


open Classical in
theorem qminor_right (S : Mat k r) (hS : S ∈ GV k r) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (x : Mat k r) (hx : x * S ∈ GV k r) (hloc : Loc (t : ℕ∞) f (x * S)) :
    qminorOp (Q.EH k r) a b u (fun y => f (y * S)) x =
      ∑ c ∈ Finset.univ.filter (fun C : Fin t → Fin (2 * r + k + 1) => StrictMono C),
        ∑ d ∈ Finset.univ.filter (fun C : Fin t → Fin (2 * r + k + 1) => StrictMono C),
          ((S⁻¹.submatrix c a).det * (S.submatrix b d).det) • qminorOp (Q.EH k r) c d u f (x * S) := by
  rw [qminor_right_all S hS a b u f x hx hloc]
  rw [collapse2 (fun c d => qminorOp (Q.EH k r) c d u f (x * S)) (fun c => ∏ j, (S⁻¹) (c j) (a j))
    (fun d => ∏ j, S (b j) (d j))
    (fun c d τ => skewRow c d u f (x * S) τ) (fun c d hc => row_zero c d u f (x * S) hc)
    (fun c d τ => skewCol c u f (x * S) hx hloc d τ) (fun c d hd => col_zero c d u f (x * S) hx hloc hd)]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  rw [det_rows, det_cols]

end Formalism.FourierDecayAlt.P.CutMP.RInvCov
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymbolLevi
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

def pw (i : Fin (2 * r + k + 1)) : ℂ := if r ≤ i.val ∧ i.val ≤ r + k then 1 else 0

theorem pw_mulVec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (diagonal (pw (k := k) (r := r)) *ᵥ x) i = pw (k := k) (r := r) i * x i := mulVec_diagonal _ _ _

theorem pw_inWb (x : Fin (2 * r + k + 1) → ℂ) : inWb k r (diagonal (pw (k := k) (r := r)) *ᵥ x) := by
  intro i hi
  rw [pw_mulVec, pw, if_neg (by omega), zero_mul]

theorem pw_fix {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : diagonal (pw (k := k) (r := r)) *ᵥ u = u := by
  funext i
  rw [pw_mulVec, pw]
  split_ifs with h
  · rw [one_mul]
  · rw [zero_mul, hu i (by omega)]

theorem herm_pw_right {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (diagonal (pw (k := k) (r := r)) *ᵥ x) = herm (Hpk k r) v x := by
  rw [herm_eq, herm_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hpk_mulVec_wb hv, pw_mulVec, pw]
  split_ifs with h
  · rw [one_mul]
  · rw [hv i (by omega), mul_zero, mul_zero, mul_zero]

theorem herm_pw_left {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (diagonal (pw (k := k) (r := r)) *ᵥ x) v = herm (Hpk k r) x v := by
  rw [herm_swap, herm_pw_right hv, ← herm_swap]

theorem flt_sub_pw (x : Fin (2 * r + k + 1) → ℂ) (hx : ∀ b : Fin r, x (esI k r b) = 0) :
    Flt r (x - diagonal (pw (k := k) (r := r)) *ᵥ x) := by
  intro i hi
  rw [Pi.sub_apply, pw_mulVec, pw]
  by_cases h : i.val ≤ r + k
  · rw [if_pos ⟨hi, h⟩, one_mul, sub_self]
  · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
    rw [if_neg (by omega), zero_mul, sub_zero, e, hx]

theorem flt_of_orth (x : Fin (2 * r + k + 1) → ℂ)
    (h : ∀ v : Fin (2 * r + k + 1) → ℂ, (∀ b : Fin r, v (esI k r b) = 0) → herm (Hpk k r) x v = 0) : Flt r x := by
  intro i hi
  by_cases h2 : i.val ≤ r + k
  · have hw := herm_w x i hi h2
    have h0 := h (bvec i) (fun b => by
      have : esI k r b ≠ i := by intro e; have := congrArg Fin.val e; simp [esI] at this; omega
      simp [bvec, this])
    rw [hw] at h0
    split_ifs at h0
    · exact neg_eq_zero.1 h0
    · exact h0
  · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
    have e2 := herm_e x ⟨2 * r + k - i.val, by omega⟩
    rw [← e] at e2
    rw [← e2]
    refine h _ (fun b => ?_)
    have : esI k r b ≠ eI k r ⟨2 * r + k - i.val, by omega⟩ := by
      intro e; have := congrArg Fin.val e; simp [esI, eI] at this; omega
    simp [bvec, this]

theorem symbolNil_direct : SymbolNil := by
  intro k r z z' _ hz _ hT _ g hg hgO ξ hξ hn hS hS'
  obtain ⟨N, hN⟩ := hn
  set H := Hpk k r with hH
  have hgu : gᴴ * H * g = H := hg
  have hdetH : H.det ≠ 0 := by
    have := congrArg Matrix.det (Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq (k := k) (r := r))
    rw [det_mul, det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hdetg : IsUnit g.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det hgu
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact hdetH this.symm
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdetg
  have hgg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdetg
  set η := g⁻¹ * ξ * g with hηdef
  have hgη : g * η = ξ * g := by
    rw [hηdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
  have hηpow : ∀ m, η ^ m = g⁻¹ * ξ ^ m * g := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hgg']
    | succ m ih =>
      rw [pow_succ, ih, pow_succ, hηdef]
      calc g⁻¹ * ξ ^ m * g * (g⁻¹ * ξ * g) = g⁻¹ * ξ ^ m * (g * g⁻¹) * ξ * g := by
            simp only [Matrix.mul_assoc]
        _ = g⁻¹ * (ξ ^ m * ξ) * g := by rw [hgg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hηN : η ^ N = 0 := by rw [hηpow, hN, Matrix.mul_zero, Matrix.zero_mul]
  have e1 : (g⁻¹)ᴴ * H = H * g := by
    calc (g⁻¹)ᴴ * H = (g⁻¹)ᴴ * (gᴴ * H * g) := by rw [hgu]
      _ = (g * g⁻¹)ᴴ * H * g := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H * g := by rw [hgg, conjTranspose_one, Matrix.one_mul]
  have e2 : H * g⁻¹ = gᴴ * H := by
    calc H * g⁻¹ = gᴴ * H * g * g⁻¹ := by rw [hgu]
      _ = gᴴ * H := by rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
  have hη : B.inLie k r η := by
    have hξ' : ξᴴ * H + H * ξ = 0 := hξ
    show ηᴴ * H + H * η = 0
    calc ηᴴ * H + H * η = gᴴ * ξᴴ * ((g⁻¹)ᴴ * H) + (H * g⁻¹) * ξ * g := by
          rw [hηdef]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * (ξᴴ * H + H * ξ) * g := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hξ', Matrix.mul_zero, Matrix.zero_mul]
  have hS'η : ∀ X ∈ lieOf (Sset k r z'), (Matrix.trace (η * X)).re = 0 := by
    intro X hX
    have := hS' X hX
    have e : Matrix.trace (ξ * (g * X * g⁻¹)) = Matrix.trace (η * X) := by
      rw [show ξ * (g * X * g⁻¹) = (ξ * g * X) * g⁻¹ by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm, hηdef]
      simp only [Matrix.mul_assoc]
    rw [← e]; exact this
  have hD : ∀ a (ha : a ≤ r), Dmin k r z z' g ⟨a, by omega⟩ ≠ 0 := by
    intro a ha
    cases a with
    | zero => rw [dmin_eq z z' g 0 ha, Matrix.det_fin_zero]; exact one_ne_zero
    | succ b => exact hgO.2 ⟨b, by omega⟩
  have hX := killX z z' g hD ξ η hξ N hN hηN hgη (colN hξ z hS) (colN hη z' hS'η) r le_rfl
  have hξgX : ∀ c : Fin r, ξ *ᵥ (g *ᵥ bvec (eI k r c)) = 0 := by
    intro c
    rw [mulVec_mulVec, ← hgη, ← mulVec_mulVec, (hX _ (flt_bvec r c c.isLt)).2, mulVec_zero]
  have hξe : ∀ c : Fin r, ξ *ᵥ bvec (eI k r c) = 0 := fun c => (hX _ (flt_bvec r c c.isLt)).1
  have hrange : ∀ v b, (ξ *ᵥ v) (esI k r b) = 0 := by
    intro v b
    rw [← herm_e (ξ *ᵥ v) b, herm_skew hξ, hξe, herm_zero_right, neg_zero]
  set P : B.Mat k r := diagonal (pw (k := k) (r := r)) with hP
  have hξP : ∀ y, (∀ b : Fin r, y (esI k r b) = 0) → ξ *ᵥ (P *ᵥ y) = ξ *ᵥ y := by
    intro y hy
    have := (hX _ (flt_sub_pw y hy)).1
    rw [mulVec_sub, sub_eq_zero] at this
    exact this.symm
  have hcomp : ∀ w, (P * ξ * P) *ᵥ w = P *ᵥ (ξ *ᵥ (P *ᵥ w)) := by
    intro w; rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hPfix : ∀ u, inWb k r u → P *ᵥ u = u := fun u hu => by rw [hP]; exact pw_fix hu
  have hPin : ∀ x, inWb k r (P *ᵥ x) := fun x => by rw [hP]; exact pw_inWb x
  have hPl : ∀ v, inWb k r v → ∀ x, herm (Hpk k r) (P *ᵥ x) v = herm (Hpk k r) x v :=
    fun v hv x => by rw [hP]; exact herm_pw_left hv x
  have hWcomp : ∀ u, inWb k r u → ∀ m, ((P * ξ * P) ^ m) *ᵥ u = P *ᵥ ((ξ ^ m) *ᵥ u) := by
    intro u hu m
    induction m with
    | zero => rw [pow_zero, pow_zero, one_mulVec, hPfix u hu]
    | succ m ih =>
      have hy : ∀ b : Fin r, ((ξ ^ m) *ᵥ u) (esI k r b) = 0 := by
        intro b
        cases m with
        | zero => rw [pow_zero, one_mulVec]; exact hu _ (Or.inr (by simp [esI]; omega))
        | succ m => rw [pow_succ', ← mulVec_mulVec]; exact hrange _ b
      rw [pow_succ', ← mulVec_mulVec, ih, hcomp, hPfix _ (hPin _), hξP _ hy, pow_succ', ← mulVec_mulVec]
  have hW := fun X (hX : X ∈ lieOf (UWset k r z)) => hS X (lieOf_mono (UWset_sub_Sset k r z) hX)
  have hcore := coreW hz hT (P * ξ * P)
    (fun u _ => by rw [hcomp]; exact hPin _)
    (fun u v hu hv => by
      rw [hcomp, hcomp, hPfix u hu, hPfix v hv, hPl v hv, herm_swap u, hPl u hu, herm_skew hξ u v, herm_swap u])
    (fun u v hu hv huz hvz => by
      rw [hcomp, hPfix u hu, hPl v hv]
      exact herm_zero_of_lieW hξ z hW u v hu hv huz hvz)
    N (fun u hu => by rw [hWcomp u hu, hN, zero_mulVec, mulVec_zero])
  have hWb : ∀ u, inWb k r u → ξ *ᵥ u = 0 := by
    intro u hu
    have hc := hcore u hu
    rw [hcomp, hPfix u hu, hP] at hc
    have hflt : Flt r (ξ *ᵥ u) := by
      intro i hi
      by_cases h2 : i.val ≤ r + k
      · have := congrFun hc i
        rw [pw_mulVec, pw, if_pos ⟨hi, h2⟩, one_mul] at this
        exact this
      · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
        rw [e]; exact hrange u _
    refine dlem_ii z z' g r le_rfl (hD r le_rfl) _ hflt (fun c _ => ?_)
    rw [herm_skew hξ, hξgX, herm_zero_right, neg_zero]
  have hperp : ∀ y, (∀ b : Fin r, y (esI k r b) = 0) → ξ *ᵥ y = 0 := by
    intro y hy
    rw [← hξP y hy]
    exact hWb _ (pw_inWb _)
  have hstar : ∀ b : Fin r, ξ *ᵥ bvec (esI k r b) = 0 := by
    intro b
    have hflt : Flt r (ξ *ᵥ bvec (esI k r b)) := by
      refine flt_of_orth _ (fun v hv => ?_)
      rw [herm_skew hξ, hperp v hv, herm_zero_right, neg_zero]
    refine dlem_ii z z' g r le_rfl (hD r le_rfl) _ hflt (fun c _ => ?_)
    rw [herm_skew hξ, hξgX, herm_zero_right, neg_zero]
  apply Matrix.ext
  intro i j
  rw [mat_eq_mulVec_bvec ξ i j]
  by_cases hj : j.val ≤ r + k
  · rw [hperp (bvec j) (fun b => by
      have : esI k r b ≠ j := by intro e; have := congrArg Fin.val e; simp [esI] at this; omega
      simp [bvec, this])]
    rfl
  · have e : j = esI k r ⟨2 * r + k - j.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
    rw [e, hstar]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

theorem symbol_nilpotent_holds : SymbolNil := Sym.symbolNil_direct

end Formalism.FourierDecayAlt.P.CutMP.JfS
end

