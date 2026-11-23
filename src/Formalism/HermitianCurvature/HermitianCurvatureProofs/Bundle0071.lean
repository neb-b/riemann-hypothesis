module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BridgeQminor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0067
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0020

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffIteratedFDerivBounded
section
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)}
    (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (n : ℕ) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) →
      UBL (C6.Epart fib es) S n (3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  intro es
  induction es with
  | nil =>
    intro _
    have e0 : C6.Epart fib ([] : List (Fin nf × List (Mat k r))) = fun _ => 1 := by
      funext g
      simp [C6.Epart]
    rw [e0]
    simpa using ubl_const (1 : C6.EndH Wp Wq) hSG n (3 * (r + 1))
  | cons e es ih =>
    intro hes
    have hA := ubl_fib D (fib e.1) (hfib e.1) hε hS e.2 (hes e (by simp)) n
    have hB := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have hL := ubl_clm ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ) hSG hA
    have hAB := ubl_app hSG hL hB
    have e1 : C6.Epart fib (e :: es) =
        fun g => ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ
          (Rw e.2 (fib e.1) g)) (C6.Epart fib es g) := by
      funext g
      simp [C6.Epart]
    rw [e1]
    convert hAB using 2
    simp only [List.map_cons, List.sum_cons]
    ring

lemma ubl_coefP (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) (L : Finset (Fin (r + 2))) {κ : ℕ} (P : Mat k r → ℂ)
    (a b : Fin (r + 2) → ℕ) (c : ℕ) (es : List (Fin nf × List (Mat k r))) (hP : U.IsPolyDeg κ P)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) (hes : ∀ e ∈ es, ∀ X ∈ e.2, inLie k r X)
    {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) S n
      (κ + 3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  have hP' := ubl_poly hP S hSG n (3 * (r + 1))
  have hM := ubl_mono hSG (ubl_monoM D L a b c hab hSG hc₀ hSD hSGf n) le_rfl
    (show 2 * r + 2 ≤ 3 * (r + 1) by omega)
  have hPM := ubl_mul hSG hP' hM
  have hE := ubl_epart D fib hfib hε hS n es hes
  let Lm : ℂ →L[ℝ] (C6.EndH Wp Wq →L[ℂ] C6.EndH Wp Wq) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (C6.EndH Wp Wq))).restrictScalars ℝ
  have hA := ubl_clm Lm hSG hPM
  have hAE := ubl_app hSG hA hE
  have e1 : (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) =
      fun g => Lm (P g * C6.monoM D a b c g) (C6.Epart fib es g) := by
    funext g
    simp [Lm]
  rw [e1]
  simpa using hAE

end fac

section cut

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end cut

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstExpansionIdentity
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem keyS_inj (k r : ℕ) : Function.Injective (keyS k r) := by
  intro p q hpq
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  unfold keyS at hpq
  split_ifs at hpq <;> omega

theorem keyS_esI (k r : ℕ) (x : Fin r) : keyS k r (esI k r x) = x.val := by
  have hx := x.isLt
  have c : r + k < 2 * r + k - x.val := by omega
  simp only [keyS, Formalism.QuantumDeterminants.esI, c, if_true]
  omega

theorem star_sgnW (m : ℕ) : star (sgnW m) = sgnW m := by
  simp [sgnW]

theorem neg_one_sq' (s : ℕ) : ((-1 : ℂ) ^ s) * ((-1) ^ s) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem zb_col_zero (i0 s' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (a : ℕ) (ha : a < i0 + s') :
    Zb i0 (s' + 1) h t a i0 = 0 := by
  unfold Zb
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

theorem first_expansion_identity : ExpansionOmittedColumn := by
  intro A _ _ M _ _ k r z' E La xi i0 s h t u hs hj hR hdet ht hxi
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  rw [AAx_congr k r E xi (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm u]
  have hhead : AAx k r E xi i0 (by omega) u =
      h.det • qminor E (xR k r i0 (by omega)) (xR k r i0 (by omega)) u := by
    apply AAx_head
    · intro a p ha hp
      rw [hxi a p (by omega)]
      split_ifs with hp'
      · unfold Zb
        rw [dite_eq_left ha, dite_eq_right (by omega)]
      · rfl
    · intro a b
      have ha := a.isLt
      have hb := b.isLt
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp [Zb, xR, Formalism.QuantumDeterminants.eI, ha, hb]
  have he : StrictMono (fun l : Fin (i0 + s') =>
      xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) := by
    intro a b hab
    have := (Fin.strictMono_succAbove (⟨i0, by omega⟩ : Fin (i0 + s' + 1))) hab
    rw [Fin.lt_def] at this ⊢
    simpa [xR, Formalism.QuantumDeterminants.eI] using this
  have hmain : AAx k r E xi (i0 + s') hm u = (h.det * t ^ s' * sgnW s') •
      qminor E (xR k r (i0 + s') hm)
        (fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) u := by
    classical
    have hX : ∀ (a : Fin (i0 + s')) (p : Fin (2 * r + k + 1)),
        p ∉ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} → xi (Fin.castLE hm a) p = 0 := by
      intro a p hp
      simp only [Set.mem_setOf_eq, not_and, not_not] at hp
      have ha := a.isLt
      rw [hxi _ p (by simp only [Fin.coe_castLE]; omega)]
      split_ifs with hp1
      · rw [hp (by omega)]
        exact zb_col_zero i0 s' h t _ (by simp only [Fin.coe_castLE]; omega)
      · rfl
    have hu : ∀ c : Fin (i0 + s') → Fin (2 * r + k + 1), StrictMono c →
        (∀ l, c l ∈ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0}) →
        c = fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) := by
      intro c hc hS
      apply uniq_mono _ _ he hc
      intro l
      obtain ⟨h1, h2⟩ := hS l
      have hne : (⟨(c l).val, h1⟩ : Fin (i0 + s' + 1)) ≠ ⟨i0, by omega⟩ := fun e => h2 (congrArg Fin.val e)
      obtain ⟨j, hj'⟩ := Fin.exists_succAbove_eq hne
      refine ⟨j, ?_⟩
      apply Fin.ext
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, hj']
    have hs := sum_single (M := A) StrictMono (fun a p => xi (Fin.castLE hm a) p)
      {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} hX _ he hu
      (fun c => qminor E (xR k r (i0 + s') hm) c u)
    have hdet' : (Matrix.of fun a l : Fin (i0 + s') => xi (Fin.castLE hm a)
        (xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l))).det =
        h.det * t ^ s' * sgnW s' := by
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp]
      congr 1
      ext a l
      have ha := a.isLt
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      simp only [Matrix.of_apply]
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]
    unfold AAx
    rw [← hdet']
    convert hs using 1
  have hpeel := first_peeling_identity A k r z' E (i0 + s') (by omega) ⟨i0, by omega⟩ u
  have hL := la_congr hR hpeel
  have hsc : (h.det * t ^ (s' + 1) * sgnW (s' + 1))⁻¹ * (h.det * t ^ s' * sgnW s') =
      (-1 : ℂ) ^ (s' + 1 - 1) * t⁻¹ * (h.det⁻¹ * h.det) := by
    rw [sgnW_succ', Nat.add_sub_cancel, scal_E _ _ _ _ s' hdet ht (sgnW_sq s') (neg_one_sq' s')]
  rw [hmain, hhead, map_smul, map_smul, hL, (derivative_leading_zb i0 (s' + 1) h t).2,
    (derivative_leading_zb i0 (s' + 1) h t).1, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [hsc]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Hpart2EqZeroOfInLie
section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Hinv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (Hsq k r)

theorem lie_inv {X : Mat k r} (hX : inLie k r X) : (Hpk k r)⁻¹ * Xᴴ * Hpk k r = -X := by
  have hX0 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX0
  rw [Hinv, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, Hsq, Matrix.one_mul]

theorem hermPart_eq_self_of_mem_lie {X : Mat k r} (hX : inLie k r X) : hpart1 (Hpk k r) X = X := by
  simp only [hpart1]
  rw [lie_inv hX, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

theorem hpart2_eq_zero_of_inLie {X : Mat k r} (hX : inLie k r X) : hpart2 (Hpk k r) X = 0 := by
  simp only [hpart2]
  rw [lie_inv hX]
  simp

theorem two_I_inv : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
  rw [div_eq_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  linear_combination Complex.I_sq

theorem hp_decomp (Z : Mat k r) : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
  simp only [hpart1, hpart2]
  have e : Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  rw [two_I_inv, smul_smul, e, ← smul_add, sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem hpart1_add' (Z W : Mat k r) : hpart1 (Hpk k r) (Z + W) = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) W := by
  simp only [hpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  rw [← smul_add]
  congr 1
  abel

theorem hpart2_add' (Z W : Mat k r) : hpart2 (Hpk k r) (Z + W) = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) W := by
  simp only [hpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  rw [← smul_add]
  congr 1
  abel

theorem hp1_real (x : ℝ) (Z : Mat k r) : hpart1 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart1 (Hpk k r) Z := by
  have hs : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [hpart1, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub, smul_comm]

theorem hpart2_ofReal_smul (x : ℝ) (Z : Mat k r) : hpart2 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart2 (Hpk k r) Z := by
  have hs : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_add, smul_comm]

theorem hpart1_I_smul (Z : Mat k r) : hpart1 (Hpk k r) (Complex.I • Z) = -hpart2 (Hpk k r) Z := by
  have hs : star Complex.I = -Complex.I := Complex.conj_I
  simp only [hpart1, hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul, two_I_inv]
  simp only [neg_smul, neg_neg, sub_neg_eq_add]
  rw [← smul_add, smul_smul, show (1 / 2 : ℂ) * Complex.I = Complex.I / 2 by ring]

theorem hpart2_I_smul (Z : Mat k r) : hpart2 (Hpk k r) (Complex.I • Z) = hpart1 (Hpk k r) Z := by
  have hs : star Complex.I = -Complex.I := Complex.conj_I
  simp only [hpart1, hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul, two_I_inv]
  have e1 : -(Complex.I / 2) * Complex.I = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  have e2 : -(Complex.I / 2) * -Complex.I = -(1 / 2) := by
    linear_combination (1 / 2 : ℂ) * Complex.I_sq
  rw [smul_add, smul_smul, smul_smul, smul_sub, e1, e2, neg_smul, sub_eq_add_neg]

theorem lie_bracket {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X * Y - Y * X) := by
  have hX0 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hY0 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX0
  have hY' : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY0
  have hX'' : ∀ M : Mat k r, Xᴴ * (Hpk k r * M) = -(Hpk k r * (X * M)) := by
    intro M
    rw [← Matrix.mul_assoc, hX', Matrix.neg_mul, Matrix.mul_assoc]
  have hY'' : ∀ M : Mat k r, Yᴴ * (Hpk k r * M) = -(Hpk k r * (Y * M)) := by
    intro M
    rw [← Matrix.mul_assoc, hY', Matrix.neg_mul, Matrix.mul_assoc]
  show (X * Y - Y * X)ᴴ * Hpk k r + Hpk k r * (X * Y - Y * X) = 0
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, hX', hY', Matrix.mul_neg, hX'', hY'', neg_neg]
  abel

theorem hp_of_parts {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) :
    hpart1 (Hpk k r) (X + Complex.I • Y) = X ∧ hpart2 (Hpk k r) (X + Complex.I • Y) = Y := by
  refine ⟨?_, ?_⟩
  · rw [hpart1_add', hpart1_I_smul, hermPart_eq_self_of_mem_lie hX, hpart2_eq_zero_of_inLie hY, neg_zero, add_zero]
  · rw [hpart2_add', hpart2_I_smul, hpart2_eq_zero_of_inLie hX, hermPart_eq_self_of_mem_lie hY, zero_add]

def Psi (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : E :=
  D (g * hpart1 (Hpk k r) Z) + Complex.I • D (g * hpart2 (Hpk k r) Z)

theorem Psi_add (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z + W) = Psi D g Z + Psi D g W := by
  simp only [Psi, hpart1_add', hpart2_add', Matrix.mul_add, map_add (f := _), smul_add]
  abel

theorem D_real (D : Mat k r →L[ℝ] E) (g M : Mat k r) (x : ℝ) : D (g * ((x : ℂ) • M)) = (x : ℂ) • D (g * M) := by
  rw [Matrix.mul_smul]
  exact (map_smul D x (g * M)).trans (Complex.coe_smul x _).symm

theorem Psi_real (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (x : ℝ) : Psi D g ((x : ℂ) • Z) = (x : ℂ) • Psi D g Z := by
  simp only [Psi, hp1_real, hpart2_ofReal_smul, D_real, smul_add]
  rw [smul_comm (x : ℂ) Complex.I]

theorem Psi_I (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : Psi D g (Complex.I • Z) = Complex.I • Psi D g Z := by
  simp only [Psi, hpart1_I_smul, hpart2_I_smul, Matrix.mul_neg, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem Psi_smul (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (c : ℂ) : Psi D g (c • Z) = c • Psi D g Z := by
  have hc := Complex.re_add_im c
  calc Psi D g (c • Z) = Psi D g ((c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z)) := by
        rw [smul_smul, ← add_smul, hc]
    _ = (c.re : ℂ) • Psi D g Z + (c.im : ℂ) • (Complex.I • Psi D g Z) := by
        rw [Psi_add, Psi_real, Psi_real, Psi_I]
    _ = c • Psi D g Z := by
        rw [smul_smul, ← add_smul, hc]

theorem Psi_zero (D : Mat k r →L[ℝ] E) (g : Mat k r) : Psi D g 0 = 0 := by
  simpa using Psi_smul D g 0 0

theorem Psi_sub (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z - W) = Psi D g Z - Psi D g W := by
  rw [sub_eq_add_neg, Psi_add, ← neg_one_smul ℂ W, Psi_smul, neg_one_smul, ← sub_eq_add_neg]

end Formalism.FourierDecayAlt.P.JFxE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormCvecSq
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section cpic

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cvec (s : ℕ) (F : ℂ → ℂ → H) (x c : ℂ) : H :=
  (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x (c / x ^ (s - 1))

theorem cvec_inner (s : ℕ) (F G : ℂ → ℂ → H) (x x' : ℂ) (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ∫ c, ⟪cvec s F x c, cvec s G x' c⟫_ℂ =
      ∫ D, ⟪F x D, ((‖x ^ (s - 1) / x' ^ (s - 1)‖ : ℝ) : ℂ) • G x' ((x ^ (s - 1) / x' ^ (s - 1)) * D)⟫_ℂ := by
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hx0' : ‖x'‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
  have hk : ‖x ^ (s - 1)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have key := integral_comp_mul_C (fun c => ⟪cvec s F x c, cvec s G x' c⟫_ℂ) (x ^ (s - 1)) ha
  have hL : ∫ c, ⟪cvec s F x c, cvec s G x' c⟫_ℂ
      = (‖x ^ (s - 1)‖ ^ 2) • ∫ z, ⟪cvec s F x (x ^ (s - 1) * z), cvec s G x' (x ^ (s - 1) * z)⟫_ℂ := by
    rw [key, smul_smul, mul_inv_cancel₀ hk, one_smul]
  rw [hL, ← integral_smul]
  congr 1
  funext D
  change ‖x ^ (s - 1)‖ ^ 2 • ⟪_, _⟫_ℂ = _
  simp only [cvec]
  rw [mul_div_cancel_left₀ D ha, mul_div_right_comm (x ^ (s - 1)) D (x' ^ (s - 1))]
  have hc : ‖x ^ (s - 1)‖ ^ 2 * (‖x‖ ^ (s - 1))⁻¹ * (‖x'‖ ^ (s - 1))⁻¹
      = ‖x ^ (s - 1) / x' ^ (s - 1)‖ := by
    rw [norm_div, norm_pow, norm_pow]
    field_simp
  rw [inner_smul_left, inner_smul_right, inner_smul_right, Complex.conj_ofReal, Complex.real_smul, ← hc]
  push_cast
  ring

theorem integral_norm_cvec_sq (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) (hx : x ≠ 0) :
    ∫ c, ‖cvec s F x c‖ ^ 2 = ∫ D, ‖F x D‖ ^ 2 := by
  have ha : (x ^ (s - 1))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hx)
  have hr : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hce : cvec s F x = fun c => (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c) := by
    funext c
    simp only [cvec, div_eq_inv_mul]
  rw [hce]
  have h1 : ∀ c, ‖((((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c))‖ ^ 2
      = ((‖x‖ ^ (s - 1)) ^ 2)⁻¹ * ‖F x ((x ^ (s - 1))⁻¹ * c)‖ ^ 2 := by
    intro c
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, inv_pow]
  simp_rw [h1]
  rw [integral_const_mul, integral_comp_mul_C (fun D => ‖F x D‖ ^ 2) _ ha, smul_eq_mul,
    norm_inv, norm_pow, inv_pow, inv_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hr), one_mul]

theorem cvec_eq_comp (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) :
    cvec s F x = fun c => (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c) := by
  funext c
  simp only [cvec, div_eq_inv_mul]

theorem memLp_cvec (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) (hx : x ≠ 0) :
    MemLp (F x) 2 volume ↔ MemLp (cvec s F x) 2 volume := by
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hr : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [cvec_eq_comp]
    exact (memLp_comp_mul h _ (inv_ne_zero ha)).const_smul _
  · have := (memLp_comp_mul h (x ^ (s - 1)) ha).const_smul ((‖x‖ ^ (s - 1) : ℝ) : ℂ)
    convert this using 1
    congr 1
    funext D
    simp only [cvec, Pi.smul_apply]
    rw [mul_div_cancel_left₀ D ha, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one, one_smul]

theorem cvec_sub (s : ℕ) (F G : ℂ → ℂ → H) (x c : ℂ) :
    cvec s F x c - cvec s G x c = cvec s (fun x D => F x D - G x D) x c := by
  simp only [cvec, smul_sub]

theorem rhoR_pow_eq {s : ℕ} (hs : s ≠ 0) (σ x : ℂ) :
    rhoR s σ x ^ s = x ^ (s - 1) / (x + σ) ^ (s - 1) := by
  unfold rhoR lamR
  rw [Complex.cpow_nat_inv_pow _ hs, div_pow]

theorem norm_rhoR_pow {s : ℕ} (hs : s ≠ 0) (σ x : ℂ) :
    ‖rhoR s σ x‖ ^ s = ‖x ^ (s - 1) / (x + σ) ^ (s - 1)‖ := by
  rw [← norm_pow, rhoR_pow_eq hs]

end cpic

section cpicMain

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pairD_of_cvec {s : ℕ} (hs : s ≠ 0) (β ε : ℂ) (bt bt' : ℂ → H) (σ x : ℂ) (hx : x ≠ 0) (hxσ : x + σ ≠ 0) :
    ∫ c, ⟪cvec s (fun x D => mainD s β ε bt x D) x c, cvec s (fun x D => mainD s β ε bt' x D) (x + σ) c⟫_ℂ =
      pairD s β ε bt bt' x (x + σ) (rhoR s σ x) := by
  rw [cvec_inner s _ _ x (x + σ) hx hxσ]
  unfold pairD
  rw [rhoR_pow_eq hs, norm_rhoR_pow hs]

end cpicMain

end

end Formalism.FourierDecayAlt.P.PBK
end

