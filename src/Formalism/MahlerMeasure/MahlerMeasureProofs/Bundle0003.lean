module

public import Formalism.MahlerMeasure.Bundle0004

@[expose] public section

-- bundled from Formalism.MahlerMeasure.MahlerMeasureProofs.LieMat
section
namespace Formalism.GM.DetBound

open Finset Polynomial

section Gauss

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem gaussR_le_iff (ρ : NNReal) (P : K[X]) (b : NNReal) :
    gaussR ρ P ≤ b ↔ ∀ k, ‖P.coeff k‖₊ * ρ ^ k ≤ b := by
  unfold gaussR
  rw [Finset.sup_le_iff]
  constructor
  · intro h k
    by_cases hk : k ∈ P.support
    · exact h k hk
    · rw [Polynomial.notMem_support_iff.mp hk]; simp
  · intro h k _; exact h k

theorem coeff_le_gaussR (ρ : NNReal) (P : K[X]) (k : ℕ) : ‖P.coeff k‖₊ * ρ ^ k ≤ gaussR ρ P :=
  (gaussR_le_iff ρ P _).mp le_rfl k

theorem nnnorm_sum_mul_le {ι : Type*} (s : Finset ι) (f : ι → K) (r b : NNReal)
    (h : ∀ i ∈ s, ‖f i‖₊ * r ≤ b) : ‖∑ i ∈ s, f i‖₊ * r ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc ‖f a + ∑ i ∈ s, f i‖₊ * r ≤ max ‖f a‖₊ ‖∑ i ∈ s, f i‖₊ * r := by
          gcongr; exact IsUltrametricDist.nnnorm_add_le_max _ _
      _ = max (‖f a‖₊ * r) (‖∑ i ∈ s, f i‖₊ * r) := max_mul_of_nonneg _ _ r.2
      _ ≤ b := max_le (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem gaussR_sum_le {ι : Type*} (ρ : NNReal) (s : Finset ι) (f : ι → K[X]) (b : NNReal)
    (h : ∀ i ∈ s, gaussR ρ (f i) ≤ b) : gaussR ρ (∑ i ∈ s, f i) ≤ b := by
  rw [gaussR_le_iff]; intro k
  rw [finsetSum_coeff]
  exact nnnorm_sum_mul_le s _ _ _ fun i hi => (coeff_le_gaussR ρ (f i) k).trans (h i hi)

theorem gaussR_neg (ρ : NNReal) (P : K[X]) : gaussR ρ (-P) = gaussR ρ P := by
  unfold gaussR; simp [support_neg]

theorem gaussR_C (ρ : NNReal) (a : K) : gaussR ρ (C a) = ‖a‖₊ := by
  apply le_antisymm
  · rw [gaussR_le_iff]; intro k
    rw [coeff_C]; split_ifs with hk
    · subst hk; simp
    · simp
  · simpa using coeff_le_gaussR ρ (C a) 0

theorem gaussR_mul_le (ρ : NNReal) (P Q : K[X]) : gaussR ρ (P * Q) ≤ gaussR ρ P * gaussR ρ Q := by
  rw [gaussR_le_iff]; intro k
  rw [coeff_mul]
  apply nnnorm_sum_mul_le
  intro x hx
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  rw [nnnorm_mul, ← hx, pow_add]
  calc ‖P.coeff x.1‖₊ * ‖Q.coeff x.2‖₊ * (ρ ^ x.1 * ρ ^ x.2)
      = (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by ring
    _ ≤ _ := mul_le_mul' (coeff_le_gaussR _ _ _) (coeff_le_gaussR _ _ _)

theorem gaussR_prod_le {ι : Type*} (ρ : NNReal) (s : Finset ι) (f : ι → K[X]) :
    gaussR ρ (∏ i ∈ s, f i) ≤ ∏ i ∈ s, gaussR ρ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [prod_empty]; rw [← C_1, gaussR_C]; simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (gaussR_mul_le _ _ _).trans (by gcongr)

theorem gaussR_det_le (ρ : NNReal) {n : ℕ} (M : Matrix (Fin n) (Fin n) K[X]) (b : Fin n → NNReal)
    (hb : ∀ i j, gaussR ρ (M i j) ≤ b i) : gaussR ρ M.det ≤ ∏ i, b i := by
  rw [Matrix.det_apply]
  apply gaussR_sum_le
  intro σ _
  have hsign : gaussR ρ (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = gaussR ρ (∏ i, M (σ i) i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, gaussR_neg]
  rw [hsign]
  calc gaussR ρ (∏ i, M (σ i) i) ≤ ∏ i, gaussR ρ (M (σ i) i) := gaussR_prod_le _ _ _
    _ ≤ ∏ i, b (σ i) := Finset.prod_le_prod' fun i _ => hb _ _
    _ = ∏ i, b i := Equiv.prod_comp σ b

theorem gaussR_le_max_coeff_zero {ρ : NNReal} (hρ : ρ ≤ 1) (P : K[X]) (hP : gaussR 1 P ≤ 1) :
    gaussR ρ P ≤ max ‖P.coeff 0‖₊ ρ := by
  rw [gaussR_le_iff]; intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have h1 : ‖P.coeff k‖₊ ≤ 1 := by simpa using (coeff_le_gaussR 1 P k).trans hP
    calc ‖P.coeff k‖₊ * ρ ^ k ≤ 1 * ρ := mul_le_mul' h1 (pow_le_of_le_one ρ.2 hρ hk.ne')
      _ = ρ := one_mul _
      _ ≤ _ := le_max_right _ _

theorem norm_det_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  have h := gaussR_det_le 1 (M.map C) (fun _ => 1) (fun i j => by
    rw [Matrix.map_apply, gaussR_C, ← NNReal.coe_le_coe]; simpa using hM i j)
  have e : (M.map C).det = C M.det := (RingHom.map_det C M).symm
  rw [e, gaussR_C, prod_const_one, ← NNReal.coe_le_coe] at h
  simpa using h

theorem norm_inv_entry_le {n : ℕ} (U : Matrix (Fin n) (Fin n) K) (hU : ∀ i j, ‖U i j‖ ≤ 1)
    (hdet : ‖U.det‖ = 1) (i j : Fin n) : ‖U⁻¹ i j‖ ≤ 1 := by
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul, norm_mul, norm_inv, hdet,
    inv_one, one_mul, Matrix.adjugate_apply]
  apply norm_det_le_one
  intro k l
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs <;> simp
  · exact hU k l

end Gauss

end Formalism.GM.DetBound

namespace Formalism.GM

open Finset Polynomial DetBound

theorem lieMat_of (hM : MahlerK) : LieMat := by
  intro p _ K _ _ _ n del₀ h E c t₀ U V d hc hU hV hdU hdV hE hdel hA
  set L : K[X] := C ((p : K) ^ h) * X + C (t₀ : K) with hL
  set ρ : NNReal := Real.toNNReal ((p : ℝ) ^ (-E)) with hρdef
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, Real.toNNReal_le_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  set A := binMatK K del₀ c with hAdef
  set B : Matrix (Fin n) (Fin n) K[X] := A.map (fun P => P.comp L) with hB
  have hdetB : A.det.comp L = B.det := by
    have := RingHom.map_det (Polynomial.compRingHom L) A
    simpa [Polynomial.coe_compRingHom_apply, RingHom.mapMatrix_apply] using this
  have hC1 : ∀ a : K, ‖a‖ ≤ 1 → gaussR 1 (C a) ≤ 1 := by
    intro a ha; rw [gaussR_C, ← NNReal.coe_le_coe]; simpa using ha
  have hmul1 : ∀ P Q : K[X], gaussR 1 P ≤ 1 → gaussR 1 Q ≤ 1 → gaussR 1 (P * Q) ≤ 1 :=
    fun P Q hP hQ => (gaussR_mul_le _ _ _).trans (mul_le_one' hP hQ)
  have hBint : ∀ i j, gaussR 1 (B i j) ≤ 1 := by
    intro i j
    simp only [hB, Matrix.map_apply, hAdef, binMatK, Polynomial.sum_comp, mul_comp, C_comp]
    apply gaussR_sum_le
    intro k hk
    apply hmul1 _ _ (hC1 _ (hc i j k))
    rw [gaussR_le_iff]
    intro m
    rw [one_pow, mul_one, ← NNReal.coe_le_coe]
    have hk' : k ≤ p ^ h := by
      have := Finset.mem_range.mp hk; omega
    rw [coe_nnnorm, NNReal.coe_one]
    exact hM p K h k t₀ hk' m
  have hB0 : B.map (Polynomial.eval 0) = U * Matrix.diagonal d * V := by
    rw [← hA]; ext i j; simp [hB, Matrix.map_apply, Polynomial.eval_comp, hL]
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [hdU]; norm_num))
  have hVu : IsUnit V.det := isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [hdV]; norm_num))
  set B' : Matrix (Fin n) (Fin n) K[X] := (U⁻¹).map C * B * (V⁻¹).map C with hB'
  have hB'0 : B'.map (Polynomial.eval 0) = Matrix.diagonal d := by
    have hmul := fun (X Y : Matrix (Fin n) (Fin n) K[X]) =>
      (Matrix.map_mul (L := X) (M := Y) (f := Polynomial.evalRingHom (0 : K)))
    simp only [coe_evalRingHom] at hmul
    have hCm : ∀ W : Matrix (Fin n) (Fin n) K, (W.map C).map (Polynomial.eval 0) = W := by
      intro W; ext i j; simp
    rw [hB', hmul, hmul, hCm, hCm, hB0]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hVu, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hUu]
  have hB'int : ∀ i j, gaussR 1 (B' i j) ≤ 1 := by
    intro i j
    simp only [hB', Matrix.mul_apply, Matrix.map_apply]
    apply gaussR_sum_le; intro l _
    apply hmul1 _ _ _ (hC1 _ (norm_inv_entry_le V hV hdV l j))
    apply gaussR_sum_le; intro k _
    exact hmul1 _ _ (hC1 _ (norm_inv_entry_le U hU hdU i k)) (hBint k l)
  classical
  let b : Fin n → NNReal := fun i => if ‖d i‖ ≤ (p : ℝ) ^ (-E) then ρ else 1
  have hrow : ∀ i j, gaussR ρ (B' i j) ≤ b i := by
    intro i j
    refine (gaussR_le_max_coeff_zero hρ1 _ (hB'int i j)).trans ?_
    have h0 : (B' i j).coeff 0 = Matrix.diagonal d i j := by
      rw [coeff_zero_eq_eval_zero, ← hB'0, Matrix.map_apply]
    rw [h0]
    simp only [b]
    split_ifs with hd
    · refine max_le ?_ le_rfl
      rw [Matrix.diagonal_apply]
      split_ifs with hij
      · rw [hρdef, Real.le_toNNReal_iff_coe_le (Real.rpow_nonneg (by linarith) _)]
        simpa using hd
      · simp
    · refine max_le ?_ hρ1
      have := coeff_le_gaussR 1 (B' i j) 0
      rw [h0, pow_zero, mul_one] at this
      exact this.trans (hB'int i j)
  have hdetB' : gaussR ρ B'.det ≤ ρ ^ (univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card := by
    refine (gaussR_det_le ρ B' b hrow).trans (le_of_eq ?_)
    simp only [b]
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
  have hBB' : B = U.map C * B' * V.map C := by
    have hmulC := fun (X Y : Matrix (Fin n) (Fin n) K) =>
      (Matrix.map_mul (L := X) (M := Y) (f := (C : K →+* K[X])))
    rw [hB']
    simp only [Matrix.mul_assoc]
    rw [← hmulC V⁻¹ V, Matrix.nonsing_inv_mul _ hVu, ← Matrix.mul_assoc (U.map C), ← hmulC U U⁻¹,
      Matrix.mul_nonsing_inv _ hUu]
    rw [Matrix.map_one _ (map_zero C) (map_one C), Matrix.one_mul, Matrix.mul_one]
  have hdetBB : B.det = C U.det * B'.det * C V.det := by
    rw [hBB', Matrix.det_mul, Matrix.det_mul, RingHom.map_det C U, RingHom.map_det C V]
    rfl
  have hnU : ‖U.det‖₊ = 1 := by ext; simpa using hdU
  have hnV : ‖V.det‖₊ = 1 := by ext; simpa using hdV
  have hfin : gaussR ρ (A.det.comp L) ≤ ρ ^ (univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card := by
    rw [hdetB, hdetBB]
    calc gaussR ρ (C U.det * B'.det * C V.det)
        ≤ gaussR ρ (C U.det * B'.det) * gaussR ρ (C V.det) := gaussR_mul_le _ _ _
      _ ≤ gaussR ρ (C U.det) * gaussR ρ B'.det * gaussR ρ (C V.det) := by
          gcongr; exact gaussR_mul_le _ _ _
      _ = gaussR ρ B'.det := by rw [gaussR_C, gaussR_C, hnU, hnV, one_mul, mul_one]
      _ ≤ _ := hdetB'
  have hfin' := NNReal.coe_le_coe.mpr hfin
  refine hfin'.trans (le_of_eq ?_)
  rw [NNReal.coe_pow, hρdef, Real.coe_toNNReal _ (Real.rpow_nonneg (by linarith) _),
    ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), neg_mul]

end Formalism.GM
end

-- bundled from Formalism.MahlerMeasure.MahlerMeasureProofs.LieRoots
section
namespace Formalism.GM

open Finset Polynomial

namespace GaussNormRoots

section
variable {K : Type} [NormedField K]

theorem gaussR_eq_sup_of_subset (ρ : NNReal) (P : K[X]) (s : Finset ℕ) (hs : P.support ⊆ s) :
    gaussR ρ P = s.sup (fun k => ‖P.coeff k‖₊ * ρ ^ k) := by
  unfold gaussR
  apply le_antisymm (Finset.sup_mono hs)
  refine Finset.sup_le fun k _ => ?_
  by_cases hk : k ∈ P.support
  · exact Finset.le_sup (f := fun k => ‖P.coeff k‖₊ * ρ ^ k) hk
  · rw [Polynomial.notMem_support_iff.mp hk]
    simp

theorem gaussR_C (ρ : NNReal) (a : K) : gaussR ρ (Polynomial.C a) = ‖a‖₊ := by
  rw [gaussR_eq_sup_of_subset ρ _ {0} (Polynomial.support_C_subset a)]
  simp

theorem gaussR_lin (ρ : NNReal) (q a : K) :
    gaussR ρ (Polynomial.C q * X + Polynomial.C a) = max ‖a‖₊ (‖q‖₊ * ρ) := by
  have hs : (Polynomial.C q * X + Polynomial.C a).support ⊆ {0, 1} := by
    intro k hk
    rw [Polynomial.mem_support_iff] at hk
    rcases k with _ | _ | k <;> simp_all [Polynomial.coeff_C, Polynomial.coeff_X]
  rw [gaussR_eq_sup_of_subset ρ _ _ hs]
  simp [Polynomial.coeff_C, Polynomial.coeff_X, max_comm]

theorem gaussR_multiset_prod (hG : GaussMulRad) [IsUltrametricDist K] (ρ : NNReal) (hρ : 0 < ρ)
    (m : Multiset K) (f : K → K[X]) :
    gaussR ρ (m.map f).prod = (m.map (fun ζ => gaussR ρ (f ζ))).prod := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [← Polynomial.C_1, gaussR_C]
    simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [hG K ρ _ _ hρ, ih]

end

theorem multiset_sum_le_sum {α : Type} (m : Multiset α) (f g : α → ℝ) (hfg : ∀ x, f x ≤ g x) :
    (m.map f).sum ≤ (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact add_le_add (hfg a) ih

theorem multiset_sum_neg {α : Type} (m : Multiset α) (f : α → ℝ) :
    (m.map fun x => -f x).sum = -(m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, neg_add]

theorem multiset_sum_add {α : Type} (m : Multiset α) (f g : α → ℝ) :
    (m.map fun x => f x + g x).sum = (m.map f).sum + (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring

theorem multiset_sum_mul_left {α : Type} (m : Multiset α) (c : ℝ) (f : α → ℝ) :
    (m.map fun x => c * f x).sum = c * (m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, mul_add]

theorem multiset_card_filter_eq_sum {α : Type} (m : Multiset α) (P : α → Prop) [DecidablePred P] :
    ((m.filter P).card : ℝ) = (m.map fun x => if P x then (1 : ℝ) else 0).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    by_cases h : P a
    · rw [Multiset.filter_cons_of_pos _ h]
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, h, if_true]
      push_cast
      rw [ih]
      ring
    · rw [Multiset.filter_cons_of_neg _ h]
      simp only [Multiset.map_cons, Multiset.sum_cons, h, if_false]
      rw [ih]
      ring

theorem multiset_prod_pos {α : Type} (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    0 < (m.map f).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_pos (hf a) ih

theorem logb_multiset_prod {α : Type} (b : ℝ) (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    Real.logb b (m.map f).prod = (m.map fun x => Real.logb b (f x)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [Real.logb_mul (hf a).ne' (multiset_prod_pos m f hf).ne', ih]

theorem vmin_step (p : ℕ) (hp1 : (1 : ℝ) < p) (h : ℕ) (E : ℝ) (hE : 0 ≤ E) (u : ℝ) (_hu : 0 ≤ u)
    [Decidable (u ≤ (p : ℝ) ^ (-(h : ℤ)))] :
    -Real.logb p (max u ((p : ℝ) ^ (-((h : ℝ) + E)))) ≤
      -Real.logb p (max u ((p : ℝ) ^ (-(h : ℤ)))) + E * (if u ≤ (p : ℝ) ^ (-(h : ℤ)) then 1 else 0) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hB : (0 : ℝ) < (p : ℝ) ^ (-((h : ℝ) + E)) := Real.rpow_pos_of_pos hp0 _
  have hAeq : (p : ℝ) ^ (-(h : ℤ)) = (p : ℝ) ^ (-(h : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  have hBA : (p : ℝ) ^ (-((h : ℝ) + E)) ≤ (p : ℝ) ^ (-(h : ℤ)) := by
    rw [hAeq]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  split_ifs with hu
  · rw [max_eq_right hu, mul_one]
    have h1 : Real.logb p ((p : ℝ) ^ (-((h : ℝ) + E))) ≤
        Real.logb p (max u ((p : ℝ) ^ (-((h : ℝ) + E)))) :=
      Real.logb_le_logb_of_le hp1 hB (le_max_right _ _)
    have h2 : Real.logb p ((p : ℝ) ^ (-((h : ℝ) + E))) = -((h : ℝ) + E) :=
      Real.logb_rpow hp0 hp1.ne'
    have h3 : Real.logb p ((p : ℝ) ^ (-(h : ℤ))) = -(h : ℝ) := by
      rw [hAeq]
      exact Real.logb_rpow hp0 hp1.ne'
    linarith
  · push_neg at hu
    rw [max_eq_left (le_trans hBA hu.le), max_eq_left hu.le]
    simp

end GaussNormRoots

open GaussNormRoots in
theorem lieRoots_of (hG : GaussMulRad) : LieRoots := by
  unfold LieRoots
  intro p _ K _ _ _ h β E D lead roots t₀ hE hlead hD hbound
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hρ : 0 < ((p : ℝ) ^ (-E)).toNNReal := Real.toNNReal_pos.mpr (Real.rpow_pos_of_pos hp0 _)
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] K) p, norm_algebraMap', Padic.norm_p]
  have hnph : ‖(p : K) ^ h‖ = (p : ℝ) ^ (-(h : ℤ)) := by
    rw [norm_pow, hnp, inv_pow, zpow_neg, zpow_natCast]
  have hcomp : D.comp (C ((p : K) ^ h) * X + C (t₀ : K)) =
      C lead * (roots.map fun ζ => C ((p : K) ^ h) * X + C ((t₀ : K) - ζ)).prod := by
    rw [hD, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.multiset_prod_comp, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun ζ _ => ?_
    simp only [Function.comp_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
    ring
  have hpt : ∀ ζ : K, ((max ‖(t₀ : K) - ζ‖₊ (‖(p : K) ^ h‖₊ * ((p : ℝ) ^ (-E)).toNNReal) : NNReal) : ℝ) =
      max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E))) := by
    intro ζ
    rw [NNReal.coe_max, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, hnph,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos hp0 _).le]
    congr 1
    rw [← Real.rpow_intCast, ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  have hreal : ((gaussR ((p : ℝ) ^ (-E)).toNNReal (D.comp (C ((p : K) ^ h) * X + C (t₀ : K))) : NNReal) : ℝ) =
      ‖lead‖ * (roots.map fun ζ => max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))).prod := by
    rw [hcomp, hG K _ _ _ hρ, gaussR_C, gaussR_multiset_prod hG _ hρ]
    simp only [gaussR_lin]
    rw [NNReal.coe_mul, coe_nnnorm, NNReal.coe_multiset_prod, Multiset.map_map]
    congr 1
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun ζ _ => hpt ζ)
  rw [hreal] at hbound
  have hFpos : ∀ ζ : K, 0 < max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E))) :=
    fun ζ => lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) (le_max_right _ _)
  have hlpos : 0 < ‖lead‖ := norm_pos_iff.mpr hlead
  have hPpos := multiset_prod_pos roots _ hFpos
  have hlog : Real.logb p (‖lead‖ * (roots.map fun ζ => max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))).prod)
      ≤ -(E * β) := by
    calc _ ≤ Real.logb p ((p : ℝ) ^ (-(E * β))) :=
          Real.logb_le_logb_of_le hp1 (mul_pos hlpos hPpos) hbound
      _ = -(E * β) := Real.logb_rpow hp0 hp1.ne'
  rw [Real.logb_mul hlpos.ne' hPpos.ne', logb_multiset_prod _ _ _ hFpos] at hlog
  have hstep := multiset_sum_le_sum roots
    (fun ζ => -Real.logb p (max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))))
    (fun ζ => vmin p h ((t₀ : K) - ζ) +
      E * (if ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) then 1 else 0)) (fun ζ => by
        have := vmin_step p hp1 h E hE ‖(t₀ : K) - ζ‖ (norm_nonneg _)
        unfold vmin
        simpa only using this)
  rw [multiset_sum_add, multiset_sum_mul_left, multiset_sum_neg] at hstep
  rw [multiset_card_filter_eq_sum]
  linarith

end Formalism.GM
end

