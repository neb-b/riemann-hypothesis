module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDomin
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

def tGL {n : ℕ} (i j : Fin n) (h : i ≠ j) (s : ℂ) : GL (Fin n) ℂ :=
  ⟨transvection i j s, transvection i j (-s),
    by rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same i j h, neg_add_cancel, transvection_zero]⟩

theorem inv_val {n : ℕ} {i j : Fin n} (h : i ≠ j) (s : ℂ) (T : GL (Fin n) ℂ)
    (hT : T.val = transvection i j s) : (T⁻¹).val = transvection i j (-s) := by
  have e : T = tGL i j h s := Units.ext hT
  subst e
  rfl

theorem eval_evalRingHom {σ : Type} (g : σ → ℂ[X]) (Q : MvPolynomial σ ℂ) (s : ℂ) :
    (MvPolynomial.aeval g Q).eval s = MvPolynomial.eval (fun v => (g v).eval s) Q := by
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  have : (Polynomial.evalRingHom s).comp (algebraMap ℂ ℂ[X]) = RingHom.id ℂ := by
    ext; simp
  rw [this]
  rfl

theorem expand {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ)
    (hΦ : IsPolyRep Φ) {i j : Fin n} (h : i ≠ j) (w : ι → ℂ) :
    ∃ q : ι → ℂ[X], ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s →
      Φ T *ᵥ w = fun a => (q a).eval s := by
  choose Q hQ using hΦ.poly
  let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ[X] :=
    Sum.elim (fun p => (transvection i j (X : ℂ[X])) p.1 p.2)
      (fun p => (transvection i j (-X : ℂ[X])) p.1 p.2)
  refine ⟨fun a => ∑ b, MvPolynomial.aeval g (Q a b) * C (w b), ?_⟩
  intro s T hT
  funext a
  simp only [mulVec, dotProduct, eval_finsetSum, eval_mul, eval_C, eval_evalRingHom]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hQ a b T]
  congr 2
  congr 1
  funext v
  rcases v with ⟨p1, p2⟩ | ⟨p1, p2⟩
  · simp only [g, Sum.elim_inl, hT, transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp
  · simp only [g, Sum.elim_inr, inv_val h s T hT, transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

theorem diagonal_eq_of_isDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsDiag) :
    A = diagonal (fun m => A m m) := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp
  · simp [diagonal_apply_ne _ hab, hA hab]

theorem diag_ne_zero {n : ℕ} (D : GL (Fin n) ℂ) (hD : D.val.IsDiag) (m : Fin n) :
    D.val m m ≠ 0 := by
  have hdet : (D.val).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp D.isUnit).ne_zero
  rw [diagonal_eq_of_isDiag _ hD, det_diagonal] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) m (Finset.mem_univ _)

theorem diagonal_mul_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) (d : Fin n → ℂ)
    (hdj : d j ≠ 0) (s : ℂ) :
    diagonal d * transvection i j s = transvection i j (s * (d i / d j)) * diagonal d := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.single_apply]
  by_cases h2 : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h2
    simp only [and_self, if_true, one_apply_ne h]
    field_simp
    ring
  · simp only [h2, if_false, mul_zero, zero_mul, add_zero]
    by_cases hab : a = b
    · subst hab; simp
    · simp [one_apply_ne hab]

theorem conj_val {n : ℕ} {i j : Fin n} (h : i ≠ j) (D : GL (Fin n) ℂ) (hD : D.val.IsDiag)
    (s : ℂ) (T : GL (Fin n) ℂ) (hT : T.val = transvection i j s) :
    (D * T * D⁻¹).val = transvection i j (s * (D.val i i / D.val j j)) := by
  have key : D.val * T.val = transvection i j (s * (D.val i i / D.val j j)) * D.val := by
    have := diagonal_mul_transvection h (fun m => D.val m m) (diag_ne_zero D hD j) s
    rw [← diagonal_eq_of_isDiag _ hD] at this
    rw [hT]
    exact this
  rw [Units.val_mul, Units.val_mul, key, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

def shiftWt {n : ℕ} (ν : Fin n → ℤ) (i j : Fin n) (k : ℕ) : Fin n → ℤ :=
  fun m => ν m + (k : ℤ) * (if m = i then 1 else 0) - (k : ℤ) * (if m = j then 1 else 0)

theorem prod_zpow_shiftWt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ m, d m ≠ 0) (ν : Fin n → ℤ)
    (i j : Fin n) (k : ℕ) :
    ∏ m, d m ^ (shiftWt ν i j k m) = (∏ m, d m ^ ν m) * (d i / d j) ^ k := by
  have e : ∀ m, d m ^ (shiftWt ν i j k m) =
      d m ^ ν m * ((if m = i then d m ^ (k : ℤ) else 1) / (if m = j then d m ^ (k : ℤ) else 1)) := by
    intro m
    simp only [shiftWt]
    rw [zpow_sub₀ (hd m), zpow_add₀ (hd m), mul_div_assoc]
    split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun m _ => e m), Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp [div_pow, zpow_natCast]

theorem domLE_shiftWt {n : ℕ} {ν lam : Fin n → ℤ} (hν : DomLE ν lam) {i j : Fin n} (hji : j < i)
    (k : ℕ) : DomLE (shiftWt ν i j k) lam := by
  obtain ⟨h1, h2⟩ := hν
  constructor
  · rw [← h1]
    simp only [shiftWt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  · intro K
    have hK := h2 K
    simp only [shiftWt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    have hji' : (j : ℕ) < i := hji
    by_cases hi : (i : ℕ) < K
    · have hj : (j : ℕ) < K := lt_trans hji' hi
      simp only [hi, hj, if_true]
      linarith
    · simp only [hi, if_false, mul_zero, add_zero]
      have : (0 : ℤ) ≤ (k : ℤ) * (if (j : ℕ) < K then 1 else 0) := by
        split_ifs <;> simp
      linarith

theorem isWtVec_coeff {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (hΦ : IsPolyRep Φ) {i j : Fin n} (h : i ≠ j)
    (ν : Fin n → ℤ) (w : ι → ℂ) (hw : IsWtVec Φ ν w) (q : ι → ℂ[X])
    (hq : ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s →
      Φ T *ᵥ w = fun a => (q a).eval s) (k : ℕ) :
    IsWtVec Φ (shiftWt ν i j k) (fun a => (q a).coeff k) := by
  intro D hD
  have hd : ∀ m, D.val m m ≠ 0 := diag_ne_zero D hD
  set c : ℂ := D.val i i / D.val j j with hc
  set P : ℂ := ∏ m, D.val m m ^ ν m with hP
  have hs : ∀ s : ℂ, Φ D *ᵥ (fun a => (q a).eval s) = P • (fun a => (q a).eval (s * c)) := by
    intro s
    have hT : (tGL i j h s).val = transvection i j s := rfl
    have hc' : Φ D * Φ (tGL i j h s) = Φ (D * tGL i j h s * D⁻¹) * Φ D := by
      rw [← hΦ.mul, ← hΦ.mul, inv_mul_cancel_right]
    rw [← hq s _ hT, ← hq (s * c) _ (conj_val h D hD s _ hT), mulVec_mulVec, hc',
      ← mulVec_mulVec, hw D hD, mulVec_smul]
  have hpoly : ∀ a, ∑ b, C (Φ D a b) * q b = C P * (q a).comp (C c * X) := by
    intro a
    apply Polynomial.funext
    intro s
    have e := congrFun (hs s) a
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
    simp only [eval_finsetSum, eval_mul, eval_C, eval_comp, eval_X]
    rw [e, mul_comm c s]
  funext a
  have e := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) (hpoly a)
  simp only [finsetSum_coeff, coeff_C_mul, comp_C_mul_X_coeff] at e
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [e, prod_zpow_shiftWt _ hd]
  ring

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW

open Polynomial LowerTransv

theorem lowerTransvection_mulVec_mem_Sle : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (lam ν : Fin n → ℤ), DomLE ν lam →
    ∀ (w : ι → ℂ), IsWtVec Φ ν w → ∀ (i j : Fin n), j < i → ∀ (s : ℂ) (T : GL (Fin n) ℂ),
    T.val = transvection i j s → Φ T *ᵥ w ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ lam ν hν w hw i j hji s T hT
  have h : i ≠ j := hji.ne'
  obtain ⟨q, hq⟩ := expand Φ hΦ h w
  set N : ℕ := (Finset.univ.sup fun a => (q a).natDegree) + 1 with hN
  have hsum : Φ T *ᵥ w = ∑ k ∈ Finset.range N, s ^ k • (fun a => (q a).coeff k) := by
    rw [hq s T hT]
    funext a
    rw [Finset.sum_apply]
    have hlt : (q a).natDegree < N :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun a => (q a).natDegree) (Finset.mem_univ a))
    rw [eval_eq_sum_range' hlt]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨shiftWt ν i j k, domLE_shiftWt hν hji k, isWtVec_coeff Φ hΦ h ν w hw q hq k⟩

end GlobalTheory.AlgWtHW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInduction
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

noncomputable def LowerGen.offDiagSupport {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ M p.1 p.2 ≠ 0

theorem LowerGen.lowerTriangular_elim_step {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ)
    (hL : L.BlockTriangular OrderDual.toDual) (i j : Fin n) (hij : j < i)
    (hjj : L j j ≠ 0)
    (hmin : ∀ a b : Fin n, b < j → a ≠ b → L a b = 0) (a b : Fin n) :
    (transvection i j (-L i j / L j j) * L) a b = if a = i ∧ b = j then 0 else L a b := by
  by_cases ha : a = i
  · subst ha
    rw [transvection_mul_apply_same]
    have hrow : L j b = if b = j then L j j else 0 := by
      rcases lt_trichotomy b j with h | h | h
      · rw [if_neg h.ne]; exact hmin j b h (Ne.symm h.ne)
      · subst h; simp
      · rw [if_neg h.ne']; exact hL (by simpa using h)
    rw [hrow]
    by_cases hb : b = j
    · subst hb; simp; field_simp; ring
    · simp [hb]
  · rw [transvection_mul_apply_of_ne _ _ _ _ ha]; simp [ha]

end GlobalTheory

open GlobalTheory GlobalTheory.LowerGen in
theorem GlobalTheory.lowerTriangular_GL_induction : ∀ {n : ℕ} (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) →
    (∀ D : GL (Fin n) ℂ, D.val.IsDiag → P D) →
    (∀ (i j : Fin n) (s : ℂ) (T : GL (Fin n) ℂ), j < i → T.val = transvection i j s → P T) →
    ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual → P L := by
  intro n P _h1 hmul hdiag htr
  suffices H : ∀ m : ℕ, ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      (LowerGen.offDiagSupport L.val).card = m → P L by
    intro L hL; exact H _ L hL rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro L hL hm

  have hdet : L.val.det ≠ 0 := by
    have h := congrArg Matrix.det L.mul_inv
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hdiag0 : ∀ k, L.val k k ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular _ hL] at hdet
    exact fun k => (Finset.prod_ne_zero_iff.mp hdet) k (Finset.mem_univ _)
  by_cases hS : (LowerGen.offDiagSupport L.val) = ∅
  · apply hdiag
    intro a b hab
    by_contra hne
    have : (a, b) ∈ LowerGen.offDiagSupport L.val := by simp [LowerGen.offDiagSupport, hab, hne]
    rw [hS] at this; simp at this
  ·
    have hne : (LowerGen.offDiagSupport L.val).Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    let cols := (LowerGen.offDiagSupport L.val).image Prod.snd
    have hcols : cols.Nonempty := hne.image _
    set j := cols.min' hcols with hjdef
    have hjmem : j ∈ cols := Finset.min'_mem _ _
    obtain ⟨⟨i, jj⟩, hp, hj'⟩ := Finset.mem_image.mp hjmem
    simp only at hj'
    subst hj'
    simp only [LowerGen.offDiagSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hij, hLij⟩ := hp
    have hlt : j < i := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact absurd (hL (by simpa using h)) hLij
      · exact h
    have hmin : ∀ a b : Fin n, b < j → a ≠ b → L.val a b = 0 := by
      intro a b hb hab
      by_contra hne'
      have hbm : b ∈ cols := Finset.mem_image.mpr
        ⟨(a, b), by simp [LowerGen.offDiagSupport, hab, hne'], rfl⟩
      have := Finset.min'_le cols b hbm
      rw [← hjdef] at this
      exact absurd hb (not_lt.mpr this)
    set c : ℂ := -L.val i j / L.val j j with hc
    have hijne : i ≠ j := hij
    let U : GL (Fin n) ℂ := ⟨transvection i j c, transvection i j (-c),
      by rw [transvection_mul_transvection_same _ _ hij]; simp,
      by rw [transvection_mul_transvection_same _ _ hij]; simp⟩
    let V : GL (Fin n) ℂ := ⟨transvection i j (-c), transvection i j c,
      by rw [transvection_mul_transvection_same _ _ hij]; simp,
      by rw [transvection_mul_transvection_same _ _ hij]; simp⟩
    have hentry := LowerGen.lowerTriangular_elim_step L.val hL i j hlt (hdiag0 j) hmin
    have hUL : ∀ a b, (U * L).val a b = if a = i ∧ b = j then 0 else L.val a b := by
      intro a b; exact hentry a b
    have hlowUL : (U * L).val.BlockTriangular OrderDual.toDual := by
      intro a b hab
      rw [hUL]
      split_ifs with h
      · rfl
      · exact hL hab
    have hsupp : LowerGen.offDiagSupport (U * L).val = (LowerGen.offDiagSupport L.val).erase (i, j) := by
      ext ⟨a, b⟩
      simp only [LowerGen.offDiagSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, hUL, ne_eq, Prod.mk.injEq]
      by_cases h : a = i ∧ b = j
      · simp [h]
      · simp only [h, if_false]; tauto
    have hcard : (LowerGen.offDiagSupport (U * L).val).card < m := by
      rw [hsupp, ← hm]
      apply Finset.card_erase_lt_of_mem
      simp [LowerGen.offDiagSupport, hij, hLij]
    have hPUL : P (U * L) := ih _ hcard _ hlowUL rfl
    have hPV : P V := htr i j (-c) V hlt rfl
    have hVUL : V * (U * L) = L := by
      rw [← mul_assoc]
      have : V * U = 1 := by
        ext : 1
        show transvection i j (-c) * transvection i j c = 1
        rw [transvection_mul_transvection_same _ _ hij]; simp
      rw [this, one_mul]
    rw [← hVUL]
    exact hmul _ _ hPV hPUL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne.WD

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} [IsAlgClosure E Ω]
variable {h : IsPlaceOver A w}


variable (h) in
theorem lpDim_zero (h : IsPlaceOver A w) : lpDim (lpZero (h := h)) = 0 := by
  simp [lpZero]

theorem lpDim_sum (a b : WD h) : lpDim (lpSum a b) = lpDim a + lpDim b := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_prod]

theorem lpDim_tw (a : WD h) (s : ℝ) : lpDim (lpTw a s) = lpDim a := by
  induction a using ind
  rw [lpTw_mk, lpDim_mk, lpDim_mk]

theorem lpDim_tensor (a b : WD h) : lpDim (lpChar a b) = lpDim a * lpDim b := by
  induction a using ind
  induction b using ind
  rw [lpChar_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_tensorProduct]

theorem lpDim_char (a χ : WD h) (hχ : lpDim χ = 1) : lpDim (lpChar a χ) = lpDim a := by
  rw [lpDim_tensor, hχ, mul_one]

theorem lpSum_zero (a : WD h) : lpSum a (lpZero (h := h)) = a := by
  induction a using ind
  rw [lpZero, lpSum_mk]
  exact sound ⟨LinearEquiv.prodUnique, fun _ _ => rfl, fun _ => rfl⟩

theorem lpSum_comm (a b : WD h) : lpSum a b = lpSum b a := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpSum_mk]
  exact sound ⟨LinearEquiv.prodComm _ _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem lpSum_assoc (a b c : WD h) : lpSum (lpSum a b) c = lpSum a (lpSum b c) := by
  induction a using ind
  induction b using ind
  induction c using ind
  rw [lpSum_mk, lpSum_mk, lpSum_mk, lpSum_mk]
  exact sound ⟨LinearEquiv.prodAssoc _ _ _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem lpTw_zero (a : WD h) : lpTw a 0 = a := by
  induction a using ind
  rw [lpTw_mk]
  exact sound ⟨.refl _ _, fun σ v => by simp, fun _ => rfl⟩

theorem lpTw_add (a : WD h) (s t : ℝ) : lpTw (lpTw a s) t = lpTw a (s + t) := by
  induction a using ind
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  rw [lpTw_mk, lpTw_mk, lpTw_mk]
  refine sound ⟨.refl _ _, fun σ v => ?_, fun _ => rfl⟩
  simp only [WDRep.tw_ρ, smul_smul, LinearEquiv.refl_apply]
  rw [Complex.ofReal_add, Complex.cpow_add _ _ hq, mul_zpow, mul_comm]

theorem lpTw_sum (a b : WD h) (s : ℝ) : lpTw (lpSum a b) s = lpSum (lpTw a s) (lpTw b s) := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpTw_mk, lpTw_mk, lpTw_mk, lpSum_mk]
  exact sound ⟨.refl _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem monomial_sum_iff (a b : WD h) : mono0 (lpSum a b) ↔ mono0 a ∧ mono0 b := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N]
  refine ⟨fun h0 => ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩, fun h0 => ?_⟩
  · exact congrArg Prod.fst (LinearMap.congr_fun h0 (v, 0))
  · exact congrArg Prod.snd (LinearMap.congr_fun h0 (0, v))
  · rw [h0.1, h0.2, LinearMap.prodMap_zero]

theorem monomial_twist_iff (a : WD h) (s : ℝ) : mono0 (lpTw a s) ↔ mono0 a := by
  induction a using ind
  rw [lpTw_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tw_N]

theorem mono0_of_lpDim_eq_one {χ : WD h} (hχ : lpDim χ = 1) : mono0 χ := by
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff]
    have h1 := b.nilpotent.charpoly_eq_X_pow_finrank
    have h2 := LinearMap.aeval_self_charpoly b.N
    rwa [h1, hχ, pow_one, aeval_X] at h2

theorem monomial_char_iff (a χ : WD h) (hχ : lpDim χ = 1) : mono0 (lpChar a χ) ↔ mono0 a := by
  have h0 := mono0_of_lpDim_eq_one hχ
  induction a using ind with
  | hP m a =>
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff] at h0
    rw [lpChar_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, LinearMap.lTensor_zero, add_zero]
    refine ⟨fun h1 => LinearMap.ext fun v => ?_, fun h1 => by rw [h1, LinearMap.rTensor_zero]⟩
    let e : (Fin n → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hχ, finrank_self])
    have h2 := congrArg (fun x => TensorProduct.rid ℂ _ (e.toLinearMap.lTensor _ x))
      (LinearMap.congr_fun h1 (v ⊗ₜ e.symm 1))
    simpa using h2

theorem charPol_lpSum (a b : WD h) (σ : Weil h) :
    charPol (lpSum a b) σ = charPol a σ * charPol b σ := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, charPol_mk, charPol_mk, charPol_mk, WDRep.sum_ρ, LinearMap.charpoly_prodMap]

theorem inePol_sum (a b : WD h) (σ : G E Ω) :
    inePol (lpSum a b) σ = inePol a σ * inePol b σ := by
  by_cases hσ : σ ∈ Weil h
  · rw [inePol_of_mem _ hσ, inePol_of_mem _ hσ, inePol_of_mem _ hσ, charPol_lpSum]
  · rw [inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, mul_one]

theorem inePol_tw (a : WD h) (s : ℝ) :
    ∀ σ ∈ Ine (F := E) A, inePol (lpTw a s) σ = inePol a σ := by
  intro σ hσ
  induction a using ind
  rw [inePol_of_mem_Ine _ hσ, inePol_of_mem_Ine _ hσ, lpTw_mk, charPol_mk, charPol_mk]
  congr 1
  simp

end GlobalTheory.WeilDeligne.WD
end
end

