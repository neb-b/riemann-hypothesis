module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0176
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQContinuousCharacterEqDetPowProd
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.UpqChar

theorem det_conj_rect {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ ℂ) (B' : Matrix κ ι ℂ) (h1 : B * B' = 1) (h2 : B' * B = 1)
    (M : Matrix κ κ ℂ) : (B * M * B').det = M.det := by
  classical
  have hcard : Fintype.card κ = Fintype.card ι := by
    let e : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
      { toFun := fun v => B *ᵥ v
        invFun := fun v => B' *ᵥ v
        map_add' := fun v w => Matrix.mulVec_add B v w
        map_smul' := fun a v => by simp [Matrix.mulVec_smul]
        left_inv := fun v => by simp [Matrix.mulVec_mulVec, h2]
        right_inv := fun v => by simp [Matrix.mulVec_mulVec, h1] }
    simpa using e.finrank_eq
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard.symm
  have hC : B.submatrix id e * B'.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_id_id]
  have hM : B * M * B' = B.submatrix id e * M.submatrix e e * B'.submatrix e id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hd : (B.submatrix id e).det * (B'.submatrix e id).det = 1 := by
    rw [← Matrix.det_mul, hC, Matrix.det_one]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  calc (B.submatrix id e).det * M.det * (B'.submatrix e id).det
      = ((B.submatrix id e).det * (B'.submatrix e id).det) * M.det := by ring
    _ = M.det := by rw [hd, one_mul]

theorem char_unitary {p : ℕ} (f : Matrix.unitaryGroup (Fin p) ℂ → ℂ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hn : ∀ a, ‖f a‖ = 1) (hc : Continuous f) :
    ∃ x : ℤ, ∀ a, f a = (Matrix.det (a : Matrix (Fin p) (Fin p) ℂ)) ^ x := by
  have hone : f 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have hne : f 1 ≠ 0 := fun h0 => by simpa [h0] using hn 1
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact h.symm)
  have hmem : ∀ a, f a ∈ Submonoid.unitSphere ℂ := fun a => mem_sphere_zero_iff_norm.2 (hn a)
  let c : Matrix.unitaryGroup (Fin p) ℂ →* Circle :=
    { toFun := fun a => ⟨f a, hmem a⟩
      map_one' := Circle.ext hone
      map_mul' := fun a b => Circle.ext (hmul a b) }
  have hcont : Continuous c := Continuous.subtype_mk hc hmem
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.UnitaryChar.char_eq_det_zpow p c hcont
  exact ⟨m, fun a => hm a⟩

private theorem matrix_eq_zero_of_eq_neg {ι κ : Type} (X : Matrix ι κ ℂ) (h : X = -X) : X = 0 := by
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.neg_apply] at h'
  simp only [Matrix.zero_apply]
  linear_combination h' / 2

theorem char_Upq : ∀ (n p q : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 → B' * B = 1 → Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) → s * B = B * Matrix.fromBlocks 1 0 0 (-1) → ∀ c : Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ k k' : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → k'ᴴ * G * k' = G → s * k' = k' * s → c (k * k') = c k * c k') → (∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → ‖c k‖ = 1) → ContinuousOn c {k | kᴴ * G * k = G ∧ s * k = k * s} → ∃ x y : ℤ, ∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → c k = ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det ^ x * ((1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s)).det ^ y := by
  intro n p q G s B B' hBB' hB'B hG hs c hmul hnorm hcont
  classical
  obtain ⟨J, hJdef⟩ : ∃ J : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, J = Matrix.fromBlocks 1 0 0 (-1) :=
    ⟨_, rfl⟩
  rw [← hJdef] at hG hs
  replace hs : s * B = B * J := hs
  replace hG : Bᴴ * G * B = J := hG
  replace hBB' : B * B' = 1 := hBB'
  replace hB'B : B' * B = 1 := hB'B
  have hconj : ∀ X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ,
      (B * X * B') * (B * Y * B') = B * (X * Y) * B' := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B' B, hB'B, Matrix.one_mul]
  have hsJ : s = B * J * B' := by
    rw [← hs, Matrix.mul_assoc, hBB', Matrix.mul_one]
  have hGJ : G = B'ᴴ * J * B' := by
    rw [← hG]
    have h0 : (B * B')ᴴ = 1 := by rw [hBB', Matrix.conjTranspose_one]
    rw [Matrix.conjTranspose_mul] at h0
    calc G = (B'ᴴ * Bᴴ) * G * (B * B') := by rw [h0, hBB', Matrix.one_mul, Matrix.mul_one]
      _ = B'ᴴ * (Bᴴ * G * B) * B' := by simp only [Matrix.mul_assoc]
  have hK : ∀ (a : Matrix (Fin p) (Fin p) ℂ) (d : Matrix (Fin q) (Fin q) ℂ), aᴴ * a = 1 → dᴴ * d = 1 →
      (B * Matrix.fromBlocks a 0 0 d * B')ᴴ * G * (B * Matrix.fromBlocks a 0 0 d * B') = G ∧
      s * (B * Matrix.fromBlocks a 0 0 d * B') = (B * Matrix.fromBlocks a 0 0 d * B') * s := by
    intro a d ha hd
    constructor
    · have hm : (Matrix.fromBlocks a 0 0 d)ᴴ * J * Matrix.fromBlocks a 0 0 d = J := by
        rw [hJdef, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
        simp [ha, hd]
      calc (B * Matrix.fromBlocks a 0 0 d * B')ᴴ * G * (B * Matrix.fromBlocks a 0 0 d * B')
          = B'ᴴ * ((Matrix.fromBlocks a 0 0 d)ᴴ * (Bᴴ * G * B) * Matrix.fromBlocks a 0 0 d) * B' := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = G := by rw [hG, hm, ← hGJ]
    · rw [hsJ, hconj, hconj, hJdef, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp
  let kA : Matrix.unitaryGroup (Fin p) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun a => B * (Matrix.fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B'
  let kD : Matrix.unitaryGroup (Fin q) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun d => B * (Matrix.fromBlocks 1 0 0 (d : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B'
  have hKA : ∀ a : Matrix.unitaryGroup (Fin p) ℂ, (kA a)ᴴ * G * kA a = G ∧ s * kA a = kA a * s := by
    intro a
    refine hK _ _ ?_ (by simp)
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 a.2
  have hKD : ∀ d : Matrix.unitaryGroup (Fin q) ℂ, (kD d)ᴴ * G * kD d = G ∧ s * kD d = kD d * s := by
    intro d
    refine hK _ _ (by simp) ?_
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 d.2
  have hkAmul : ∀ a b : Matrix.unitaryGroup (Fin p) ℂ, kA (a * b) = kA a * kA b := by
    intro a b
    show B * (Matrix.fromBlocks ((a * b : Matrix.unitaryGroup (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' =
      (B * (Matrix.fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B') *
        (B * (Matrix.fromBlocks (b : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    rw [hconj, Matrix.fromBlocks_multiply]
    simp
  have hkDmul : ∀ a b : Matrix.unitaryGroup (Fin q) ℂ, kD (a * b) = kD a * kD b := by
    intro a b
    show B * (Matrix.fromBlocks 1 0 0 ((a * b : Matrix.unitaryGroup (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' =
      (B * (Matrix.fromBlocks 1 0 0 (a : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B') *
        (B * (Matrix.fromBlocks 1 0 0 (b : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    rw [hconj, Matrix.fromBlocks_multiply]
    simp
  have hkAc : Continuous kA := by
    show Continuous (fun a : Matrix.unitaryGroup (Fin p) ℂ =>
      B * (Matrix.fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    fun_prop
  have hkDc : Continuous kD := by
    show Continuous (fun d : Matrix.unitaryGroup (Fin q) ℂ =>
      B * (Matrix.fromBlocks 1 0 0 (d : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    fun_prop
  obtain ⟨x, hx⟩ := char_unitary (fun a => c (kA a))
    (fun a b => by
      show c (kA (a * b)) = c (kA a) * c (kA b)
      rw [hkAmul]
      exact hmul _ _ (hKA a).1 (hKA a).2 (hKA b).1 (hKA b).2)
    (fun a => hnorm _ (hKA a).1 (hKA a).2) (hcont.comp_continuous hkAc hKA)
  obtain ⟨y, hy⟩ := char_unitary (fun d => c (kD d))
    (fun a b => by
      show c (kD (a * b)) = c (kD a) * c (kD b)
      rw [hkDmul]
      exact hmul _ _ (hKD a).1 (hKD a).2 (hKD b).1 (hKD b).2)
    (fun d => hnorm _ (hKD d).1 (hKD d).2) (hcont.comp_continuous hkDc hKD)
  have hx' : ∀ a : Matrix.unitaryGroup (Fin p) ℂ, c (kA a) = (a : Matrix (Fin p) (Fin p) ℂ).det ^ x := hx
  have hy' : ∀ d : Matrix.unitaryGroup (Fin q) ℂ, c (kD d) = (d : Matrix (Fin q) (Fin q) ℂ).det ^ y := hy
  refine ⟨x, y, fun k hk1 hk2 => ?_⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = B' * k * B := ⟨_, rfl⟩
  have hk_eq : k = B * m * B' := by
    calc k = (B * B') * k * (B * B') := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
      _ = B * m * B' := by simp only [hmdef, Matrix.mul_assoc]
  have hJm : J * m = m * J := by
    have hJ : J = B' * s * B := by
      rw [Matrix.mul_assoc, hs, ← Matrix.mul_assoc, hB'B, Matrix.one_mul]
    rw [hJ, hmdef]
    calc B' * s * B * (B' * k * B) = B' * (s * k) * B := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc B B', hBB', Matrix.one_mul]
      _ = B' * (k * s) * B := by rw [hk2]
      _ = B' * k * B * (B' * s * B) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc B B', hBB', Matrix.one_mul]
  have hoff : m.toBlocks₁₂ = 0 ∧ m.toBlocks₂₁ = 0 := by
    have h := hJm
    rw [hJdef, ← Matrix.fromBlocks_toBlocks m, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at h
    obtain ⟨-, hb, hc, -⟩ := h
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add,
      Matrix.neg_mul, Matrix.mul_neg] at hb hc
    exact ⟨matrix_eq_zero_of_eq_neg _ hb, matrix_eq_zero_of_eq_neg _ hc.symm⟩
  obtain ⟨a, d, hmad⟩ : ∃ a d, m = Matrix.fromBlocks a 0 0 d :=
    ⟨m.toBlocks₁₁, m.toBlocks₂₂, by rw [← hoff.1, ← hoff.2, Matrix.fromBlocks_toBlocks]⟩
  have hmU : mᴴ * J * m = J := by
    rw [← hG, hmdef]
    calc (B' * k * B)ᴴ * (Bᴴ * G * B) * (B' * k * B)
        = Bᴴ * (kᴴ * ((B * B')ᴴ * G * (B * B')) * k) * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * G * B := by rw [hBB', Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hk1]
  rw [hmad, hJdef, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hmU
  obtain ⟨ha, -, -, hd⟩ := hmU
  simp only [Matrix.conjTranspose_zero, Matrix.mul_one, Matrix.mul_zero,
    add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_inj] at ha hd
  have ha' : a ∈ Matrix.unitaryGroup (Fin p) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (by rw [Matrix.star_eq_conjTranspose]; exact ha)
  have hd' : d ∈ Matrix.unitaryGroup (Fin q) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (by rw [Matrix.star_eq_conjTranspose]; exact hd)
  have hkAD : k = kA ⟨a, ha'⟩ * kD ⟨d, hd'⟩ := by
    rw [hk_eq, hmad]
    show B * Matrix.fromBlocks a 0 0 d * B' =
      (B * (Matrix.fromBlocks a 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B') * (B * (Matrix.fromBlocks 1 0 0 d : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    rw [hconj, Matrix.fromBlocks_multiply]
    simp
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = B * (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by rw [Matrix.mul_one, hBB']
  have hJ1 : (1 / 2 : ℂ) • (1 + J) = (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    rw [hJdef]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> (try split_ifs) <;> norm_num
  have hJ2 : (1 / 2 : ℂ) • (1 - J) = (Matrix.fromBlocks 0 0 0 (1 : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    rw [hJdef]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> (try split_ifs) <;> norm_num
  have hP1 : (1 / 2 : ℂ) • (1 + s) = B * (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [← hJ1, hsJ, h1, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]
  have hP2 : (1 / 2 : ℂ) • (1 - s) = B * (Matrix.fromBlocks 0 0 0 (1 : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [← hJ2, hsJ, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul]
  have hE1 : (1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s) = B * (Matrix.fromBlocks a 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [hP1, hP2, hk_eq, hmad, hconj, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_add]
    simp
  have hE2 : (1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s) = B * (Matrix.fromBlocks 1 0 0 d : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [hP1, hP2, hk_eq, hmad, hconj, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_add]
    simp
  rw [hE1, hE2, det_conj_rect B B' hBB' hB'B, det_conj_rect B B' hBB' hB'B,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one,
    one_mul, hkAD, hmul _ _ (hKA _).1 (hKA _).2 (hKD _).1 (hKD _).2, hx', hy']

end GlobalTheory.UpqChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassConstantQExpansion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem weierstrass_constant_eq_E2 (τ : ℍ) : gN τ = (-1 / 12) * EisensteinSeries.E2 τ := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [gN, EisensteinSeries.E2, Pi.smul_apply, smul_eq_mul, riemannZeta_two, mul_pow, Complex.I_sq]
  field_simp
  ring

theorem hasQ_gN : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by
  intro N _ τ
  have hN : N ≠ 0 := NeZero.ne N
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hinj : Function.Injective (fun m : ℕ => N * m) := fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h
  rw [← hinj.hasSum_iff]
  · have h := (EisensteinSeries.hasSum_qExpansion_E2 (z := τ)).mul_left (-1 / 12 : ℂ)
    rw [weierstrass_constant_eq_E2]
    convert! h using 1
    funext m
    have he : Complex.exp (2 * Real.pi * Complex.I * ((N * m : ℕ) : ℂ) * τ / N) =
        Complex.exp (2 * Real.pi * Complex.I * τ) ^ m := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
    simp only [Function.comp, he, smul_eq_mul]
    by_cases hm : m = 0
    · simp [hm, cG]
    · have h1 : N * m ≠ 0 := mul_ne_zero hN hm
      simp only [cG, if_neg h1, if_neg hm, if_pos (dvd_mul_right N m),
        Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hN)]
      ring
  · intro k hk
    have hd : ¬ N ∣ k := fun ⟨m, hm⟩ => hk ⟨m, hm.symm⟩
    have h0 : k ≠ 0 := fun h => hd (h ▸ dvd_zero N)
    simp [cG, hd, h0]

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPAddSubWeierstrassPSub
section
namespace GlobalTheory

theorem weierstrassP_add_sub_weierstrassP_sub (L : PeriodPair) (z w : ℂ) (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h₁ : z - w ∉ L.lattice) (h₂ : z + w ∉ L.lattice) :
    (L.weierstrassP z - L.weierstrassP w) ^ 2 *
        (L.weierstrassP (z + w) - L.weierstrassP (z - w)) =
      -(L.derivWeierstrassP z * L.derivWeierstrassP w) := by
  have hne : L.weierstrassP z ≠ L.weierstrassP w := by
    rw [Ne, weierstrassP_eq_iff L hz hw]; tauto
  have e1 := (weierstrassP_add L hz hw hne).1
  have e2 := (weierstrassP_add L (w := -w) hz (by simpa using hw) (by simpa using hne)).1
  rw [← sub_eq_add_neg, L.weierstrassP_neg, L.derivWeierstrassP_neg] at e2
  have hd : L.weierstrassP z - L.weierstrassP w ≠ 0 := sub_ne_zero.mpr hne
  rw [e1, e2]
  field_simp
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTwoMulMulSq
section
open PeriodPair WeierstrassCurve

namespace GlobalTheory

theorem weierstrassP_two_mul_mul_sq (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice)
    (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 =
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 -
        2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  rw [two_mul z] at h2 ⊢
  have hd : L.derivWeierstrassP z ≠ 0 := (derivWeierstrassP_eq_zero_iff L hz).not.mpr h2
  have hy : L.derivWeierstrassP z / 2 ≠
      (latticeCurve L).toAffine.negY (L.weierstrassP z) (L.derivWeierstrassP z / 2) := by
    intro h
    apply hd
    simp only [Affine.negY, latticeCurve] at h
    linear_combination h
  have h := latticePoint_add L z z
  rw [latticePoint_of_notMem L hz, latticePoint_of_notMem L h2,
    Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq] at h
  have e := h.1
  rw [Affine.slope_of_Y_ne rfl hy] at e
  simp only [Affine.negY, Affine.addX, latticeCurve] at e
  have e2 : L.derivWeierstrassP z / 2 -
      (-(L.derivWeierstrassP z / 2) - 0 * L.weierstrassP z - 0) = L.derivWeierstrassP z := by ring
  rw [e2] at e
  rw [e]
  field_simp
  ring

end GlobalTheory
end

