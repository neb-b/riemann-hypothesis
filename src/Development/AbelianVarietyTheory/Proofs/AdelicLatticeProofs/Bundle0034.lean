module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SiegelCover
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma le_two_pow_mul_of_consecutive_le {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (h : ∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) (i j : Fin N) (hij : i < j) :
    a i ≤ 2 ^ N * a j := by
  have key : ∀ d : ℕ, ∀ i j : Fin N, (j : ℕ) = i + d → a i ≤ 2 ^ d * a j := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have : i = j := Fin.ext (by simpa using hij.symm)
      subst this
      simp
    | succ d ih =>
      intro i j hij
      have hm : (i : ℕ) + d < N := by have := j.isLt; omega
      have h1 := ih i ⟨i + d, hm⟩ rfl
      have h2 := h ⟨i + d, hm⟩ j (by simp only; omega)
      calc a i ≤ 2 ^ d * a ⟨i + d, hm⟩ := h1
        _ ≤ 2 ^ d * (2 * a j) := by gcongr
        _ = 2 ^ (d + 1) * a j := by ring
  have hlt : (i : ℕ) < j := hij
  have hd := key ((j : ℕ) - i) i j (by omega)
  calc a i ≤ 2 ^ ((j : ℕ) - i) * a j := hd
    _ ≤ 2 ^ N * a j :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by have := j.isLt; omega))
        (ha j).le

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_reduced_iwasawa_decomposition {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (g : Matrix ι ι ℝ) (hg : g.det ≠ 0) :
    ∃ (γ : Matrix ι ι ℤ) (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ),
      (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧
      (∀ i j, j < i → n i j = 0) ∧ (∀ i j, |n i j| ≤ 1) ∧
      (∀ i j, i < j → a i ≤ 2 ^ Fintype.card ι * a j) ∧
      g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  set N := Fintype.card ι
  let e : Fin N ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  let f : Fin N ≃ ι := e.toEquiv
  have hmono : ∀ i j : ι, f.symm i < f.symm j ↔ i < j := by
    intro i j
    have := (e.lt_iff_lt (x := f.symm i) (y := f.symm j))
    simpa [f] using this
  obtain ⟨γ, k, a, n, hγ, hk, ha, hn1, hn0, hnb, hcons, hdec⟩ :=
    _root_.GlobalTheory.ClassFin.HermiteReduction.exists_reduced N (g.submatrix f f)
      (by rw [det_submatrix_equiv_self f g]; exact hg)
  refine ⟨γ.submatrix f.symm f.symm, k.submatrix f.symm f.symm, a ∘ f.symm,
    n.submatrix f.symm f.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]; exact hγ
  · rw [transpose_submatrix, submatrix_mul_equiv, hk, submatrix_one_equiv]
  · exact fun i => ha _
  · exact fun i => hn1 _
  · intro i j hij
    exact hn0 _ _ ((hmono j i).mpr hij)
  · intro i j
    show |n (f.symm i) (f.symm j)| ≤ 1
    rcases lt_trichotomy (f.symm i) (f.symm j) with h | h | h
    · exact (hnb _ _ h).trans (by norm_num)
    · rw [h, hn1]; simp
    · rw [hn0 _ _ h]; simp
  · intro i j hij
    exact le_two_pow_mul_of_consecutive_le a ha hcons _ _ ((hmono i j).mpr hij)
  · have hg' : g = (g.submatrix f f).submatrix f.symm f.symm := by ext i j; simp
    rw [hg', ← submatrix_map, submatrix_mul_equiv, hdec, ← submatrix_diagonal_equiv,
      submatrix_mul_equiv, submatrix_mul_equiv]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma isSiegel_of_reduced {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] {C : ℝ} {g : Matrix ι ι ℝ} {γ : Matrix ι ι ℤ} {k : Matrix ι ι ℝ}
    {a : ι → ℝ} {n : Matrix ι ι ℝ} (hC : 1 ≤ C) (hg : g.det = 1) (hγ : γ.det = 1)
    (hk : kᵀ * k = 1) (ha : ∀ i, 0 < a i) (hn1 : ∀ i, n i i = 1)
    (hn0 : ∀ i j, j < i → n i j = 0) (hnb : ∀ i j, |n i j| ≤ 1)
    (hlt : ∀ i j, i < j → a i ≤ C * a j)
    (hdec : g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n) :
    _root_.GlobalTheory.ClassFin.IsSiegel C k a n := by
  have hn : n.det = 1 := by
    rw [det_of_upperTriangular (by intro i j h; exact hn0 i j h)]
    simp [hn1]
  have hγR : (γ.map (Int.cast : ℤ → ℝ)).det = 1 := by
    rw [show γ.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix γ from rfl,
      ← RingHom.map_det, hγ]
    simp
  have hdet : k.det * ∏ i, a i = 1 := by
    have := congrArg det hdec
    rw [det_mul, det_mul, det_mul, hg, hn, det_diagonal, hγR] at this
    linarith
  have hk2 : k.det * k.det = 1 := by
    have := congrArg det hk
    rwa [det_mul, det_transpose, det_one] at this
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  have hk1 : k.det = 1 := by
    rcases mul_self_eq_one_iff.mp hk2 with h | h
    · exact h
    · exfalso
      rw [h] at hdet
      linarith
  refine ⟨hk, hk1, ha, ?_, hlt, hn1, hn0, fun i j => (hnb i j).trans hC⟩
  rw [hk1, one_mul] at hdet
  exact hdet

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_det_one_of_det_neg_one {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] {g : Matrix ι ι ℝ} {γ : Matrix ι ι ℤ} {k : Matrix ι ι ℝ} {a : ι → ℝ}
    {n : Matrix ι ι ℝ} (hγ : γ.det = -1) (hk : kᵀ * k = 1) (hn1 : ∀ i, n i i = 1)
    (hn0 : ∀ i j, j < i → n i j = 0) (hnb : ∀ i j, |n i j| ≤ 1)
    (hdec : g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n) :
    ∃ (γ' : Matrix ι ι ℤ) (k' n' : Matrix ι ι ℝ), γ'.det = 1 ∧ k'ᵀ * k' = 1 ∧
      (∀ i, n' i i = 1) ∧ (∀ i j, j < i → n' i j = 0) ∧ (∀ i j, |n' i j| ≤ 1) ∧
      g * γ'.map (Int.cast : ℤ → ℝ) = k' * diagonal a * n' := by
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [det_isEmpty] at hγ
    norm_num at hγ
  set d : ι → ℤ := fun i => if i = i₀ then -1 else 1 with hd_def
  have hd : ∀ i, (d i : ℝ) * d i = 1 := by
    intro i; simp only [hd_def]; split_ifs <;> norm_num
  have hda : ∀ i, |(d i : ℝ)| = 1 := by
    intro i; simp only [hd_def]; split_ifs <;> norm_num
  set D : Matrix ι ι ℝ := diagonal (fun i => (d i : ℝ)) with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hd i
  have hcomm : D * diagonal a = diagonal a * D := by
    rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hentry : ∀ i j, (D * n * D) i j = d i * n i j * d j := by
    intro i j
    simp [hD, mul_diagonal, diagonal_mul]
  refine ⟨γ * diagonal d, k * D, D * n * D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_mul, hγ, det_diagonal]
    have : ∏ i, d i = -1 := by
      simp [hd_def, Finset.prod_ite_eq']
    rw [this]; norm_num
  · rw [transpose_mul, hD, diagonal_transpose, ← hD, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ,
      hk, Matrix.one_mul, hDD]
  · intro i
    rw [hentry, hn1, mul_one]
    exact hd i
  · intro i j hij
    rw [hentry, hn0 i j hij]; simp
  · intro i j
    rw [hentry, abs_mul, abs_mul, hda, hda]
    simpa using hnb i j
  · have hmap : (γ * diagonal d).map (Int.cast : ℤ → ℝ) = γ.map (Int.cast) * D := by
      ext i j
      simp [hD, mul_diagonal]
    rw [hmap, ← Matrix.mul_assoc, hdec]
    calc k * diagonal a * n * D = k * (D * D) * diagonal a * n * D := by
          rw [hDD, Matrix.mul_one]
      _ = k * D * diagonal a * (D * n * D) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (diagonal a) D (n * D), ← hcomm]
          simp only [Matrix.mul_assoc]


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.siegel_cover (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] :
    ∃ C : ℝ, ∀ g : Matrix ι ι ℝ, g.det = 1 → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ ∃ k a n, _root_.GlobalTheory.ClassFin.IsSiegel C k a n ∧
      g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  refine ⟨2 ^ Fintype.card ι, fun g hg => ?_⟩
  have hC : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ (by norm_num)
  obtain ⟨γ, k, a, n, hγ, hk, ha, hn1, hn0, hnb, hlt, hdec⟩ :=
    exists_reduced_iwasawa_decomposition g (by rw [hg]; norm_num)
  rcases hγ with hγ | hγ
  · exact ⟨γ, hγ, k, a, n,
      isSiegel_of_reduced hC hg hγ hk ha hn1 hn0 hnb hlt hdec, hdec⟩
  · obtain ⟨γ', k', n', hγ', hk', hn1', hn0', hnb', hdec'⟩ :=
      exists_det_one_of_det_neg_one hγ hk hn1 hn0 hnb hdec
    exact ⟨γ', hγ', k', a, n',
      isSiegel_of_reduced hC hg hγ' hk' ha hn1' hn0' hnb' hlt hdec', hdec'⟩

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexUnitsOfIsAdicComplete
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pIdx_eq_pTor_of_finite_group (p : ℕ) {G : Type} [CommGroup G] [Finite G]
    (U : Subgroup G) : pTor p U ≠ 0 ∧ pIdx p U = pTor p U := by
  have h1 : pTor p U = Nat.card (powMonoidHom p : U →* U).ker := by
    unfold pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        invFun := fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : pIdx p U = (powMonoidHom p : U →* U).range.index := by
    unfold pIdx pows Subgroup.relIndex
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext h⟩
    · rintro ⟨y, h⟩
      exact ⟨y.1, y.2, congrArg Subtype.val h⟩
  have h3 := (powMonoidHom p : U →* U).range.card_mul_index
  have h4 := (powMonoidHom p : U →* U).ker.card_mul_index
  rw [Subgroup.index_ker] at h4
  have h5 : Nat.card (powMonoidHom p : U →* U).range ≠ 0 := Nat.card_pos.ne'
  refine ⟨h1 ▸ Nat.card_pos.ne', ?_⟩
  rw [h1, h2]
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5)
  rw [h3, ← h4, mul_comm]

theorem pIdx_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  intro p O _ _ _ π hp hπ hc hfin
  haveI : Finite (O ⧸ Ideal.span {(p : O) * π}) := Nat.finite_of_card_ne_zero hfin
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  obtain ⟨hd1, hd2⟩ := _root_.GlobalTheory.CNorm.deep_units_pows p O π hp hπ hc
  have hle : Ideal.span {(p : O) * π} ≤ Ideal.span {π} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro_left _ rfl)
  have hle' : Ideal.span {(p : O) * π} ≤ Ideal.span {(p : O)} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro _ rfl)
  have hs := _root_.GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient O ((p : O) * π) p (mul_ne_zero hp0 hπ) (Dvd.intro _ rfl)
    (hle.trans (IsAdicComplete.le_jacobson_bot _))
  have hk : pIdx p (oneUnits ((p : O) * π)) = Nat.card (O ⧸ Ideal.span {(p : O)}) := by
    unfold pIdx
    rw [hd1, ← hs, sq, mul_assoc]
  haveI : Finite (O ⧸ Ideal.span {(p : O)}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle')
  have hk0 : Nat.card (O ⧸ Ideal.span {(p : O)}) ≠ 0 := Nat.card_pos.ne'
  let g : Oˣ →* (O ⧸ Ideal.span {(p : O) * π})ˣ :=
    Units.map (Ideal.Quotient.mk (Ideal.span {(p : O) * π}) : O →* O ⧸ Ideal.span {(p : O) * π})
  have hker : g.ker = oneUnits ((p : O) * π) := rfl
  obtain ⟨hr1, hr2⟩ := pIdx_eq_pTor_of_finite_group p g.range
  obtain ⟨-, h2, h3⟩ := _root_.GlobalTheory.CNorm.pIdx_pTor_ker_range p _ _ g (by rw [hker, hk]; exact hk0)
    (by rw [hker, hd2]; exact one_ne_zero) (by rw [hr2]; exact hr1) hr1
  refine ⟨h2, ?_⟩
  rw [hker, hd2, hk, hr2, mul_one, mul_right_comm] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr1) h3

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorActionHermitianExpFixedOfMinNorm
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.act_exp_eq_of_isMinVec : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (U : Matrix ι ι ℂ) (δ : ι → ℝ), _root_.GlobalTheory.ClassFin.IsMinVec d v → U * Uᴴ = 1 → ∑ i, δ i = 0 → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (δ i) : ℂ)) * Uᴴ)) = _root_.GlobalTheory.ClassFin.nsq v → ∀ s : ℝ, _root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (s * δ i) : ℂ)) * Uᴴ) = v := by
  intro ι _ _ m d v U δ hmin hU hδ hone s
  obtain ⟨act1, actmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  have hUH : Uᴴ * Uᴴᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have hnormU := (_root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity ι m d).1
  set u := _root_.GlobalTheory.ClassFin.act d v U with hu
  set lam : _root_.GlobalTheory.ClassFin.TIdx ι d → ℝ := fun k => ∑ j, δ (k.2 j) with hlam
  have hdiag : ∀ r : ℝ,
      _root_.GlobalTheory.ClassFin.act d u (diagonal fun i => (Real.exp (r * δ i) : ℂ)) =
        fun k => u k * (Real.exp (r * lam k) : ℂ) := by
    intro r
    funext k
    rw [((_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d u).2.2.1]
    simp only [hlam, Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod]
  have hsplit : ∀ r : ℝ,
      _root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ) =
        _root_.GlobalTheory.ClassFin.act d (fun k => u k * (Real.exp (r * lam k) : ℂ)) Uᴴ := by
    intro r
    rw [actmul, actmul, hdiag]
  have hF : ∀ r : ℝ, _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v
      (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ)) =
        ∑ k, ‖u k‖ ^ 2 * Real.exp (r * lam k) ^ 2 := by
    intro r
    rw [hsplit, hnormU _ _ hUH]
    unfold _root_.GlobalTheory.ClassFin.nsq
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
  have hdet : ∀ r : ℝ, (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ).det = 1 := by
    intro r
    have h1 : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
    rw [det_mul, det_mul, det_diagonal, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum,
      hδ, mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one, h1]
  have hmin' : ∀ r : ℝ, _root_.GlobalTheory.ClassFin.nsq v ≤ ∑ k, ‖u k‖ ^ 2 * Real.exp (r * lam k) ^ 2 := by
    intro r
    rw [← hF r]
    exact hmin _ ⟨_, hdet r, rfl⟩
  have h0 : ∑ k, ‖u k‖ ^ 2 * Real.exp (0 * lam k) ^ 2 = _root_.GlobalTheory.ClassFin.nsq v := by
    simp only [zero_mul, Real.exp_zero, one_pow, mul_one]
    exact hnormU v U hU
  have h1 : ∑ k, ‖u k‖ ^ 2 * Real.exp (1 * lam k) ^ 2 = _root_.GlobalTheory.ClassFin.nsq v := by
    rw [← hF 1]
    simpa only [one_mul] using hone
  have hhalf := hmin' (1 / 2)
  have hsq : ∀ k, Real.exp (1 * lam k) ^ 2 = (Real.exp (1 / 2 * lam k) ^ 2) ^ 2 := by
    intro k
    have e : Real.exp (1 * lam k) = Real.exp (1 / 2 * lam k) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [e]
  have hterm : ∀ k ∈ Finset.univ, 0 ≤ ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 :=
    fun k _ => by positivity
  have hsum : ∑ k, ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 = 0 := by
    have e : ∑ k, ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 =
        ∑ k, ‖u k‖ ^ 2 * Real.exp (1 * lam k) ^ 2 + ∑ k, ‖u k‖ ^ 2 * Real.exp (0 * lam k) ^ 2
          - 2 * ∑ k, ‖u k‖ ^ 2 * Real.exp (1 / 2 * lam k) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsq]
      simp only [zero_mul, Real.exp_zero]
      ring
    refine le_antisymm ?_ (Finset.sum_nonneg hterm)
    rw [e, h0, h1]
    linarith
  have hfix : ∀ k, u k * (Real.exp (s * lam k) : ℂ) = u k := by
    intro k
    have hk := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum k (Finset.mem_univ k)
    rcases mul_eq_zero.mp hk with ha | hb
    · have hz : u k = 0 := by simpa using ha
      simp [hz]
    · have ht : Real.exp (1 / 2 * lam k) ^ 2 = 1 := by
        have := (pow_eq_zero_iff (n := 2) two_ne_zero).mp hb
        linarith
      have hl : lam k = 0 := by
        rw [← Real.exp_nat_mul] at ht
        simpa using (Real.exp_eq_one_iff _).mp ht
      simp [hl]
  rw [hsplit s]
  simp only [hfix]
  rw [← actmul, hU, act1]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardPlacesLeCardOverQuadratic
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_mul_card_le_card_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → 2 * S.card ≤ SE.card + tFin F δ S := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hSE
  classical
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tFin F δ S
      = ∑ v ∈ S, if ¬ IsSquare (algebraMap F (v.adicCompletion F) δ) then 1 else 0 := by
    rw [← Finset.card_filter, tFin, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) δ)
  · obtain ⟨w, w', hne, hw, hw'⟩ := _root_.GlobalTheory.QNorm.two_places_of_isSquare F E δ θ σ hq v hs
    have : 1 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.one_lt_card.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩,
        w', Finset.mem_filter.2 ⟨(hSE w').2 (hw' ▸ hv), hw'⟩, hne⟩
    omega
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPlacesOfEmbeddings
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem two_places_of_embeddings : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (ψ ψ' : E →ₐ[F] v.adicCompletion F), ψ ≠ ψ' → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  intro F E _ _ _ _ _ v ψ ψ' hne
  let V : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  let u : Valuation E ℤᵐ⁰ := V.comap (ψ : E →+* v.adicCompletion F)
  let u' : Valuation E ℤᵐ⁰ := V.comap (ψ' : E →+* v.adicCompletion F)
  have hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ _) = _
    rw [AlgHom.commutes]
    exact v.valuedAdicCompletion_eq_valuation' a
  have hu' : ∀ a : F, u' (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ' _) = _
    rw [AlgHom.commutes]
    exact v.valuedAdicCompletion_eq_valuation' a
  obtain ⟨w, hw, hwm⟩ := exists_centre_over v u hu
  obtain ⟨w', hw', hwm'⟩ := exists_centre_over v u' hu'
  refine ⟨w, w', ?_, hw, hw'⟩
  rintro rfl
  obtain ⟨z, hz⟩ : ∃ z, ψ z ≠ ψ' z := by
    by_contra hc
    push Not at hc
    exact hne (AlgHom.ext hc)
  obtain ⟨d, hd⟩ : ∃ d, d = ψ z - ψ' z := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by rw [hd]; exact sub_ne_zero.2 hz
  have hVd : V d ≠ 0 := (Valuation.ne_zero_iff _).2 hd0
  obtain ⟨ρ, hρ⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    (ψ z) d⁻¹
  obtain ⟨c, hc⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    d d⁻¹
  set t := (ψ z - algebraMap F (v.adicCompletion F) ρ) * d⁻¹ with ht
  set s := (d - algebraMap F (v.adicCompletion F) c) * d⁻¹ with hs
  have e1 : ψ z - algebraMap F (v.adicCompletion F) ρ = d * t := by
    rw [ht]; field_simp
  have e2 : ψ' z - algebraMap F (v.adicCompletion F) ρ = -(d * (1 - t)) := by
    linear_combination e1 + hd
  have e3 : algebraMap F (v.adicCompletion F) c = d * (1 - s) := by
    rw [hs]; field_simp; ring
  obtain ⟨y, hy⟩ : ∃ y, y = (z - algebraMap F E ρ) / algebraMap F E c := ⟨_, rfl⟩
  have huy : u y < 1 := by
    change V (ψ y) < 1
    rw [hy, map_div₀, map_sub, AlgHom.commutes, AlgHom.commutes, e1, e3, map_div₀,
      map_mul _ _ t, map_mul _ _ (1 - s), Valuation.map_one_sub_of_lt _ hc, mul_one,
      mul_div_cancel_left₀ _ hVd]
    exact hρ
  have huy' : u' y = 1 := by
    change V (ψ' y) = 1
    rw [hy, map_div₀, map_sub, AlgHom.commutes, AlgHom.commutes, e2, e3, map_div₀,
      Valuation.map_neg, map_mul _ _ (1 - t), map_mul _ _ (1 - s),
      Valuation.map_one_sub_of_lt _ hc, Valuation.map_one_sub_of_lt _ hρ, div_self]
    rwa [mul_one]
  obtain ⟨n, ⟨m, hm⟩, hnd | hnd⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
  · have hd1 : 1 ≤ u' (algebraMap (𝓞 E) E m) := not_lt.1 fun a => hm ((hwm' m).2 a)
    have h1 : u (algebraMap (𝓞 E) E n) < 1 := by
      rw [← hnd, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u m)) huy
    have h2 := (hwm' n).1 ((hwm n).2 h1)
    rw [← hnd, map_mul, huy', one_mul] at h2
    exact absurd h2 (not_lt.2 hd1)
  · have hd1 : 1 ≤ u (algebraMap (𝓞 E) E m) := not_lt.1 fun a => hm ((hwm m).2 a)
    rw [← hnd, map_mul] at hd1
    exact absurd (lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u n)) huy)
      (not_lt.2 hd1)

end GlobalTheory.CNorm
end

