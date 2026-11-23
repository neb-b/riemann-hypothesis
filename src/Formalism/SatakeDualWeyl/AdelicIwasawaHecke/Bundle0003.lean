module

public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
section
open Matrix

namespace Formalism.UG.P

open Formalism.UG

theorem cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply]

section Sig

variable {n : Type} [Fintype n] [DecidableEq n]

theorem sig_data (J : Matrix n n ℂ) (p q : ℕ) (h : HasSignature J p q) :
    Fintype.card n = p + q ∧ ∃ Q : Matrix n (Fin p ⊕ Fin q) ℂ, Qᴴ * J * Q = Jpq p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin], ?_⟩
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e id, ?_⟩
  rw [cT_conj_eq] at hP

  have hJ : J = (J.reindex e e).submatrix e e := by
    ext i j; simp
  rw [hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]
  exact hP

theorem sig_quad {p q : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (x : Fin p ⊕ Fin q → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) =
      (∑ i, star (x (Sum.inl i)) * x (Sum.inl i)) - ∑ j, star (x (Sum.inr j)) * x (Sum.inr j) := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hQ, ← Matrix.dotProduct_mulVec]
  simp [Jpq, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg,
    Matrix.neg_mulVec, Finset.sum_neg_distrib]

private lemma eq_zero_of_sum_star_mul_self_add_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℂ) (b : κ → ℂ)
    (h : (∑ i, star (a i) * a i) + ∑ j, star (b j) * b j = 0) : a = 0 ∧ b = 0 := by
  have hz : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [hz] at h
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_add, Complex.ofReal_eq_zero] at h
  have h1 : 0 ≤ ∑ i, Complex.normSq (a i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h2 : 0 ≤ ∑ j, Complex.normSq (b j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hA : ∑ i, Complex.normSq (a i) = 0 := by linarith
  have hB : ∑ j, Complex.normSq (b j) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _] at hA hB
  exact ⟨funext fun i => Complex.normSq_eq_zero.1 (hA i (Finset.mem_univ _)),
    funext fun j => Complex.normSq_eq_zero.1 (hB j (Finset.mem_univ _))⟩

theorem sig_dim {p q p' q' : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (Q' : Matrix n (Fin p' ⊕ Fin q') ℂ)
    (hQ' : Q'ᴴ * J * Q' = Jpq p' q') :
    p + q' ≤ Fintype.card n := by
  classical

  let φ : ((Fin p → ℂ) × (Fin q' → ℂ)) →ₗ[ℂ] (n → ℂ) :=
    { toFun := fun ab => Q *ᵥ Sum.elim ab.1 (0 : Fin q → ℂ) + Q' *ᵥ Sum.elim (0 : Fin p' → ℂ) ab.2
      map_add' := by
        intro x y
        have h1 : Sum.elim (x.1 + y.1) (0 : Fin q → ℂ) = Sum.elim x.1 (0 : Fin q → ℂ) + Sum.elim y.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (x.2 + y.2) = Sum.elim (0 : Fin p' → ℂ) x.2 + Sum.elim (0 : Fin p' → ℂ) y.2 := by
          ext (i | i) <;> simp
        simp only [Prod.fst_add, Prod.snd_add, h1, h2, Matrix.mulVec_add]
        abel
      map_smul' := by
        intro c x
        have h1 : Sum.elim (c • x.1) (0 : Fin q → ℂ) = c • Sum.elim x.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (c • x.2) = c • Sum.elim (0 : Fin p' → ℂ) x.2 := by
          ext (i | i) <;> simp
        simp only [Prod.smul_fst, Prod.smul_snd, h1, h2, Matrix.mulVec_smul, RingHom.id_apply,
          smul_add] }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hw : Q *ᵥ Sum.elim a (0 : Fin q → ℂ) = Q' *ᵥ (-(Sum.elim (0 : Fin p' → ℂ) b)) := by
      rw [Matrix.mulVec_neg]
      exact eq_neg_of_add_eq_zero_left hab
    have e1 := sig_quad J Q hQ (Sum.elim a (0 : Fin q → ℂ))
    have e2 := sig_quad J Q' hQ' (-(Sum.elim (0 : Fin p' → ℂ) b))
    rw [← hw, e1] at e2
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Pi.neg_apply, star_zero, mul_zero,
      Finset.sum_const_zero, sub_zero, zero_sub, star_neg, neg_mul_neg] at e2
    have := eq_zero_of_sum_star_mul_self_add_eq_zero a b (by rw [e2]; ring)
    rw [this.1, this.2]
    rfl
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun,
    Module.finrank_fintype_fun_eq_card] at this

end Sig

theorem signature_unique : Formalism.UG.SigUnique := by
  intro n _ _ J p q p' q' h h'
  obtain ⟨hc, Q, hQ⟩ := sig_data J p q h
  obtain ⟨hc', Q', hQ'⟩ := sig_data J p' q' h'
  have d1 := sig_dim J Q hQ Q' hQ'
  have d2 := sig_dim J Q' hQ' Q hQ
  omega

end Formalism.UG.P
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
section
namespace Formalism.UG.P

open Matrix

theorem sigex_cT_conj_eq {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  first
    | rfl
    | (ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply])

noncomputable def scal {n : Type} (ev : n → ℝ) : n → ℂ := fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)

theorem star_scal {n : Type} (ev : n → ℝ) : star (scal ev) = scal ev := by
  funext i
  simp only [Pi.star_apply, scal]
  exact Complex.conj_ofReal _

theorem scal_sq {n : Type} (ev : n → ℝ) (i : n) :
    scal ev i * (ev i : ℂ) * scal ev i = ((ev i / |ev i| : ℝ) : ℂ) := by
  have key : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = ev i / |ev i| := by
    set t := Real.sqrt |ev i| with ht
    have hs : t * t = |ev i| := Real.mul_self_sqrt (abs_nonneg _)
    rw [div_eq_mul_inv, ← hs]
    ring
  simp only [scal]
  rw [← key]
  push_cast
  ring

theorem herm_diag {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) :
    ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues))ᴴ * J *
        ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues)) =
      diagonal (fun i => ((hJ.eigenvalues i / |hJ.eigenvalues i| : ℝ) : ℂ)) := by
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_scal]
  have hU : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hJ.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hJ.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  have key : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J * (hJ.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (RCLike.ofReal ∘ hJ.eigenvalues) := by
    have h1 := congrArg (fun M => ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * M *
      (hJ.eigenvectorUnitary : Matrix n n ℂ)) hJ.spectral_theorem
    first
      | simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h1
      | simp only [Unitary.conjStarAlgAut, Matrix.star_eq_conjTranspose] at h1
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  calc _ = diagonal (scal hJ.eigenvalues) * (((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J *
          (hJ.eigenvectorUnitary : Matrix n n ℂ)) * diagonal (scal hJ.eigenvalues) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [key, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        exact scal_sq _ i

theorem eig_ne_zero {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hdet : IsUnit J.det) (i : n) : hJ.eigenvalues i ≠ 0 := by
  intro h0
  apply hdet.ne_zero
  rw [hJ.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])

theorem sign_pos {x : ℝ} (h : 0 < x) : x / |x| = 1 := by
  rw [abs_of_pos h, div_self h.ne']

theorem sign_neg {x : ℝ} (h : x < 0) : x / |x| = -1 := by
  rw [abs_of_neg h, div_neg, div_self h.ne]

theorem signature_exists : Formalism.UG.SigExists := by
  unfold Formalism.UG.SigExists
  intro n _ _ J hJ hdet
  unfold Formalism.UG.IsHerm at hJ
  unfold Formalism.UG.HasSignature
  unfold Formalism.UG.Jpq
  have hH : J.IsHermitian := (sigex_cT_conj_eq J).symm.trans hJ
  have hU : ((hH.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix n n ℂ,
      Q = (hH.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hH.eigenvalues) := ⟨_, rfl⟩
  have hQ : Qᴴ * J * Q = diagonal (fun i => ((hH.eigenvalues i / |hH.eigenvalues i| : ℝ) : ℂ)) := by
    rw [hQdef]
    exact herm_diag hH
  obtain ⟨e, he⟩ : ∃ e : n ≃ Fin (Fintype.card {i // 0 < hH.eigenvalues i}) ⊕
      Fin (Fintype.card {i // ¬ 0 < hH.eigenvalues i}),
      e = (Equiv.sumCompl (fun i => 0 < hH.eigenvalues i)).symm.trans
        (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)) := ⟨_, rfl⟩
  have hinl : ∀ a, e.symm (Sum.inl a) =
      ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hinr : ∀ a, e.symm (Sum.inr a) =
      ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hdetQ : IsUnit (reindex e e Q).det := by
    rw [Matrix.det_reindex_self, hQdef, Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul (Matrix.isUnit_det_of_left_inverse hU) ?_
    rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    have h1 : hH.eigenvalues i ≠ 0 := eig_ne_zero hH hdet i
    simp only [scal, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.mpr (abs_pos.mpr h1)).ne'
  refine ⟨_, _, e, Matrix.nonsingInvUnit _ hdetQ, ?_⟩
  change Formalism.UG.cT (starRingEnd ℂ) (reindex e e Q) * reindex e e J * reindex e e Q = _
  rw [sigex_cT_conj_eq]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [hQ, Matrix.submatrix_diagonal_equiv]
  ext (a | a) (b | b)
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply, Function.comp_apply, hinl,
      Sum.inl.injEq, Matrix.one_apply]
    split_ifs
    · rw [sign_pos ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a).2, Complex.ofReal_one]
    · rfl
  · simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Function.comp_apply, hinr,
      Sum.inr.injEq, Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · have hx := ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a).2
      have hneg : hH.eigenvalues ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) < 0 :=
        lt_of_le_of_ne (not_lt.mp hx) (eig_ne_zero hH hdet _)
      rw [sign_neg hneg]
      push_cast
      ring
    · simp

end Formalism.UG.P
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SplitUnitaryGroupIso
section
noncomputable section

open Matrix

namespace Formalism.UG.P

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem split_mat_ext {M N : Matrix n n (R × R)} (h1 : M.map Prod.fst = N.map Prod.fst)
    (h2 : M.map Prod.snd = N.map Prod.snd) : M = N := by
  ext i j
  · simpa using congrFun (congrFun h1 i) j
  · simpa using congrFun (congrFun h2 i) j

theorem split_map_fst_mul (M N : Matrix n n (R × R)) :
    (M * N).map Prod.fst = M.map Prod.fst * N.map Prod.fst := by
  ext i j
  simp [Matrix.mul_apply, Prod.fst_sum]

theorem split_map_snd_mul (M N : Matrix n n (R × R)) :
    (M * N).map Prod.snd = M.map Prod.snd * N.map Prod.snd := by
  ext i j
  simp [Matrix.mul_apply, Prod.snd_sum]

theorem split_cT_fst (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.fst = (g.map Prod.snd)ᵀ := by
  ext i j
  simp [cT, swapR, Matrix.map_apply, Matrix.transpose_apply]

theorem split_cT_snd (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.snd = (g.map Prod.fst)ᵀ := by
  ext i j
  simp [cT, swapR, Matrix.map_apply, Matrix.transpose_apply]

theorem splitJ_fst (J₁ : Matrix n n R) : (splitJ J₁).map Prod.fst = J₁ := by
  ext i j
  simp [splitJ, Matrix.map_apply]

theorem splitJ_snd (J₁ : Matrix n n R) : (splitJ J₁).map Prod.snd = J₁ᵀ := by
  ext i j
  simp [splitJ, Matrix.map_apply, Matrix.transpose_apply]

theorem split_mem_iff (J₁ : Matrix n n R) (g : GL n (R × R)) :
    g ∈ Formalism.UG.UJ (swapR R) (splitJ J₁) ↔
      ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * (g : Matrix n n (R × R)).map Prod.fst
        = J₁ := by
  constructor
  · intro h
    have h' := congrArg (fun M : Matrix n n (R × R) => M.map Prod.fst)
      (show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁ from h)
    simpa only [split_map_fst_mul, split_cT_fst, splitJ_fst] using h'
  · intro h
    show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁
    apply split_mat_ext
    · rw [split_map_fst_mul, split_map_fst_mul, split_cT_fst, splitJ_fst, h]
    · rw [split_map_snd_mul, split_map_snd_mul, split_cT_snd, splitJ_snd]
      have h' := congrArg Matrix.transpose h
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h'
      rw [← Matrix.mul_assoc] at h'
      exact h'

theorem split_conj_mul (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) {P Q : Matrix n n R}
    (hPQ : P * Q = 1) : (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = 1 := by
  have h1 : J₁⁻¹ * J₁ = 1 := Matrix.nonsing_inv_mul _ hJ
  have h2 : J₁ * J₁⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  calc (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = J₁ * (P * (J₁⁻¹ * J₁) * Q) * J₁⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, hPQ, Matrix.mul_one, h2]

def pairMat (X Y : Matrix n n R) : Matrix n n (R × R) := fun i j => (X i j, Y i j)

theorem pairMat_fst (X Y : Matrix n n R) : (pairMat X Y).map Prod.fst = X := by
  ext i j
  rfl

theorem pairMat_snd (X Y : Matrix n n R) : (pairMat X Y).map Prod.snd = Y := by
  ext i j
  rfl

theorem pairMat_mul_eq_one {X Y X' Y' : Matrix n n R} (h1 : X * X' = 1) (h2 : Y * Y' = 1) :
    pairMat X Y * pairMat X' Y' = 1 := by
  apply split_mat_ext
  · rw [split_map_fst_mul, pairMat_fst, pairMat_fst, h1]
    exact (Matrix.map_one _ rfl rfl).symm
  · rw [split_map_snd_mul, pairMat_snd, pairMat_snd, h2]
    exact (Matrix.map_one _ rfl rfl).symm

theorem split_injective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (g g' : GL n (R × R))
    (hg : g ∈ Formalism.UG.UJ (swapR R) (splitJ J₁)) (hg' : g' ∈ Formalism.UG.UJ (swapR R) (splitJ J₁))
    (h : (g : Matrix n n (R × R)).map Prod.fst = (g' : Matrix n n (R × R)).map Prod.fst) :
    g = g' := by
  have hF : (g : Matrix n n (R × R)).map Prod.fst * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst = 1 := by
    rw [← split_map_fst_mul, Units.mul_inv]
    exact Matrix.map_one _ rfl rfl
  have e1 := (split_mem_iff J₁ g).mp hg
  have e2 := (split_mem_iff J₁ g').mp hg'
  rw [← h] at e2
  have k1 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1]
  have k2 : ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e2]
  have k3 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ := by
    have h3 := congrArg (fun M : Matrix n n R => M * J₁⁻¹) (k1.trans k2.symm)
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one] using h3
  have k4 := congrArg Matrix.transpose k3
  rw [Matrix.transpose_transpose, Matrix.transpose_transpose] at k4
  exact Units.ext (split_mat_ext h k4)

theorem split_surjective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (h : GL n R) :
    ∃ g : GL n (R × R), g ∈ Formalism.UG.UJ (swapR R) (splitJ J₁) ∧ bc (RingHom.fst R R) g = h := by
  have hS : (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ * (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ (Units.mul_inv h), Matrix.transpose_one]
  have hSi : (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ * (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ (Units.inv_mul h), Matrix.transpose_one]
  refine ⟨⟨pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ,
    pairMat ((h⁻¹ : GL n R) : Matrix n n R) (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ,
    pairMat_mul_eq_one (Units.mul_inv h) hS, pairMat_mul_eq_one (Units.inv_mul h) hSi⟩, ?_, ?_⟩
  · apply (split_mem_iff J₁ _).mpr
    show ((pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ).map Prod.snd)ᵀ * J₁ *
      (pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ).map Prod.fst = J₁
    rw [pairMat_snd, pairMat_fst, Matrix.transpose_transpose]
    calc J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹ * J₁ * (h : Matrix n n R)
        = J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * (J₁⁻¹ * J₁) * (h : Matrix n n R) := by
          simp only [Matrix.mul_assoc]
      _ = J₁ := by
          rw [Matrix.nonsing_inv_mul _ hJ, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  · exact Units.ext (pairMat_fst (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ)

theorem split_unitary_group_iso : Formalism.UG.SplitIso := by
  intro R _ n _ _ J₁ hJ
  refine ⟨MulEquiv.ofBijective ((bc (RingHom.fst R R)).comp (Formalism.UG.UJ (swapR R) (splitJ J₁)).subtype) ⟨?_, ?_⟩,
    fun g => rfl⟩
  · intro a b hab
    apply Subtype.ext
    apply split_injective J₁ hJ a b a.2 b.2
    exact congrArg (fun u : GL n R => (u : Matrix n n R)) hab
  · intro h
    obtain ⟨g, hg, he⟩ := split_surjective J₁ hJ h
    exact ⟨⟨g, hg⟩, he⟩

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
section
noncomputable section

namespace Formalism.UG.P

open Matrix

variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

theorem mem_stdLat_iff' (x : n → A) :
    x ∈ stdLat (n := n) (A := A) R ↔ ∀ i, x i ∈ Set.range (algebraMap R A) := by
  simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
    LinearMap.mem_range, Algebra.linearMap_apply, Set.mem_range]

theorem map_mulVec_mem_stdLat (M : Matrix n n R) (x : n → A)
    (hx : x ∈ stdLat (n := n) (A := A) R) :
    (M.map (algebraMap R A)) *ᵥ x ∈ stdLat (n := n) (A := A) R := by
  rw [mem_stdLat_iff'] at hx ⊢
  choose y hy using hx
  have hxy : x = fun j => algebraMap R A (y j) := funext fun j => (hy j).symm
  subst hxy
  intro i
  refine ⟨(M *ᵥ y) i, ?_⟩

  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem entries_mem_of_mem_stabGL (h : GL n A)
    (hh : h ∈ Formalism.UG.stabGL (stdLat (n := n) (A := A) R))
    (i j : n) : (h : Matrix n n A) i j ∈ Set.range (algebraMap R A) := by
  have hmem : (Pi.single j 1 : n → A) ∈ stdLat (n := n) (A := A) R := by
    rw [mem_stdLat_iff']
    intro k
    by_cases hk : k = j
    · subst hk; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, hk]⟩
  have h2 := ((hh (Pi.single j 1)).1 hmem)
  rw [mem_stdLat_iff'] at h2
  have h3 := h2 i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

theorem coe_bc (φ : R →+* A) (u : GL n R) :
    ((bc (n := n) φ u : GL n A) : Matrix n n A) = (u : Matrix n n R).map φ := by
  simp [bc, RingHom.mapMatrix_apply]

theorem stabilizer_standard_lattice : Formalism.UG.StabStd := by
  unfold Formalism.UG.StabStd
  intro A R _ _ _ n _ _ hinj
  ext g
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ Formalism.UG.stabGL (stdLat (n := n) (A := A) R) := inv_mem hg
    choose r hr using entries_mem_of_mem_stabGL (R := R) g hg
    choose r' hr' using entries_mem_of_mem_stabGL (R := R) g⁻¹ hg'
    let M : Matrix n n R := Matrix.of r
    let M' : Matrix n n R := Matrix.of r'
    have hM : M.map (algebraMap R A) = (g : Matrix n n A) := by
      ext i j; simp [M, hr]
    have hM' : M'.map (algebraMap R A) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j; simp [M', hr']
    have h1 : M * M' = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact Units.mul_inv g
    have h2 : M' * M = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact Units.inv_mul g
    refine ⟨⟨M, M', h1, h2⟩, ?_⟩
    ext : 1
    rw [coe_bc]
    exact hM
  · rintro ⟨u, rfl⟩
    intro x
    constructor
    · intro hx
      rw [coe_bc]
      exact map_mulVec_mem_stdLat _ x hx
    · intro hx
      have hinv := map_mulVec_mem_stdLat (A := A) ((u⁻¹ : GL n R) : Matrix n n R) _ hx
      rw [← coe_bc, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
        Units.val_one, Matrix.one_mulVec] at hinv
      exact hinv

end Formalism.UG.P
end
end

