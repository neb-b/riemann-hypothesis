module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SortedSpec

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOf
section
open Matrix Finset

noncomputable section

namespace PI.ET

theorem expTri_of (hS : SpecExists) (hHS : HSEq) (hH : Horn) (hA : AbelSq) (hE : EuclTri) :
    PI.ExpTri := by
  unfold PI.ExpTri
  intro n X Y Z U hX hY hZ hU hexp
  obtain ⟨ξ, hξ⟩ := hS n X hX
  obtain ⟨η, hη⟩ := hS n Y hY
  obtain ⟨ζ, hζ⟩ := hS n Z hZ
  obtain ⟨hmaj, hsum⟩ := hH n X Y Z U ξ η ζ hξ hη hζ hU hexp
  have hζ' := hζ
  obtain ⟨hanti, -⟩ := hζ'

  have hsq : ∑ i, ζ i ^ 2 ≤ ∑ i, (ξ i + η i) ^ 2 :=
    hA n ζ (fun i => ξ i + η i) hanti hmaj hsum
  rw [hHS n Z ζ hζ, hHS n X ξ hξ, hHS n Y η hη]
  exact le_trans (Real.sqrt_le_sqrt hsq) (hE n ξ η)

end PI.ET
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ProdLeOfInjective
section
open Matrix Finset

noncomputable section

namespace PI.ET

theorem det_mul_rect {R : Type*} [CommRing R] {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [det_apply, Matrix.mul_apply, Fintype.prod_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
  ring

theorem sum_comp_perm {M : Type*} [AddCommMonoid M] {k n : ℕ} (F : (Fin k → Fin n) → M)
    (τ : Equiv.Perm (Fin k)) : ∑ f : Fin k → Fin n, F (fun i => f (τ i)) = ∑ f, F f := (Equiv.arrowCongr τ.symm (Equiv.refl (Fin n))).sum_comp F

theorem factorial_mul_det (k n : ℕ) (q : Fin n → ℂ) (V : Matrix (Fin n) (Fin k) ℂ) :
    (k.factorial : ℂ) * (Vᴴ * diagonal q * V).det =
      ∑ f : Fin k → Fin n, (∏ i, q (f i)) *
        ((V.submatrix f id).det * star (V.submatrix f id).det) := by
  have h2 : ∀ f : Fin k → Fin n, ((Vᴴ * diagonal q).submatrix id f).det =
      (∏ i, q (f i)) * star (V.submatrix f id).det := by
    intro f
    have he : (Vᴴ * diagonal q).submatrix id f = (V.submatrix f id)ᴴ * diagonal (fun i => q (f i)) := by
      ext a b
      simp [conjTranspose_apply, mul_diagonal, submatrix_apply]
    rw [he, det_mul, det_diagonal, det_conjTranspose, mul_comm]
  have h3 : ∀ (f : Fin k → Fin n) (τ : Equiv.Perm (Fin k)),
      (V.submatrix (fun i => f (τ i)) id).det = Equiv.Perm.sign τ * (V.submatrix f id).det := by
    intro f τ
    exact det_permute τ (V.submatrix f id)
  have hperm : ∀ τ : Equiv.Perm (Fin k),
      ∑ f : Fin k → Fin n, (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) =
        ∑ f : Fin k → Fin n, ((Equiv.Perm.sign τ : ℂ) * ∏ i, V (f (τ i)) i) *
          ((∏ i, q (f i)) * star (V.submatrix f id).det) := by
    intro τ
    rw [← sum_comp_perm (fun f : Fin k → Fin n =>
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det)) τ]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only
    rw [h3 f τ, Equiv.prod_comp τ (fun i => q (f i)), star_mul', star_intCast]
    ring
  rw [det_mul_rect]
  simp_rw [h2]
  rw [show (k.factorial : ℂ) * ∑ f : Fin k → Fin n,
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) =
      ∑ τ : Equiv.Perm (Fin k), ∑ f : Fin k → Fin n,
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]]
  rw [Finset.sum_congr rfl fun τ _ => hperm τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hd : (V.submatrix f id).det = ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℂ) * ∏ i, V (f (τ i)) i := by
    rw [det_apply']
    rfl
  rw [← Finset.sum_mul, ← hd]
  ring

theorem prod_le_of_injective {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 ≤ p i) (f : Fin k → Fin n) (hf : Function.Injective f) :
    ∏ i, p (f i) ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by
  classical
  have hs : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  set e := (Finset.univ.image f).orderEmbOfFin hs with he
  have h1 : ∏ i, p (f i) = ∏ j : Fin k, p (e j) := by
    rw [← Finset.prod_image (fun i _ j _ h => hf h), ← Finset.map_orderEmbOfFin_univ _ hs,
      Finset.prod_map]
    rfl
  have h3 : ∀ m (hm : m < k), m ≤ (e ⟨m, hm⟩ : ℕ) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have hlt : e ⟨m, by omega⟩ < e ⟨m + 1, hm⟩ := e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self m))
      have h' : (e ⟨m, by omega⟩ : ℕ) < e ⟨m + 1, hm⟩ := hlt
      have := ih (by omega)
      omega
  rw [h1]
  refine Finset.prod_le_prod₀ (fun j _ => hpos _) fun j _ => hp ?_
  rw [Fin.le_iff_val_le_val, Fin.val_castLE]
  exact h3 j.1 j.2

theorem kyFan_diag {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 < p i) (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by
  have hT := factorial_mul_det k n (fun i => (p i : ℂ)) V
  have hU := factorial_mul_det k n (fun _ => (1 : ℂ)) V
  rw [diagonal_one, Matrix.mul_one, hV, det_one, mul_one] at hU
  simp only [Finset.prod_const_one, one_mul] at hU
  have hsq : ∀ f : Fin k → Fin n, (V.submatrix f id).det * star (V.submatrix f id).det =
      ((‖(V.submatrix f id).det‖ ^ 2 : ℝ) : ℂ) := by
    intro f
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  simp_rw [hsq] at hU
  have hU' : (k.factorial : ℝ) = ∑ f : Fin k → Fin n, ‖(V.submatrix f id).det‖ ^ 2 := by
    exact_mod_cast hU
  set P := ∏ i : Fin k, p (Fin.castLE hk i)
  have hterm : ∀ f : Fin k → Fin n,
      ‖(∏ i, ((p (f i) : ℝ) : ℂ)) * ((V.submatrix f id).det * star (V.submatrix f id).det)‖ ≤
        P * ‖(V.submatrix f id).det‖ ^ 2 := by
    intro f
    rw [hsq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), norm_prod]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _)]
    by_cases hf : Function.Injective f
    · exact mul_le_mul_of_nonneg_right (prod_le_of_injective hk p hp (fun i => (hpos i).le) f hf)
        (sq_nonneg _)
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        exact hf fun i j h => by_contra fun hne => hc ⟨i, j, h, hne⟩
      have h0 : (V.submatrix f id).det = 0 := det_zero_of_row_eq hne (by ext c; simp [hij])
      simp [h0]
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hmain : (k.factorial : ℝ) * ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ ≤ P * k.factorial := by
    calc (k.factorial : ℝ) * ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖
        = ‖(k.factorial : ℂ) * (Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ f : Fin k → Fin n, (∏ i, ((p (f i) : ℝ) : ℂ)) *
          ((V.submatrix f id).det * star (V.submatrix f id).det)‖ := by rw [hT]
      _ ≤ ∑ f : Fin k → Fin n, ‖(∏ i, ((p (f i) : ℝ) : ℂ)) *
          ((V.submatrix f id).det * star (V.submatrix f id).det)‖ := norm_sum_le _ _
      _ ≤ ∑ f : Fin k → Fin n, P * ‖(V.submatrix f id).det‖ ^ 2 := Finset.sum_le_sum fun f _ => hterm f
      _ = P * k.factorial := by rw [← Finset.mul_sum, hU']
  nlinarith [norm_nonneg (Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det]

theorem kyFanDet : KyFanDet := by
  intro n k hk p W V hp hpos hW hV
  have hW1 : Wᴴ * W = 1 := by
    have := (mem_unitaryGroup_iff').1 hW
    rwa [star_eq_conjTranspose] at this
  have hW2 : W * Wᴴ = 1 := by
    have := (mem_unitaryGroup_iff).1 hW
    rwa [star_eq_conjTranspose] at this
  have e1 : Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V =
      (Wᴴ * V)ᴴ * diagonal (fun i => (p i : ℂ)) * (Wᴴ * V) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have e2 : (Wᴴ * V)ᴴ * (Wᴴ * V) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc W,
      hW2, Matrix.one_mul, hV]
  rw [e1]
  exact kyFan_diag hk p hp hpos (Wᴴ * V) e2

end PI.ET
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.PsumEqRange
section
open Finset

noncomputable section

namespace PI.ET

theorem euclTri : EuclTri := by
  intro n a b
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  rw [Real.sqrt_le_left (by positivity)]
  have e : ∑ i, (a i + b i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1; congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith

theorem abel_nat (a c : ℕ → ℝ) : ∀ (n : ℕ), (∀ i j, i ≤ j → j < n → a j ≤ a i) →
    (∀ k ≤ n, 0 ≤ ∑ i ∈ range k, c i) → ∀ t : ℝ, (∀ i < n, t ≤ a i) →
    t * ∑ i ∈ range n, c i ≤ ∑ i ∈ range n, a i * c i := by
  intro n
  induction n with
  | zero => intro _ _ t _; simp
  | succ n ih =>
    intro ha hc t ht
    have ih' := ih (fun i j hij hj => ha i j hij (by omega)) (fun k hk => hc k (by omega)) (a n)
      (fun i hi => ha i n hi.le (by omega))
    have hS : 0 ≤ ∑ i ∈ range (n + 1), c i := hc (n + 1) le_rfl
    have htn : t ≤ a n := ht n (by omega)
    rw [Finset.sum_range_succ] at hS ⊢
    rw [Finset.sum_range_succ]
    nlinarith

theorem psum_eq_range {n : ℕ} (f : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    psum f k = ∑ i ∈ range k, (fun m => if h : m < n then f ⟨m, h⟩ else 0) i := by
  unfold psum
  rw [Finset.sum_filter]
  have h1 : ∑ i : Fin n, (if i.val < k then f i else 0) =
      ∑ i : Fin n, (fun m => if m < k then (if h : m < n then f ⟨m, h⟩ else 0) else 0) i.val := by
    apply Finset.sum_congr rfl; intro i _; simp [i.isLt]
  rw [h1, Fin.sum_univ_eq_sum_range (fun m => if m < k then (if h : m < n then f ⟨m, h⟩ else 0) else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega

theorem sum_eq_range {n : ℕ} (f : Fin n → ℝ) :
    ∑ i, f i = ∑ i ∈ range n, (fun m => if h : m < n then f ⟨m, h⟩ else 0) i := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl; intro i _; simp [i.isLt]

theorem abelSq : AbelSq := by
  intro n a b ha hk htot

  set a' : ℕ → ℝ := fun m => if h : m < n then a ⟨m, h⟩ else 0 with ha'
  set c' : ℕ → ℝ := fun m => if h : m < n then (b ⟨m, h⟩ - a ⟨m, h⟩) else 0 with hc'
  have hc : ∀ k ≤ n, 0 ≤ ∑ i ∈ range k, c' i := by
    intro k hkn
    have := hk k hkn
    rw [psum_eq_range a k hkn, psum_eq_range b k hkn] at this
    have e : ∑ i ∈ range k, c' i = ∑ i ∈ range k, (fun m => if h : m < n then b ⟨m, h⟩ else 0) i -
        ∑ i ∈ range k, (fun m => if h : m < n then a ⟨m, h⟩ else 0) i := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro m _
      simp only [hc']; split_ifs <;> simp
    linarith
  have hmono : ∀ i j, i ≤ j → j < n → a' j ≤ a' i := by
    intro i j hij hj
    simp only [ha', dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
    exact ha (show (⟨i, lt_of_le_of_lt hij hj⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  set t : ℝ := -∑ i ∈ range n, |a' i| with ht
  have htle : ∀ i < n, t ≤ a' i := by
    intro i hi
    have : |a' i| ≤ ∑ i ∈ range n, |a' i| :=
      Finset.single_le_sum (f := fun i => |a' i|) (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hi)
    have := neg_abs_le (a' i)
    linarith
  have key := abel_nat a' c' n hmono hc t htle
  have hc0 : ∑ i ∈ range n, c' i = 0 := by
    have e1 : ∑ i, (b i - a i) = 0 := by rw [Finset.sum_sub_distrib, htot]; ring
    rw [sum_eq_range (fun i => b i - a i)] at e1
    rw [← e1]
  rw [hc0, mul_zero] at key
  have hab : 0 ≤ ∑ i, a i * (b i - a i) := by
    rw [sum_eq_range (fun i => a i * (b i - a i))]
    convert key using 2 with m
    simp only [ha', hc']; split_ifs <;> simp
  have h1 : ∑ i, a i ^ 2 ≤ ∑ i, a i * b i := by
    have : ∑ i, a i * (b i - a i) = ∑ i, a i * b i - ∑ i, a i ^ 2 := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    linarith
  have hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have x0 := Real.sqrt_nonneg (∑ i, a i ^ 2)
  have y0 := Real.sqrt_nonneg (∑ i, b i ^ 2)
  have hx := Real.sq_sqrt hA
  have hy := Real.sq_sqrt hB
  nlinarith [sq_nonneg (Real.sqrt (∑ i, a i ^ 2) - Real.sqrt (∑ i, b i ^ 2)),
    mul_nonneg x0 y0]

end PI.ET
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SpecExists
section
open Matrix Finset

noncomputable section

namespace PI.ET

theorem specExists : SpecExists := by
  intro n A hA
  have hH : A.IsHermitian := hA
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hH.eigenvectorUnitary.2
  have hspec := hH.spectral_theorem
  set l : Fin n → ℝ := hH.eigenvalues with hl

  let σ : Equiv.Perm (Fin n) := Tuple.sort (fun i => OrderDual.toDual (l i))
  have hmono : Monotone ((fun i => OrderDual.toDual (l i)) ∘ σ) := Tuple.monotone_sort _
  refine ⟨l ∘ σ, fun i j hij => hmono hij, U.submatrix id σ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hUU, Matrix.submatrix_id_id]
  · have hD : Matrix.diagonal (fun i => ((l ∘ σ) i : ℂ)) =
        (Matrix.diagonal (fun i => (l i : ℂ))).submatrix σ σ := by
      rw [Matrix.submatrix_diagonal_equiv]
      rfl
    rw [hD, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
    conv_lhs => rw [hspec]
    rfl

theorem hsEq : HSEq := by
  intro n A d ⟨_, W, hW, hA⟩
  have hWW : star W * W = 1 := (Matrix.mem_unitaryGroup_iff').1 hW
  rw [Matrix.star_eq_conjTranspose] at hWW
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (d i : ℂ) with hD
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [Pi.star_apply, Complex.star_def]
  have hAh : Aᴴ = W * D * Wᴴ := by
    rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh,
      Matrix.mul_assoc]
  have key : (A * Aᴴ).trace = ∑ i, ((d i : ℂ)) ^ 2 := by
    rw [hAh, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, hWW, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc, hWW, Matrix.mul_one, hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp [sq]
  have lhs : (A * Aᴴ).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have := lhs.symm.trans key
  exact_mod_cast this

end PI.ET
end
end

