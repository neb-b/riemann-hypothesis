module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import Lemmata.GeneralBFact.Imports
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CBinet
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private lemma cb_det_mul_fun {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  have hrow : A * B = Matrix.of (fun a => ∑ j, A a j • B j) := by
    ext a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow]
  have h1 := (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_sum
    (fun a j => A a j • B j)
  have h2 : ∀ f : Fin i → Fin N,
      (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap (fun a => A a (f a) • B (f a)) =
        (∏ a, A a (f a)) * (B.submatrix f id).det := by
    intro f
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    rfl
  exact h1.trans (Finset.sum_congr rfl fun f _ => h2 f)

private def cbPar {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding

private lemma cbPar_image {i N : ℕ} (S : Finset (Fin N)) (hS : S.card = i) (σ : Equiv.Perm (Fin i)) :
    univ.map (cbPar ⟨⟨S, hS⟩, σ⟩) = S := by
  simp only [cbPar]
  rw [← Finset.map_map, Finset.map_univ_equiv]
  exact Finset.map_orderEmbOfFin_univ S hS

private lemma cbPar_bij {i N : ℕ} : Function.Bijective (cbPar (i := i) (N := N)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨S', hS'⟩, σ'⟩ h
    have hSS : S = S' := by
      rw [← cbPar_image S hS σ, ← cbPar_image S' hS' σ', h]
    subst hSS
    have hσ : σ = σ' := by
      ext a
      have h2 := DFunLike.congr_fun h a
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)
    subst hσ
    rfl
  · intro g
    have hcard : (univ.map g).card = i := by simp
    have hmem : ∀ a, g a ∈ univ.map g := fun a => Finset.mem_map_of_mem g (Finset.mem_univ a)
    let g' : Fin i ≃ (univ.map g) := Equiv.ofBijective (fun a => ⟨g a, hmem a⟩)
      ⟨fun a b h => g.injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx
        exact ⟨a, rfl⟩⟩
    refine ⟨⟨⟨univ.map g, hcard⟩, g'.trans ((univ.map g).orderIsoOfFin hcard).symm.toEquiv⟩, ?_⟩
    refine DFunLike.ext _ _ fun a => ?_
    change ((univ.map g).orderEmbOfFin hcard) (((univ.map g).orderIsoOfFin hcard).symm (g' a)) = g a
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    rfl

theorem det_mul_eq_sum_submatrix {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin N) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  have hz : ∀ f : Fin i → Fin N, ¬ Function.Injective f →
      (∏ a, A a (f a)) * (B.submatrix f id).det = 0 := by
    intro f hf
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨a, b, hab, hne⟩ := hf
    rw [Matrix.det_zero_of_row_eq hne (by funext c; simp [hab]), mul_zero]
  have hS : ∀ S : {S : Finset (Fin N) // S.card = i},
      ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det =
        (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    intro S
    have hA : (A.submatrix id (S.1.orderEmbOfFin S.2)).det =
        ∑ σ : Equiv.Perm (Fin i), ((Equiv.Perm.sign σ : ℤ) : R) *
          ∏ a, A a (S.1.orderEmbOfFin S.2 (σ a)) := by
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl
    rw [hA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hB : B.submatrix (cbPar ⟨S, σ⟩) id = (B.submatrix (S.1.orderEmbOfFin S.2) id).submatrix σ id := rfl
    rw [hB, Matrix.det_permute]
    change (∏ a, A a (S.1.orderEmbOfFin S.2 (σ a))) * _ = _
    ring
  calc (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        cb_det_mul_fun A B
    _ = ∑ f ∈ univ.filter Function.Injective, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        (Finset.sum_filter_of_ne fun f _ hf => by
          by_contra hni
          exact hf (hz f hni)).symm
    _ = ∑ x : {f : Fin i → Fin N // Function.Injective f},
          (∏ a, A a (x.1 a)) * (B.submatrix x.1 id).det :=
        Finset.sum_subtype _ (fun f => by simp) _
    _ = ∑ g : Fin i ↪ Fin N, (∏ a, A a (g a)) * (B.submatrix g id).det :=
        Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding _ _) _ _ (fun _ => rfl)
    _ = ∑ p, (∏ a, A a (cbPar p a)) * (B.submatrix (cbPar p) id).det :=
        (cbPar_bij.sum_comp (fun g : Fin i ↪ Fin N => (∏ a, A a (g a)) * (B.submatrix g id).det)).symm
    _ = ∑ S, ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det :=
        Fintype.sum_sigma _
    _ = _ := Finset.sum_congr rfl fun S _ => hS S

theorem lead_unitary_diag {U : Matrix (Fin n) (Fin n) ℂ} (d : Fin n → ℂ) (i : ℕ) (hi : i ≤ n) :
    lead i (U * Matrix.diagonal d * Uᴴ) =
      ∑ J : {J : Finset (Fin n) // J.card = i},
        ((‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 : ℝ) : ℂ) * ∏ j ∈ J.1, d j := by
  unfold lead
  rw [dite_eq_left hi]
  have hsub : (U * Matrix.diagonal d * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d) * (U.submatrix (Fin.castLE hi) id)ᴴ := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hsub, det_mul_eq_sum_submatrix]
  refine Finset.sum_congr rfl fun J _ => ?_
  have h1 : (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d).submatrix id (J.1.orderEmbOfFin J.2) =
      U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2) *
        Matrix.diagonal (fun a => d (J.1.orderEmbOfFin J.2 a)) := by
    ext a b
    simp [Matrix.mul_diagonal]
  have h2 : (U.submatrix (Fin.castLE hi) id)ᴴ.submatrix (J.1.orderEmbOfFin J.2) id =
      (U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2))ᴴ := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  have hp : ∏ a, d (J.1.orderEmbOfFin J.2 a) = ∏ j ∈ J.1, d j := by
    calc ∏ a, d (J.1.orderEmbOfFin J.2 a)
        = ∏ j ∈ univ.map (J.1.orderEmbOfFin J.2).toEmbedding, d j := (Finset.prod_map _ _ _).symm
      _ = ∏ j ∈ J.1, d j := by rw [Finset.map_orderEmbOfFin_univ]
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1, h2, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose, hp, hn]
  ring

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasPsA
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

namespace CasPsA

variable {n : ℕ}

theorem entry_conj_single (u v : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) :
    (u * Matrix.single a b (1 : ℂ) * v) i j = u i a * v b j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem conj_single_eq (u v : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    u * Matrix.single a b (1 : ℂ) * v = ∑ c, ∑ d, (u c a * v b d) • Matrix.single c d (1 : ℂ) := by
  ext i j
  rw [entry_conj_single]
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem sum_coef_conj (u v : Matrix (Fin n) (Fin n) ℂ) (huv : u * v = 1) (c d : Fin n) :
    ∑ a, ∑ b, (u c a * v b d) • (u * Matrix.single b a (1 : ℂ) * v) = Matrix.single d c (1 : ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, entry_conj_single]
  have h1 : ∀ x y, ∑ k, u x k * v k y = (1 : Matrix (Fin n) (Fin n) ℂ) x y := fun x y => by
    rw [← huv, Matrix.mul_apply]
  calc ∑ a, ∑ b, u c a * v b d * (u i b * v a j)
      = (∑ a, u c a * v a j) * (∑ b, u i b * v b d) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = Matrix.single d c (1 : ℂ) i j := by
        rw [h1, h1, Matrix.one_apply, Matrix.one_apply, Matrix.single_apply]
        split_ifs <;> simp_all

theorem sum_sum_sum_sum_comm (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum_bilin_conj (B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (u v : Matrix (Fin n) (Fin n) ℂ) (huv : u * v = 1) :
    ∑ a, ∑ b, B (u * Matrix.single a b 1 * v) (u * Matrix.single b a 1 * v) =
      ∑ a, ∑ b, B (Matrix.single a b 1) (Matrix.single b a 1) := by
  calc ∑ a, ∑ b, B (u * Matrix.single a b 1 * v) (u * Matrix.single b a 1 * v)
      = ∑ a, ∑ b, ∑ c, ∑ d, (u c a * v b d) • B (Matrix.single c d 1) (u * Matrix.single b a 1 * v) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [conj_single_eq u v a b]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, (u c a * v b d) • B (Matrix.single c d 1) (u * Matrix.single b a 1 * v) :=
        sum_sum_sum_sum_comm _
    _ = ∑ c, ∑ d, B (Matrix.single c d 1) (Matrix.single d c 1) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [← sum_coef_conj u v huv c d]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul]

end CasPsA

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecLog
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exp_ge_one_add_add_sq_div_three {u : ℝ} (hu : |u| ≤ 1) :
    1 + u + u ^ 2 / 3 ≤ Real.exp u := by
  have hb := Real.exp_bound hu (n := 5) (by norm_num)
  have h1 : -(|u| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5))) ≤
      Real.exp u - ∑ i ∈ Finset.range 5, u ^ i / (Nat.factorial i : ℝ) := (abs_le.mp hb).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  have hu2 : |u| ^ 5 ≤ u ^ 2 := by
    have h0 : 0 ≤ |u| := abs_nonneg u
    have h3 : |u| ^ 3 ≤ 1 := pow_le_one₀ h0 hu
    calc |u| ^ 5 = |u| ^ 2 * |u| ^ 3 := by ring
      _ ≤ |u| ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = u ^ 2 := by rw [mul_one, sq_abs]
  have hlo : -1 ≤ u := (abs_le.mp hu).1
  have hq : 0 ≤ (u + 1) * (u + 3) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg (sq_nonneg u) hq, sq_nonneg u]

theorem logSumExp_lower {ι : Type*} [Fintype ι] (w y : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (h1 : ∑ j, w j = 1) (h0 : ∑ j, w j * y j = 0) {R : ℝ} (hR : 0 < R) (hy : ∀ j, |y j| ≤ R) :
    min 1 (1 / R) * (∑ j, w j * y j ^ 2) / 4 ≤ Real.log (∑ j, w j * Real.exp (y j)) := by
  have hc0 : 0 < min 1 (1 / R) := lt_min one_pos (by positivity)
  have hc1 : min 1 (1 / R) ≤ 1 := min_le_left _ _
  have hcR : min 1 (1 / R) * R ≤ 1 := by
    calc min 1 (1 / R) * R ≤ (1 / R) * R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
      _ = 1 := by field_simp
  generalize hcdef : min 1 (1 / R) = c at hc0 hc1 hcR ⊢
  have hQ0 : 0 ≤ ∑ j, w j * y j ^ 2 := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have hQR : ∑ j, w j * y j ^ 2 ≤ R ^ 2 := by
    calc ∑ j, w j * y j ^ 2 ≤ ∑ j, w j * R ^ 2 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by
            have h := hy j
            have : y j ^ 2 = |y j| ^ 2 := (sq_abs _).symm
            rw [this]
            exact pow_le_pow_left₀ (abs_nonneg _) h 2) (hw j)
      _ = R ^ 2 := by rw [← Finset.sum_mul, h1, one_mul]
  have hpt : ∀ j, 1 + c * y j + (c * y j) ^ 2 / 3 ≤ Real.exp (c * y j) := fun j =>
    exp_ge_one_add_add_sq_div_three (by
      rw [abs_mul, abs_of_pos hc0]
      calc c * |y j| ≤ c * R := mul_le_mul_of_nonneg_left (hy j) hc0.le
        _ ≤ 1 := hcR)
  have hsum : ∑ j, w j * (1 + c * y j + (c * y j) ^ 2 / 3) =
      1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3 := by
    have e : ∑ j, w j * (1 + c * y j + (c * y j) ^ 2 / 3) =
        ∑ j, w j + c * ∑ j, w j * y j + c ^ 2 / 3 * ∑ j, w j * y j ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, h1, h0]
    ring
  have hS : 1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3 ≤ ∑ j, w j * Real.exp (c * y j) := by
    rw [← hsum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpt j) (hw j)
  have hS1 : 0 < 1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3 := by positivity
  have hSpos : 0 < ∑ j, w j * Real.exp (c * y j) := lt_of_lt_of_le hS1 hS
  have hJ : (∑ j, w j * Real.exp (c * y j)) ^ (1 / c) ≤ ∑ j, w j * Real.exp (y j) := by
    have := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ w (fun j => Real.exp (c * y j))
      (fun j _ => hw j) h1 (fun j _ => (Real.exp_pos _).le) (p := 1 / c)
      (by rw [le_div_iff₀ hc0]; linarith)
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [← Real.exp_mul]
    congr 2
    field_simp
  have ht1 : c ^ 2 * (∑ j, w j * y j ^ 2) ≤ 1 := by
    calc c ^ 2 * (∑ j, w j * y j ^ 2) ≤ c ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hQR (sq_nonneg c)
      _ = (c * R) ^ 2 := by ring
      _ ≤ 1 := by nlinarith [mul_pos hc0 hR]
  have hlog1 : 3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3) ≤
      Real.log (1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hS1)
    rw [Real.log_inv] at h
    have hinv : (1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3)⁻¹ ≤
        1 - 3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3) := by
      rw [inv_eq_one_div, div_le_iff₀ hS1]
      nlinarith [mul_nonneg (sq_nonneg c) hQ0]
    linarith
  have hlog : 3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3) ≤ Real.log (∑ j, w j * Real.exp (c * y j)) :=
    hlog1.trans (Real.log_le_log hS1 hS)
  calc c * (∑ j, w j * y j ^ 2) / 4
      = (1 / c) * (3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3)) := by
        field_simp
    _ ≤ (1 / c) * Real.log (∑ j, w j * Real.exp (c * y j)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = Real.log ((∑ j, w j * Real.exp (c * y j)) ^ (1 / c)) := by rw [Real.log_rpow hSpos]
    _ ≤ Real.log (∑ j, w j * Real.exp (y j)) := Real.log_le_log (by positivity) hJ

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecSum
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def nuNext (ν : Fin n → ℝ) (i : Fin n) : ℝ := if h : (i : ℕ) + 1 < n then ν ⟨(i : ℕ) + 1, h⟩ else 0

lemma inP_entry_zero {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) {a b : Fin n}
    (hab : ε a = ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hY.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, hab] at h
  cases hb : ε b <;> simp [hb] at h <;>
    first | exact h | linear_combination h / 2 | linear_combination -h / 2

lemma conjTranspose_eq_self_of_mem_noncompactPart {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) : Yᴴ = Y := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    split_ifs <;> norm_num
  have h1 : Yᴴ * Jm ε = Y * Jm ε := by
    rw [hY.2]
    exact eq_neg_of_add_eq_zero_left hY.1
  calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Y * Jm ε * Jm ε := by rw [h1]
    _ = Y := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]

lemma inP_norm_symm {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) (a b : Fin n) :
    ‖Y b a‖ = ‖Y a b‖ := by
  have h := congrFun (congrFun (conjTranspose_eq_self_of_mem_noncompactPart hY) b) a
  rw [← h, Matrix.conjTranspose_apply, norm_star]

lemma hs_eq_two_lower {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    hs Y = 2 * ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0 := by
  have hsplit : ∀ a b : Fin n, ‖Y a b‖ ^ 2 =
      (if b < a then ‖Y a b‖ ^ 2 else 0) + (if a < b then ‖Y a b‖ ^ 2 else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [inP_entry_zero hY rfl]
    · simp [h, not_lt.mpr h.le]
  have hswap : (∑ a : Fin n, ∑ b : Fin n, if a < b then ‖Y a b‖ ^ 2 else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [inP_norm_symm hY]
  unfold hs
  calc (∑ a : Fin n, ∑ b : Fin n, ‖Y a b‖ ^ 2)
      = ∑ a : Fin n, ∑ b : Fin n, ((if b < a then ‖Y a b‖ ^ 2 else 0) + (if a < b then ‖Y a b‖ ^ 2 else 0)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b
    _ = (∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0) +
        ∑ a : Fin n, ∑ b : Fin n, if a < b then ‖Y a b‖ ^ 2 else 0 := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

lemma sum_Ico_tele (f : ℕ → ℝ) {b : ℕ} : ∀ m, b ≤ m → ∑ i ∈ Finset.Ico b m, (f i - f (i + 1)) = f b - f m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]; ring

lemma nuNext_tele (ν : Fin n → ℝ) {a b : Fin n} (hba : b < a) :
    ∑ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) = ν b - ν a := by
  let f : ℕ → ℝ := fun k => if h : k < n then ν ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) =
      (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then f i - f (i + 1) else 0) := by
    intro i
    simp [f, nuNext, i.isLt]
  rw [Finset.sum_congr rfl (fun i _ => h1 i),
    Fin.sum_univ_eq_sum_range (fun k => if (b : ℕ) ≤ k ∧ k < (a : ℕ) then f k - f (k + 1) else 0) n,
    ← Finset.sum_filter]
  have hfil : (Finset.range n).filter (fun k => (b : ℕ) ≤ k ∧ k < (a : ℕ)) = Finset.Ico (b : ℕ) a := by
    ext k
    have := a.isLt
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfil, sum_Ico_tele f (b := (b : ℕ)) (a : ℕ) (Fin.lt_iff_val_lt_val.mp hba).le]
  simp [f, b.isLt, a.isLt]

theorem dec_weighted {ε : Fin n → Bool} (ν : Fin n → ℝ) (hν : Antitone ν) {g : ℝ}
    (hg : ∀ a b : Fin n, ε a ≠ ε b → b < a → g ≤ ν b - ν a) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    g * hs Y / 2 ≤
      ∑ i : Fin n, (ν i - nuNext ν i) *
        (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ‖Y a b‖ ^ 2 else 0) := by
  rw [hs_eq_two_lower hY]
  have hR : ∑ i : Fin n, (ν i - nuNext ν i) *
      (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ‖Y a b‖ ^ 2 else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then (ν b - ν a) * ‖Y a b‖ ^ 2 else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hba
    · rw [← nuNext_tele ν hba, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg, mul_zero]
      intro h
      exact hba (Fin.lt_iff_val_lt_val.mpr (lt_of_le_of_lt h.1 h.2))
  rw [hR]
  have hL : g * (2 * ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0) / 2 =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then g * ‖Y a b‖ ^ 2 else 0 := by
    have hg' : ∀ a b : Fin n, (if b < a then g * ‖Y a b‖ ^ 2 else 0) =
        g * (if b < a then ‖Y a b‖ ^ 2 else 0) := by
      intro a b; split_ifs <;> simp
    simp_rw [hg', ← Finset.mul_sum]
    ring
  rw [hL]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  split_ifs with hba
  · by_cases hε : ε a = ε b
    · rw [inP_entry_zero hY hε]; simp
    · exact mul_le_mul_of_nonneg_right (hg a b hε hba) (by positivity)
  · exact le_rfl

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exists_mu {lam : Fin n → ℝ} (hlam : IsHCParam lam) : ∃ μ : Fin n → ℤ, IsMu lam μ := by
  choose m hm using hlam.2
  refine ⟨fun a => m a + (n : ℤ) - 1 - ((a : ℕ) : ℤ), ?_⟩
  unfold IsMu
  intro a
  have h := hm a
  simp only [rho]
  push_cast
  linarith

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

