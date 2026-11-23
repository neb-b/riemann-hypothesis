module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PSpecB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPaHadApply
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def detPaCj (P Q : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun W := P * W * Q
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp

def detPaRow (t : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi (fun j => (t j • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp (LinearMap.proj j))

def detPaHad (s : Fin n → Fin n → ℂ) : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  LinearMap.pi (fun i => (detPaRow (s i)).comp (LinearMap.proj i))

theorem detPaRow_det (t : Fin n → ℂ) : LinearMap.det (detPaRow t) = ∏ j, t j := by
  unfold detPaRow
  rw [LinearMap.det_pi]
  simp

theorem detPaHad_det (s : Fin n → Fin n → ℂ) : LinearMap.det (detPaHad s) = ∏ i, ∏ j, s i j := by
  unfold detPaHad
  rw [LinearMap.det_pi]
  simp [detPaRow_det]

theorem detPa {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      ∏ i, ∏ j, shc (pev y i - pev y j) ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hmem : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ((pmat_isHermitian y).eigenvectorUnitary).2
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hmem
  set s : Fin n → Fin n → ℂ := fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) with hs
  let H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ := detPaHad s
  let T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (detPaCj U Uᴴ).comp (H.comp (detPaCj Uᴴ U))
  have hT : ∀ W, T W = shcAd y W := by
    intro W
    simp only [T, H, LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, shcAd]
    congr 2
  have hC : shcAd y = ⇑(LinearMap.toContinuousLinearMap (T.restrictScalars ℝ)) := by
    funext W; exact (hT W).symm
  rw [hC, ContinuousLinearMap.fderiv, LinearMap.coe_toContinuousLinearMap, LinearMap.det_restrictScalars]
  have hAB : LinearMap.det (detPaCj U Uᴴ) * LinearMap.det (detPaCj Uᴴ U) = 1 := by
    rw [← LinearMap.det_comp]
    have : (detPaCj U Uᴴ).comp (detPaCj Uᴴ U) = LinearMap.id := by
      ext W : 1
      simp only [LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2, Matrix.mul_one]
    rw [this, LinearMap.det_id]
  have hdet : LinearMap.det T = ∏ i, ∏ j, s i j := by
    simp only [T]
    rw [LinearMap.det_comp, LinearMap.det_comp]
    have hH : LinearMap.det H = ∏ i, ∏ j, s i j := detPaHad_det s
    rw [hH, mul_left_comm, hAB, mul_one]
  rw [hdet, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Algebra.norm_complex_apply, hs, Complex.normSq_ofReal, sq]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdStep
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdS_strictAnti {lam : Fin n → ℝ} (hlam : StrictAnti lam) {c : Fin n → ℕ} (hc : Antitone c) :
    StrictAnti (lam + fun i => (c i : ℝ)) := by
  intro i j hij
  simp only [Pi.add_apply]
  exact add_lt_add_of_lt_of_le (hlam hij) (by exact_mod_cast hc hij.le)

theorem fdS_hc {lam : Fin n → ℝ} (hlam : IsHCParam lam) {c : Fin n → ℕ} (hc : Antitone c) :
    IsHCParam (lam + fun i => (c i : ℝ)) := by
  unfold IsHCParam at hlam ⊢
  refine ⟨fdS_strictAnti hlam.1 hc, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hlam.2 a
  refine ⟨m + (c a : ℤ), ?_⟩
  simp only [Pi.add_apply]
  push_cast
  linarith

theorem fdS_gap {ε : Fin n → Bool} {h : ℝ} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) {c : Fin n → ℕ} (hc : Antitone c) :
    GapAtLeast ε (lam + fun i => (c i : ℝ)) h := by
  unfold GapAtLeast at hgap ⊢
  intro a b hab
  have h0 := hgap a b hab
  simp only [Pi.add_apply]
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have h1 := hlam hlt
    have h2 : (c b : ℝ) ≤ c a := by exact_mod_cast hc hlt.le
    rw [abs_of_pos (by linarith)] at h0
    rw [abs_of_pos (by linarith)]
    linarith
  · exact absurd (congrArg ε heq) hab
  · have h1 := hlam hgt
    have h2 : (c a : ℝ) ≤ c b := by exact_mod_cast hc hgt.le
    rw [abs_of_neg (by linarith)] at h0
    rw [abs_of_neg (by linarith)]
    linarith

private theorem vand_ne_zero_of_strictAnti {μ : Fin n → ℝ} (hμ : StrictAnti μ) : Vand μ ≠ 0 := by
  unfold Vand
  refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
  have hab : a < b := (Finset.mem_filter.mp hb).2
  exact sub_ne_zero.mpr (hμ hab).ne'

theorem fdS_stepQ {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {μ : Fin n → ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (s : Fin n)
    (hg' : GapAtLeast ε (μ + Pi.single s 1) h) (hs : StrictAnti (μ + Pi.single s 1)) :
    dfun (μ + Pi.single s 1) / Vand (μ + Pi.single s 1) = dfun μ / Vand μ := by
  have hμ1 : StrictAnti μ := by unfold IsHCParam at hμ; exact hμ.1
  rw [hstep μ s hμ hg hg' hs, ratioV_eq_vand hμ1 s]
  have h1 := vand_ne_zero_of_strictAnti hμ1
  have h2 := vand_ne_zero_of_strictAnti hs
  field_simp

theorem fdS_main {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) :
    ∀ (N : ℕ) (c : Fin n → ℕ), Antitone c → ∑ i, c i = N →
      dfun (lam + fun i => (c i : ℝ)) / Vand (lam + fun i => (c i : ℝ)) = dfun lam / Vand lam := by
  have hlam1 : StrictAnti lam := by unfold IsHCParam at hlam; exact hlam.1
  intro N
  induction N with
  | zero =>
    intro c _ hsum
    have hc0 : ∀ i, c i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
    have hfun : (lam + fun i => (c i : ℝ)) = lam := by
      funext i
      simp [hc0 i]
    rw [hfun]
  | succ N ih =>
    intro c hc hsum
    have hne : (univ.filter (fun i => c i ≠ 0)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      have h0 : ∑ i, c i = 0 := Finset.sum_eq_zero (fun i hi => by simpa using hemp hi)
      omega
    obtain ⟨s, hs_mem, hs_max⟩ : ∃ s ∈ univ.filter (fun i => c i ≠ 0), ∀ j ∈ univ.filter (fun i => c i ≠ 0), j ≤ s :=
      ⟨_, Finset.max'_mem _ hne, fun j hj => Finset.le_max' _ j hj⟩
    have hcs : c s ≠ 0 := (Finset.mem_filter.mp hs_mem).2
    have hbig : ∀ j, s < j → c j = 0 := by
      intro j hj
      by_contra hcj
      exact absurd hj (not_lt.mpr (hs_max j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩)))
    set c' : Fin n → ℕ := fun i => if i = s then c i - 1 else c i with hc'_def
    have hcc : ∀ i, c i = c' i + (if i = s then 1 else 0) := by
      intro i
      simp only [hc'_def]
      by_cases h : i = s
      · rw [if_pos h, if_pos h, h]; omega
      · rw [if_neg h, if_neg h]; rfl
    have hc' : Antitone c' := by
      intro i j hij
      simp only [hc'_def]
      rcases eq_or_ne i s with hi | hi <;> rcases eq_or_ne j s with hj | hj
      · rw [hi, hj]
      · have hsj : s < j := lt_of_le_of_ne (hi ▸ hij) (Ne.symm hj)
        rw [if_neg hj, hbig j hsj]
        exact Nat.zero_le _
      · have h' := hc hij
        rw [if_pos hj, if_neg hi]
        omega
      · rw [if_neg hj, if_neg hi]
        exact hc hij
    have hsum' : ∑ i, c' i = N := by
      have h' : ∑ i, c i = ∑ i, c' i + 1 := by
        rw [Finset.sum_congr rfl (fun i _ => hcc i), Finset.sum_add_distrib]
        simp
      omega
    have hfun : (lam + fun i => (c' i : ℝ)) + Pi.single s 1 = lam + fun i => (c i : ℝ) := by
      funext i
      simp only [Pi.add_apply, Pi.single_apply]
      rw [hcc i]
      push_cast
      split_ifs <;> ring
    have hQ := fdS_stepQ dfun hstep (fdS_hc hlam hc') (fdS_gap hlam1 hgap hc') s
      (by rw [hfun]; exact fdS_gap hlam1 hgap hc) (by rw [hfun]; exact fdS_strictAnti hlam1 hc)
    rw [hfun] at hQ
    rw [hQ, ih c' hc' hsum']

theorem fd_step {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (t : ℕ) :
    dfun (lamT lam t) / Vand (lamT lam t) = dfun lam / Vand lam := by
  have hD : ∀ a : Fin n, ((n : ℝ) - 1) - ((a : ℕ) : ℝ) = ((n - 1 - (a : ℕ) : ℕ) : ℝ) := by
    intro a
    have ha := a.2
    rw [Nat.cast_sub (by omega : (a : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hc : Antitone (fun a : Fin n => t * (n - 1 - (a : ℕ))) := by
    intro i j hij
    have h' := Fin.le_iff_val_le_val.mp hij
    exact Nat.mul_le_mul le_rfl (by omega)
  have hfun : lamT lam t = lam + fun i => (((fun a : Fin n => t * (n - 1 - (a : ℕ))) i : ℕ) : ℝ) := by
    funext i
    simp only [lamT, Pi.add_apply, Pi.smul_apply, Dvec, smul_eq_mul]
    rw [hD i]
    push_cast
    ring
  rw [hfun]
  exact fdS_main dfun hstep hlam hgap _ _ hc rfl

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.LeadingMinorConjDiagonal
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

theorem sum_castLE_eq_sum_ite_lt_formal_degree {M : Type*} [AddCommMonoid M] {n i : ℕ} (hi : i ≤ n) (g : Fin n → M) :
    ∑ a : Fin i, g (Fin.castLE hi a) = ∑ a : Fin n, if (a : ℕ) < i then g a else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE hi a) ?_ ?_ ?_ ?_
  · intro a _
    simp [Finset.mem_filter]
  · intro a _ b _ h
    exact Fin.castLE_injective hi h
  · intro b hb
    exact ⟨⟨b, (Finset.mem_filter.1 hb).2⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro a _
    rfl

theorem prod_orderEmbOfFin {R : Type*} [CommMonoid R] {n i : ℕ} (S : Finset (Fin n)) (h : S.card = i)
    (d : Fin n → R) : ∏ k : Fin i, d (S.orderEmbOfFin h k) = ∏ s ∈ S, d s := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S h, Finset.prod_map]
  rfl

theorem leading_minor_conj_diagonal {R : Type*} [CommRing R] (f : ℂ →+* R) {n i : ℕ} (hi : i ≤ n)
    (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → R) :
    ((U.map f * diagonal d * (Uᴴ).map f).submatrix (Fin.castLE hi) (Fin.castLE hi)).det =
      ∑ S : {S : Finset (Fin n) // S.card = i},
        f ((U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).det *
          star (U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).det) * ∏ s ∈ S.1, d s := by
  have hsplit : (U.map f * diagonal d * (Uᴴ).map f).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      ((U.map f).submatrix (Fin.castLE hi) id * diagonal d) * ((Uᴴ).map f).submatrix id (Fin.castLE hi) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
  have hdet : ∀ M : Matrix (Fin i) (Fin i) ℂ, (M.map f).det = f M.det :=
    fun M => (RingHom.map_det f M).symm
  rw [hsplit, cauchyBinet]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hA : ((U.map f).submatrix (Fin.castLE hi) id * diagonal d).submatrix id (S.1.orderEmbOfFin S.2) =
      (U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).map f *
        diagonal (fun k => d (S.1.orderEmbOfFin S.2 k)) := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.map_apply]
  have hB : (((Uᴴ).map f).submatrix id (Fin.castLE hi)).submatrix (S.1.orderEmbOfFin S.2) id =
      ((U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2))ᴴ).map f := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [hA, hB, Matrix.det_mul, Matrix.det_diagonal, hdet, hdet, Matrix.det_conjTranspose,
    prod_orderEmbOfFin S.1 S.2 d, map_mul]
  ring

open Polynomial in
theorem coeff_prod_one_add_low {ι : Type*} [DecidableEq ι] (S : Finset ι) (v : ι → ℂ) :
    (∏ s ∈ S, (1 + X * C (v s))).coeff 0 = 1 ∧ (∏ s ∈ S, (1 + X * C (v s))).coeff 1 = ∑ s ∈ S, v s ∧
    2 * (∏ s ∈ S, (1 + X * C (v s))).coeff 2 = (∑ s ∈ S, v s) ^ 2 - ∑ s ∈ S, v s ^ 2 := by
  refine Finset.induction_on S ?_ ?_
  · simp [Polynomial.coeff_one]
  · intro a S ha ih
    obtain ⟨h0, h1, h2⟩ := ih
    have e : ∀ P : ℂ[X], (1 + X * C (v a)) * P = P + X * (C (v a) * P) := fun P => by ring
    rw [Finset.prod_insert ha, e, Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, ?_, ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, h0, add_zero]
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, h1, h0]
      ring
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, mul_add, h2, h1]
      ring

open Polynomial in
theorem conj_polynomial_diagonal {m : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (hV : V * Vᴴ = 1) (ν : Fin m → ℂ) :
    V.map C * diagonal (fun s => 1 + X * C (ν s)) * (Vᴴ).map C =
      1 + (X : ℂ[X]) • (V * diagonal ν * Vᴴ).map C := by
  have hD : diagonal (fun s => 1 + X * C (ν s)) = 1 + (X : ℂ[X]) • (diagonal ν).map C := by
    ext a b
    by_cases h : a = b
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hV,
    Matrix.map_one _ (map_zero C) (map_one C)]

theorem trace_conj_eq_trace_of_conjTranspose_mul_self {m : ℕ} (V D : Matrix (Fin m) (Fin m) ℂ) (hV : Vᴴ * V = 1) :
    trace (V * D * Vᴴ) = trace D := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

theorem sq_conj_diagonal {m : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (ν : Fin m → ℂ) (hV : Vᴴ * V = 1) :
    V * diagonal ν * Vᴴ * (V * diagonal ν * Vᴴ) = V * diagonal (fun s => ν s ^ 2) * Vᴴ := by
  calc V * diagonal ν * Vᴴ * (V * diagonal ν * Vᴴ) = V * diagonal ν * (Vᴴ * V) * diagonal ν * Vᴴ := by
        simp only [Matrix.mul_assoc]
    _ = V * diagonal (fun s => ν s ^ 2) * Vᴴ := by
        rw [hV, Matrix.mul_one, Matrix.mul_assoc V, Matrix.diagonal_mul_diagonal]
        simp [sq]

open Polynomial in
theorem coeff_two_det_hermitian {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.IsHermitian) :
    2 * (det (1 + (X : ℂ[X]) • A.map C)).coeff 2 = (trace A) ^ 2 - trace (A * A) := by
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  set ν : Fin m → ℂ := fun s => ((hA.eigenvalues s : ℝ) : ℂ) with hν
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.prop
  have hUU' : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.prop
  have hAeq : A = U * diagonal ν * Uᴴ := hA.spectral_theorem
  have hconj := conj_polynomial_diagonal U hUU ν
  have hdU : (U.map C).det * ((Uᴴ).map C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero C) (map_one C), Matrix.det_one]
  have hdet : (1 + (X : ℂ[X]) • (U * diagonal ν * Uᴴ).map C).det = ∏ s, (1 + X * C (ν s)) := by
    rw [← hconj, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm ((U.map C).det), mul_assoc,
      hdU, mul_one]
  rw [hAeq, hdet, (coeff_prod_one_add_low Finset.univ ν).2.2, sq_conj_diagonal U ν hUU', trace_conj_eq_trace_of_conjTranspose_mul_self U _ hUU',
    trace_conj_eq_trace_of_conjTranspose_mul_self U _ hUU', Matrix.trace_diagonal, Matrix.trace_diagonal]

theorem trace_leading_submatrix {n i : ℕ} (hi : i ≤ n) (M : Matrix (Fin n) (Fin n) ℂ) :
    trace (M.submatrix (Fin.castLE hi) (Fin.castLE hi)) = ∑ a : Fin n, if (a : ℕ) < i then M a a else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact sum_castLE_eq_sum_ite_lt_formal_degree hi (fun a => M a a)

theorem variance_eq_trace_diff {n i : ℕ} (hi : i ≤ n) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    ((Vi M i : ℝ) : ℂ) = trace ((M * M).submatrix (Fin.castLE hi) (Fin.castLE hi)) -
      trace (M.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi)) := by
  have hMab : ∀ a b, M a b * M b a = (‖M b a‖ : ℂ) ^ 2 := by
    intro a b
    rw [← hM.apply a b]
    exact Complex.conj_mul' (M b a)
  have h1 : trace ((M * M).submatrix (Fin.castLE hi) (Fin.castLE hi)) =
      ∑ a : Fin n, if (a : ℕ) < i then ∑ b : Fin n, M a b * M b a else 0 := by
    rw [trace_leading_submatrix hi]
    simp only [Matrix.mul_apply]
  have inner : ∀ a : Fin n, ∑ b : Fin i, M a (Fin.castLE hi b) * M (Fin.castLE hi b) a =
      ∑ b : Fin n, if (b : ℕ) < i then M a b * M b a else 0 :=
    fun a => sum_castLE_eq_sum_ite_lt_formal_degree hi (fun b => M a b * M b a)
  have h2 : trace (M.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi)) =
      ∑ a : Fin n, if (a : ℕ) < i then
        ∑ b : Fin n, (if (b : ℕ) < i then M a b * M b a else 0) else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.submatrix_apply]
    calc ∑ a : Fin i, ∑ b : Fin i, M (Fin.castLE hi a) (Fin.castLE hi b) * M (Fin.castLE hi b) (Fin.castLE hi a)
        = ∑ a : Fin i, (fun a' : Fin n => ∑ b : Fin n, if (b : ℕ) < i then M a' b * M b a' else 0)
            (Fin.castLE hi a) := Finset.sum_congr rfl fun a _ => inner _
      _ = _ := sum_castLE_eq_sum_ite_lt_formal_degree hi (fun a' : Fin n => ∑ b : Fin n, if (b : ℕ) < i then M a' b * M b a' else 0)
  rw [h1, h2, ← Finset.sum_sub_distrib]
  simp only [Vi, Complex.ofReal_sum, apply_ite Complex.ofReal, Complex.ofReal_zero, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : ℕ) < i
  · rw [if_pos ha, if_pos ha, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : (b : ℕ) < i
    · rw [if_pos hb, sub_self, if_neg (by omega)]
    · rw [if_neg hb, sub_zero, if_pos (by omega), hMab]
  · rw [if_neg ha, if_neg ha, sub_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (by omega)]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem toMK_inv_eq_conjTranspose {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h : toMK k⁻¹ = star (toMK k) :=
    Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem (show toMK k ∈ Kset ε from k.2).1)
  rw [h, Matrix.star_eq_conjTranspose]

theorem conj_pmat_eq_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    toMK k⁻¹ * pmat z * toMK k = pmat (adK k⁻¹ z) := by
  rw [pmat_adK, toMK_inv_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

theorem rhoP_real_smul {ε : Fin n → Bool} (t : ℝ) (z : PCoord ε → ℂ) : rhoP ((t : ℂ) • z) = |t| * rhoP z := by
  have hS : ∑ ab, ‖((t : ℂ) • z) ab‖ ^ 2 = t ^ 2 * ∑ ab, ‖z ab‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    simp [Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold rhoP
  rw [hs_pmat, hs_pmat, hS, show 2 * (t ^ 2 * ∑ ab, ‖z ab‖ ^ 2) = t ^ 2 * (2 * ∑ ab, ‖z ab‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ShcAdC
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) (w : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => shcAd y (pmat w) ab.1.1 ab.1.2

theorem detPb {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      (LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
        (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))) ^ 4 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  have hU : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have hU' : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  have hY : U * dpbD (pev y) * Uᴴ = pmat y := (pmat_isHermitian y).spectral_theorem.symm
  have e1 : shcAd y = LinearMap.toContinuousLinearMap (dpbL U (pev y) shc) := rfl
  have e2 : shcAdC y = LinearMap.toContinuousLinearMap (dpbP ε ∘ₗ dpbL U (pev y) shc ∘ₗ dpbE ε) := by
    funext w ab
    refine (dpbP_herm (W := dpbH U (pev y) shc (pmat w)) ?_ ab).symm
    rw [dpbH_conjTranspose U _ shc dpb_shc_neg, (pmat_isHermitian w).eq]
  rw [e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact dpb_det hU hU' (by rw [hY]; exact dpb_JYJ y)

end ReciprocityTheory.ChartRestriction.DS
end
end

