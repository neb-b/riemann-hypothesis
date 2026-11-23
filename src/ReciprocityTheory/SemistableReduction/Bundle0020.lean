module

public import ReciprocityTheory.SemistableReduction.Bundle0014

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegDA
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem sdd_quad_conj {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin m → ℂ) :
    star w ⬝ᵥ ((Pᴴ * Q * P) *ᵥ w) = star (P *ᵥ w) ⬝ᵥ (Q *ᵥ (P *ᵥ w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, star_mulVec]

theorem sdd_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, A = Bᴴ * B ∧ IsUnit B.det := by
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)
  refine ⟨B, hB, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hp := hA.det_pos
  rw [hB, star_eq_conjTranspose, det_mul, h0, mul_zero] at hp
  exact lt_irrefl _ hp

theorem sdd_star_self_eig {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian) (i : Fin n) :
    star (⇑(hD.eigenvectorBasis i)) ⬝ᵥ (⇑(hD.eigenvectorBasis i)) = 1 := by
  have h := orthonormal_iff_ite.mp hD.eigenvectorBasis.orthonormal i i
  rw [if_pos rfl, PiLp.inner_apply] at h
  rw [← h]
  simp only [dotProduct, Pi.star_apply, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Complex.star_def, mul_comm]

theorem sdd_quad_eig {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian) (i : Fin n) :
    star (⇑(hD.eigenvectorBasis i)) ⬝ᵥ (D *ᵥ ⇑(hD.eigenvectorBasis i)) = (hD.eigenvalues i : ℂ) := by
  rw [hD.mulVec_eigenvectorBasis, dotProduct_smul, sdd_star_self_eig hD i]
  simp

theorem sdd_det_abs_le_one {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian)
    (h : ∀ w : Fin n → ℂ, ‖star w ⬝ᵥ (D *ᵥ w)‖ ≤ (star w ⬝ᵥ w).re) : ‖D.det‖ ≤ 1 := by
  rw [hD.det_eq_prod_eigenvalues, norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i _
  have hi := h (hD.eigenvectorBasis i)
  rwa [sdd_quad_eig hD i, sdd_star_self_eig hD i, Complex.one_re] at hi

theorem sdd_det_ge_one {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian)
    (h : ∀ w : Fin n → ℂ, (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (D *ᵥ w)).re) :
    D.det = ((D.det.re : ℝ) : ℂ) ∧ 1 ≤ D.det.re := by
  have hev : ∀ i, 1 ≤ hD.eigenvalues i := by
    intro i
    have hi := h (hD.eigenvectorBasis i)
    rwa [sdd_quad_eig hD i, sdd_star_self_eig hD i, Complex.one_re, Complex.ofReal_re] at hi
  have hdet : D.det = ((∏ i, hD.eigenvalues i : ℝ) : ℂ) := by
    rw [hD.det_eq_prod_eigenvalues, Complex.ofReal_prod]
    rfl
  rw [hdet, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => hev i)

theorem sdd_congr {n : ℕ} (B X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit B.det) :
    X = Bᴴ * ((B⁻¹)ᴴ * X * B⁻¹) * B ∧
    ∀ w : Fin n → ℂ, star w ⬝ᵥ (((B⁻¹)ᴴ * X * B⁻¹) *ᵥ w) =
      star (B⁻¹ *ᵥ w) ⬝ᵥ (X *ᵥ (B⁻¹ *ᵥ w)) := by
  refine ⟨?_, fun w => sdd_quad_conj B⁻¹ X w⟩
  have h1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hu
  have h2 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  calc X = (Bᴴ * (B⁻¹)ᴴ) * X * (B⁻¹ * B) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem sdd_quad_self {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit B.det) (w : Fin n → ℂ) :
    star w ⬝ᵥ w = star (B⁻¹ *ᵥ w) ⬝ᵥ ((Bᴴ * B) *ᵥ (B⁻¹ *ᵥ w)) := by
  have hw : B *ᵥ (B⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hu, Matrix.one_mulVec]
  have e := sdd_quad_conj B 1 (B⁻¹ *ᵥ w)
  rw [Matrix.mul_one, hw, Matrix.one_mulVec] at e
  exact e.symm

theorem sdd_norm_det_sq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    (Bᴴ * B).det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem sdd_det_congr {n : ℕ} (B D : Matrix (Fin n) (Fin n) ℂ) :
    (Bᴴ * D * B).det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) * D.det := by
  rw [det_mul, det_mul, ← sdd_norm_det_sq B, det_mul]
  ring

theorem sdd_absDet {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hC : C.IsHermitian)
    (h : ∀ v : Fin n → ℂ, ‖star v ⬝ᵥ (C *ᵥ v)‖ ≤ (star v ⬝ᵥ (A *ᵥ v)).re) :
    ‖C.det‖ ≤ A.det.re := by
  obtain ⟨B, hAB, hu⟩ := sdd_factor hA
  obtain ⟨hCe, hq⟩ := sdd_congr B C hu
  have hDh : ((B⁻¹)ᴴ * C * B⁻¹).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hC.eq, Matrix.mul_assoc]
  have hD1 : ‖((B⁻¹)ᴴ * C * B⁻¹).det‖ ≤ 1 := by
    apply sdd_det_abs_le_one hDh
    intro w
    rw [hq w, sdd_quad_self B hu w, ← hAB]
    exact h _
  have hdetA : A.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by rw [hAB, sdd_norm_det_sq]
  rw [hCe, sdd_det_congr, hdetA, Complex.ofReal_re, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖B.det‖ ^ 2 * ‖((B⁻¹)ᴴ * C * B⁻¹).det‖ ≤ ‖B.det‖ ^ 2 * 1 := by gcongr
    _ = _ := mul_one _

theorem sdd_det_mono {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) (hY : Y.IsHermitian)
    (h : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).re ≤ (star v ⬝ᵥ (Y *ᵥ v)).re) :
    0 < X.det.re ∧ X.det.re ≤ Y.det.re := by
  obtain ⟨B, hXB, hu⟩ := sdd_factor hX
  obtain ⟨hYe, hq⟩ := sdd_congr B Y hu
  have hDh : ((B⁻¹)ᴴ * Y * B⁻¹).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hY.eq, Matrix.mul_assoc]
  obtain ⟨hDr, hD1⟩ := sdd_det_ge_one hDh (fun w => by
    rw [hq w, sdd_quad_self B hu w, ← hXB]
    exact h _)
  have hdetX : X.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by rw [hXB, sdd_norm_det_sq]
  have hBpos : 0 < ‖B.det‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu.ne_zero) 2
  rw [hdetX, hYe, sdd_det_congr, hDr, Complex.ofReal_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact ⟨hBpos, le_mul_of_one_le_right hBpos.le hD1⟩

def embM {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun l i => σ (b i l)

theorem sdd_gramX_eq {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    gramX H σ b c = (embM σ b)ᴴ * H * embM σ c := by
  ext i j
  simp only [gramX, embM, embVec, Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sdd_gramC_eq {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embM σ b)ᴴ * H * embM σ b := sdd_gramX_eq H σ b b

theorem sdd_embM_inj {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) : Function.Injective (embM σ b).mulVec := by
  classical
  let M : Matrix (Fin r) (Fin k) K := Matrix.of fun l i => b i l
  have hM : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hs : ∑ i, x i • b i = M.mulVecLin x := by
      ext l
      simp [M, Matrix.mulVec, dotProduct, mul_comm, Finset.sum_apply]
    rw [hx] at hs
    exact funext (Fintype.linearIndependent_iff.mp hb x hs)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.mpr hM)
  have hLM : LinearMap.toMatrix' g * M = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      LinearMap.toMatrix'_mulVec]
    exact LinearMap.congr_fun hg x
  have hE : embM σ b = M.map σ := rfl
  intro x y hxy
  have e := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simp only [hE, Matrix.mulVec_mulVec, ← Matrix.map_mul, hLM, Matrix.map_one _ (map_zero σ) (map_one σ),
    Matrix.one_mulVec] at e
  exact e

theorem sdd_diag_quad {r : ℕ} (d : Fin r → ℝ) (x : Fin r → ℂ) :
    (star x ⬝ᵥ (diagonal (fun l => (d l : ℂ)) *ᵥ x)).re = ∑ l, d l * ‖x l‖ ^ 2 := by
  have e : star x ⬝ᵥ (diagonal (fun l => (d l : ℂ)) *ᵥ x) = ∑ l, ((d l * ‖x l‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, ← mul_assoc, mul_comm ((starRingEnd ℂ) (x l)), mul_assoc, Complex.conj_mul']
    push_cast
    ring
  rw [e, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem sdd_cut_quad {r k : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 ≤ d l) (e : ℕ)
    (E B1 : Matrix (Fin r) (Fin k) ℂ) (hB1 : ∀ l j, B1 l j = if e ≤ (l : ℕ) then E l j else 0)
    (v : Fin k → ℂ) :
    (star v ⬝ᵥ ((B1ᴴ * diagonal (fun l => (d l : ℂ)) * B1) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * diagonal (fun l => (d l : ℂ)) * E) *ᵥ v)).re := by
  rw [sdd_quad_conj, sdd_quad_conj, sdd_diag_quad, sdd_diag_quad]
  refine Finset.sum_le_sum fun l _ => ?_
  have hrow : (B1 *ᵥ v) l = if e ≤ (l : ℕ) then (E *ᵥ v) l else 0 := by
    by_cases hc : e ≤ (l : ℕ) <;> simp [Matrix.mulVec, dotProduct, hB1, hc]
  rw [hrow]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    nlinarith [hd l, sq_nonneg ‖(E *ᵥ v) l‖]

theorem sdd_schur {r k₀ k₁ : ℕ} (B : Matrix (Fin r) (Fin k₀) ℂ) (C : Matrix (Fin r) (Fin k₁) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : Hᴴ = H) (hG : (Bᴴ * H * B).IsHermitian)
    (hu : IsUnit (Bᴴ * H * B).det) :
    Cᴴ * H * C - (Cᴴ * H * B) * (Bᴴ * H * B)⁻¹ * (Bᴴ * H * C) =
      (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C)))ᴴ * H *
        (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C))) := by
  set G := Bᴴ * H * B with hGdef
  have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hu
  have hGinvH : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hG.eq]
  have hYH : (Bᴴ * H * C)ᴴ = Cᴴ * H * B := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  have hXh : (G⁻¹ * (Bᴴ * H * C))ᴴ = (Cᴴ * H * B) * G⁻¹ := by
    rw [conjTranspose_mul, hYH, hGinvH]
  have hcanc : ∀ Z : Matrix (Fin k₀) (Fin k₁) ℂ, G⁻¹ * (Bᴴ * (H * (B * Z))) = Z := by
    intro Z
    have hz : Bᴴ * (H * (B * Z)) = G * Z := by simp only [hGdef, Matrix.mul_assoc]
    rw [hz, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
  rw [conjTranspose_sub, conjTranspose_mul, hXh]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hcanc]
  abel

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegE
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem exists_kBasisIn {K : Type} [Field K] [NumberField K] {r : ℕ}
    (B : Submodule (𝓞 K) (Fin r → K)) : ∃ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b := by
  classical
  obtain ⟨s, hsB, hspan, hli⟩ := exists_linearIndependent K (B : Set (Fin r → K))
  have hfin : s.Finite := by
    first
    | exact hli.setFinite
    | exact Set.toFinite s
    | exact (Set.finite_coe_iff.mp hli.finite)
  haveI : Fintype s := hfin.fintype
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => ((e.symm i : s) : Fin r → K), fun i => hsB (e.symm i).2,
    hli.comp _ e.symm.injective, ?_⟩
  intro x hx
  have hx' : x ∈ Submodule.span K s := by
    rw [hspan]
    exact Submodule.subset_span hx
  have hr : Set.range (fun i => ((e.symm i : s) : Fin r → K)) = s := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
  rw [hr]
  exact hx'

theorem kBasisIn_bot_eq {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : IsKBasisIn (⊥ : Submodule (𝓞 K) (Fin r → K)) b) : k = 0 := by
  obtain ⟨hmem, hli, -⟩ := hb
  by_contra hk
  have i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
  exact hli.ne_zero i ((Submodule.mem_bot _).mp (hmem i))

theorem latDeg_zero_fam {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin 0 → Fin r → K) (hb : IsKBasisIn B b) : latDeg H B b = 0 := by
  obtain ⟨-, -, hspan⟩ := hb
  have hB : B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h := hspan x hx
    simpa [Set.range_eq_empty] using h
  subst hB
  simp [latDeg, Set.range_eq_empty]

theorem spanIdx_ne_zero {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (hB : B.FG)
    (hb : IsKBasisIn B b) : spanIdx B b ≠ 0 := by
  classical
  obtain ⟨hmem, hli, hspan⟩ := hb
  obtain ⟨G, hG⟩ := id hB
  have hcoef : ∀ g ∈ G, ∃ c : Fin k → K, g = ∑ i, c i • b i := by
    intro g hg
    have hgB : g ∈ B := by
      rw [← hG]
      exact Submodule.subset_span hg
    exact ((Submodule.mem_span_range_iff_exists_fun K).mp (hspan g hgB)).imp fun c hc => hc.symm
  choose! c hc using hcoef
  obtain ⟨β, hβ⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 K)) (S := K)
    (G ×ˢ (Finset.univ : Finset (Fin k))) (fun p => c p.1 p.2)
  have hβS : ∀ x ∈ B, (β : 𝓞 K) • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro x hx
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      rw [hc g hg, Finset.smul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨t, ht⟩ := hβ (g, i) (Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩)
      rw [← smul_assoc]
      simp only at ht
      rw [← ht, algebraMap_smul]
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ a hx
  have hβ0 : (β : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero β
  have hint : IsIntegral ℤ (β : 𝓞 K) := Algebra.IsIntegral.isIntegral _
  have hp0 : (minpoly ℤ (β : 𝓞 K)).coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := minpoly ℤ (β : 𝓞 K))
    rw [h0, map_zero, sub_zero] at hq
    have hmon : q.Monic := Polynomial.monic_X.of_mul_monic_left (hq ▸ minpoly.monic hint)
    have hq0 : Polynomial.aeval (β : 𝓞 K) q = 0 := by
      have h := minpoly.aeval ℤ (β : 𝓞 K)
      rw [hq, map_mul, Polynomial.aeval_X] at h
      exact (mul_eq_zero.mp h).resolve_left hβ0
    have hdeg : (minpoly ℤ (β : 𝓞 K)).degree ≤ q.degree := by
      first
      | exact minpoly.min ℤ (β : 𝓞 K) hmon hq0
      | exact minpoly.min (A := ℤ) (x := (β : 𝓞 K)) hmon hq0
    rw [hq, Polynomial.degree_mul, Polynomial.degree_X,
      Polynomial.degree_eq_natDegree hmon.ne_zero] at hdeg
    have h2 : 1 + q.natDegree ≤ q.natDegree := by exact_mod_cast hdeg
    omega
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := minpoly ℤ (β : 𝓞 K))
  have hdiv : (((minpoly ℤ (β : 𝓞 K)).coeff 0 : ℤ) : 𝓞 K) =
      (β : 𝓞 K) * (-(Polynomial.aeval (β : 𝓞 K) q)) := by
    have h := congrArg (Polynomial.aeval (β : 𝓞 K)) hq
    simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, minpoly.aeval,
      zero_sub] at h
    rw [mul_neg, ← h, neg_neg, eq_intCast]
  set m : ℤ := (minpoly ℤ (β : 𝓞 K)).coeff 0 with hm
  have hmS : ∀ x ∈ B, m • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro x hx
    rw [← Int.cast_smul_eq_zsmul (𝓞 K), hdiv, mul_smul]
    exact hβS _ (Submodule.smul_mem _ _ hx)
  have hfinB : Module.Finite ℤ B := by
    haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr hB
    exact Module.Finite.trans (𝓞 K) B
  haveI hfg : AddGroup.FG B := Module.Finite.iff_addGroup_fg.mp hfinB
  let N : Submodule (𝓞 K) B := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype
  haveI hfgQ : AddGroup.FG (B ⧸ N.toAddSubgroup) := by
    first
    | exact AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective N.toAddSubgroup)
    | exact QuotientAddGroup.fg N.toAddSubgroup
    | infer_instance
  have htors : IsAddTorsion (B ⧸ N.toAddSubgroup) := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H x =>
      refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨m.natAbs, Int.natAbs_pos.mpr hp0, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      show (m.natAbs • (x : Fin r → K)) ∈ Submodule.span (𝓞 K) (Set.range b)
      have e1 : (m.natAbs • (x : Fin r → K)) = ((m.natAbs : ℤ) • (x : Fin r → K)) := by simp
      rw [e1]
      rcases Int.natAbs_eq m with h | h
      · rw [← h]
        exact hmS _ x.2
      · rw [show ((m.natAbs : ℤ)) = -m by omega, neg_smul]
        exact Submodule.neg_mem _ (hmS _ x.2)
  have hfinQ : Finite (B ⧸ N.toAddSubgroup) := by
    first
    | exact AddCommGroup.finite_of_fg_torsion _ htors
    | exact AddCommGroup.finite_of_fg_torsion htors
  have : N.toAddSubgroup.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  exact this

theorem latDeg_le_of_le {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (C B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (hCB : C ≤ B) (hB : B.FG) (hbC : IsKBasisIn C b)
    (hbB : IsKBasisIn B b) : latDeg H C b ≤ latDeg H B b := by
  have hSC : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup ≤ C.toAddSubgroup := by
    intro x hx
    exact (Submodule.span_le.mpr (Set.range_subset_iff.mpr hbC.1)) hx
  have hCB' : C.toAddSubgroup ≤ B.toAddSubgroup := fun x hx => hCB hx
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hSC hCB'
  have hne : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 :=
    spanIdx_ne_zero B b hB hbB
  have h1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hne) ⟨_, hmul.symm⟩
  have h2 : 0 < (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup := by
    refine Nat.pos_of_ne_zero fun h => hne ?_
    rw [← hmul, h, zero_mul]
  unfold latDeg
  have h3 : Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      C.toAddSubgroup : ℕ) : ℝ) ≤ Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      B.toAddSubgroup : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast h2) (by exact_mod_cast h1)
  linarith

theorem sum_log_norm_emb {K : Type} [Field K] [NumberField K] (a : K) :
    ∑ σ : K →+* ℂ, Real.log ‖σ a‖ = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  by_cases ha : a = 0
  · subst ha
    simp
  · have h1 : ((Algebra.norm ℚ a : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ a := by
      have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
      simp only [eq_ratCast] at h
      rw [h]
      exact Fintype.prod_bijective (fun σ : K →ₐ[ℚ] ℂ => (σ : K →+* ℂ))
        ⟨fun σ τ h => AlgHom.coe_ringHom_injective h,
          fun τ => ⟨τ.toRatAlgHom, RingHom.ext fun x => rfl⟩⟩ _ _ (fun σ => rfl)
    rw [← Real.log_prod (s := Finset.univ) (f := fun σ : K →+* ℂ => ‖σ a‖)
      (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ha)), ← norm_prod,
      ← h1]
    first
    | rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    | simp [Complex.norm_ratCast]
    | simp

def embMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a i => σ (b i a)

theorem gramC_eq {K : Type} [Field K] [NumberField K] {r k : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embMat σ b)ᴴ * H * embMat σ b := by
  ext i j
  rw [Matrix.mul_assoc]
  simp [gramC, embMat, Matrix.mul_apply, Matrix.mulVec, dotProduct, embVec]

theorem embMat_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (hli : LinearIndependent K b) :
    Function.Injective (embMat σ b).mulVec := by
  classical
  let A : Matrix (Fin r) (Fin k) K := Matrix.of fun a i => b i a
  have hA : Function.Injective (Matrix.toLin' A) := by
    intro x y hxy
    have hinj : Function.Injective A.mulVec := by
      rw [Matrix.mulVec_injective_iff]
      exact hli
    exact hinj (by simpa [Matrix.toLin'_apply] using hxy)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A)
    (LinearMap.ker_eq_bot.mpr hA)
  have hBA : LinearMap.toMatrix' g * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h
  have hE : embMat σ b = A.map σ := by
    ext a i
    rfl
  have hBA' : (LinearMap.toMatrix' g).map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one σ (map_zero σ) (map_one σ)]
  intro x y hxy
  rw [hE] at hxy
  have := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, hBA'] using this

theorem gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hli : LinearIndependent K b) : (gramC H σ b).PosDef := by
  rw [gramC_eq]
  exact hH.conjTranspose_mul_mul_same (embMat_injective S σ b hli)

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

