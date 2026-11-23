module

public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.StatementQ

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetTopConvergence
section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.Ux7

theorem decayMin : DecayMin := by
  intro x A hx hA
  refine le_min ?_ ?_
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  · rw [Real.rpow_neg (by linarith), Real.rpow_neg hx.le]
    have h1 : 0 < x ^ A := Real.rpow_pos_of_pos hx A
    have h2 : x ^ A ≤ (1 + x) ^ A := Real.rpow_le_rpow hx.le (by linarith) hA
    first
      | exact inv_anti₀ h1 h2
      | exact inv_le_inv_of_le h1 h2

theorem scaleMatch : ScaleMatch := by
  have e1 : ∀ x : ℂ, (cStd * (starRingEnd ℂ) x).re = (betaU * x).re := by
    intro x
    simp [cStd, betaU, Complex.mul_re]
  have e2 : ∀ x : ℂ, (betaU * x).re = -(cStd * x).re := by
    intro x
    simp [cStd, betaU, Complex.mul_re]
  refine ⟨?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · apply Complex.ext <;> simp [cStd, betaU]
  · simp [betaU, cStd]
  · simp only [G.psi]
    rw [e1]
  · simp only [G.psi]
    rw [e2]
    show (starRingEnd ℂ) (Complex.exp _) = _
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring

theorem budget_second_corollary_holds : DerivativeBudgetCount := by
  intro r m mmB o κjo As Cc A₀ hr hm hmm ho hk hCc hA
  have hX : (m + 1 + mmB) + o ≤ 3 * As := by omega
  refine ⟨hX, ?_⟩
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hXR : ((((m + 1 + mmB) + o : ℕ)) : ℝ) ≤ 3 * As := by exact_mod_cast hX
  have hkR : (κjo : ℝ) ≤ As := by exact_mod_cast hk
  have hmR : (m : ℝ) + 1 ≤ As := by exact_mod_cast hm
  have hmmR : (mmB : ℝ) ≤ As := by exact_mod_cast hmm
  have hAs0 : (0 : ℝ) ≤ As := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have p1 := mul_le_mul_of_nonneg_left hXR (show (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) by linarith)
  have p2 := mul_le_mul_of_nonneg_left hmR (show (0 : ℝ) ≤ 5 * (r : ℝ) by linarith)
  have p3 := mul_le_mul_of_nonneg_left hmmR (show (0 : ℝ) ≤ 2 * (r : ℝ) by linarith)
  have h2 : A₀ - (As : ℝ) - 6 * ((r : ℝ) + 1) * (As : ℝ) ≤
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) := by nlinarith
  have h3' : A₀ - (13 * (r : ℝ) + 7) * (As : ℝ) ≤
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) - 5 * r * ((m : ℝ) + 1) -
        2 * r * mmB := by nlinarith
  have hden : (0 : ℝ) < 8 * (2 * (r : ℝ) + 1) := by linarith
  have ha1 : 8 * (2 * (r : ℝ) + 1) *
      a1 r (A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ)) m mmB =
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) - 5 * r * ((m : ℝ) + 1) -
        2 * r * mmB := by
    unfold a1
    field_simp
  have hrA : (0 : ℝ) ≤ r * As := mul_nonneg hr0 hAs0
  refine ⟨h2, by rw [ha1]; exact h3', by nlinarith, ?_⟩
  apply le_of_mul_le_mul_left _ hden
  rw [ha1]
  have hQ : 0 ≤ (Cc - 20) * (((r : ℝ) + 1) ^ 3 * As) :=
    mul_nonneg (by linarith) (by positivity)
  have h4 : 1 + 4 * (r : ℝ) ≤ ((r : ℝ) + 1) ^ 4 := by
    nlinarith [pow_nonneg hr0 2, pow_nonneg hr0 3, pow_nonneg hr0 4]
  have h5 := mul_le_mul_of_nonneg_right h4 hAs0
  calc 8 * (2 * (r : ℝ) + 1) * ((Cc - 20) / 16 * ((r : ℝ) + 1) ^ 3 * (As : ℝ))
      = (2 * (r : ℝ) + 1) / 2 * ((Cc - 20) * (((r : ℝ) + 1) ^ 3 * As)) := by ring
    _ ≤ ((r : ℝ) + 1) * ((Cc - 20) * (((r : ℝ) + 1) ^ 3 * As)) :=
        mul_le_mul_of_nonneg_right (by linarith) hQ
    _ = Cc * (((r : ℝ) + 1) ^ 4 * As) - 20 * (((r : ℝ) + 1) ^ 4 * As) := by ring
    _ ≤ Cc * (((r : ℝ) + 1) ^ 4 * As) - (13 * (r : ℝ) + 7) * As := by nlinarith
    _ ≤ A₀ - (13 * (r : ℝ) + 7) * (As : ℝ) := by nlinarith
    _ ≤ _ := h3'

theorem thresholds_second_corollary_holds : GermThresholds := by
  intro r n s As C₁ c AB hn hs hAs hAB hc hC
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hAsR : (n : ℝ) ^ 3 ≤ As := by exact_mod_cast hAs
  have hsR : (s : ℝ) ≤ r := by exact_mod_cast hs
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hn3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hnR (show 1 ≤ 3 by norm_num)
  have hAs1 : (1 : ℝ) ≤ As := by nlinarith
  have hnA : (n : ℝ) ≤ As := by linarith
  have hR : (1 : ℝ) + 3 * r ≤ ((r : ℝ) + 1) ^ 3 := by nlinarith [sq_nonneg (r : ℝ)]
  have hP : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := by linarith
  have hPA : 0 ≤ ((r : ℝ) + 1) ^ 3 * (As : ℝ) := by positivity
  have key : ((r : ℝ) + 1) ^ 3 * (As : ℝ) ≤ c * ((r : ℝ) + 1) ^ 3 * (As : ℝ) := by
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have e1 : 2 * (r : ℝ) * n ≤ 2 * r * As := by nlinarith
    have e2 : 2 * (r : ℝ) * As < (1 + 3 * r) * As := by nlinarith
    have e3 : (1 + 3 * (r : ℝ)) * As ≤ ((r : ℝ) + 1) ^ 3 * As :=
      mul_le_mul_of_nonneg_right hR (by linarith)
    linarith
  · have e3 : (As : ℝ) ≤ ((r : ℝ) + 1) ^ 3 * As := by nlinarith
    linarith
  · have e1 : (s : ℝ) ^ 2 ≤ ((r : ℝ) + 1) ^ 3 := by nlinarith [mul_le_mul hsR hsR hs0 hr0]
    have hC0 : (0 : ℝ) ≤ C₁ := Nat.cast_nonneg _
    have e2 : (C₁ : ℝ) * s ^ 2 ≤ c * ((r : ℝ) + 1) ^ 3 :=
      calc (C₁ : ℝ) * s ^ 2 ≤ c * s ^ 2 := mul_le_mul_of_nonneg_right hC (by positivity)
        _ ≤ c * ((r : ℝ) + 1) ^ 3 := mul_le_mul_of_nonneg_left e1 (by linarith)
    have hcP : 0 ≤ c * ((r : ℝ) + 1) ^ 3 := mul_nonneg (by linarith) (by positivity)
    have e3 : c * ((r : ℝ) + 1) ^ 3 ≤ c * ((r : ℝ) + 1) ^ 3 * As := by nlinarith
    linarith

theorem powerMatch : PowerMatch := by
  intro m M β t D V _ _ Φ hM ht
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
  have hnt : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have key : ((‖t‖ ^ (m + 1))⁻¹ * ‖t‖ ^ ((m + 1) * (M' + 2 + m)) * ‖D / t ^ (m + 1)‖ ^ M' : ℝ) =
      ‖D‖ ^ M' * ‖t‖ ^ ((m + 1) ^ 2) := by
    rw [norm_div, norm_pow, div_pow]
    field_simp
    ring
  have hc : D / t ^ (m + 1) * t ^ (m + 1) = D := div_mul_cancel₀ D (pow_ne_zero _ ht)
  simp only [uD, aD, G.remainder, Nat.add_sub_cancel]
  rw [key, hc, smul_sub, smul_smul, Complex.ofReal_mul]

theorem derivBoundOfDecay : DerivBoundOfDecay := by
  intro s k V _ _ Φ A K Kd hs hA hK hKd h Z hZ
  have hdet : G.detM Z ≠ 0 := fun e => hKd (by rw [← e]; exact hZ)
  obtain ⟨hc, hb⟩ := h Z hdet
  have hZ0 : Z ≠ 0 := by
    rintro rfl
    apply hdet
    haveI : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
    simp only [G.detM]
    exact Matrix.det_zero
  have hpos : 0 < ‖Z‖ := norm_pos_iff.mpr hZ0
  exact ⟨hc, fun j hj => (hb j hj).trans (mul_le_mul_of_nonneg_left (decayMin _ _ hpos hA) hK)⟩

end Formalism.FourierDecayAlt.P.Ux7

open Formalism.FourierDecayAlt.P.Ux7 in
open Formalism.FourierDecayAlt.P.Ux7 in
open Formalism.FourierDecayAlt.P.Ux7 in
theorem Formalism.FourierDecayAlt.P.budget_second_corollary : Formalism.FourierDecayAlt.U.DerivativeBudgetCount := by
  exact budget_second_corollary_holds
open Formalism.FourierDecayAlt.P.Ux7 in
theorem Formalism.FourierDecayAlt.P.thresholds_second_corollary : Formalism.FourierDecayAlt.U.GermThresholds := by
  exact thresholds_second_corollary_holds
open Formalism.FourierDecayAlt.P.Ux7 in
open Formalism.FourierDecayAlt.P.Ux7 in
open Formalism.FourierDecayAlt.P.Ux7 in
open Formalism.FourierDecayAlt.P.Ux7 in
theorem Formalism.FourierDecayAlt.P.scale_matching : Formalism.FourierDecayAlt.U.ScaleMatch := by
  exact scaleMatch
open Formalism.FourierDecayAlt.P.Ux7 in
theorem Formalism.FourierDecayAlt.P.power_matching : Formalism.FourierDecayAlt.U.PowerMatch := by
  exact powerMatch
open Formalism.FourierDecayAlt.P.Ux7 in
theorem Formalism.FourierDecayAlt.P.derivative_bound_of_decay : Formalism.FourierDecayAlt.U.DerivBoundOfDecay := by
  exact derivBoundOfDecay
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChain
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ChainBd : Prop :=
  ∀ (k r : ℕ) (V E' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (Ψ : V → E'), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ →
    ∀ (F : Mat k r → V) (U K : Set (Mat k r)), IsOpen U → CkOn ⊤ (U ∩ GV k r) F → K ⊆ U → K ⊆ GV k r →
    ∀ Bg : ℝ, 0 ≤ Bg →
    (∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ K, ‖dLR u v F g‖ ≤ C * gN g ^ (Bg * m)) →
    ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ K, ‖dLR u v (fun g => Ψ (F g)) g‖ ≤ C * gN g ^ (Bg * m)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormBasics
section
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.HermitianProjections

section proj

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

end proj

lemma strict_pow_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j : Fin m, j ≤ i → M i j = 0) :
    ∀ p : ℕ, ∀ i j : Fin m, j.val < i.val + p → (M ^ p) i j = 0 := by
  intro p
  induction p with
  | zero =>
    intro i j hij
    rw [pow_zero]
    exact Matrix.one_apply_ne (fun h => by subst h; omega)
  | succ p ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < i.val + p
    · rw [ih i k hk, zero_mul]
    · rw [hM k j (Fin.le_iff_val_le_val.mpr (by omega)), mul_zero]

lemma strict_pow_eq_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j : Fin m, j ≤ i → M i j = 0) :
    M ^ m = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  exact strict_pow_apply M hM m i j (by have := j.isLt; omega)

section herm

variable {n : Type*} [Fintype n]

lemma herm_add_left (H : Matrix n n ℂ) (a b w : n → ℂ) : herm H (a + b) w = herm H a w + herm H b w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

lemma herm_add_right (H : Matrix n n ℂ) (v a b : n → ℂ) : herm H v (a + b) = herm H v a + herm H v b := by
  simp only [herm, star_add, add_dotProduct]

lemma herm_smul_left (H : Matrix n n ℂ) (c : ℂ) (a w : n → ℂ) : herm H (c • a) w = c * herm H a w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma herm_smul_right (H : Matrix n n ℂ) (c : ℂ) (v a : n → ℂ) : herm H v (c • a) = conj c * herm H v a := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
  rfl

lemma herm_mulVec {m ι κ : Type*} [Fintype m] [Fintype ι] [Fintype κ] (H : Matrix m m ℂ)
    (A : Matrix m ι ℂ) (B : Matrix m κ ℂ) (a : ι → ℂ) (b : κ → ℂ) :
    herm H (A *ᵥ a) (B *ᵥ b) = star b ⬝ᵥ ((Bᴴ * H * A) *ᵥ a) := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end herm

section uni

variable {n : Type*} [Fintype n] [DecidableEq n]

end uni

section sig

lemma star_mul_real (a : ℝ) (x : ℂ) : (star x * ((a : ℂ) * x)).re = a * Complex.normSq x := by
  simp [Complex.mul_re, Complex.normSq_apply]
  try ring

lemma sig_split {p q : ℕ} (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hG : G.IsHermitian) (hdet : G.det ≠ 0)
    (ψ₁ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin p → ℂ)) (h₁ : ∀ c, ψ₁ c = 0 → (star c ⬝ᵥ (G *ᵥ c)).re ≤ 0)
    (ψ₂ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin q → ℂ)) (h₂ : ∀ c, ψ₂ c = 0 → 0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re) :
    ∃ Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, IsUnit Q.det ∧ Qᴴ * G * Q = fromBlocks 1 0 0 (-1) := by
  classical
  set U : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ↑hG.eigenvectorUnitary with hUd
  set lam := hG.eigenvalues with hlam
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
  have hspec : G = U * diagonal (RCLike.ofReal ∘ lam) * star U := by
    have := hG.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hD : Uᴴ * G * U = diagonal (fun i => (lam i : ℂ)) := by
    rw [← Matrix.star_eq_conjTranspose]
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rfl
  have hform : ∀ c, star (U *ᵥ c) ⬝ᵥ (G *ᵥ (U *ᵥ c)) = ∑ i, star (c i) * ((lam i : ℂ) * c i) := by
    intro c
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  have hlam0 : ∀ i, lam i ≠ 0 := by
    have h1 : Uᴴ.det * U.det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, hUU, Matrix.det_one]
    have hdD : (diagonal (fun i => (lam i : ℂ))).det ≠ 0 := by
      rw [← hD, Matrix.det_mul, Matrix.det_mul, mul_comm (Uᴴ.det), mul_assoc, h1, mul_one]
      exact hdet
    rw [Matrix.det_diagonal] at hdD
    intro i
    have := (Finset.prod_ne_zero_iff.mp hdD) i (Finset.mem_univ i)
    exact_mod_cast this

  have hext : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (d : Fin p ⊕ Fin q → ℂ),
      (∀ i, d i = if h : P i then c ⟨i, h⟩ else 0) →
      ∑ i, star (d i) * ((lam i : ℂ) * d i) = ∑ j : {i // P i}, star (c j) * ((lam j.1 : ℂ) * c j) := by
    intro P _ c d hd
    rw [← Fintype.sum_subtype_add_sum_subtype P (fun i => star (d i) * ((lam i : ℂ) * d i))]
    have h0 : ∑ i : {x // ¬ P x}, star (d i.1) * ((lam i.1 : ℂ) * d i.1) = 0 := by
      apply Finset.sum_eq_zero; intro i _; rw [hd, dite_eq_right i.2]; simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [hd, dite_eq_left i.2]
  have hEv : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (i : Fin p ⊕ Fin q),
      ((Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // P i}) => if i = j.1 then (1 : ℂ) else 0) *ᵥ c) i =
        if h : P i then c ⟨i, h⟩ else 0 := by
    intro P _ c i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i, h⟩]
      · simp
      · intro b _ hb; rw [if_neg]; intro e; exact hb (Subtype.ext e.symm)
      · simp
    · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; intro e; exact h (e ▸ b.2)
  have hcardP : Fintype.card {i // 0 < lam i} ≤ p := by
    by_contra hlt0
    have hlt := not_le.mp hlt0
    set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0
    set L : ({i // 0 < lam i} → ℂ) →ₗ[ℂ] (Fin p → ℂ) := ψ₁ ∘ₗ Matrix.mulVecLin (U * E)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hlt)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hL : ψ₁ (U *ᵥ (E *ᵥ c)) = 0 := by
      have : L c = 0 := hc
      simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using this
    have hle := h₁ _ hL
    rw [hform, hext _ c _ (hEv _ c)] at hle
    rw [Complex.re_sum] at hle
    simp only [star_mul_real] at hle
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hall; exact hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))
    have hpos : 0 < ∑ j : {i // 0 < lam i}, lam j.1 * Complex.normSq (c j) := by
      apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // 0 < lam i} => lam j.1 * Complex.normSq (c j))
        (fun j _ => mul_nonneg j.2.le (Complex.normSq_nonneg _)) (Finset.mem_univ j))
      exact mul_pos j.2 (Complex.normSq_pos.mpr hj)
    linarith
  have hcardN : Fintype.card {i // ¬ 0 < lam i} ≤ q := by
    by_contra hlt0
    have hlt := not_le.mp hlt0
    set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // ¬ 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0
    set L : ({i // ¬ 0 < lam i} → ℂ) →ₗ[ℂ] (Fin q → ℂ) := ψ₂ ∘ₗ Matrix.mulVecLin (U * E)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hlt)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hL : ψ₂ (U *ᵥ (E *ᵥ c)) = 0 := by
      have : L c = 0 := hc
      simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using this
    have hle := h₂ _ hL
    rw [hform, hext _ c _ (hEv _ c)] at hle
    rw [Complex.re_sum] at hle
    simp only [star_mul_real] at hle
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hall; exact hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))
    have hneg : ∀ j : {i // ¬ 0 < lam i}, lam j.1 < 0 := fun j => lt_of_le_of_ne (not_lt.mp j.2) (hlam0 j.1)
    have hpos : 0 < ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j) := by
      apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // ¬ 0 < lam i} => (-lam j.1) * Complex.normSq (c j))
        (fun j _ => mul_nonneg (neg_nonneg.mpr (hneg j).le) (Complex.normSq_nonneg _)) (Finset.mem_univ j))
      exact mul_pos (neg_pos.mpr (hneg j)) (Complex.normSq_pos.mpr hj)
    have e : ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j) =
        -∑ j : {i // ¬ 0 < lam i}, lam j.1 * Complex.normSq (c j) := by
      rw [← Finset.sum_neg_distrib]; simp only [neg_mul]
    linarith
  have hsum : Fintype.card {i // 0 < lam i} + Fintype.card {i // ¬ 0 < lam i} = p + q := by
    rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl fun i => 0 < lam i), Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have hp : Fintype.card {i // 0 < lam i} = p := by omega
  have hq : Fintype.card {i // ¬ 0 < lam i} = q := by omega
  set e₁ := Fintype.equivFinOfCardEq hp
  set e₂ := Fintype.equivFinOfCardEq hq
  set e : Fin p ⊕ Fin q ≃ Fin p ⊕ Fin q := (Equiv.sumCongr e₁.symm e₂.symm).trans (Equiv.sumCompl fun i => 0 < lam i)
  have he1 : ∀ j, 0 < lam (e (Sum.inl j)) := by
    intro j; simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact (e₁.symm j).2
  have he2 : ∀ j, lam (e (Sum.inr j)) < 0 := by
    intro j; simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact lt_of_le_of_ne (not_lt.mp (e₂.symm j).2) (hlam0 _)
  set s : Fin p ⊕ Fin q → ℂ := fun i => (((Real.sqrt |lam i|)⁻¹ : ℝ) : ℂ)
  set A := U * diagonal s
  have hA : Aᴴ * G * A = diagonal (fun i => ((lam i / |lam i| : ℝ) : ℂ)) := by
    have : Aᴴ * G * A = (diagonal s)ᴴ * (Uᴴ * G * U) * diagonal s := by
      simp only [A, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hab : 0 < |lam i| := abs_pos.mpr (hlam0 i)
    have hsq : Real.sqrt |lam i| * Real.sqrt |lam i| = |lam i| := Real.mul_self_sqrt hab.le
    have hsne : Real.sqrt |lam i| ≠ 0 := (Real.sqrt_pos.mpr hab).ne'
    simp only [s, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    rw [Real.sq_sqrt hab.le]
    ring
  have hQ : (A.submatrix id e)ᴴ * G * A.submatrix id e = fromBlocks 1 0 0 (-1) := by
    have : (A.submatrix id e)ᴴ * G * A.submatrix id e = (Aᴴ * G * A).submatrix e e := by
      ext a b; rfl
    rw [this, hA, Matrix.submatrix_diagonal_equiv]
    have h1 : ∀ j, ((lam (e (Sum.inl j)) / |lam (e (Sum.inl j))| : ℝ) : ℂ) = 1 := by
      intro j; rw [abs_of_pos (he1 j), div_self (he1 j).ne']; simp
    have h2 : ∀ j, ((lam (e (Sum.inr j)) / |lam (e (Sum.inr j))| : ℝ) : ℂ) = -1 := by
      intro j; rw [abs_of_neg (he2 j), div_neg, div_self (he2 j).ne]; simp
    have hfe : (fun i => ((lam i / |lam i| : ℝ) : ℂ)) ∘ e = Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ)) := by
      funext x
      cases x with
      | inl j => exact h1 j
      | inr j => exact h2 j
    rw [hfe, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one]
    congr 1
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨A.submatrix id e, ?_, hQ⟩
  have hdB : (fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
      Fintype.card_fin]
    exact pow_ne_zero _ (by norm_num)
  rw [← hQ, Matrix.det_mul, Matrix.det_mul] at hdB
  exact isUnit_iff_ne_zero.mpr (fun h => hdB (by rw [h, mul_zero]))

end sig

end Formalism.FourierDecayAlt.P.HermitianProjections
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelLevelMultiplier
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Qx1

theorem model_level_multiplier (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.m0 Y = M.m0A P Y := by
  obtain ⟨-, -, -, -, -, -, hz, -, -, -, -, hGGi, -, hnabs, -⟩ := hL
  simp only [R.LevelData.m0, M.m0A, hz, hGGi, hnabs]

theorem model_level_lowering (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.l0 Y = M.l0A P Y := by
  obtain ⟨-, -, -, -, -, -, -, -, hzb, -, -, hGGi, hnab, -, -⟩ := hL
  simp only [R.LevelData.l0, M.l0A, hzb, hGGi, hnab]

end Qx1

theorem model_is_normal_form : Formalism.FourierDecayAlt.Q.ModelIsNF := by
  intro P L hL Y
  have hm := Qx1.model_level_multiplier P L hL Y
  have hl := Qx1.model_level_lowering P L hL Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -, -, -⟩ := hL
  simp only [NFData.QQ, hm, hl, hGG, hGGi]
  rfl

end Formalism.FourierDecayAlt.P
end
end

