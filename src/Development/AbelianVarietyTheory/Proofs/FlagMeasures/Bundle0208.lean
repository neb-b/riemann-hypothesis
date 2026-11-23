module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingWithDensity
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.HaarMul

theorem measurePreserving_withDensity {X : Type} [MeasurableSpace X] (μ : Measure X) {f : X → X}
    (hf : Measurable f) {ρ : X → ENNReal} (hρ : Measurable ρ) {c d : ENNReal} (hcd : d * c = 1)
    (hμ : μ.map f = c • μ) (hρf : ∀ x, ρ x = d * ρ (f x)) :
    MeasurePreserving f (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨hf, ?_⟩
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]

  have h1 : ∫⁻ x in f ⁻¹' s, ρ x ∂μ = ∫⁻ x, d * s.indicator ρ (f x) ∂μ := by
    rw [← lintegral_indicator (hf hs)]
    congr 1
    funext x
    by_cases hx : f x ∈ s
    · simp [Set.indicator_apply, hx, ← hρf x]
    · simp [Set.indicator_apply, hx]
  rw [h1, lintegral_const_mul d (f := fun x => s.indicator ρ (f x)) ((hρ.indicator hs).comp hf),
    ← lintegral_map (hρ.indicator hs) hf, hμ,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, hcd, one_mul, lintegral_indicator hs]

theorem measurePreserving_mul_mul : ∀ (j : ℕ) (a b : Matrix (Fin j) (Fin j) ℂ), a.det ≠ 0 → b.det ≠ 0 →
    MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => (a * Matrix.of x * b) r s)
      (haarLoc j) (haarLoc j) := by
  intro j a b ha hb

  let L : (Fin j → Fin j → ℂ) →ₗ[ℝ] (Fin j → Fin j → ℂ) :=
    { toFun := fun x r s => (a * Matrix.of x * b) r s
      map_add' := fun x y => by
        have h : a * Matrix.of (x + y) * b = a * Matrix.of x * b + a * Matrix.of y * b := by
          rw [show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add, Matrix.add_mul]
        funext r s
        exact congrFun (congrFun h r) s
      map_smul' := fun c x => by
        have h : a * Matrix.of (c • x) * b = c • (a * Matrix.of x * b) := by
          rw [show Matrix.of (c • x) = c • Matrix.of x from rfl, Matrix.mul_smul, Matrix.smul_mul]
        funext r s
        exact congrFun (congrFun h r) s }
  have hdet : LinearMap.det L = ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    GlobalTheory.TwoSidedJac.real_jacobians.1 j j a b L (fun T => rfl)
  have hA : ‖a.det‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hB : ‖b.det‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have hD : 0 < ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    mul_pos (pow_pos (norm_pos_iff.2 ha) _) (pow_pos (norm_pos_iff.2 hb) _)
  have hcont : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_id.matrix_det : Continuous fun A : Matrix (Fin j) (Fin j) ℂ => A.det)
  have hρ : Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) :=
    ENNReal.measurable_ofReal.comp (((hcont.measurable.norm.pow_const 2).inv).pow_const j)

  haveI : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure ℂ))
  haveI : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure (Fin j → ℂ)))
  have hμ : (volume : Measure (Fin j → Fin j → ℂ)).map L =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact hD.ne')
  have hcd : ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) * ENNReal.ofReal |(LinearMap.det L)⁻¹| = 1 := by
    rw [hdet, abs_of_pos (inv_pos.2 hD), ← ENNReal.ofReal_mul hD.le, mul_inv_cancel₀ hD.ne', ENNReal.ofReal_one]

  have hρf : ∀ x : Fin j → Fin j → ℂ, ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) =
      ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) *
        ENNReal.ofReal ((‖(Matrix.of (L x)).det‖ ^ 2)⁻¹ ^ j) := by
    intro x
    rw [← ENNReal.ofReal_mul hD.le]
    congr 1
    rw [show Matrix.of (L x) = a * Matrix.of x * b from rfl, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul]
    have hP : (‖a.det‖ ^ 2) ^ j * ((‖a.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hA))
    have hQ : (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hB))
    rw [mul_pow, mul_pow, mul_inv, mul_inv, mul_pow, mul_pow, inv_pow (‖a.det‖ ^ 2), inv_pow (‖b.det‖ ^ 2),
      pow_mul, pow_mul]
    linear_combination (-((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹)) * hP
      - (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * hQ
  unfold haarLoc
  exact measurePreserving_withDensity volume L.continuous_of_finiteDimensional.measurable hρ hcd hμ hρf

end GlobalTheory.HaarMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIsotropicFlagSelfAdjointLeviIffBlock
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ inUJ Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviIso.Range

variable {n n₀ a : ℕ} {j : Fin a → ℕ} {ε : Fin n → Bool} {ε₀ : Fin n₀ → Bool}
  {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {B₀ : Matrix (Fin n) (Fin n₀) ℂ}
  {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}

theorem ext_mulVec {p q : ℕ} {M N : Matrix (Fin p) (Fin q) ℂ} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  exact Matrix.mulVec_injective (funext h)

theorem proj (h : IsFrame ε ε₀ B B₀) (u : ∀ i, Fin (j i) → ℂ) (k : Fin a) :
    (B k)ᴴ *ᵥ ∑ l, B l *ᵥ u l = u k := by
  rw [Matrix.mulVec_sum, Finset.sum_eq_single k]
  · rw [Matrix.mulVec_mulVec, h.1 k, Matrix.one_mulVec]
  · intro l _ hl
    rw [Matrix.mulVec_mulVec, h.2.1 k l (Ne.symm hl), Matrix.zero_mulVec]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem col_mem (hW : SpansFlag B W) (i : Fin a) (v : Fin (j i) → ℂ) : B i *ᵥ v ∈ W i.succ := by
  classical
  rw [hW]
  refine ⟨Pi.single i v, fun l hl => ?_, ?_⟩
  · have hne : l ≠ i := by
      rintro rfl
      exact hl (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
    exact Pi.single_eq_of_ne (M := fun l => Fin (j l) → ℂ) hne v
  · rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro l _ hl
      rw [Pi.single_eq_of_ne (M := fun l => Fin (j l) → ℂ) hl, Matrix.mulVec_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem upper (h : IsFrame ε ε₀ B B₀) (hW : SpansFlag B W) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ k, ∀ y ∈ W k, M *ᵥ y ∈ W k) {i k : Fin a} (hik : i < k) : (B k)ᴴ * M * B i = 0 := by
  apply ext_mulVec
  intro v
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨u, hu, hyu⟩ := (hW _ _).1 (hM _ _ (col_mem hW i v))
  rw [hyu, proj h]
  apply hu
  intro hlt
  have hik' := Fin.lt_def.1 hik
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hlt
  omega

theorem expand (h : IsFrame ε ε₀ B B₀) (hW : SpansFlag B W) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ k, ∀ y ∈ W k, M *ᵥ y ∈ W k) (i : Fin a) : M * B i = ∑ k, B k * ((B k)ᴴ * M * B i) := by
  apply ext_mulVec
  intro v
  obtain ⟨u, -, hyu⟩ := (hW _ _).1 (hM _ _ (col_mem hW i v))
  have hk : ∀ k, (B k * ((B k)ᴴ * M * B i)) *ᵥ v = B k *ᵥ u k := by
    intro k
    have e : (B k * ((B k)ᴴ * M * B i)) *ᵥ v = B k *ᵥ ((B k)ᴴ *ᵥ (M *ᵥ (B i *ᵥ v))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, hyu, proj h]
  rw [Matrix.sum_mulVec, Finset.sum_congr rfl (fun k _ => hk k), ← hyu, Matrix.mulVec_mulVec]

theorem diag (h : IsFrame ε ε₀ B B₀) (hW : SpansFlag B W) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ k, ∀ y ∈ W k, M *ᵥ y ∈ W k) (hM' : ∀ k, ∀ y ∈ W k, Mᴴ *ᵥ y ∈ W k) (i : Fin a) :
    M * B i = B i * ((B i)ᴴ * M * B i) := by
  rw [expand h hW hM i, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · have e := upper h hW hM' hlt
      have e' : (B k)ᴴ * M * B i = 0 := by
        have := congrArg Matrix.conjTranspose e
        simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
      rw [e', Matrix.mul_zero]
    · rw [upper h hW hM hgt, Matrix.mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem lev_keeps (h : IsFrame ε ε₀ B B₀) (hW : SpansFlag B W) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ)
    (g : Matrix (Fin n₀) (Fin n₀) ℂ) (k : Fin (a + 1)) (y : Fin n → ℂ) (hy : y ∈ W k) :
    lev ε B B₀ x g *ᵥ y ∈ W k := by
  obtain ⟨u, hu, rfl⟩ := (hW _ _).1 hy
  rw [hW]
  refine ⟨fun i => x i *ᵥ u i, fun i hi => by
    show x i *ᵥ u i = 0
    rw [hu i hi, Matrix.mulVec_zero], ?_⟩
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec_mulVec, h.lev_mul_B x g i]

theorem left_inv {p : ℕ} {ε : Fin p → Bool} {M : Matrix (Fin p) (Fin p) ℂ} (hU : Mᴴ * Jm ε * M = Jm ε) :
    Jm ε * Mᴴ * Jm ε * M = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hU, Jm_mul_self]

theorem block (h : IsFrame ε ε₀ B B₀) {M : Matrix (Fin n) (Fin n) ℂ} (hU : Mᴴ * Jm ε * M = Jm ε)
    {x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ} (h1 : ∀ i, M * B i = B i * x i)
    (h2 : ∀ i, Mᴴ * B i = B i * (x i)ᴴ) :
    (∀ i, (x i).det ≠ 0) ∧ inUJ ε₀ (B₀ᴴ * M * B₀) ∧ M = lev ε B B₀ x (B₀ᴴ * M * B₀) := by
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJH : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  have hR : M * (Jm ε * Mᴴ * Jm ε) = 1 := mul_eq_one_comm.1 (left_inv hU)
  have hMJ : M * Jm ε * Mᴴ = Jm ε := by
    calc M * Jm ε * Mᴴ = M * (Jm ε * Mᴴ * Jm ε) * Jm ε := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = Jm ε := by rw [hR, Matrix.one_mul]
  have hy : ∀ i, ((B i)ᴴ * Jm ε * Mᴴ * Jm ε * B i) * x i = 1 := by
    intro i
    calc ((B i)ᴴ * Jm ε * Mᴴ * Jm ε * B i) * x i
        = (B i)ᴴ * Jm ε * (Mᴴ * Jm ε * (B i * x i)) := by simp only [Matrix.mul_assoc]
      _ = (B i)ᴴ * Jm ε * (Mᴴ * Jm ε * (M * B i)) := by rw [h1]
      _ = (B i)ᴴ * (Jm ε * Jm ε) * B i := by
          rw [← Matrix.mul_assoc (Mᴴ * Jm ε), hU]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, Matrix.mul_one, h.1 i]
  have hdet : ∀ i, (x i).det ≠ 0 := fun i => Matrix.det_ne_zero_of_left_inverse (hy i)
  have hdetU : ∀ i, IsUnit (x i).det := fun i => isUnit_iff_ne_zero.2 (hdet i)
  have hA : ∀ i, Mᴴ * Jm ε * B i = Jm ε * B i * (x i)⁻¹ := by
    intro i
    have e : Mᴴ * Jm ε * B i * x i = Jm ε * B i := by
      rw [Matrix.mul_assoc (Mᴴ * Jm ε) (B i) (x i), ← h1 i, ← Matrix.mul_assoc (Mᴴ * Jm ε) M (B i), hU]
    calc Mᴴ * Jm ε * B i = Mᴴ * Jm ε * B i * x i * (x i)⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right (x i) _ (hdetU i)).symm
      _ = Jm ε * B i * (x i)⁻¹ := by rw [e]
  have hC : ∀ i, M * (Jm ε * B i) = Jm ε * B i * (x i)⁻¹ᴴ := by
    intro i
    have e : M * (Jm ε * B i) * (x i)ᴴ = Jm ε * B i := by
      calc M * (Jm ε * B i) * (x i)ᴴ = M * Jm ε * (B i * (x i)ᴴ) := by simp only [Matrix.mul_assoc]
        _ = M * Jm ε * (Mᴴ * B i) := by rw [h2]
        _ = (M * Jm ε * Mᴴ) * B i := by simp only [Matrix.mul_assoc]
        _ = Jm ε * B i := by rw [hMJ]
    have hu : IsUnit ((x i)ᴴ).det := by
      rw [Matrix.det_conjTranspose]
      exact isUnit_iff_ne_zero.2 (star_ne_zero.2 (hdet i))
    calc M * (Jm ε * B i) = M * (Jm ε * B i) * (x i)ᴴ * ((x i)ᴴ)⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right ((x i)ᴴ) _ hu).symm
      _ = Jm ε * B i * (x i)⁻¹ᴴ := by rw [e, Matrix.conjTranspose_nonsing_inv]
  have e1 : ∀ i, (B i)ᴴ * (M * B₀) = 0 := by
    intro i
    have hBM : (B i)ᴴ * M = x i * (B i)ᴴ := by
      have := congrArg Matrix.conjTranspose (h2 i)
      simpa [Matrix.conjTranspose_mul] using this
    rw [← Matrix.mul_assoc, hBM, Matrix.mul_assoc, h.2.2.2.1 i, Matrix.mul_zero]
  have e2 : ∀ i, (B i)ᴴ * Jm ε * (M * B₀) = 0 := by
    intro i
    have hBJM : (B i)ᴴ * Jm ε * M = ((x i)⁻¹)ᴴ * ((B i)ᴴ * Jm ε) := by
      have := congrArg Matrix.conjTranspose (hA i)
      simpa [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc] using this
    rw [← Matrix.mul_assoc, hBJM, Matrix.mul_assoc, h.J_B₀ i, Matrix.mul_zero]
  have hD : M * B₀ = B₀ * (B₀ᴴ * M * B₀) := by
    have s1 : ∀ i, B i * (B i)ᴴ * (M * B₀) = 0 := fun i => by
      rw [Matrix.mul_assoc, e1 i, Matrix.mul_zero]
    have s2 : ∀ i, Jm ε * B i * (B i)ᴴ * Jm ε * (M * B₀) = 0 := fun i => by
      rw [show Jm ε * B i * (B i)ᴴ * Jm ε * (M * B₀) = Jm ε * B i * ((B i)ᴴ * Jm ε * (M * B₀)) by
        simp only [Matrix.mul_assoc], e2 i, Matrix.mul_zero]
    calc M * B₀ = (∑ i, B i * (B i)ᴴ + ∑ i, Jm ε * B i * (B i)ᴴ * Jm ε + B₀ * B₀ᴴ) * (M * B₀) := by
          rw [h.2.2.2.2.2.2, Matrix.one_mul]
      _ = B₀ * (B₀ᴴ * M * B₀) := by
          rw [Matrix.add_mul, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_mul]
          simp only [s1, s2, Finset.sum_const_zero, zero_add]
          simp only [Matrix.mul_assoc]
  have hJB₀ : Jm ε * B₀ = B₀ * Jm ε₀ := h.2.2.2.2.2.1
  have hE : inUJ ε₀ (B₀ᴴ * M * B₀) := by
    show (B₀ᴴ * M * B₀)ᴴ * Jm ε₀ * (B₀ᴴ * M * B₀) = Jm ε₀
    calc (B₀ᴴ * M * B₀)ᴴ * Jm ε₀ * (B₀ᴴ * M * B₀)
        = B₀ᴴ * Mᴴ * (B₀ * Jm ε₀) * (B₀ᴴ * M * B₀) := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B₀ᴴ * Mᴴ * Jm ε * (B₀ * (B₀ᴴ * M * B₀)) := by
          rw [← hJB₀]
          simp only [Matrix.mul_assoc]
      _ = B₀ᴴ * (Mᴴ * Jm ε * M) * B₀ := by
          rw [← hD]
          simp only [Matrix.mul_assoc]
      _ = B₀ᴴ * B₀ * Jm ε₀ := by
          rw [hU, Matrix.mul_assoc, hJB₀, ← Matrix.mul_assoc]
      _ = Jm ε₀ := by rw [h.2.2.2.2.1, Matrix.one_mul]
  refine ⟨hdet, hE, ?_⟩
  apply h.ext
  · intro i
    rw [h1 i, h.lev_mul_B]
  · intro i
    rw [hC i, h.lev_mul_JB]
  · rw [hD, h.lev_mul_B₀]

theorem mem_flagM_iff : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ →
    ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ m : Formalism.REAL.UJ ε,
      m ∈ flagM ε W ↔ ∃ (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Formalism.REAL.UJ ε₀),
        (∀ i, (x i).det ≠ 0) ∧ uMat m = lev ε B B₀ x (uMat g) := by
  intro n n₀ a j ε ε₀ B B₀ h W hW m
  constructor
  · intro hm
    have hm' : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hM : ∀ k, ∀ y ∈ W k, uMat m *ᵥ y ∈ W k := fun k y hy => (hm' k y hy).1
    have hM' : ∀ k, ∀ y ∈ W k, (uMat m)ᴴ *ᵥ y ∈ W k := fun k y hy => (hm' k y hy).2
    have hM'' : ∀ k, ∀ y ∈ W k, (uMat m)ᴴᴴ *ᵥ y ∈ W k := by
      intro k y hy
      rw [Matrix.conjTranspose_conjTranspose]
      exact hM k y hy
    have hU : (uMat m)ᴴ * Jm ε * uMat m = Jm ε := m.2
    have h2 : ∀ i, (uMat m)ᴴ * B i = B i * ((B i)ᴴ * uMat m * B i)ᴴ := by
      intro i
      rw [diag h hW hM' hM'' i]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    obtain ⟨hdet, hE, heq⟩ := block h hU (x := fun i => (B i)ᴴ * uMat m * B i)
      (fun i => diag h hW hM hM' i) h2
    have hinv : (Jm ε₀ * (B₀ᴴ * uMat m * B₀)ᴴ * Jm ε₀) * (B₀ᴴ * uMat m * B₀) = 1 := left_inv hE
    have hinv' : (B₀ᴴ * uMat m * B₀) * (Jm ε₀ * (B₀ᴴ * uMat m * B₀)ᴴ * Jm ε₀) = 1 :=
      mul_eq_one_comm.1 hinv
    refine ⟨fun i => (B i)ᴴ * uMat m * B i,
      ⟨⟨B₀ᴴ * uMat m * B₀, Jm ε₀ * (B₀ᴴ * uMat m * B₀)ᴴ * Jm ε₀, hinv', hinv⟩, hE⟩, hdet, ?_⟩
    exact heq
  · rintro ⟨x, g, -, hmg⟩
    show ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i
    intro k y hy
    rw [hmg]
    refine ⟨lev_keeps h hW x (uMat g) k y hy, ?_⟩
    rw [lev_conjTranspose]
    exact lev_keeps h hW _ _ k y hy

end GlobalTheory.LeviIso.Range
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatticeAutSplitIffFirstColSingle
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm.SplitStab

variable {E : Type} [Field E] {k : ℕ}

theorem det_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) : M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h, Fin.succ_ne_zero]

theorem mulVec_zero_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) (y : Fin (k + 1) → E) :
    (M *ᵥ y) 0 = y 0 + (fun b => M 0 (Fin.succ b)) ⬝ᵥ Fin.tail y := by
  have h0 : M 0 0 = 1 := by simpa using h 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h0, Fin.tail]

theorem tail_mulVec_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) (y : Fin (k + 1) → E) :
    Fin.tail (M *ᵥ y) = M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail y := by
  funext b
  have hb : M b.succ 0 = 0 := by simpa [Fin.succ_ne_zero] using h b.succ
  simp [Fin.tail, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hb, Matrix.submatrix]

theorem preserves_iff [NumberField E] (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) (hΛ : ∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ')
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E) (h : ∀ a, M a 0 = if a = 0 then 1 else 0) :
    (∀ y, M *ᵥ y ∈ Λ ↔ y ∈ Λ) ↔ (∀ y, M.submatrix Fin.succ Fin.succ *ᵥ y ∈ Λ' ↔ y ∈ Λ') ∧
      ∀ y ∈ Λ', (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ y) ∈ Λ₀ := by
  have key : ∀ y : Fin (k + 1) → E, M *ᵥ y ∈ Λ ↔
      ((fun _ => y 0) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ Fin.tail y) : Fin 1 → E) ∈ Λ₀ ∧
        M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail y ∈ Λ' := by
    intro y
    rw [hΛ, mulVec_zero_of_col M h y, tail_mulVec_of_col M h y]
    exact Iff.rfl
  have hcons : ∀ (c : E) (z : Fin k → E),
      (Fin.cons c z : Fin (k + 1) → E) 0 = c ∧ Fin.tail (Fin.cons c z : Fin (k + 1) → E) = z :=
    fun c z => ⟨Fin.cons_zero _ _, Fin.tail_cons _ _⟩
  constructor
  · intro hM
    refine ⟨fun z => ⟨fun hz => ?_, fun hz => ?_⟩, fun z hz => ?_⟩
    ·
      set c : E := -((fun b => M 0 (Fin.succ b)) ⬝ᵥ z)
      have h1 : M *ᵥ (Fin.cons c z : Fin (k + 1) → E) ∈ Λ := by
        rw [key, (hcons c z).1, (hcons c z).2]
        refine ⟨?_, hz⟩
        have hz0 : ((fun _ => c) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z) : Fin 1 → E) = 0 := by
          funext i; simp [c]
        rw [hz0]; exact Λ₀.zero_mem
      have h2 := (hΛ _).1 ((hM _).1 h1)
      rw [(hcons c z).2] at h2
      exact h2.2
    · have h1 : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
        rw [hΛ, (hcons 0 z).1, (hcons 0 z).2]; exact ⟨Λ₀.zero_mem, hz⟩
      have h2 := (key _).1 ((hM _).2 h1)
      rw [(hcons 0 z).2] at h2
      exact h2.2
    · have h1 : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
        rw [hΛ, (hcons 0 z).1, (hcons 0 z).2]; exact ⟨Λ₀.zero_mem, hz⟩
      have h2 := ((key _).1 ((hM _).2 h1)).1
      rw [(hcons 0 z).1, (hcons 0 z).2] at h2
      have he : ((fun _ => (0 : E)) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z) : Fin 1 → E) =
          fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z := by
        funext i; simp
      rwa [he] at h2
  · rintro ⟨hA, hr⟩ y
    rw [key, hΛ, hA]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(add_mem_cancel_right (hr _ h2)).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Λ₀.add_mem h1 (hr _ h2), h2⟩

end GlobalTheory.OrbitTerm.SplitStab

namespace GlobalTheory.OrbitTerm


open SplitStab in
theorem mem_autGL_split_iff : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → ∀ x : MatInf E (k + 1), (∀ w a, x w a 0 = if a = 0 then 1 else 0) → (x ∈ autGL E (k + 1) Λ ↔ (fun w a b => x w a.succ b.succ) ∈ autGL E k Λ' ∧ ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ ∀ w b, x w 0 b.succ = w.embedding (τ b)) := by
  intro E _ _ k Λ Λ₀ Λ' hΛ x hx
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  simp only [autGL, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨γ, hγ, hxγ⟩
    have hcol : ∀ a, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) a 0 = if a = 0 then 1 else 0 := by
      intro a
      apply w₀.embedding.injective
      rw [← hxγ w₀ a 0, hx w₀ a]
      split_ifs <;> simp
    have hdet : (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
    rw [det_of_col _ hcol] at hdet
    obtain ⟨hA, hr⟩ := (preserves_iff Λ Λ₀ Λ' hΛ _ hcol).1 hγ
    exact ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, hA, fun w a b => hxγ w a.succ b.succ⟩,
      fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ, hr, fun w b => hxγ w 0 b.succ⟩
  · rintro ⟨⟨γ', hγ', hxγ'⟩, τ, hτ, hxτ⟩

    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin (k + 1)) (Fin (k + 1)) E,
        M = Matrix.of (Fin.cons (Fin.cons 1 τ : Fin (k + 1) → E)
          (fun a => (Fin.cons 0 ((γ' : Matrix (Fin k) (Fin k) E) a) : Fin (k + 1) → E)) :
            Fin (k + 1) → Fin (k + 1) → E) := ⟨_, rfl⟩
    have hcol : ∀ a, M a 0 = if a = 0 then 1 else 0 := by
      intro a
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;> simp [hM, Fin.succ_ne_zero]
    have hsub : M.submatrix Fin.succ Fin.succ = (γ' : Matrix (Fin k) (Fin k) E) := by
      ext a b; simp [hM]
    have hrow : (fun b => M 0 (Fin.succ b)) = τ := by
      funext b; simp [hM]
    have hdet : M.det ≠ 0 := by
      rw [det_of_col M hcol, hsub]; exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
    · show ∀ y, M *ᵥ y ∈ Λ ↔ y ∈ Λ
      refine (preserves_iff Λ Λ₀ Λ' hΛ M hcol).2 ⟨?_, ?_⟩
      · rw [hsub]; exact hγ'
      · rw [hrow]; exact hτ
    · intro w a b
      show x w a b = w.embedding (M a b)
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b, rfl⟩
      · rw [hx]; simp [hM]
      · rw [hxτ]; simp [hM]
      · rw [hx]; simp [hM, Fin.succ_ne_zero]
      · refine (hxγ' w a b).trans ?_
        simp [hM]

end GlobalTheory.OrbitTerm
end

