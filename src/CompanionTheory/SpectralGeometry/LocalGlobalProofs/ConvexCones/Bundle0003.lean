module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.RatFormPosOfIntPos
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan


open Matrix in
theorem ratForm_pos_of_int_pos {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ)
    (hQ : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j)
    (w : Fin n → ℚ) (hw : w ≠ 0) : 0 < ∑ i, ∑ j, Q i j * w i * w j := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) w
  choose v hv using hb
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero b.2
  have hv' : ∀ i, (v i : ℚ) = (b : ℤ) * w i := by
    intro i
    have := hv i
    simpa [Algebra.smul_def] using this
  have hv0 : v ≠ 0 := by
    intro h
    apply hw
    funext i
    have h1 := hv' i
    rw [h] at h1
    simp only [Pi.zero_apply, Int.cast_zero] at h1
    have := (mul_eq_zero.1 h1.symm).resolve_left hb0
    simpa using this
  have h := hQ v hv0
  have h2 : ∑ i, ∑ j, Q i j * (v i : ℚ) * (v j : ℚ)
      = ((b : ℤ) : ℚ) ^ 2 * ∑ i, ∑ j, Q i j * w i * w j := by
    simp only [Finset.mul_sum, hv']
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2] at h
  have hb2 : 0 < ((b : ℤ) : ℚ) ^ 2 := by positivity
  exact (pos_iff_pos_of_mul_pos h).1 hb2


open Matrix in
theorem posDef_of_int_pos (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℚ) (hs : Q.IsSymm)
    (hQ : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j) :
    (Q.map (Rat.cast : ℚ → ℝ)).PosDef := by
  have hrat := ratForm_pos_of_int_pos Q hQ
  set R : Matrix (Fin n) (Fin n) ℝ := Q.map (Rat.cast : ℚ → ℝ) with hR
  have hRh : R.IsHermitian := by
    ext i j
    simpa [hR] using congrArg (Rat.cast : ℚ → ℝ) (hs.apply i j)
  have hform : ∀ x : Fin n → ℝ, x ⬝ᵥ (R *ᵥ x) = ∑ i, ∑ j, R i j * x i * x j := by
    intro x
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcast : ∀ w : Fin n → ℚ, ((fun i => (w i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (w i : ℝ)))
      = ((∑ i, ∑ j, Q i j * w i * w j : ℚ) : ℝ) := by
    intro w
    rw [hform]
    push_cast
    simp [hR]
  have hdense : DenseRange (fun (w : Fin n → ℚ) (i : Fin n) => (w i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (R *ᵥ x) := by
    simp only [hform]
    fun_prop
  have hnonneg : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (R *ᵥ x) := by
    have hcl : IsClosed {x : Fin n → ℝ | 0 ≤ x ⬝ᵥ (R *ᵥ x)} :=
      isClosed_le continuous_const hcont
    intro x
    refine hdense.induction_on (p := fun x => 0 ≤ x ⬝ᵥ (R *ᵥ x)) x hcl fun w => ?_
    show 0 ≤ (fun i => (w i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (w i : ℝ))
    rw [hcast]
    by_cases hw : w = 0
    · simp [hw]
    · exact_mod_cast (hrat w hw).le
  have hpsd : R.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hRh fun x => ?_
    simpa using hnonneg x
  rw [hpsd.posDef_iff_det_ne_zero]
  intro h0
  have hRQ : R = (Rat.castHom ℝ).mapMatrix Q := by
    ext i j
    simp [hR]
  rw [hRQ, ← RingHom.map_det, map_eq_zero] at h0
  obtain ⟨w, hw, hQw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := hrat w hw
  have h2 : ∑ i, ∑ j, Q i j * w i * w j = w ⬝ᵥ (Q *ᵥ w) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, hQw, dotProduct_zero] at h1
  exact lt_irrefl _ h1

end GlobalTheory.CompanionTheory.Ar.Fan
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VorFunValueLe
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem vorFun_value_le : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (n : ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X)
    (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) →
    Covers2 (fun y => r (a y)) ∧ ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∀ y, 0 ≤ B y y) →
      (2 : ℝ) ^ n * evalR (vorFun O g) B ≤ 2 ^ g * ∑ y, B (r (a y)) (r (a y)) ∧
      ((2 : ℝ) ^ n * evalR (vorFun O g) B = 2 ^ g * ∑ y, B (r (a y)) (r (a y)) ↔ ∀ y, IsMin2 B (r (a y))) := by
  intro O _ _ _ _ bar g X _ _ _ n r a hr ha
  have hfin : Module.Finite ℤ X := Module.Finite.of_surjective r hr
  have hs : ∀ c d : Fin n → ℤ, r (c + (((1 : ℕ) : ℤ) + 1) • d) = r c + (r d + r d) := fun c d => by
    rw [map_add (f := _), map_smul, show (((1 : ℕ) : ℤ) + 1) = 2 by norm_num, two_smul]
  refine ⟨fun x => ?_, fun B hB => ?_⟩
  · obtain ⟨b, rfl⟩ := hr x
    obtain ⟨d, hd⟩ := exists_eq_add_of_redV_eq (M := 1) (a := b) (a' := a (redV 1 b)) (ha _).symm
    exact ⟨redV 1 b, r d, by rw [← hs, ← hd]⟩
  set Br : (Fin n → ℤ) → (Fin n → ℤ) → ℝ := fun c d => B (r c) (r d) with hBr
  have hval : (2 : ℝ) ^ n * evalR (vorFun O g) B = 2 ^ g * ∑ y, classMin 1 Br y := by
    have h0 : zeroFun.eval X (fun c d => B c d) = 0 := by
      rw [zeroFun.eval_eq hr]; rfl
    have h1 : (fineMean 1).eval X (fun c d => B c d) =
        (((((1 : ℕ) : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin 1 Br y - Br 0 0) := by
      rw [(fineMean 1).eval_eq hr]; rfl
    have h2 : Br 0 0 = 0 := by simp [hBr]
    have h3 : ((fineDen g {1} : ℕ) : ℝ) = 2 ^ g := by
      simp only [fineDen, Finset.prod_singleton]; norm_num
    have h4 : (((1 : ℕ) : ℝ) + 1) = 2 := by norm_num
    unfold evalR vorFun
    rw [eval_baseFun, h0, Finset.sum_singleton, h1, h2, h3, h4]
    field_simp
    ring
  have hbdd : ∀ y, BddBelow {x | ∃ c : Fin n → ℤ, redV 1 c = y ∧ Br c c = x} := fun y =>
    ⟨0, by rintro x ⟨c, -, rfl⟩; exact hB _⟩
  have hle : ∀ y, classMin 1 Br y ≤ B (r (a y)) (r (a y)) := fun y =>
    csInf_le (hbdd y) ⟨a y, ha y, rfl⟩
  have hiff : ∀ y, classMin 1 Br y = B (r (a y)) (r (a y)) ↔ IsMin2 B (r (a y)) := fun y => by
    constructor
    · intro h x
      obtain ⟨b, rfl⟩ := hr x
      rw [← h, ← hs]
      refine csInf_le (hbdd y) ⟨_, ?_, rfl⟩
      rw [redV_add_smul, ha]
    · intro h
      refine le_antisymm (hle y) (le_csInf ⟨_, a y, ha y, rfl⟩ ?_)
      rintro x ⟨c, hc, rfl⟩
      obtain ⟨d, rfl⟩ := exists_eq_add_of_redV_eq (M := 1) (a := c) (a' := a y) (by rw [hc, ha])
      simp only [hBr]
      rw [hs]
      exact h _
  have hp : (0 : ℝ) < 2 ^ g := by positivity
  rw [hval]
  refine ⟨mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hle y) hp.le, ?_⟩
  rw [mul_right_inj' hp.ne', Finset.sum_eq_sum_iff_of_le fun y _ => hle y]
  simp only [Finset.mem_univ, true_imp_iff, hiff]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

