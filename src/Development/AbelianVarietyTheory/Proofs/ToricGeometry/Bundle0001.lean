module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertNormalFormOfLinearExponent
section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory
namespace AppellHumbert


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.AppellHumbert.exists_real_extension {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : Λ →+ W) : ∃ F : (Fin g → ℂ) →ₗ[ℝ] W, ∀ l : Λ, F l = f l := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  refine ⟨bR.constr ℝ (fun i => f (b i)), fun l => ?_⟩
  have key : ((bR.constr ℝ (fun i => f (b i))).restrictScalars ℤ ∘ₗ Λ.subtype) =
      f.toIntLinearMap := by
    refine b.ext fun i => ?_
    show bR.constr ℝ (fun i => f (b i)) (b i : Fin g → ℂ) = f (b i)
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ Λ b i, Module.Basis.constr_basis]
  exact LinearMap.congr_fun key l

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.AppellHumbert.eq_sum_re_im {g : ℕ} (u : Fin g → ℂ) :
    u = ∑ j, ((u j).re • (Pi.single j (1 : ℂ) : Fin g → ℂ)
      + (u j).im • (Pi.single j I : Fin g → ℂ)) := by
  ext i
  simp [Finset.sum_apply, Finset.sum_add_distrib, Pi.single_apply, Complex.re_add_im]

end AppellHumbert


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.appellHumbert_normal_form_of_linear_exponent :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) → (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Q : (Fin g → ℂ) → ℂ), Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ ∀ (l : Λ) z, a l * cexp (B l z) * cexp (Q z - Q (z + l)) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))))) := by
  intro g Λ hdisc hΛ a B ha hcoc
  classical
  haveI := hdisc
  let b : Λ →+ (Fin g → ℂ) :=
    { toFun := fun l j => B l (Pi.single j 1)
      map_zero' := by ext j; simp
      map_add' := fun l m => by ext j; simp }
  obtain ⟨F, hF0⟩ := _root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ b
  have hF : ∀ (l : Λ) z, B l z = F l ⬝ᵥ z := by
    intro l z
    rw [hF0]
    conv_lhs => rw [show z = ∑ j, z j • (Pi.single j (1 : ℂ) : Fin g → ℂ) by ext i; simp [Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, dotProduct, b, mul_comm]
  have hskew : ∀ l m : Λ, ∃ n : ℤ, B l m = B m l + n * (2 * π * I) := by
    intro l m
    have h := hcoc l m
    rw [add_comm, hcoc m l, mul_comm (a m) (a l)] at h
    exact Complex.exp_eq_exp_iff_exists_int.mp (mul_left_cancel₀ (mul_ne_zero (ha l) (ha m)) h).symm
  have hlin : ∀ (P : (Fin g → ℂ) → Prop), P 0 → (∀ x y, P x → P y → P (x + y)) →
      (∀ (c : ℝ) x, P x → P (c • x)) → (∀ l : Λ, P l) → ∀ x, P x := by
    intro P h0 hadd hsmul hl x
    have hx : x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact hl ⟨y, hy⟩
    | zero => exact h0
    | add y z _ _ hy hz => exact hadd y z hy hz
    | smul c y _ hy => exact hsmul c y hy
  have hD1 : ∀ u (m : Λ), (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0 := by
    intro u m
    refine hlin (fun u => (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_)
      (fun c x hx => ?_) (fun l => ?_) u
    · simp only [map_add (f := _), add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢
      linarith
    · simp only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re,
        smul_eq_mul] at hx ⊢
      rw [← mul_sub, hx, mul_zero]
    · obtain ⟨n, hn⟩ := hskew l m
      rw [← hF, ← hF, hn]; simp
  have hD : ∀ u v, (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0 := by
    intro u v
    refine hlin (fun v => (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_)
      (fun c x hx => ?_) (fun m => hD1 u m) v
    · simp only [map_add (f := _), add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢
      linarith
    · simp only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re,
        smul_eq_mul] at hx ⊢
      rw [← mul_sub, hx, mul_zero]
  let M : Matrix (Fin g) (Fin g) ℂ := fun k j =>
    (1/2 : ℝ) • (F (Pi.single k 1) j - I * F (Pi.single k I) j)
  let N : Matrix (Fin g) (Fin g) ℂ := fun k j =>
    (1/2 : ℝ) • (F (Pi.single k 1) j + I * F (Pi.single k I) j)
  have hFMN : ∀ u, F u = u ᵥ* M + star u ᵥ* N := by
    intro u; ext j
    conv_lhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_add (f := _), map_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, vecMul,
      dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    apply Complex.ext <;> simp [M, N, Complex.mul_re, Complex.mul_im] <;> ring
  have hsym : ∀ k j, (F (Pi.single k 1) j).re = (F (Pi.single j 1) k).re ∧
      (F (Pi.single k I) j).im = (F (Pi.single j I) k).im ∧
      (F (Pi.single k I) j).re = -(F (Pi.single j 1) k).im := by
    intro k j
    have h1 := hD (Pi.single k 1) (Pi.single j 1)
    have h2 := hD (Pi.single k I) (Pi.single j I)
    have h3 := hD (Pi.single k I) (Pi.single j 1)
    simp only [dotProduct_single, mul_one, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_sub, sub_zero] at h1 h2 h3
    refine ⟨by linarith, by linarith, by linarith⟩
  have hMsym : Mᵀ = M := by
    ext k j
    rw [transpose_apply]
    obtain ⟨a1, a2, a3⟩ := hsym k j
    obtain ⟨b1, b2, b3⟩ := hsym j k
    apply Complex.ext <;> simp [M, Complex.mul_re, Complex.mul_im] <;> linarith
  have hNherm : ∀ i j, (starRingEnd ℂ) (N i j) = N j i := by
    intro k j
    obtain ⟨a1, a2, a3⟩ := hsym k j
    obtain ⟨b1, b2, b3⟩ := hsym j k
    apply Complex.ext <;> simp [N, Complex.mul_re, Complex.mul_im] <;> linarith

  let A : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun u v => u ⬝ᵥ M *ᵥ v
  let K : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun z u => z ⬝ᵥ Nᵀ *ᵥ star u
  have hAsym : ∀ u v, A u v = A v u := by
    intro u v
    simp only [A]
    conv_rhs => rw [← hMsym]
    rw [mulVec_transpose, dotProduct_comm v, ← dotProduct_mulVec]
  have hBF : ∀ (l : Λ) z, B l z = A l z + K z l := by
    intro l z
    simp only [A, K]
    rw [hF, hFMN, add_dotProduct, dotProduct_mulVec, mulVec_transpose, dotProduct_comm z]
  have hKherm : ∀ u v, K v u = (starRingEnd ℂ) (K u v) := by
    intro u v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [K, dotProduct, mulVec, transpose_apply, map_sum, map_mul, Pi.star_apply,
      Complex.star_def, Complex.conj_conj, hNherm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAadd : ∀ u v, A (u + v) (u + v) = A u u + A u v + A u v + A v v := by
    intro u v
    have := hAsym v u
    simp only [A, mulVec_add, dotProduct_add, add_dotProduct] at this ⊢
    rw [this]; ring
  have hKadd : ∀ u v, K (u + v) (u + v) = K u u + K u v + K v u + K v v := by
    intro u v
    simp only [K, star_add, mulVec_add, dotProduct_add, add_dotProduct]
    ring

  let Hm : Matrix (Fin g) (Fin g) ℂ := (Real.pi⁻¹ : ℝ) • Nᵀ
  have hHmK : ∀ x y, (Real.pi : ℂ) * (x ⬝ᵥ Hm *ᵥ star y) = K x y := by
    intro x y
    simp only [Hm, K, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul, Complex.ofReal_inv]
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hHerm : Hm.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [Hm, hNherm]
  have hint : ∀ l m : Λ, ∃ n : ℤ, ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = n := by
    intro l m
    obtain ⟨n, hn⟩ := hskew l m
    rw [hBF, hBF, hAsym m l, hKherm l m] at hn
    have him := congrArg Complex.im hn
    simp [Complex.mul_im] at him
    have h1 : Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = (K l m).im := by
      rw [← hHmK]; simp
    refine ⟨-n, ?_⟩
    push_cast
    apply mul_left_cancel₀ Real.pi_pos.ne'
    rw [h1]; linarith
  choose e he using hint
  have headd1 : ∀ l l' m, e (l + l') m = e l m + e l' m := by
    intro l l' m
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← he, ← he, ← he]
    simp only [Submodule.coe_add, add_dotProduct, Complex.add_im]
  have headd2 : ∀ l m m', e l (m + m') = e l m + e l m' := by
    intro l m m'
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← he, ← he, ← he]
    simp only [Submodule.coe_add, star_add, mulVec_add, dotProduct_add, Complex.add_im]
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ e headd1
    (fun c l m => map_zsmul (AddMonoidHom.mk' (fun l => e l m) (fun l l' => headd1 l l' m)) c l)
    headd2
    (fun c l m => map_zsmul (AddMonoidHom.mk' (fun m => e l m) (fun m m' => headd2 l m m')) c m)
  have ha0 : a 0 = 1 := by
    have h := hcoc 0 0
    rw [add_zero, map_zero, LinearMap.zero_apply, Complex.exp_zero, mul_one] at h
    exact mul_left_cancel₀ (ha 0) (h.symm.trans (mul_one (a 0)).symm)
  let φ0 : Λ →+ ℝ :=
    { toFun := fun l => Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2
      map_zero' := by simp [ha0, A, K]
      map_add' := fun l m => by
        rw [hcoc, norm_mul, norm_mul, Complex.norm_exp,
          Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m)))
            (Real.exp_pos _).ne',
          Real.log_mul (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m)), Real.log_exp,
          Submodule.coe_add, hAadd, hKadd, hBF, hKherm (l : Fin g → ℂ) m]
        simp only [Complex.add_re, Complex.conj_re]
        ring }
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ φ0
  let c : Fin g → ℂ := fun j => (φ (Pi.single j 1) : ℂ) - I * φ (Pi.single j I)
  have hc : ∀ u, (c ⬝ᵥ u).re = φ u := by
    intro u
    conv_rhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_add (f := _), map_smul, smul_eq_mul, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [c, Complex.mul_re]
    ring
  let χ : Λ → ℂ := fun l => a l * cexp (-(A l l) / 2 - K l l / 2) * cexp (-(c ⬝ᵥ (l : Fin g → ℂ)))
  have hχ : ∀ l, ‖χ l‖ = 1 := by
    intro l
    have h1 : (c ⬝ᵥ (l : Fin g → ℂ)).re = Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2 := by
      rw [hc, hφ]; rfl
    simp only [χ, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.sub_re, Complex.div_ofNat_re,
      h1, mul_assoc, ← Real.exp_add]
    rw [show -(A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2 +
        -(Real.log ‖a l‖ - (A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2) = -Real.log ‖a l‖ by ring,
      Real.exp_neg, Real.exp_log (norm_pos_iff.mpr (ha l))]
    exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr (ha l))
  let Q : (Fin g → ℂ) → ℂ := fun z => A z z / 2 + c ⬝ᵥ z
  refine ⟨Hm, χ, Ef, Q, hHerm, hχ, fun l m => (he l m).symm, ?_, by simp [Q, A], ?_⟩
  · simp only [Q, A, dotProduct, mulVec]
    fun_prop
  · intro l z
    have hQ : Q z - Q (z + l) = -A l z - A l l / 2 - c ⬝ᵥ l := by
      simp only [Q, dotProduct_add]
      rw [hAadd, hAsym z l]; ring
    have h2 : (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (l : Fin g → ℂ)) = K l l / 2 := by
      rw [← hHmK]; ring
    rw [hHmK, h2, mul_assoc, ← Complex.exp_add, hBF, hQ]
    simp only [χ]
    rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.AutomorphyFactorExpLinearOfCube
section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem entire_hom_eq_cexp_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (h : V → ℂ) (hd : Differentiable ℂ h) (h0 : h 0 = 1) (hadd : ∀ y z, h (y + z) = h y * h z)
    (z : V) : h z = cexp (fderiv ℂ h 0 z) := by
  set B : V →L[ℂ] ℂ := fderiv ℂ h 0 with hB
  have hder : ∀ w, HasFDerivAt h (h w • B) w := by
    intro w
    have e : h = fun u => h w * h (u - w) := by
      funext u
      rw [← hadd]; congr 1; abel
    have h1 : HasFDerivAt h B (w - w) := by
      rw [sub_self]; exact (hd 0).hasFDerivAt
    have h2 : HasFDerivAt (fun u => h (u - w)) B w := by
      have := HasFDerivAt.comp (f := fun u => u - w) w h1 ((hasFDerivAt_id w).sub_const w)
      simpa [Function.comp_def] using this
    have h3 := h2.const_mul (h w)
    rw [← e] at h3
    exact h3
  have hφ : ∀ w, HasFDerivAt (fun u => h u * cexp (-(B u))) (0 : V →L[ℂ] ℂ) w := by
    intro w
    have h1 : HasFDerivAt (fun u => cexp (-(B u))) (cexp (-(B w)) • (-B)) w :=
      (B.hasFDerivAt.neg).cexp
    have h2 := (hder w).mul h1
    have e : h w • cexp (-B w) • -B + cexp (-B w) • h w • B = 0 := by
      rw [smul_comm (h w) (cexp (-B w)), smul_neg, smul_neg, neg_add_cancel]
    rw [e] at h2
    exact h2
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun u => h u * cexp (-(B u)))
    (fun w => (hφ w).differentiableAt) (fun w => (hφ w).fderiv) z 0
  simp only [h0, map_zero, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [Complex.exp_neg] at hc
  have := Complex.exp_ne_zero (B z)
  field_simp at hc
  exact hc

theorem clm_eq_of_cexp_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B C : V →L[ℂ] ℂ) (h : ∀ z, cexp (B z) = cexp (C z)) : B = C := by
  have h1 : HasFDerivAt (fun u => cexp (B u)) (cexp (B 0) • B) 0 := B.hasFDerivAt.cexp
  have h2 : HasFDerivAt (fun u => cexp (C u)) (cexp (C 0) • C) 0 := C.hasFDerivAt.cexp
  have e : (fun u => cexp (B u)) = fun u => cexp (C u) := funext h
  rw [e] at h1
  simpa using h1.unique h2

theorem prod_finset_fin_three {M : Type*} [CommMonoid M] (f : Finset (Fin 3) → M) :
    ∏ I, f I = f ∅ * (f {0} * (f {1} * (f {2} * (f {0, 1} * (f {0, 2} * (f {1, 2} *
      f {0, 1, 2})))))) := by
  have e : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [e]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]

theorem automorphyFactor_exp_linear_of_cube :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) ∧ (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) ∧ ∀ (l : Λ) i z, z ∈ W i → fr i z = a l * cexp (B l z) * fr i (z + l)) := by
  intro g ι W c hWo hcov _ _ _ T _ hT0 _ Λ _ _ hWp hcp hTp fr κ ⟨hfd, hf0, hfc⟩ hcube
  choose σ hσ using hcov
  have hf0' : ∀ i z, z ∈ W i → fr i z ≠ 0 := fun i z hz => hf0 i z hz (Set.mem_univ _)
  have hfa : ∀ i z, z ∈ W i → DifferentiableAt ℂ (fr i) z := fun i z hz => by
    have := hfd i
    rw [Set.inter_univ] at this
    exact this.differentiableAt ((hWo i).mem_nhds hz)
  let α : Λ → (Fin g → ℂ) → ℂ := fun l z => fr (σ z) z / fr (σ z) (z + l)
  have hα : ∀ (l : Λ) i z, z ∈ W i → α l z = fr i z / fr i (z + l) := by
    intro l i z hz
    have hzl : z + l ∈ W i := (hWp i z l l.2).2 hz
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    have e1 := hfc (σ z) i z (hσ z) hz (Set.mem_univ _)
    have e2 := hfc (σ z) i (z + l) hzl' hzl (Set.mem_univ _)
    rw [hcp _ _ z l l.2] at e2
    have hc0 : c (σ z) i z ≠ 0 := by
      intro h
      rw [h, zero_mul] at e1
      exact hf0' _ _ (hσ z) e1
    show fr (σ z) z / fr (σ z) (z + l) = _
    rw [e1, e2, mul_div_mul_left _ _ hc0]
  have hα0 : ∀ (l : Λ) z, α l z ≠ 0 := fun l z =>
    div_ne_zero (hf0' _ _ (hσ z)) (hf0' _ _ ((hWp _ z l l.2).2 (hσ z)))
  have hαd : ∀ l : Λ, Differentiable ℂ (α l) := by
    intro l z
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    have h1 : DifferentiableAt ℂ (fun w => fr (σ z) (w + l)) z :=
      (hfa _ _ hzl').comp z (differentiableAt_id.add_const _)
    have h2 : DifferentiableAt ℂ (fun w => fr (σ z) w / fr (σ z) (w + l)) z := by
      simp only [div_eq_mul_inv]
      exact (hfa _ _ (hσ z)).mul (h1.inv (hf0' _ _ hzl'))
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [(hWo (σ z)).mem_nhds (hσ z)] with w hw
    exact hα l _ w hw
  have hαc : ∀ (l m : Λ) z, α (l + m) z = α l z * α m (z + l) := by
    intro l m z
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    rw [hα (l + m) _ z (hσ z), hα l _ z (hσ z), hα m _ (z + l) hzl', Submodule.coe_add,
      ← add_assoc]
    have := hf0' _ _ hzl'
    field_simp
  have hcubeα : ∀ (l : Λ) y z, α l (y + z) * α l 0 = α l y * α l z := by
    intro l y z
    let x : Fin 3 → Fin g → ℂ := ![0, y, z]
    let L : Fin 3 → Fin g → ℂ := ![l, 0, 0]
    have hL : ∀ a, L a ∈ Λ := by
      intro a
      fin_cases a
      · exact l.2
      · exact Λ.zero_mem
      · exact Λ.zero_mem
    let j : Finset (Fin 3) → ι := fun I => σ (∑ a ∈ I, x a)
    have hj : ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I) := fun I => hσ _
    have hs : ∀ I : Finset (Fin 3), ∑ a ∈ I, (x + L) a = ∑ a ∈ I, x a + ∑ a ∈ I, L a := by
      intro I
      simp only [Pi.add_apply, Finset.sum_add_distrib]
    have hj' : ∀ I : Finset (Fin 3), ∑ a ∈ I, (x + L) a ∈ W (j I) := by
      intro I
      rw [hs]
      exact (hWp _ _ _ (Λ.sum_mem fun a _ => hL a)).2 (hj I)
    have e1 := hcube j x hj
    have e2 := hcube j (x + L) hj'
    have hκ : κ ≠ 0 := by
      intro h
      rw [h, zero_mul] at e1
      exact hT0 j x hj e1
    rw [hTp j x L hL, e1] at e2
    have e3 := mul_left_cancel₀ hκ e2
    have e4 : ∏ I : Finset (Fin 3), (fr (j I) (∑ a ∈ I, x a) /
        fr (j I) (∑ a ∈ I, x a + ∑ a ∈ I, L a)) ^ ((-1 : ℤ) ^ (3 - I.card)) = 1 := by
      simp only [div_zpow, Finset.prod_div_distrib]
      simp only [hs] at e3
      rw [← e3]
      exact div_self (Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hf0' _ _ (hj I)))
    have hz : ∀ (m : Λ) w, (m : Fin g → ℂ) = 0 → α m w = 1 := by
      intro m w hm
      show fr (σ w) w / fr (σ w) (w + m) = 1
      rw [hm, add_zero]
      exact div_self (hf0' _ _ (hσ w))
    have hl : ∀ (m : Λ) w w', (m : Fin g → ℂ) = l → w = w' → α m w = α l w' := by
      intro m w w' hm hw
      rw [Subtype.ext hm, hw]
    let F : Finset (Fin 3) → ℂ := fun I =>
      α ⟨∑ a ∈ I, L a, Λ.sum_mem fun a _ => hL a⟩ (∑ a ∈ I, x a)
    have e6 : ∏ I : Finset (Fin 3), F I ^ ((-1 : ℤ) ^ (3 - I.card)) = 1 := e4
    have f0 : F ∅ = 1 := hz _ _ (by simp)
    have f1 : F {0} = α l 0 := hl _ _ _ (by simp [L]) (by simp [x])
    have f2 : F {1} = 1 := hz _ _ (by simp [L])
    have f3 : F {2} = 1 := hz _ _ (by simp [L])
    have f4 : F {0, 1} = α l y := hl _ _ _ (by simp [L]) (by simp [x])
    have f5 : F {0, 2} = α l z := hl _ _ _ (by simp [L]) (by simp [x])
    have f6 : F {1, 2} = 1 := hz _ _ (by simp [L])
    have f7 : F {0, 1, 2} = α l (y + z) := hl _ _ _ (by simp [L]) (by simp [x])
    clear e4
    have e4 := e6
    rw [prod_finset_fin_three, f0, f1, f2, f3, f4, f5, f6, f7] at e4
    have c1 : ({0} : Finset (Fin 3)).card = 1 := rfl
    have c2 : ({0, 1} : Finset (Fin 3)).card = 2 := rfl
    have c3 : ({0, 2} : Finset (Fin 3)).card = 2 := rfl
    have c4 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := rfl
    rw [c1, c2, c3, c4] at e4
    norm_num at e4
    have := hα0 l y
    have := hα0 l z
    field_simp at e4
    linear_combination e4
  let B₀ : Λ → ((Fin g → ℂ) →L[ℂ] ℂ) := fun l => fderiv ℂ (fun z => α l z / α l 0) 0
  have hexp : ∀ (l : Λ) z, α l z = α l 0 * cexp (B₀ l z) := by
    intro l z
    have h0 := hα0 l 0
    have := entire_hom_eq_cexp_fderiv (fun z => α l z / α l 0)
      (by simp only [div_eq_mul_inv]; exact (hαd l).mul_const _)
      (div_self h0) (fun y z => by
        have := hcubeα l y z
        field_simp
        linear_combination this) z
    show _ = _ * cexp (fderiv ℂ (fun z => α l z / α l 0) 0 z)
    rw [← this]
    field_simp
  have ha : ∀ l m : Λ, α (l + m) 0 = α l 0 * α m 0 * cexp (B₀ l m) := by
    intro l m
    rw [add_comm, hαc, zero_add, hexp l m]
    ring
  have hBadd : ∀ l m : Λ, B₀ (l + m) = B₀ l + B₀ m := by
    intro l m
    apply clm_eq_of_cexp_eq
    intro z
    have e := hαc m l z
    rw [add_comm m l, hexp (l + m), hexp m, hexp l, ha, map_add (f := _), Complex.exp_add] at e
    rw [ContinuousLinearMap.add_apply, Complex.exp_add]
    have h1 : α l 0 * α m 0 * cexp (B₀ l m) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (hα0 _ _) (hα0 _ _)) (Complex.exp_ne_zero _)
    apply mul_left_cancel₀ h1
    linear_combination e
  refine ⟨fun l => α l 0, AddMonoidHom.mk' (fun l => (B₀ l).toLinearMap) ?_, fun l => hα0 l 0,
    ha, ?_⟩
  · intro l m
    rw [hBadd]; rfl
  · intro l i z hz
    have e := hexp l z
    rw [hα l i z hz, div_eq_iff (hf0' _ _ ((hWp _ z l l.2).2 hz))] at e
    exact e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfMemPowMaximal
section
namespace GlobalTheory.EqZeroOfMemMaximalPow

theorem eq_zero_of_mem_pow_maximal {R : Type} [CommRing R] [IsNoetherianRing R] (y : R)
    (h : ∀ i : MaximalSpectrum R × ℕ, y ∈ i.1.asIdeal ^ (i.2 + 1)) : y = 0 := by
  by_contra hy
  have hJ : LinearMap.ker (LinearMap.toSpanSingleton R R y) ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hy h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
  have hmem : y ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    rcases i with _ | i
    · simp
    · have hi := h (⟨m, hm⟩, i)
      simpa [smul_eq_mul, Ideal.mul_top] using hi
  obtain ⟨⟨r, hr⟩, hry⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff m y).mp hmem
  have hJr : (1 - r) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, sub_smul, one_smul]
    exact sub_eq_zero.mpr hry.symm
  have h1 : (1 : R) ∈ m := by simpa using m.add_mem (hle hJr) hr
  exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end GlobalTheory.EqZeroOfMemMaximalPow
end

