module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjEqNegOfSqEqNegNat
section
namespace GlobalTheory.ConjNegSquareNat

theorem conj_eq_neg_of_sq_eq_neg_nat {z : ℂ} {d : ℕ} (hd : (0 : ℕ) < d)
    (h : z ^ (2 : ℕ) = -(↑d : ℂ)) : (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h0 : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hm with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp

end GlobalTheory.ConjNegSquareNat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAwaySubalgebraEmbedding
section
namespace GlobalTheory.AwaySubalgebraEmbedding

theorem exists_away_subalgebra_embedding (K : Type) [Field K] (S : Type) [CommRing S]
    [Algebra K S] (S₁ : Subalgebra K S) (x : S) (hx : x ∈ S₁) :
    ∃ (κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x),
      (∀ s : S₁, κ (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) s)
        = algebraMap S (Localization.Away x) (s : S)) ∧
      Function.Injective κ ∧
      ∀ (z : Localization.Away x) (m : ℕ), ∀ s ∈ S₁,
        z * algebraMap S (Localization.Away x) x ^ m = algebraMap S (Localization.Away x) s →
          z ∈ AlgHom.range κ := by
  let f : S₁ →ₐ[K] Localization.Away x :=
    (IsScalarTower.toAlgHom K S (Localization.Away x)).comp S₁.val
  have hxu : IsUnit (algebraMap S (Localization.Away x) x) :=
    IsLocalization.Away.algebraMap_isUnit x
  have hf : ∀ y : Submonoid.powers (⟨x, hx⟩ : S₁), IsUnit (f y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact hxu.pow n
  let κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (⟨x, hx⟩ : S₁)) hf
  have hκ : ∀ s : S₁, κ (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) s)
      = algebraMap S (Localization.Away x) (s : S) := by
    intro s
    exact IsLocalization.lift_eq (M := Submonoid.powers (⟨x, hx⟩ : S₁))
      (g := (f : S₁ →+* Localization.Away x)) hf s
  have hxu₁ : IsUnit (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨x, hx⟩) :=
    IsLocalization.Away.algebraMap_isUnit _
  refine ⟨κ, hκ, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨n, s, hs⟩ := IsLocalization.Away.surj (⟨x, hx⟩ : S₁) a
    have h0 : algebraMap S (Localization.Away x) (s : S) = 0 := by
      rw [← hκ, ← hs, map_mul, ha, zero_mul]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers x) (Localization.Away x) _).1 h0
    have h1 : (⟨x, hx⟩ : S₁) ^ k * s = 0 := by
      apply Subtype.ext
      simpa using hk
    have h2 : a * algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨x, hx⟩ ^ (n + k) = 0 := by
      rw [pow_add, ← mul_assoc, hs, ← map_pow, ← map_mul, mul_comm, h1, map_zero]
    exact (hxu₁.pow (n + k)).mul_left_eq_zero.1 h2
  · intro z m s hs hz
    obtain ⟨u, hu⟩ := hxu₁.pow m
    refine ⟨algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨s, hs⟩ * ↑u⁻¹, ?_⟩
    apply (hxu.pow m).mul_right_cancel
    have h3 : κ ↑u = algebraMap S (Localization.Away x) x ^ m := by
      rw [hu, map_pow, hκ]
    show κ _ * _ = _
    rw [hz, ← h3, ← map_mul, mul_assoc, Units.inv_mul, mul_one, hκ]

end GlobalTheory.AwaySubalgebraEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntMulMem
section
namespace GlobalTheory.IntMulMem

open NumberField

theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (Λ : Submodule (RingOfIntegers E) V) :
    ∀ v ∈ Submodule.span E (↑Λ : Set V), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ (↑N : E) • v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hNx⟩ := hx
    obtain ⟨M, hM, hMy⟩ := hy
    refine ⟨N * M, mul_ne_zero hN hM, ?_⟩
    have h1 : ((N * M : ℤ) : E) • x = ((M : ℤ) : RingOfIntegers E) • ((N : E) • x) := by
      rw [← algebraMap_smul E ((M : ℤ) : RingOfIntegers E), smul_smul]
      congr 1
      simp [mul_comm]
    have h2 : ((N * M : ℤ) : E) • y = ((N : ℤ) : RingOfIntegers E) • ((M : E) • y) := by
      rw [← algebraMap_smul E ((N : ℤ) : RingOfIntegers E), smul_smul]
      congr 1
      simp
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem _ hNx) (Λ.smul_mem _ hMy)
  | smul c x _ hx =>
    obtain ⟨N, hN, hNx⟩ := hx
    have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
    obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
    let a : RingOfIntegers E := ⟨y • c, hyi⟩
    refine ⟨y * N, mul_ne_zero hy0 hN, ?_⟩
    have h : ((y * N : ℤ) : E) • (c • x) = a • ((N : E) • x) := by
      rw [← algebraMap_smul E a, smul_smul, smul_smul]
      congr 1
      show _ = (y • c) * (N : E)
      rw [zsmul_eq_mul]; push_cast; ring
    rw [h]
    exact Λ.smul_mem _ hNx

end GlobalTheory.IntMulMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryApplyEqOfFormSubNeZero
section
open MeasureTheory Topology Matrix
open scoped ENNReal

namespace GlobalTheory

section Abstract
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem exists_isometry_apply_eq_of_form_sub_ne_zero (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x y, B y x = (starRingEnd ℂ) (B x y)) (x₀ v : V) (hv : B v v = B x₀ x₀)
    (hc : B x₀ (x₀ - v) ≠ 0) :
    ∃ u : V →ₗ[ℂ] V, (∀ x y, B (u x) (u y) = B x y) ∧ u x₀ = v := by
  set d := x₀ - v with hd
  set c := B x₀ d with hcdef
  have hdd : B d d = c + (starRingEnd ℂ) c := by
    rw [hcdef, ← hB x₀ d, hd]
    simp only [map_sub, LinearMap.sub_apply, hv]
    ring
  have hc' : (starRingEnd ℂ) c ≠ 0 := by simpa using hc
  refine ⟨LinearMap.id - (c⁻¹ • (B.flip d)).smulRight d, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, map_sub, map_smul, map_smulₛₗ, smul_eq_mul,
      map_mul, map_inv₀, hdd, hB y d, RingHom.id_apply]
    field_simp
    ring
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, ← hcdef, inv_mul_cancel₀ hc,
      one_smul]
    rw [hd]; abel

theorem form_eq_smul_of_const_on_orbit (A B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hA : ∀ x y, A y x = (starRingEnd ℂ) (A x y))
    (hB : ∀ x y, B y x = (starRingEnd ℂ) (B x y)) (x₀ : V) (e : ℂ) (he : e ≠ 0)
    (hnd : ∃ y, B x₀ y ≠ 0)
    (h : ∀ u : V →ₗ[ℂ] V, (∀ x y, B (u x) (u y) = B x y) → A (u x₀) (u x₀) = e) :
    ∃ t : ℝ, t ≠ 0 ∧ ∀ x y, A x y = (t : ℂ) * B x y := by
  have reach : ∀ v, B v v = B x₀ x₀ → B x₀ (x₀ - v) ≠ 0 → A v v = e := by
    intro v hv hc
    obtain ⟨u, hu, hx⟩ := exists_isometry_apply_eq_of_form_sub_ne_zero B hB x₀ v hv hc
    rw [← hx]; exact h u hu
  have hBre : ∀ y, ((B y y).re : ℂ) = B y y := fun y => Complex.conj_eq_iff_re.mp (hB y y).symm
  have hAre : ∀ y, ((A y y).re : ℂ) = A y y := fun y => Complex.conj_eq_iff_re.mp (hA y y).symm
  have h0 : A x₀ x₀ = e := h LinearMap.id (fun _ _ => rfl)
  by_cases ha : B x₀ x₀ = 0
  · exfalso
    obtain ⟨y, hy⟩ := hnd
    have hy' : (starRingEnd ℂ) (B x₀ y) ≠ 0 := by simpa using hy
    set w := y + (-(B y y) / (2 * B x₀ y)) • x₀ with hw
    have hww : B w w = 0 := by
      have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
      simp only [hw, map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, ha, hB x₀ y, map_div₀, map_neg, map_mul, ← hB y y, h2, RingHom.id_apply]
      field_simp
      ring
    have hxw : B x₀ w = B x₀ y := by
      simp only [hw, map_add (f := _), map_smulₛₗ, ha, smul_eq_mul, mul_zero, add_zero]
    have h1 : A w w = e := reach w (by rw [hww, ha]) (by simpa [ha, hxw] using hy)
    have h2 : A (w + w) (w + w) = e := reach (w + w) (by simp [hww, ha])
      (by
        simp only [map_sub, map_add (f := _), ha, hxw]
        intro hh
        apply hy
        linear_combination (-1 / 2 : ℂ) * hh)
    simp only [map_add (f := _), LinearMap.add_apply, h1] at h2
    apply he
    linear_combination (1 / 3 : ℂ) * h2
  · have reach2 : ∀ v, B v v = B x₀ x₀ → A v v = e := by
      intro v hv
      by_cases hc : B x₀ (x₀ - v) = 0
      · have := reach (-v) (by simpa using hv) (by
          simp only [map_sub, map_neg] at hc ⊢
          intro hh
          apply ha
          linear_combination (1 / 2 : ℂ) * (hh + hc))
        simpa using this
      · exact reach v hv hc
    set a : ℝ := (B x₀ x₀).re with hadef
    have haC : B x₀ x₀ = (a : ℂ) := (hBre x₀).symm
    have ha0 : a ≠ 0 := by
      intro hh; apply ha; rw [haC, hh]; simp
    have ha0C : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
    have reach3 : ∀ v, 0 < a * (B v v).re → (a : ℂ) * A v v = e * B v v := by
      intro v hv
      have hb : (B v v).re ≠ 0 := by
        intro hh; rw [hh] at hv; simp at hv
      have hq : 0 < a / (B v v).re := by
        have : a / (B v v).re = a * (B v v).re / ((B v v).re) ^ 2 := by field_simp
        rw [this]; positivity
      set s : ℝ := Real.sqrt (a / (B v v).re) with hs
      have hss : s * s * (B v v).re = a := by
        rw [hs, Real.mul_self_sqrt hq.le]; field_simp
      have hssC : (s : ℂ) * s * B v v = a := by
        rw [← hBre v]; exact_mod_cast hss
      have := reach2 ((s : ℂ) • v) (by
        simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal,
          RingHom.id_apply, haC]
        linear_combination hssC)
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal,
          RingHom.id_apply] at this
      rw [← this, ← hssC]; ring
    have diag : ∀ y, (a : ℂ) * A y y = e * B y y := by
      intro y
      have hcont : Continuous fun t : ℝ => a * (B (x₀ + (t : ℂ) • y) (x₀ + (t : ℂ) • y)).re := by
        simp only [map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, Complex.conj_ofReal, RingHom.id_apply]
        fun_prop
      have hpos : 0 < (fun t : ℝ => a * (B (x₀ + (t : ℂ) • y) (x₀ + (t : ℂ) • y)).re) 0 := by
        simp only [Complex.ofReal_zero, zero_smul, add_zero]
        exact mul_self_pos.mpr ha0
      have hev := hcont.continuousAt.eventually (lt_mem_nhds hpos)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
      have h1 := reach3 _ (hball (y := ε / 2) (by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith))
      have h2 := reach3 _ (hball (y := -(ε / 2)) (by
        rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith))
      have hεC : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (ε / 2 : ℝ) ≠ 0)
      generalize (ε / 2 : ℝ) = t at h1 h2 hεC
      simp only [map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, Complex.conj_ofReal, RingHom.id_apply, h0, haC] at h1 h2
      push_cast at h1 h2
      have : (t : ℂ) ^ 2 * ((a : ℂ) * A y y - e * B y y) = 0 := by
        linear_combination (1 / 2 : ℂ) * (h1 + h2)
      have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hεC)
      exact sub_eq_zero.mp this
    have heC : e = (e.re : ℂ) := by rw [← h0]; exact (hAre x₀).symm
    have he0 : e.re ≠ 0 := by
      intro hh; apply he; rw [heC, hh]; simp
    refine ⟨e.re / a, div_ne_zero he0 ha0, fun x y => ?_⟩
    have h1 := diag (x + y)
    have h2 := diag (x + Complex.I • y)
    have h3 := diag x
    have h4 := diag y
    simp only [map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, Complex.conj_I, RingHom.id_apply] at h1 h2
    push_cast
    rw [← heC]
    field_simp
    have hI := Complex.I_mul_I
    linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (1 / 2 + Complex.I / 2) * h3
      - (1 / 2 + Complex.I / 2) * h4
      + ((1 / 2 : ℂ) * ((a : ℂ) * A x y - e * B x y - ((a : ℂ) * A y x - e * B y x))
        + (Complex.I / 2) * ((a : ℂ) * A y y - e * B y y)) * hI

end Abstract

private noncomputable def matForm {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) :
    (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x ⬝ᵥ M *ᵥ star y)
    (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => by simp [smul_dotProduct])
    (fun _ _ _ => by rw [star_add, mulVec_add, dotProduct_add])
    (fun _ _ _ => by rw [star_smul, mulVec_smul, dotProduct_smul]; rfl)

private theorem matForm_apply {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (x y : Fin r → ℂ) :
    matForm M x y = ∑ k, ∑ l, x k * M k l * (starRingEnd ℂ) (y l) := by
  simp [matForm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem matForm_single {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    matForm M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [matForm_apply, Pi.single_apply, apply_ite]

private theorem matForm_symm {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : M.IsHermitian)
    (x y : Fin r → ℂ) : matForm M y x = (starRingEnd ℂ) (matForm M x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [matForm_apply, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have : (starRingEnd ℂ) (M k l) = M l k := hM.apply l k
  rw [this]; ring

private theorem matForm_conj {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ)
    (u : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ)) (i j : Fin r) :
    ((LinearMap.toMatrix' u)ᵀ * M * (LinearMap.toMatrix' u).map (starRingEnd ℂ)) i j
      = matForm M (u (Pi.single i 1)) (u (Pi.single j 1)) := by
  simp only [matForm_apply, Matrix.mul_apply, transpose_apply, map_apply,
    LinearMap.toMatrix'_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hermitian_eq_smul_of_const_on_unitary_orbit :
    ∀ (r : ℕ) (A B : Matrix (Fin r) (Fin r) ℂ) (i : Fin r) (e : ℂ), e ≠ 0 → A.IsHermitian → B.IsHermitian → B.det ≠ 0 → (∀ u : Matrix (Fin r) (Fin r) ℂ, uᵀ * B * u.map (starRingEnd ℂ) = B → (uᵀ * A * u.map (starRingEnd ℂ)) i i = e) → ∃ t : ℝ, t ≠ 0 ∧ A = (t : ℂ) • B := by
  intro r A B i e he hA hB hdet h
  obtain ⟨t, ht, hAB⟩ := form_eq_smul_of_const_on_orbit (matForm A) (matForm B)
    (matForm_symm hA) (matForm_symm hB) (Pi.single i 1) e he
    (by
      by_contra hcon
      push_neg at hcon
      apply hdet
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      rw [← matForm_single B i j, hcon])
    (fun u hu => by
      rw [← matForm_conj]
      apply h
      ext j k
      rw [matForm_conj, hu, matForm_single])
  refine ⟨t, ht, ?_⟩
  ext j k
  rw [← matForm_single A j k, hAB, matForm_single, Matrix.smul_apply, smul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNatMulMem
section
namespace GlobalTheory.NatMulMemUnitaryExistence

open NumberField

theorem exists_nat_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : 𝓞 E, (a : E) = (k : E) * c := by
  obtain ⟨y, hy, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  have hcast : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  have hint' : IsIntegral ℤ ((y.natAbs : E) * c) := by
    rcases Int.natAbs_eq y with h | h
    · rw [hcast, ← h, ← zsmul_eq_mul]; exact hint
    · have h2 : (y.natAbs : ℤ) = -y := by omega
      rw [hcast, h2, Int.cast_neg, neg_mul, ← zsmul_eq_mul]; exact hint.neg
  exact ⟨⟨_, hint'⟩, rfl⟩

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (y + z) = d₂ • (d₁ • y) + d₁ • (d₂ • z) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_of_tower_mem d₂ h₁) (L.smul_of_tower_mem d₁ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨k, hk, a, ha⟩ := exists_nat_mul_mem c
    refine ⟨k * d, Nat.mul_pos hk hd, ?_⟩
    have e : (k * d) • (c • y) = a • (d • y) := by
      funext i
      simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
      rw [Algebra.smul_def, show algebraMap (𝓞 E) E a = (a : E) from rfl, ha]
      simp only [Pi.mul_apply, Pi.natCast_apply]
      push_cast; ring
    rw [e]
    exact L.smul_mem a h

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E), ∃ (d : ℕ), (0 : ℕ) < d ∧ d • x ∈ L :=
  fun L hL x => main L hL x

end GlobalTheory.NatMulMemUnitaryExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNeZeroSmulMemOfMemSpan
section
namespace GlobalTheory.NonzeroSmulMemSpan

theorem exists_ne_zero_smul_mem_of_mem_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (A : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E (↑A : Set (Fin n → E))) :
    ∃ (o : NumberField.RingOfIntegers E), o ≠ (0 : NumberField.RingOfIntegers E) ∧ o • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact A.smul_mem b hay
    · rw [mul_smul]
      exact A.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(q : NumberField.RingOfIntegers E) * a,
      mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩
    have key : ((q : NumberField.RingOfIntegers E) * a) • c • y = p • a • y := by
      rw [← algebraMap_smul E ((q : NumberField.RingOfIntegers E) * a),
        ← algebraMap_smul E p, ← algebraMap_smul E a y, smul_smul, smul_smul, map_mul]
      simp only at hpq
      rw [← hpq]
      congr 1
      ring
    rw [key]
    exact A.smul_mem p hay

end GlobalTheory.NonzeroSmulMemSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfSpanEqTop
section
namespace GlobalTheory.SmulMemSpanTop

open NumberField

theorem exists_smul_mem_of_span_eq_top {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (h : Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (↑Λ : Set (Fin n → E)) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ hax
    · rw [mul_smul, smul_comm]
      rw [smul_comm]; exact Λ.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) c
    refine ⟨a * s, mul_ne_zero ha (nonZeroDivisors.coe_ne_zero s), ?_⟩
    have h1 : (s : 𝓞 E) • c • x = r • x := by
      rw [← algebraMap_smul E (s : 𝓞 E), ← algebraMap_smul E r, smul_smul, mul_comm]
      exact congrArg (· • x) hrs
    rw [mul_smul, h1, smul_comm]
    exact Λ.smul_mem _ hax

end GlobalTheory.SmulMemSpanTop
end

