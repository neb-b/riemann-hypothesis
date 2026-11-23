module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensChLift
section
noncomputable section

open NumberField Complex

namespace PI.VolStabSW

namespace ChLiftW

theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hne : ∀ x, χ x ≠ 0 := by
    intro x h
    have h1 := hadd x (-x)
    rw [add_neg_cancel, h0, h, zero_mul] at h1
    exact one_ne_zero h1
  have hpow : ∀ (k : ℕ) (y : W), χ ((k : ℝ) • y) = χ y ^ k := by
    intro k y
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ y : W, ‖y‖ ≤ δ → ‖χ y - 1‖ < 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
    have h2 := h (x := y) (by rw [dist_zero_right]; linarith)
    rwa [h0, dist_eq_norm] at h2
  have hre : ∀ y : W, ‖y‖ ≤ δ → 0 < (χ y).re := by
    intro y hy
    have h1 := hball y hy
    have h2 : |(χ y - 1).re| ≤ ‖χ y - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.1 (h2.trans h1.le)).1
    linarith
  have harg : ∀ y : W, ‖y‖ ≤ δ → |Complex.arg (χ y)| < Real.pi / 2 := fun y hy =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre y hy))
  set L : W → ℂ := fun y => Complex.log (χ y) with hL
  have hL0 : L 0 = 0 := by simp [hL, h0]
  have hLadd : ∀ y z : W, ‖y‖ ≤ δ → ‖z‖ ≤ δ → L (y + z) = L y + L z := by
    intro y z hy hz
    simp only [hL]
    have h1 := abs_lt.1 (harg y hy)
    have h2 := abs_lt.1 (harg z hz)
    rw [hadd, Complex.log_mul (hne y) (hne z)]
    constructor <;> linarith [Real.pi_pos]
  have hLsmul : ∀ (k : ℕ) (y : W), (k : ℝ) * ‖y‖ ≤ δ → L ((k : ℝ) • y) = k * L y := by
    intro k y
    induction k with
    | zero => intro _; simp [hL0]
    | succ k ih =>
      intro hk
      have hy0 := norm_nonneg y
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast at hk
      have h1 : (k : ℝ) * ‖y‖ ≤ δ := by nlinarith
      have h2 : ‖y‖ ≤ δ := by nlinarith
      have h3 : ‖(k : ℝ) • y‖ ≤ δ := by rw [norm_smul, Real.norm_natCast]; exact h1
      rw [Nat.cast_succ, add_smul, one_smul, hLadd _ _ h3 h2, ih h1]
      push_cast
      ring
  have hkey : ∀ (a b : ℕ) (x : W), 0 < a → 0 < b → ‖x‖ ≤ a * δ → ‖x‖ ≤ b * δ →
      (a : ℂ) * L ((a : ℝ)⁻¹ • x) = (b : ℂ) * L ((b : ℝ)⁻¹ • x) := by
    intro a b x ha hb hxa hxb
    have ha' : (0 : ℝ) < a := Nat.cast_pos.2 ha
    have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
    have e1 : (b : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (a : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have e2 : (a : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (b : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have ny : ‖((a : ℝ) * b)⁻¹ • x‖ = ‖x‖ / (a * b) := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
      ring
    have hb1 : (b : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (b : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / a by field_simp, div_le_iff₀ ha']
      linarith
    have ha1 : (a : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (a : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / b by field_simp, div_le_iff₀ hb']
      linarith
    rw [← e1, ← e2, hLsmul b _ hb1, hLsmul a _ ha1]
    ring
  set N : W → ℕ := fun x => ⌈‖x‖ / δ⌉₊ + 1 with hN
  have hNpos : ∀ x, 0 < N x := fun x => Nat.succ_pos _
  have hNle : ∀ x, ‖x‖ ≤ (N x : ℝ) * δ := by
    intro x
    have h1 : ‖x‖ / δ ≤ ⌈‖x‖ / δ⌉₊ := Nat.le_ceil _
    have h2 : ‖x‖ ≤ (⌈‖x‖ / δ⌉₊ : ℝ) * δ := by rwa [div_le_iff₀ hδ] at h1
    simp only [hN]
    push_cast
    nlinarith
  set f : W → ℂ := fun x => (N x : ℂ) * L ((N x : ℝ)⁻¹ • x) with hf
  have hfM : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → f x = M * L ((M : ℝ)⁻¹ • x) :=
    fun M x hM hx => hkey (N x) M x (hNpos x) hM (hNle x) hx
  have hsmall : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → ‖(M : ℝ)⁻¹ • x‖ ≤ δ := by
    intro M x hM hx
    have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hM'.le, inv_mul_le_iff₀ hM']
    linarith
  have fadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    have hMpos : 0 < N x + N y := by have := hNpos x; omega
    have hcx : (N x : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N x ≤ N x + N y)
    have hcy : (N y : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N y ≤ N x + N y)
    have hx : ‖x‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle x).trans hcx
    have hy : ‖y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle y).trans hcy
    have hxy : ‖x + y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      have h1 := norm_add_le x y
      have h2 := hNle x
      have h3 := hNle y
      push_cast
      linarith
    rw [hfM _ (x + y) hMpos hxy, hfM _ x hMpos hx, hfM _ y hMpos hy, smul_add,
      hLadd _ _ (hsmall _ x hMpos hx) (hsmall _ y hMpos hy), mul_add]
  have fexp : ∀ x, χ x = Complex.exp (f x) := by
    intro x
    show χ x = Complex.exp ((N x : ℂ) * Complex.log (χ ((N x : ℝ)⁻¹ • x)))
    rw [Complex.exp_nat_mul, Complex.exp_log (hne _), ← hpow, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast (hNpos x).ne'), one_smul]
  have fcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hMpos : 0 < N x0 + 1 := Nat.succ_pos _
    have hMr : ((N x0 + 1 : ℕ) : ℝ) = N x0 + 1 := by push_cast; ring
    have hx0 : ‖x0‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
      rw [hMr]
      nlinarith [hNle x0]
    have heq : (fun x => ((N x0 + 1 : ℕ) : ℂ) * L (((N x0 + 1 : ℕ) : ℝ)⁻¹ • x)) =ᶠ[nhds x0] f := by
      filter_upwards [Metric.ball_mem_nhds x0 hδ] with x hx
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h1 : ‖x‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
        have h2 := norm_sub_norm_le x x0
        rw [hMr]
        nlinarith [hNle x0]
      exact (hfM _ x hMpos h1).symm
    refine ContinuousAt.congr ?_ heq
    apply ContinuousAt.mul continuousAt_const
    simp only [hL]
    apply ContinuousAt.clog
    · exact (hc.comp (continuous_const_smul _)).continuousAt
    · exact Complex.mem_slitPlane_iff.2 (Or.inl (hre _ (hsmall _ x0 hMpos hx0)))
  exact ⟨AddMonoidHom.mk' f fadd, fcont, fexp⟩

theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have he0 : e 0 = 0 := by simpa using he 0 0
  have hs0 : e.symm 0 = 0 := by rw [← he0, Homeomorph.symm_apply_apply]
  have hsadd : ∀ w w' : W, e.symm (w + w') = e.symm w + e.symm w' := by
    intro w w'
    apply e.injective
    rw [he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (fun w => χ (e.symm w)) (hc.comp e.symm.continuous)
    (fun w w' => by simp only [hsadd, hadd]) (by simp only [hs0, h0])
  refine ⟨AddMonoidHom.mk' (fun x => ℓ' (e x)) (fun x y => by simp only [he, map_add (f := _)]),
    hℓc.comp e.continuous, fun x => ?_⟩
  have h1 := hℓ (e x)
  simp only [Homeomorph.symm_apply_apply] at h1
  exact h1

theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) x y) χ hc hadd h0
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) x y) χ hc hadd h0

theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  refine Finset.induction_on s (by simp [AddChar.map_zero_eq_one]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW


open Classical in
def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single v

open Classical in
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x := by
  simp only [sgl]
  exact Finset.univ_sum_single x

open ChLiftW in
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have key : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := by
    intro v
    exact lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul]) (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓ hℓc hℓ using key
  refine ⟨AddMonoidHom.mk' (fun x => ∑ v, ℓ v (x v)) (fun x y => ?_), ?_, fun x => ?_⟩
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← map_add (f := _)]
    rfl
  · exact continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · show χ x = Complex.exp (∑ v, ℓ v (x v))
    conv_lhs => rw [← sum_sgl x]
    rw [ChLiftW.addChar_sum, Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFHS
section
noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add (f := _), ← hs.herm, ← hs.herm]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z := by
  rw [sub_eq_add_neg, hs.add_right, ← neg_one_smul K z, hs.smul_right]
  ring

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := by
  exact LinearMap.mem_ker

theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') := by
  refine ⟨⟨fun x y z => hs.add_right x y z, fun c x y => hs.smul_right c x y,
    fun x y => hs.herm x y⟩, ?_⟩
  · intro w hw
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : LinearMap.range (hs.lin e) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / h e e) • e, ?_⟩
    rw [IsSq.lin_apply, hs.smul_right, div_mul_cancel₀ _ he]
  have e1 := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [hsurj, finrank_top, Module.finrank_self] at e1
  unfold perp
  omega

theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have e1 := congrArg (hs.lin (f i)) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at e1
  simp only [map_smul, IsSq.lin_apply, smul_eq_mul] at e1
  rw [Finset.sum_eq_single i] at e1
  · exact (mul_eq_zero.1 e1).resolve_right (h2 i)
  · intro j _ hji
    rw [h1 i j (Ne.symm hji), mul_zero]
  · simp

theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  have hwe : h w e = 0 := by rw [hs.herm e w, hw, map_zero]
  rw [hs.add_right, IsSq.add_left hs, IsSq.add_left hs, IsSq.smul_left hs, IsSq.smul_left hs, hs.smul_right,
    hs.smul_right, hw, hwe]
  ring

end basic

end PI.VolStabSW.FFHS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAInt
section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace PI.VolStabSW

private theorem addHom_eq_zero_of_integralBasis_mul {F : Type} [Field F] [NumberField F] (g : F →+ ℂ)
    {y : F} (hy : y ≠ 0) (h0 : ∀ i, g (integralBasis F i * y) = 0) (w : F) : g w = 0 := by
  have hw : w = (∑ i, (integralBasis F).repr (w * y⁻¹) i • integralBasis F i) * y := by
    rw [(integralBasis F).sum_repr, mul_assoc, inv_mul_cancel₀ hy, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hw, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [smul_mul_assoc, map_rat_smul, h0 i, smul_zero]

private theorem exists_mul_integers_of_fg {F : Type} [Field F] [NumberField F]
    (Λ : Submodule (𝓞 F) F) (hfg : (Λ.restrictScalars ℤ).FG) :
    ∃ c : F, c ≠ 0 ∧ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r := by
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (M := (𝓞 F)⁰) (S := F) s
  have hB0 : algebraMap (𝓞 F) F b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  let T : Submodule ℤ F :=
    { carrier := {a | ∃ r : 𝓞 F, algebraMap (𝓞 F) F b * a = algebraMap (𝓞 F) F r}
      add_mem' := by
        rintro a a' ⟨r, hr⟩ ⟨r', hr'⟩
        exact ⟨r + r', by rw [mul_add, hr, hr', map_add (f := _)]⟩
      zero_mem' := ⟨0, by rw [mul_zero, map_zero]⟩
      smul_mem' := by
        rintro n a ⟨r, hr⟩
        exact ⟨n • r, by rw [mul_smul_comm, hr, map_zsmul]⟩ }
  have hsT : Submodule.span ℤ (s : Set F) ≤ T := by
    rw [Submodule.span_le]
    intro a ha
    obtain ⟨r, hr⟩ := hb a ha
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  refine ⟨(algebraMap (𝓞 F) F b)⁻¹, inv_ne_zero hB0, fun a ha => ?_⟩
  have has : a ∈ Submodule.span ℤ (s : Set F) := by rw [hs]; exact ha
  obtain ⟨r, hr⟩ := hsT has
  refine ⟨r, ?_⟩
  have hrr : ((r : 𝓞 F) : F) = algebraMap (𝓞 F) F r := by
    rfl
  rw [hrr, ← hr, ← mul_assoc, inv_mul_cancel₀ hB0, one_mul]

private theorem fg_of_addHom_intValued {F : Type} [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F)
    (g : F →+ ℂ) (hg : ∀ a ∈ Λ, ∃ n : ℤ, g a = n) (hne : ∃ w, g w ≠ 0) :
    (Λ.restrictScalars ℤ).FG := by
  classical
  let φ : F →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun y i => g (integralBasis F i * y)
      map_add' := fun y y' => by funext i; simp only [mul_add, map_add (f := _), Pi.add_apply]
      map_smul' := fun n y => by
        funext i; simp only [mul_smul_comm, map_zsmul, RingHom.id_apply, Pi.smul_apply] }
  let ψ : (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ) →ₗ[ℤ]
      (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun z i => (z i : ℂ)
      map_add' := fun z z' => by funext i; simp only [Pi.add_apply, Int.cast_add]
      map_smul' := fun n z => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply, zsmul_eq_mul] }
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    obtain ⟨w, hw⟩ := hne
    exact hw (addHom_eq_zero_of_integralBasis_mul g hy0 (fun i => congrFun hy i) w)
  have hrange : (Λ.restrictScalars ℤ).map φ ≤ LinearMap.range ψ := by
    rintro _ ⟨y, hy, rfl⟩
    have hmem : ∀ i, integralBasis F i * y ∈ Λ := fun i => by
      have h := Λ.smul_mem (RingOfIntegers.basis F i) hy
      rwa [Algebra.smul_def, ← integralBasis_apply] at h
    choose n hn using fun i => hg _ (hmem i)
    exact ⟨n, funext fun i => (hn i).symm⟩
  have hQ : (((Λ.restrictScalars ℤ).map φ).comap ψ).FG := IsNoetherian.noetherian _
  have hmap : (((Λ.restrictScalars ℤ).map φ).comap ψ).map ψ = (Λ.restrictScalars ℤ).map φ := by
    apply le_antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact hz
    · intro x hx
      obtain ⟨z, rfl⟩ := hrange hx
      exact ⟨z, hx, rfl⟩
  have hfg := hQ.map ψ
  rw [hmap] at hfg
  exact Submodule.fg_of_fg_map_injective φ hφ hfg

theorem addIntF_holds : AddIntF := by
  intro F _ _ Λ _ hnp g hg
  by_contra hall
  obtain ⟨c, hc0, hc⟩ := exists_mul_integers_of_fg Λ (fg_of_addHom_intValued Λ g hg (not_forall.mp hall))
  exact hnp c hc0 hc

theorem chInf_of_lift (hL : ChLift) : ChInf :=
  chInf_of hL addIntF_holds

end PI.VolStabSW
end
end

