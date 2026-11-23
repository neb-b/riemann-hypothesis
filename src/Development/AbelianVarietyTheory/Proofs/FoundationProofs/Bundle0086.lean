module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatio
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory

open TensorProduct

theorem tensor_padic_cls_eq {G : Type} [CommGroup G] (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : G)
    (h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul f' - (1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul f) ∈
      ((Ideal.span {(l : ℤ_[l])}) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] Additive G)))) :
    ∃ u : G, f' = f * u ^ (l ^ n) := by
  classical
  let M := Additive G
  let ψ : M →ₗ[ℤ] M := {
    toFun := fun x : M => (((l : ℤ) ^ n) • x)
    map_add' := fun x y => by simp
    map_smul' := fun (k : ℤ) x => by simp [smul_smul, mul_comm]
  }
  let P : Submodule ℤ M := LinearMap.range ψ
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hkill : ∀ q : M ⧸ P, (l ^ n) • q = 0 := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨m, by change ((l : ℤ) ^ n) • m = l ^ n • m; rw [← Nat.cast_pow, natCast_zsmul]⟩
  letI : Module (ZMod (l ^ n)) (M ⧸ P) := AddCommGroup.zmodModule hkill
  let B : ℤ_[l] →ₗ[ℤ] M →ₗ[ℤ] M ⧸ P :=
    LinearMap.mk₂ ℤ (fun c m => (PadicInt.toZModPow n c) • P.mkQ m)
      (fun c c' m => by simp [add_smul])
      (fun k c m => by
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)), ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)),
          smul_smul, smul_eq_mul])
      (fun c m m' => by simp [smul_add])
      (fun k c m => by
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)), ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)),
          smul_smul, smul_smul, mul_comm])
  let φ : ℤ_[l] ⊗[ℤ] M →ₗ[ℤ] M ⧸ P := TensorProduct.lift B
  have hφ : ∀ c m, φ (c ⊗ₜ m) = (PadicInt.toZModPow n c) • P.mkQ m := fun c m => by
    exact TensorProduct.lift.tmul (f' := B) c m
  have hI : (Ideal.span {(l : ℤ_[l])}) ^ n = RingHom.ker (PadicInt.toZModPow (p := l) n) := by
    rw [PadicInt.ker_toZModPow, Ideal.span_singleton_pow]
  have hzero : ∀ x ∈ ((Ideal.span {(l : ℤ_[l])}) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] M))), φ x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
    rw [hI, RingHom.mem_ker] at hr
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hφ, map_mul, hr, zero_mul, zero_smul]
    | add a b ha hb => rw [smul_add, map_add (f := _), ha, hb, add_zero]
  have h0 := hzero _ h
  rw [map_sub, hφ, hφ, map_one, one_smul, one_smul, sub_eq_zero, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq] at h0
  obtain ⟨y, hy⟩ := h0
  refine ⟨Additive.toMul y, ?_⟩
  have hy' : Additive.toMul (((l : ℤ) ^ n) • y) = f' / f := by
    have hy2 : ((l : ℤ) ^ n) • y = Additive.ofMul f' - Additive.ofMul f := hy
    rw [hy2]; rfl
  rw [toMul_zsmul] at hy'
  rw [← div_eq_iff_eq_mul', ← hy']
  norm_cast

theorem Tower.cls_eq_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (f f' : X.Kˣ) (h : X.cls l n f = X.cls l n f') :
    ∃ u : X.Kˣ, (f' : X.K) = f * (u : X.K) ^ (l ^ n) := by
  unfold Tower.cls at h
  rw [Submodule.Quotient.eq'] at h
  obtain ⟨u, hu⟩ := tensor_padic_cls_eq l n f f' (by simpa [neg_add_eq_sub] using h)
  exact ⟨u, by rw [hu]; push_cast; rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionSlTwoIntInvariant
section
open scoped MatrixGroups
open GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.InvFun

open Filter Topology

theorem mob_ofSL_den_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) :
    (ent (ofSL γ) 1 0 : ℂ) * z + (ent (ofSL γ) 1 1 : ℂ) ≠ 0 := by
  have hz' : 0 < z.im := hz
  have e10 : (ent (ofSL γ) 1 0 : ℂ) = ((γ 1 0 : ℤ) : ℂ) := by simp [ent, ofSL]
  have e11 : (ent (ofSL γ) 1 1 : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by simp [ent, ofSL]
  rw [e10, e11]
  intro h0
  have him := congrArg Complex.im h0
  simp at him
  rcases him with hc | hc
  · have hre := congrArg Complex.re h0
    simp [hc] at hre
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    rw [hc, hre] at hdet
    simp at hdet
  · exact absurd hc hz'.ne'

theorem continuousAt_mob_ofSL (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : ContinuousAt (mob (ofSL γ)) z := by
  unfold mob
  exact ((continuous_const.mul continuous_id).add continuous_const).continuousAt.div
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt (mob_ofSL_den_ne_zero γ hz)

theorem mob_ofSL_mem (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : mob (ofSL γ) z ∈ Hs := by
  have := SiegelModel.mob_ofSL γ ⟨z, hz⟩
  show 0 < (mob (ofSL γ) z).im
  have e : ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) = z := rfl
  rw [e] at this
  rw [this]
  exact (γ • (⟨z, hz⟩ : UpperHalfPlane)).im_pos

theorem fun_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ) :
    ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z := by
  intro hφ han hinv γ z hz
  have e := X.an_sl (ofSL γ) h φ han
  rw [hinv γ, han, Filter.Germ.coe_eq] at e
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 e) z hz
  have h2 : Hs ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds (SiegelModel.isOpen_Hs.mem_nhds hz)
  have hev : (fun w => φ (mob (ofSL γ) w)) =ᶠ[𝓝[≠] z] φ := by
    filter_upwards [h1, h2] with w hw1 hw2
    rcases hw1 with hw | hw
    · exact hw.symm
    · exact absurd hw2 hw
  have hc1 : ContinuousAt φ z := hφ.continuousAt (SiegelModel.isOpen_Hs.mem_nhds hz)
  have hc2 : ContinuousAt (fun w => φ (mob (ofSL γ) w)) z :=
    ContinuousAt.comp (f := mob (ofSL γ)) (g := φ)
      (hφ.continuousAt (SiegelModel.isOpen_Hs.mem_nhds (mob_ofSL_mem γ hz))) (continuousAt_mob_ofSL γ hz)
  have t1 : Tendsto (fun w => φ (mob (ofSL γ) w)) (𝓝[≠] z) (𝓝 (φ (mob (ofSL γ) z))) :=
    hc2.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun w => φ (mob (ofSL γ) w)) (𝓝[≠] z) (𝓝 (φ z)) :=
    (hc1.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  exact tendsto_nhds_unique t1 t2

end GlobalTheory.KZ.InvFun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionTendstoConstTermExponential
section
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.KZ.ExpBound

theorem series_bound (a : ℕ → ℂ) (ψ : ℂ → ℂ) (C : ℝ)
    (hs : ∀ z : ℂ, C < z.im →
      HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (ψ z)) :
    ∃ B t : ℝ, ∀ w : ℂ, t < w.im → ‖ψ w - a 0‖ ≤ B * Real.exp (-(2 * Real.pi * (w.im - t))) := by
  have hnorm : ∀ (n : ℕ) (z : ℂ), ‖a n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)‖ =
      ‖a n‖ * Real.exp (-(2 * Real.pi * n * z.im)) := by
    intro n z
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, Complex.mul_im]
  set t0 : ℝ := C + 1 with ht0
  have hz0 : ((t0 : ℂ) * Complex.I).im = t0 := by simp
  have hsm : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0))) := by
    have h1 := (hs ((t0 : ℂ) * Complex.I) (by rw [hz0]; linarith)).summable
    have h2 := summable_norm_iff.mpr h1
    simpa only [hnorm, hz0] using h2
  set B0 : ℝ := ∑' n : ℕ, ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0)) with hB0
  have hle : ∀ n : ℕ, ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0)) ≤ B0 := fun n =>
    hsm.le_tsum n (fun j _ => by positivity)
  have hB0nn : 0 ≤ B0 := tsum_nonneg (fun j => by positivity)
  refine ⟨2 * B0, t0 + 1, fun w hw => ?_⟩
  set ρ : ℝ := Real.exp (-(2 * Real.pi * (w.im - t0))) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hpi := Real.pi_gt_three
  have hρ2 : ρ ≤ 1 / 2 := by
    have h1 : 1 ≤ 2 * Real.pi * (w.im - t0) := by nlinarith
    have h2 := Real.add_one_le_exp (2 * Real.pi * (w.im - t0))
    rw [hρ, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hsh := (hasSum_nat_add_iff' 1).mpr (hs w (by linarith))
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at hsh
  have hg : HasSum (fun n : ℕ => B0 * ρ * ρ ^ n) (B0 * ρ * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0.le (by linarith)).mul_left _
  have hb := tsum_of_norm_bounded hg (f := fun n : ℕ =>
      a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * w)) (fun n => by
    rw [hnorm]
    have e : Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * w.im)) =
        Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t0)) * ρ ^ (n + 1) := by
      rw [hρ, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [e, ← mul_assoc, mul_assoc B0, ← pow_succ']
    exact mul_le_mul_of_nonneg_right (hle (n + 1)) (by positivity))
  rw [hsh.tsum_eq] at hb
  have h3 : B0 * ρ * (1 - ρ)⁻¹ ≤ 2 * B0 * ρ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hB0nn hρ0.le) (show 0 ≤ 1 - 2 * ρ by linarith)]
  have h4 : ρ ≤ Real.exp (-(2 * Real.pi * (w.im - (t0 + 1)))) := by
    rw [hρ]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc ‖ψ w - a 0‖ ≤ B0 * ρ * (1 - ρ)⁻¹ := hb
    _ ≤ 2 * B0 * ρ := h3
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem bound_at_infinity : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n) → ∃ B t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z - ε ((X.exp h).coeff 0)‖ ≤ B * Real.exp (-(2 * Real.pi * (z.im - t))) := by
  intro Ω _ _ ε X h φ hφc hφ hsupp
  obtain ⟨φ', C, hφ', hsum⟩ := X.an_exp h
  have hsumN : ∀ z : ℂ, C < z.im → HasSum (fun n : ℕ => ε ((X.exp h).coeff (n : ℚ)) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (φ' z) := by
    intro z hz
    have h1 := hsum z hz
    rw [← (Nat.cast_injective (R := ℚ)).hasSum_iff] at h1
    · simpa [Function.comp_def] using h1
    · intro r hr
      have : (X.exp h).coeff r = 0 := by
        by_contra hne
        obtain ⟨n, rfl⟩ := hsupp r hne
        exact hr ⟨n, rfl⟩
      simp [this]
  obtain ⟨B, t, hB⟩ := series_bound (fun n : ℕ => ε ((X.exp h).coeff (n : ℚ))) φ' C hsumN
  simp only [Nat.cast_zero] at hB
  refine ⟨B, t, fun z hz htz => ?_⟩
  have hev : φ =ᶠ[Filter.codiscreteWithin Hs] φ' := Filter.Germ.coe_eq.mp (hφ.symm.trans hφ')
  have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hev z hz
  have hHs : Hs ∈ nhds z := SiegelModel.isOpen_Hs.mem_nhds hz
  have h2 : Hs ∈ nhdsWithin z {z}ᶜ := mem_nhdsWithin_of_mem_nhds hHs
  have h3 : {w : ℂ | t < w.im} ∈ nhdsWithin z {z}ᶜ :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds htz)
  have hl : Filter.Tendsto (fun w => ‖φ w - ε ((X.exp h).coeff 0)‖) (nhdsWithin z {z}ᶜ)
      (nhds ‖φ z - ε ((X.exp h).coeff 0)‖) :=
    (((hφc.continuousAt hHs).sub continuousAt_const).norm.tendsto).mono_left nhdsWithin_le_nhds
  have hc : Continuous fun w : ℂ => B * Real.exp (-(2 * Real.pi * (w.im - t))) := by fun_prop
  refine le_of_tendsto_of_tendsto hl ((hc.tendsto z).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  rcases hw1 with e | e
  · have e' : φ w = φ' w := e
    rw [e']
    exact hB w hw3
  · exact absurd hw2 e

end GlobalTheory.KZ.ExpBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariant
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.TInv

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

theorem const_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {L : ℕ} (hL : 0 < L) {x : X.K} (hx : x ^ L = 1) : ∃ c : Ω, algebraMap Ω X.K c = x := by
  have hint : IsIntegral Ω x := IsIntegral.of_pow hL (by rw [hx]; exact isIntegral_one)
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one (hx := hdeg))
  exact ⟨c, hc⟩

theorem cast_eq_of_dvd {d : ℕ} {y c : ℤ} (h : (d : ℤ) ∣ y - c) : (y : ZMod d) = (c : ZMod d) := ((ZMod.intCast_eq_intCast_iff_dvd_sub c y d).mpr h).symm

theorem exists_sl2_scalar_mod_coprime (A₁ A₂ : ℕ) (hcop : Nat.Coprime A₁ A₂) :
    ∃ δ : SL(2, ℤ), (A₁ : ℤ) ∣ δ 0 0 - 1 ∧ (A₁ : ℤ) ∣ δ 1 1 - 1 ∧ ((A₁ : ℤ) * A₂) ∣ δ 1 0 ∧
      ((A₁ : ℤ) * A₂) ∣ δ 0 1 ∧ (A₂ : ℤ) ∣ δ 0 0 + 1 ∧ (A₂ : ℤ) ∣ δ 1 1 + 1 ∧ ((A₁ : ℤ) * A₂) ∣ δ 0 0 - δ 1 1 := by
  obtain ⟨u, v, huv⟩ : IsCoprime ((A₁ : ℤ) ^ 2) ((A₂ : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow
  refine ⟨⟨!![v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2, (A₁ : ℤ) * A₂;
      -4 * u * v * ((A₁ : ℤ) * A₂), v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination (u * (A₁ : ℤ) ^ 2 + v * (A₂ : ℤ) ^ 2 + 1) * huv
  · exact ⟨-2 * u * A₁, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - 1 = _
      linear_combination huv⟩
  · exact ⟨-2 * u * A₁, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - 1 = _
      linear_combination huv⟩
  · exact ⟨-4 * u * v, by
      show -4 * u * v * ((A₁ : ℤ) * A₂) = _
      ring⟩
  · exact ⟨1, by
      show (A₁ : ℤ) * A₂ = _
      ring⟩
  · exact ⟨2 * v * A₂, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 + 1 = _
      linear_combination (-1 : ℤ) * huv⟩
  · exact ⟨2 * v * A₂, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 + 1 = _
      linear_combination (-1 : ℤ) * huv⟩
  · exact ⟨0, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - (v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2) = _
      ring⟩

private lemma t_inv_mul_mul_t_mul_inv_mem_gamma {M : ℕ} (δ : SL(2, ℤ)) (hc : (M : ℤ) ∣ δ 1 0) (had : (M : ℤ) ∣ δ 0 0 - δ 1 1) :
    ModularGroup.T⁻¹ * δ * ModularGroup.T * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  have hc' : ((δ 1 0 : ℤ) : ZMod M) = 0 := by
    simpa using cast_eq_of_dvd (d := M) (c := 0) (by simpa using hc)
  have had' : ((δ 0 0 : ℤ) : ZMod M) = ((δ 1 1 : ℤ) : ZMod M) := cast_eq_of_dvd had
  rw [CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
    mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, hc', had'] <;> ring

theorem exists_delta (N M l n : ℕ) (hl : l.Prime) (hlN : ¬ l ∣ N) (hN : 1 ≤ N) (hM : 0 < M) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma1 N ∧ -δ ∈ CongruenceSubgroup.Gamma (l ^ n) ∧
      ModularGroup.T⁻¹ * δ * ModularGroup.T * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  obtain ⟨e, m, hlm, hM'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.one_lt.ne'
  have hcl : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlm
  have hcN : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlN
  have hcop : Nat.Coprime (N * m) (l ^ (n + e)) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.mul_left hcN.symm hcl.symm)
  obtain ⟨δ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_sl2_scalar_mod_coprime (N * m) (l ^ (n + e)) hcop
  have hN1 : (N : ℤ) ∣ ((N * m : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr (Dvd.intro m rfl)
  have hln : ((l ^ n : ℕ) : ℤ) ∣ ((l ^ (n + e) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (pow_dvd_pow l (Nat.le_add_right n e))
  have hln' : ((l ^ n : ℕ) : ℤ) ∣ ((N * m : ℕ) : ℤ) * ((l ^ (n + e) : ℕ) : ℤ) := Dvd.dvd.mul_left hln _
  have hMd : (M : ℤ) ∣ ((N * m : ℕ) : ℤ) * ((l ^ (n + e) : ℕ) : ℤ) := by
    have : M ∣ (N * m) * l ^ (n + e) := by
      rw [hM']
      exact ⟨N * l ^ n, by ring⟩
    exact_mod_cast this
  refine ⟨δ, ?_, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · simpa using cast_eq_of_dvd (d := N) (dvd_trans hN1 h1)
    · simpa using cast_eq_of_dvd (d := N) (dvd_trans hN1 h2)
    · simpa using cast_eq_of_dvd (d := N) (c := 0) (by rw [sub_zero]; exact dvd_trans (hN1.mul_right _) h3)
  · rw [CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 0 0) (c := 1) (by rw [← neg_add']; exact (dvd_trans hln h5).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 0 1) (c := 0) (by rw [sub_zero]; exact (dvd_trans hln' h4).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 1 0) (c := 0) (by rw [sub_zero]; exact (dvd_trans hln' h3).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 1 1) (c := 1) (by rw [← neg_add']; exact (dvd_trans hln h6).neg_right)
  · exact t_inv_mul_mul_t_mul_inv_mem_gamma δ (dvd_trans hMd h3) (dvd_trans hMd h7)

private lemma sl_eq_self_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {L : ℕ} (hL : 0 < L) {x : X.K} (hx : x ^ L = 1) (g : GQ) : X.sl g x = x := by
  obtain ⟨c, rfl⟩ := const_of_pow_eq_one X hL hx
  exact (X.sl g).commutes c

theorem sl_T_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hN : 1 ≤ N) (u : X.K) (hu : u ≠ 0)
    (hinv : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)))
    (hδ : ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) :
    X.sl (ofSL ModularGroup.T) u = u := by
  have hL : 0 < l ^ n := pow_pos hl.pos n
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (N * l ^ n) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  have huL : u ^ (l ^ n) ≠ 0 := pow_ne_zero _ hu
  obtain ⟨ζ, hTu⟩ : ∃ ζ : X.K, X.sl (ofSL ModularGroup.T) u = ζ * u :=
    ⟨X.sl (ofSL ModularGroup.T) u / u, (div_mul_cancel₀ _ hu).symm⟩
  have hζL : ζ ^ (l ^ n) = 1 := by
    have h1 : X.sl (ofSL ModularGroup.T) (u ^ (l ^ n)) = u ^ (l ^ n) := hinv _ hT
    rw [map_pow, hTu, mul_pow] at h1
    exact mul_right_cancel₀ huL (h1.trans (one_mul _).symm)
  have hζfix : ∀ h : GQ, X.sl h ζ = ζ := fun h => sl_eq_self_of_pow_eq_one X hL hζL h
  obtain ⟨M, hM, hMu⟩ := X.level u
  obtain ⟨δ, hδ1, hδl, hδM⟩ := exists_delta N M l n hl hlN hN hM
  obtain ⟨g, hg, hgL⟩ := hδ δ hδ1 hδl
  have hsu : X.sl (ofSL δ) u ≠ 0 := fun h =>
    hu ((X.sl (ofSL δ)).injective (h.trans (map_zero _).symm))
  have hP0 : u * X.sl (ofSL δ) u ≠ 0 := mul_ne_zero hu hsu
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hL.ne'] at hgL
    exact hP0 ((pow_eq_zero_iff hL.ne').mp hgL)
  have hw : (u * X.sl (ofSL δ) u / g) ^ (l ^ n) = 1 := by
    rw [div_pow, hgL, div_self (pow_ne_zero _ hg0)]
  have hTP : X.sl (ofSL ModularGroup.T) (u * X.sl (ofSL δ) u) = u * X.sl (ofSL δ) u := by
    rw [← div_mul_cancel₀ (u * X.sl (ofSL δ) u) hg0, map_mul, sl_eq_self_of_pow_eq_one X hL hw, hg _ hT]
  obtain ⟨γ, hγ, hγeq⟩ : ∃ γ ∈ CongruenceSubgroup.Gamma M,
      δ * ModularGroup.T = ModularGroup.T * γ * δ := ⟨_, hδM, by group⟩
  have hTδ : X.sl (ofSL ModularGroup.T) (X.sl (ofSL δ) u) = ζ * X.sl (ofSL δ) u := by
    rw [← X.sl_mul, ← map_mul ofSL δ ModularGroup.T, hγeq, map_mul, map_mul, X.sl_mul, X.sl_mul, hTu,
      map_mul (X.sl (ofSL γ)), hζfix, hMu γ hγ, map_mul (X.sl (ofSL δ)), hζfix]
  have hsq : ζ ^ 2 = 1 := by
    have h := hTP
    rw [map_mul, hTu, hTδ] at h
    have h2 : ζ ^ 2 * (u * X.sl (ofSL δ) u) = 1 * (u * X.sl (ofSL δ) u) := by
      linear_combination h
    exact mul_right_cancel₀ hP0 h2
  have hodd : Odd (l ^ n) := (hl.odd_of_ne_two hl2).pow
  obtain ⟨k, hk⟩ := hodd
  have hζ1 : ζ = 1 := by
    have h3 : ζ ^ (l ^ n) = ζ := by rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [← h3, hζL]
  rw [hTu, hζ1, one_mul]

end GlobalTheory.TInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialEqOfUpperUnipotentDoubleCoset
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem perm_apply_eq_of_le {N : ℕ} (τ : Equiv.Perm (Fin N)) (h : ∀ b, τ b ≤ b) (b : Fin N) : τ b = b := by
  have hs : ∑ i : Fin N, (τ i : ℕ) = ∑ i : Fin N, (i : ℕ) := Equiv.sum_comp τ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin N => (τ i : ℕ))
    (g := fun i : Fin N => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)
  exact Fin.ext this

theorem monomial_eq_of_unipotent_double_coset : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (w w' u u' : GG g N), (∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) → (∃ σ : Equiv.Perm (Fin N), ∀ a b, w'.val a b ≠ 0 → a = σ b) → IsUp g N u → IsUp g N u' → u * w = w' * u' → w = w' := by
  intro g _ N w w' u u' ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hu hu' h
  have hz : ∀ a b, a ≠ σ b → w.val a b = 0 := fun a b hab => by
    by_contra hne; exact hab (hσ a b hne)
  have hz' : ∀ a b, a ≠ σ' b → w'.val a b = 0 := fun a b hab => by
    by_contra hne; exact hab (hσ' a b hne)
  have hne : ∀ b, w.val (σ b) b ≠ 0 := by
    intro b h0
    have h1 : ((w⁻¹).val * w.val) b b = 1 := by
      rw [Units.inv_mul, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : k = σ b
      · rw [hk, h0, mul_zero]
      · rw [hz k b hk, mul_zero]
  have key : ∀ b, w.val (σ b) b = w'.val (σ b) (σ'.symm (σ b)) * u'.val (σ'.symm (σ b)) b := by
    intro b
    have h1 : (u.val * w.val) (σ b) b = (w'.val * u'.val) (σ b) b := by
      rw [← Units.val_mul, ← Units.val_mul, h]
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ b),
      Finset.sum_eq_single (σ'.symm (σ b)), hu.1, one_mul] at h1
    · exact h1
    · intro k _ hk
      rw [hz' (σ b) k, zero_mul]
      intro hh
      apply hk
      rw [hh, Equiv.symm_apply_apply]
    · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro k _ hk
      rw [hz k b hk, mul_zero]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have hle : ∀ b, (σ.trans σ'.symm) b ≤ b := by
    intro b
    by_contra hlt
    have hlt' : b < σ'.symm (σ b) := not_le.1 hlt
    apply hne b
    rw [key b, hu'.2 _ _ hlt', mul_zero]
  have hfix : ∀ b, σ'.symm (σ b) = b := fun b => perm_apply_eq_of_le _ hle b
  have hσσ : ∀ b, σ b = σ' b := fun b => by
    have := congrArg σ' (hfix b)
    rwa [Equiv.apply_symm_apply] at this
  apply Units.ext
  ext a b
  by_cases hab : a = σ b
  · rw [hab, key b, hfix b, hu'.1, mul_one]
  · rw [hz a b hab, hz' a b (by rwa [← hσσ])]

end GlobalTheory.BadShare
end

