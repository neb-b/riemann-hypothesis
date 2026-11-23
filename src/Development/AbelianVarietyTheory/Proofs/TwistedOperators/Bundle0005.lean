module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitDetAddMulOfFromBlocksLocalRing
section
open Matrix

namespace GlobalTheory.BlockInvertibleLocal

theorem exists_linearMap_injective_add_comp {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (a c : V →ₗ[k] V) (h : LinearMap.ker a ⊓ LinearMap.ker c = ⊥) :
    ∃ x : V →ₗ[k] V, Function.Injective (a + x ∘ₗ c) := by
  set W := LinearMap.range (c ∘ₗ (LinearMap.ker a).subtype) with hWdef
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl (LinearMap.range a)
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl W
  have hinjK : Function.Injective (c ∘ₗ (LinearMap.ker a).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : (u : V) ∈ LinearMap.ker a ⊓ LinearMap.ker c :=
      Submodule.mem_inf.2 ⟨u.2, by simpa using hu⟩
    rw [h, Submodule.mem_bot] at hu'
    exact Subtype.ext hu'
  have h1 := LinearMap.finrank_range_of_inj hinjK
  have h2 := Submodule.finrank_add_eq_of_isCompl hR
  have h3 := LinearMap.finrank_range_add_finrank_ker a
  have hdim : Module.finrank k W = Module.finrank k R := by rw [hWdef, h1]; omega
  let e : W ≃ₗ[k] R := LinearEquiv.ofFinrankEq W R hdim
  let x : V →ₗ[k] V := LinearMap.ofIsCompl hW (R.subtype ∘ₗ e.toLinearMap) 0
  refine ⟨x, ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.1 (hW.sup_eq_top ▸ Submodule.mem_top : c v ∈ W ⊔ W')
  have hxw : x (c v) = ((e ⟨w, hw⟩ : R) : V) := by
    rw [← hsum, map_add (f := _)]
    have hl := LinearMap.ofIsCompl_left_apply (φ := R.subtype ∘ₗ e.toLinearMap) (ψ := (0 : W' →ₗ[k] V)) hW ⟨w, hw⟩
    have hr := LinearMap.ofIsCompl_right_apply (φ := R.subtype ∘ₗ e.toLinearMap) (ψ := (0 : W' →ₗ[k] V)) hW ⟨w', hw'⟩
    simp only at hl hr
    rw [hl, hr]; simp
  have hv' : a v + ((e ⟨w, hw⟩ : R) : V) = 0 := by
    rw [← hxw]; simpa using hv
  have hav : a v = 0 := by
    refine Submodule.disjoint_def.1 hR.disjoint (a v) (LinearMap.mem_range_self a v) ?_
    rw [eq_neg_of_add_eq_zero_left hv']
    exact R.neg_mem (e ⟨w, hw⟩).2
  have he0 : ((e ⟨w, hw⟩ : R) : V) = 0 := by simpa [hav] using hv'
  have hw0 : w = 0 := by
    have : e ⟨w, hw⟩ = 0 := Subtype.ext he0
    have : (⟨w, hw⟩ : W) = 0 := by simpa using this
    simpa using congrArg Subtype.val this
  have hcvW : c v ∈ W := ⟨⟨v, hav⟩, rfl⟩
  have hcvW' : c v ∈ W' := by rw [← hsum, hw0, zero_add]; exact hw'
  have hcv : c v = 0 := Submodule.disjoint_def.1 hW.disjoint _ hcvW hcvW'
  have hmem : v ∈ LinearMap.ker a ⊓ LinearMap.ker c := Submodule.mem_inf.2 ⟨hav, hcv⟩
  rw [h, Submodule.mem_bot] at hmem
  exact hmem

theorem exists_isUnit_det_add_mul_of_field {k : Type} [Field k] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) k) (h : IsUnit (fromBlocks A B C D).det) :
    ∃ X : Matrix (Fin n) (Fin n) k, IsUnit (A + X * C).det := by
  have hinj : Function.Injective (fromBlocks A B C D).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 h)
  have hker : LinearMap.ker (toLin' A) ⊓ LinearMap.ker (toLin' C) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, toLin'_apply, toLin'_apply] at hv
    have hz : (fromBlocks A B C D) *ᵥ (Sum.elim v 0) = (fromBlocks A B C D) *ᵥ 0 := by
      rw [fromBlocks_mulVec, mulVec_zero]
      ext i <;> cases i <;> simp [hv.1, hv.2]
    have h2 := hinj hz
    rw [Submodule.mem_bot]
    funext i
    exact congrFun h2 (Sum.inl i)
  obtain ⟨x, hx⟩ := exists_linearMap_injective_add_comp _ _ hker
  refine ⟨LinearMap.toMatrix' x, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  convert hx using 1
  funext v
  simp [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]

theorem exists_isUnit_det_add_mul : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  intro O _ _ n A B C D h
  have h' : IsUnit (fromBlocks (A.map (IsLocalRing.residue O)) (B.map (IsLocalRing.residue O))
      (C.map (IsLocalRing.residue O)) (D.map (IsLocalRing.residue O))).det := by
    rw [← fromBlocks_map]
    have := h.map (IsLocalRing.residue O)
    rwa [RingHom.map_det] at this
  obtain ⟨Y, hY⟩ := exists_isUnit_det_add_mul_of_field _ _ _ _ h'
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) O, X.map (IsLocalRing.residue O) = Y :=
    ⟨Y.map (Function.surjInv IsLocalRing.residue_surjective), by
      ext i j; simp [Function.surjInv_eq]⟩
  refine ⟨X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add _), Matrix.map_mul, hX]
  exact hY.ne_zero

end GlobalTheory.BlockInvertibleLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitIntegral
section
open NormedSpace Filter Topology

namespace GlobalTheory.ExponentialIntegralUnits

universe u_1

variable {𝔸 : Type u_1} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasDerivAt_primitive (M : ℝ → 𝔸) (hc : Continuous M) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, M s) (M t) t := by
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem exists_isUnit_integral (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1) :
    ∃ δ : ℝ, IsUnit (∫ s in (0 : ℝ)..δ, M s) := by
  have hd := (hasDerivAt_primitive M hc 0).tendsto_slope_zero
  rw [h0] at hd
  have hev := hd.eventually (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨δ, hδU, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0' : δ ≠ 0 := Set.mem_compl_singleton_iff.1 hδ0
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at hδU
  refine ⟨δ, ?_⟩
  have e : (∫ s in (0 : ℝ)..δ, M s) = algebraMap ℝ 𝔸 δ * (δ⁻¹ • ∫ s in (0 : ℝ)..δ, M s) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ0', one_smul]
  rw [e]
  exact ((isUnit_iff_ne_zero.2 hδ0').map (algebraMap ℝ 𝔸)).mul hδU

theorem mul_integral (M : ℝ → 𝔸) (hc : Continuous M)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) (t δ : ℝ) :
    M t * (∫ s in (0 : ℝ)..δ, M s)
      = (∫ s in (0 : ℝ)..(t + δ), M s) - ∫ s in (0 : ℝ)..t, M s := by
  have hL := ((ContinuousLinearMap.mul ℝ 𝔸) (M t)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
  simp only [ContinuousLinearMap.mul_apply'] at hL
  rw [← hL]
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_left (fun s => M s) t, add_zero,
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _)]

theorem exists_hasDerivAt (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, HasDerivAt M (M t * X) t := by
  obtain ⟨δ, hA⟩ := exists_isUnit_integral M hc h0
  have hAA : (∫ s in (0 : ℝ)..δ, M s) * ↑(hA.unit⁻¹) = 1 := hA.mul_val_inv
  refine ⟨(M δ - 1) * ↑(hA.unit⁻¹), fun t => ?_⟩
  have hM : ∀ u, M u = ((∫ s in (0 : ℝ)..(u + δ), M s) - ∫ s in (0 : ℝ)..u, M s) * ↑(hA.unit⁻¹) := fun u => by
    rw [← mul_integral M hc hadd u δ, mul_assoc, hAA, mul_one]
  have hP : HasDerivAt (fun u => ∫ s in (0 : ℝ)..(u + δ), M s) (M (t + δ)) t := by
    first
      | exact (hasDerivAt_primitive M hc (t + δ)).comp_add_const t δ
      | exact HasDerivAt.comp_add_const t δ (hasDerivAt_primitive M hc (t + δ))
  have hF := (hP.sub (hasDerivAt_primitive M hc t)).mul_const (↑(hA.unit⁻¹) : 𝔸)
  have hF' := hF.congr_of_eventuallyEq (Eventually.of_forall hM)
  refine hF'.congr_deriv ?_
  rw [hadd, ← mul_assoc, mul_sub, mul_one]

theorem exists_exp_eq (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M (0 : ℝ) = (1 : 𝔸))
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, NormedSpace.exp (t • X) = M t := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨X, hX⟩ := exists_hasDerivAt M hc h0 hadd
  refine ⟨X, fun t => ?_⟩
  have hN : ∀ u : ℝ, HasDerivAt (fun v => M v * NormedSpace.exp (v • (-X))) 0 u := fun u => by
    have h3 := (hX u).mul (hasDerivAt_exp_smul_const (-X) u)
    refine h3.congr_deriv ?_
    have hcomm : Commute (NormedSpace.exp (u • (-X))) X :=
      (((Commute.refl X).neg_left).smul_left u).exp_left
    rw [mul_neg, hcomm.eq, mul_neg, ← mul_assoc, add_neg_cancel]
  have hconst : ∀ u, M u * NormedSpace.exp (u • (-X)) = 1 := fun u => by
    have h4 := is_const_of_deriv_eq_zero (fun v => (hN v).differentiableAt) (fun v => (hN v).deriv) u 0
    rw [h4, h0, zero_smul, NormedSpace.exp_zero, one_mul]
  have hinv : NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute ((((Commute.refl X).neg_left).smul_left t).smul_right t), smul_neg,
      neg_add_cancel, NormedSpace.exp_zero]
  calc NormedSpace.exp (t • X) = (M t * NormedSpace.exp (t • (-X))) * NormedSpace.exp (t • X) := by
        rw [hconst t, one_mul]
    _ = M t := by rw [mul_assoc, hinv, mul_one]

end GlobalTheory.ExponentialIntegralUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroIntSmulMemOfIsLattice
section
namespace GlobalTheory.IntSmulMemLatticeTwistedOperators

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a))
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (v : Fin n → E) : ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hcx d
    · rw [mul_smul]; exact zsmul_mem hdy c
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_mul_integral a
    let b : RingOfIntegers E := ⟨(d : E) * a, hint⟩
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    have key : (d * c) • (a • x) = b • (c • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      rw [Algebra.smul_def]
      have hb : algebraMap (RingOfIntegers E) E b = (d : E) * a := rfl
      rw [hb]
      simp
      ring
    rw [key]
    exact L.smul_mem b hcx

theorem exists_nonzero_int_smul_mem_of_isLattice : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : Fin n → E), ∃ (c : ℤ), c ≠ (0 : ℤ) ∧ c • v ∈ L :=
  fun L hL v => exists_int_smul_mem L hL v

end GlobalTheory.IntSmulMemLatticeTwistedOperators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulMemLattice
section
namespace GlobalTheory.NatMultipleInLattice

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * a) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have h1 := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) * a = y • a := by
      rw [zsmul_eq_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1
  · have e : ((y.natAbs : ℕ) : E) * a = -(y • a) := by
      rw [zsmul_eq_mul, ← neg_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1.neg

theorem exists_nsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨F, hF, hz⟩ := hz
    refine ⟨D * F, mul_ne_zero hD hF, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.toAddSubmonoid.nsmul_mem hy F
    · rw [mul_smul]; exact L.toAddSubmonoid.nsmul_mem hz D
  | smul a y _ hy =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨m, hm, hi⟩ := exists_nat_mul_integral a
    refine ⟨m * D, mul_ne_zero hm hD, ?_⟩
    have key := L.smul_mem (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) hy
    have : (m * D) • a • y =
        (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y := by
      have h3 : (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y
          = ((m : E) * a) • D • y := rfl
      rw [h3]
      ext i
      simp only [Pi.smul_apply]
      simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]
      ring
    rw [this]; exact key

end GlobalTheory.NatMultipleInLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothMulExtensionOfContinuousChar
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff

namespace GlobalTheory


open Filter MeasureTheory Topology in
open MeasureTheory Filter Topology in
theorem contDiff_of_continuous_of_map_add_eq_mul {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℂ) (hf : Continuous f)
    (hadd : ∀ x y, f (x + y) = f x * f y) (h0 : f 0 ≠ 0) : ContDiff ℝ ∞ f := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let b : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous (μ := μ) hb hf 0
  obtain ⟨n, hn⟩ := (ht.eventually_ne h0).exists
  have hs : ContDiff ℝ ∞
      (convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ) :=
    HasCompactSupport.contDiff_convolution_left _ (b n).hasCompactSupport_normed
      (b n).contDiff_normed hf.locallyIntegrable
  have key : ∀ x, convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
      = f x * convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ 0 := by
    intro x
    rw [convolution_def, convolution_def, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have : x - t = x + (0 - t) := by abel
    simp only [ContinuousLinearMap.lsmul_apply]
    rw [this, hadd, mul_smul_comm]
  have : f = fun x => convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
      * (convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ 0)⁻¹ := by
    funext x
    rw [key x, mul_inv_cancel_right₀ hn]
  rw [this]
  exact hs.mul contDiff_const

noncomputable def mixedExpUnit (K : Type) [Field K] (y : mixedSpace K) : (mixedSpace K)ˣ :=
  ⟨(fun w => Real.exp (y.1 w), fun w => Complex.exp (y.2 w)),
    (fun w => Real.exp (-y.1 w), fun w => Complex.exp (-y.2 w)),
    Prod.ext (funext fun w => by simp [← Real.exp_add])
      (funext fun w => by simp [← Complex.exp_add]),
    Prod.ext (funext fun w => by simp [← Real.exp_add])
      (funext fun w => by simp [← Complex.exp_add])⟩

theorem mixedExpUnit_add (K : Type) [Field K] (x y : mixedSpace K) :
    mixedExpUnit K (x + y) = mixedExpUnit K x * mixedExpUnit K y :=
  Units.ext (Prod.ext (funext fun w => Real.exp_add (x.1 w) (y.1 w))
    (funext fun w => Complex.exp_add (x.2 w) (y.2 w)))

theorem continuous_mixedExpUnit (K : Type) [Field K] : Continuous (mixedExpUnit K) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun y : mixedSpace K =>
      (((fun w => Real.exp (y.1 w), fun w => Complex.exp (y.2 w))) : mixedSpace K)
    fun_prop
  · show Continuous fun y : mixedSpace K =>
      (((fun w => Real.exp (-y.1 w), fun w => Complex.exp (-y.2 w))) : mixedSpace K)
    fun_prop

noncomputable def mixedLog (K : Type) [Field K] (x : mixedSpace K) : mixedSpace K :=
  (fun w => Real.log (x.1 w), fun w => Complex.log (x.2 w))

theorem contDiffAt_mixedLog_one (K : Type) [Field K] [NumberField K] :
    ContDiffAt ℝ ∞ (mixedLog K) 1 := by
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun w => ?_) (contDiffAt_pi.mpr fun w => ?_)
  · have h1 : ContDiff ℝ ∞ (fun x : mixedSpace K => x.1 w) :=
      (contDiff_apply ℝ (fun _ => ℝ) w).comp contDiff_fst
    exact h1.contDiffAt.log (by simp)
  · have h1 : ContDiff ℝ ∞ (fun x : mixedSpace K => x.2 w) :=
      (contDiff_apply ℝ (fun _ => ℂ) w).comp contDiff_snd
    have h2 : ContDiffAt ℝ ∞ Complex.log ((1 : mixedSpace K).2 w) :=
      (Complex.contDiffAt_log (by simp)).restrict_scalars ℝ
    exact h2.comp 1 h1.contDiffAt

open Filter Topology in
theorem eventually_mixedExpUnit_mixedLog (K : Type) [Field K] [NumberField K] :
    ∀ᶠ x in 𝓝 (1 : mixedSpace K), (mixedExpUnit K (mixedLog K x) : mixedSpace K) = x := by
  have h1 : ∀ᶠ x in 𝓝 (1 : mixedSpace K), ∀ w, 0 < x.1 w := by
    refine eventually_all.mpr fun w => ?_
    have hc : Continuous (fun x : mixedSpace K => x.1 w) := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simp))
  have h2 : ∀ᶠ x in 𝓝 (1 : mixedSpace K), ∀ w, x.2 w ≠ 0 := by
    refine eventually_all.mpr fun w => ?_
    have hc : Continuous (fun x : mixedSpace K => x.2 w) := by fun_prop
    exact hc.continuousAt.eventually_ne (by simp)
  filter_upwards [h1, h2] with x hx1 hx2
  exact Prod.ext (funext fun w => Real.exp_log (hx1 w)) (funext fun w => Complex.exp_log (hx2 w))

theorem mixedSpace_norm_ne_zero_iff_isUnit (K : Type) [Field K] [NumberField K]
    (x : mixedSpace K) : mixedEmbedding.norm x ≠ 0 ↔ IsUnit x := by
  rw [mixedEmbedding.norm_ne_zero_iff, Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  constructor
  · intro h
    refine ⟨fun w => ?_, fun w => ?_⟩
    · have := h w.1
      rw [normAtPlace_apply_of_isReal w.2] at this
      exact (norm_ne_zero_iff.mp this).isUnit
    · have := h w.1
      rw [normAtPlace_apply_of_isComplex w.2] at this
      exact (norm_ne_zero_iff.mp this).isUnit
  · rintro ⟨h1, h2⟩ w
    rcases w.isReal_or_isComplex with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]
      exact norm_ne_zero_iff.mpr (h1 _).ne_zero
    · rw [normAtPlace_apply_of_isComplex hw]
      exact norm_ne_zero_iff.mpr (h2 _).ne_zero

theorem exists_smooth_mul_extension_of_continuous_char :
    ∀ (K : Type) [Field K] [NumberField K] (ψ : (mixedSpace K)ˣ →* ℂˣ), Continuous ψ → ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ u : (mixedSpace K)ˣ, φ u = (ψ u : ℂ)) ∧ ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 ↔ IsUnit x := by
  intro K _ _ ψ hψ
  let φ : mixedSpace K → ℂ := fun x => if h : IsUnit x then (ψ h.unit : ℂ) else 0
  have hu : ∀ u : (mixedSpace K)ˣ, φ u = (ψ u : ℂ) := by
    intro u
    simp only [φ, dif_pos u.isUnit, IsUnit.unit_of_val_units]
  have hn : ∀ x, ¬ IsUnit x → φ x = 0 := fun x hx => dif_neg hx
  have hmul : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    by_cases hx : IsUnit x
    · by_cases hy : IsUnit y
      · obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        rw [← Units.val_mul, hu, hu, hu, map_mul, Units.val_mul]
      · rw [hn y hy, hn _ (fun h => hy (isUnit_of_mul_isUnit_right h)), mul_zero]
    · rw [hn x hx, hn _ (fun h => hx (isUnit_of_mul_isUnit_left h)), zero_mul]
  have hf : ContDiff ℝ ∞ (fun y => (ψ (mixedExpUnit K y) : ℂ)) :=
    contDiff_of_continuous_of_map_add_eq_mul _
      (Units.continuous_val.comp (hψ.comp (continuous_mixedExpUnit K)))
      (fun x y => by rw [mixedExpUnit_add, map_mul, Units.val_mul]) (Units.ne_zero _)
  have h1 : ContDiffAt ℝ ∞ φ 1 := by
    refine (hf.contDiffAt.comp 1 (contDiffAt_mixedLog_one K)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_mixedExpUnit_mixedLog K] with x hx
    rw [Function.comp_apply, ← hu, hx]
  refine ⟨φ, hmul, fun x hx => ?_, hu, mixedSpace_norm_ne_zero_iff_isUnit K⟩
  obtain ⟨u, rfl⟩ := (mixedSpace_norm_ne_zero_iff_isUnit K x).mp hx
  have h2 : φ = fun z => φ u * φ ((u⁻¹ : (mixedSpace K)ˣ) * z) := by
    funext z
    rw [← hmul, Units.mul_inv_cancel_left]
  have h3 : ContDiffAt ℝ ∞ φ (((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K) * u) := by
    rw [Units.inv_mul]
    exact h1
  have h4 : ContDiffAt ℝ ∞
      (fun z : mixedSpace K => φ u * φ ((u⁻¹ : (mixedSpace K)ˣ) * z)) (u : mixedSpace K) :=
    contDiffAt_const.mul (h3.comp (u : mixedSpace K)
      (f := fun z : mixedSpace K => ((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K) * z)
      (contDiffAt_const.mul contDiffAt_id))
  rw [← h2] at h4
  exact h4.contDiffWithinAt

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumEqSumOfMatchingFamily
section
open Finset

namespace GlobalTheory

theorem hasSum_eq_sum_of_matching_family : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by
  intro C n m t m' c R s hs h1 h2 h3 h4 h5
  classical
  set P : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => m' i ≠ 0) with hPdef
  let g : P → C := fun i => Classical.choose (h2 i.1 (Finset.mem_filter.1 i.2).2)
  have hg : ∀ i : P, R (g i) i.1 := fun i => Classical.choose_spec (h2 i.1 (Finset.mem_filter.1 i.2).2)
  have ginj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    have hj := hg j
    rw [← hij] at hj
    exact h4 _ _ _ (hg i) hj
  have hT : ∀ x ∉ (Finset.univ.image g), (m x : ℂ) * t x = 0 := by
    intro x hx
    by_contra hne
    have hm : m x ≠ 0 := by intro h; apply hne; simp [h]
    have ht : t x ≠ 0 := by intro h; apply hne; simp [h]
    obtain ⟨i, hi⟩ := h1 x hm ht
    have hmi : m' i ≠ 0 := by rw [← (h3 x i hi).1]; exact hm
    have hiP : i ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ _, hmi⟩
    apply hx
    rw [Finset.mem_image]
    exact ⟨⟨i, hiP⟩, Finset.mem_univ _, h5 _ _ _ (hg ⟨i, hiP⟩) hi⟩
  have hs2 : HasSum (fun x => (m x : ℂ) * t x) (∑ x ∈ Finset.univ.image g, (m x : ℂ) * t x) := hasSum_sum_of_ne_finset_zero hT
  rw [hs.unique hs2, Finset.sum_image (fun i _ j _ h => ginj h)]
  rw [← Finset.sum_filter_of_ne (p := fun i => m' i ≠ 0) (fun i _ hne => by intro h; apply hne; simp [h])]
  rw [← hPdef, ← Finset.sum_attach P (fun i => (m' i : ℂ) * c i), Finset.univ_eq_attach]
  apply Finset.sum_congr rfl
  intro i _
  rw [(h3 _ _ (hg i)).1, (h3 _ _ (hg i)).2]

end GlobalTheory
end

