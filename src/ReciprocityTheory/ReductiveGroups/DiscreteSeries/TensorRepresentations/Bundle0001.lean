module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefAInnerEqZero
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

section Spec

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

theorem coefA_decomp {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {F : Submodule ℂ X} (hFd : FiniteDimensional ℂ F) (hF : ∀ x ∈ F, T x ∈ F) {y : X} (hy : y ∈ F) :
    ∃ m : ℕ, ∃ b : Fin m → X, ∃ θ : Fin m → ℝ, y = ∑ i, b i ∧
      ∀ i, b i ∈ F ∧ T (b i) = (θ i : ℂ) • b i := by
  haveI := hFd
  have hS : (T.restrict hF).IsSymmetric :=
    LinearMap.IsSymmetric.restrict_invariant (show T.IsSymmetric from hT) hF
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ F = n := ⟨_, rfl⟩
  refine ⟨n, fun i => ((inner ℂ (hS.eigenvectorBasis hn i) (⟨y, hy⟩ : F) •
      hS.eigenvectorBasis hn i : F) : X), fun i => hS.eigenvalues hn i, ?_, ?_⟩
  · have h2 := congrArg (fun z : F => (z : X)) ((hS.eigenvectorBasis hn).sum_repr' (⟨y, hy⟩ : F))
    simp only [Submodule.coe_sum] at h2
    exact h2.symm
  · intro i
    refine ⟨Submodule.coe_mem _, ?_⟩
    have hev : T ((hS.eigenvectorBasis hn i : F) : X) =
        (hS.eigenvalues hn i : ℂ) • ((hS.eigenvectorBasis hn i : F) : X) := by
      have h3 := congrArg (fun z : F => (z : X)) (hS.apply_eigenvectorBasis hn i)
      simp only [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h3
      exact h3
    beta_reduce
    rw [Submodule.coe_smul, map_smul, hev, smul_comm]

theorem coefA_inner_eq_zero {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {u v : X} {α β : ℝ} (hu : T u = (α : ℂ) • u) (hv : T v = (β : ℂ) • v) (hne : α ≠ β) :
    inner ℂ u v = 0 := by
  have h := hT u v
  rw [hu, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have hne' : (α : ℂ) - β ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have h0 : ((α : ℂ) - β) * inner ℂ u v = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left hne'

end Spec

section Rep

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

def CoefLocFin (T : X →ₗ[ℂ] X) (M' : Submodule ℂ X) : Prop :=
  ∀ y ∈ M', ∃ F : Submodule ℂ X, FiniteDimensional ℂ F ∧ F ≤ M' ∧ (∀ x ∈ F, T x ∈ F) ∧ y ∈ F

theorem coefA_decompM {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') {y : X} (hy : y ∈ M') :
    ∃ m : ℕ, ∃ b : Fin m → X, ∃ θ : Fin m → ℝ, y = ∑ i, b i ∧
      ∀ i, b i ∈ M' ∧ T (b i) = (θ i : ℂ) • b i := by
  obtain ⟨F, hFd, hFM, hF, hyF⟩ := hloc y hy
  obtain ⟨m, b, θ, hsum, hb⟩ := coefA_decomp hT hFd hF hyF
  exact ⟨m, b, θ, hsum, fun i => ⟨hFM (hb i).1, (hb i).2⟩⟩

private theorem exists_mem_inner_eq_functional_of_finiteDim {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (L : Submodule ℂ Z) [FiniteDimensional ℂ L] (ψ : Z →ₗ[ℂ] ℂ) :
    ∃ f ∈ L, ∀ w ∈ L, inner ℂ f w = ψ w := by
  haveI : CompleteSpace L := FiniteDimensional.complete ℂ L
  refine ⟨(((InnerProductSpace.toDual ℂ L).symm
      (LinearMap.toContinuousLinearMap (ψ.comp L.subtype)) : L) : Z), Submodule.coe_mem _,
      fun w hw => ?_⟩
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := L) (x := ⟨w, hw⟩)
    (y := LinearMap.toContinuousLinearMap (ψ.comp L.subtype))
  rw [Submodule.coe_inner] at h
  simpa using h

private theorem inner_span_eq_zero_of_eigenvalue_gt {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {s : Set X} {C : ℝ} (hs : ∀ u ∈ s, ∃ α : ℝ, α ≤ C ∧ T u = (α : ℂ) • u) {v : X} {β : ℝ}
    (hv : T v = (β : ℂ) • v) (hβ : C < β) : ∀ w ∈ Submodule.span ℂ s, inner ℂ w v = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, hx'⟩ := hs x hx
    exact coefA_inner_eq_zero hT hx' hv (ne_of_lt (lt_of_le_of_lt hα hβ))
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

theorem coefA_toSum {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') (ℓ : X →ₗ[ℂ] ℂ) (C : ℝ)
    {Z₀ : Submodule ℂ X} (hZ₀ : FiniteDimensional ℂ Z₀) (hZM : Z₀ ≤ M')
    (hlow : ∀ y ∈ M', ∀ θ : ℝ, θ ≤ C → T y = (θ : ℂ) • y → y ∈ Z₀)
    (hhigh : ∀ y ∈ M', ∀ θ : ℝ, C < θ → T y = (θ : ℂ) • y → ℓ y = 0) :
    ∃ z ∈ M', ∀ y ∈ M', inner ℂ z y = ℓ y := by
  classical
  have hLZ : Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y} ≤ Z₀ :=
    Submodule.span_le.mpr (fun y ⟨hyM, θ, hθ, hTy⟩ => hlow y hyM θ hθ hTy)
  haveI := hZ₀
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y}) :=
    Submodule.finiteDimensional_of_le hLZ
  obtain ⟨z, hzL, hz⟩ := exists_mem_inner_eq_functional_of_finiteDim
    (Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y}) ℓ
  refine ⟨z, hZM (hLZ hzL), fun y hy => ?_⟩
  obtain ⟨m, b, θ, hsum, hb⟩ := coefA_decompM hT hloc hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, inner_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hθ : θ i ≤ C
  · exact hz (b i) (Submodule.subset_span ⟨(hb i).1, θ i, hθ, (hb i).2⟩)
  · push_neg at hθ
    rw [hhigh (b i) (hb i).1 (θ i) hθ (hb i).2]
    exact inner_span_eq_zero_of_eigenvalue_gt hT
      (s := {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y})
      (fun _ hu => hu.2) (hb i).2 hθ z hzL

theorem coefA_high {T : Y →ₗ[ℂ] Y} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {L : Submodule ℂ Y} (hLd : FiniteDimensional ℂ L) (hL : ∀ x ∈ L, T x ∈ L) :
    ∃ C : ℝ, ∀ F ∈ L, ∀ u : Y, ∀ θ : ℝ, C < θ → T u = (θ : ℂ) • u → inner ℂ F u = 0 := by
  haveI := hLd
  have hS : (T.restrict hL).IsSymmetric :=
    LinearMap.IsSymmetric.restrict_invariant (show T.IsSymmetric from hT) hL
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ L = n := ⟨_, rfl⟩
  have hev : ∀ i, T ((hS.eigenvectorBasis hn i : L) : Y) =
      (hS.eigenvalues hn i : ℂ) • ((hS.eigenvectorBasis hn i : L) : Y) := by
    intro i
    have h3 := congrArg (fun z : L => (z : Y)) (hS.apply_eigenvectorBasis hn i)
    simp only [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h3
    exact h3
  refine ⟨∑ i, |hS.eigenvalues hn i|, ?_⟩
  intro F hF u θ hθ hu
  have hle : ∀ i, hS.eigenvalues hn i ≤ ∑ j, |hS.eigenvalues hn j| := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |hS.eigenvalues hn j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have horth : ∀ i, inner ℂ ((hS.eigenvectorBasis hn i : L) : Y) u = 0 := fun i =>
    coefA_inner_eq_zero hT (hev i) hu (ne_of_lt (lt_of_le_of_lt (hle i) hθ))
  have hsum := congrArg (fun z : L => (z : Y)) ((hS.eigenvectorBasis hn).sum_repr' (⟨F, hF⟩ : L))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  rw [← hsum, sum_inner]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_smul_left, horth i, mul_zero]

private theorem exists_inner_comp_eq_functional_of_injOn {E : Submodule ℂ X} [FiniteDimensional ℂ E] (ι : X →ₗ[ℂ] Y)
    (hinj : ∀ y ∈ E, ι y = 0 → y = 0) (φ : X →ₗ[ℂ] ℂ) :
    ∃ x ∈ E, ∀ y ∈ E, inner ℂ (ι x) (ι y) = φ y := by
  have hker : LinearMap.ker (ι.comp E.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hinj w w.2 hw)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (ι.comp E.subtype) hker
  obtain ⟨f, hfR, hf⟩ := exists_mem_inner_eq_functional_of_finiteDim (LinearMap.range (ι.comp E.subtype))
    ((φ.comp E.subtype).comp g)
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hfR
  refine ⟨x, x.2, fun y hy => ?_⟩
  have h1 := hf (ι y) ⟨⟨y, hy⟩, rfl⟩
  have hgy : g (ι y) = ⟨y, hy⟩ := by
    have h2 := LinearMap.congr_fun hg ⟨y, hy⟩
    simpa using h2
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
  rw [h1, hgy]

theorem coefA_ofSum {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {TY : Y →ₗ[ℂ] Y} (hTY : ∀ x y, inner ℂ (TY x) y = inner ℂ x (TY y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') (ι : X →ₗ[ℂ] Y)
    (hιT : ∀ y ∈ M', ι (T y) = TY (ι y)) (hinj : ∀ y ∈ M', ι y = 0 → y = 0)
    (hfin : ∀ θ : ℝ, ∃ Z : Submodule ℂ X, FiniteDimensional ℂ Z ∧
      ∀ y ∈ M', T y = (θ : ℂ) • y → y ∈ Z) :
    ∀ z ∈ M', ∃ f ∈ M'.map ι, ∀ y ∈ M', inner ℂ f (ι y) = inner ℂ z y := by
  classical
  intro z hz
  obtain ⟨m, b, θ, hzs, hb⟩ := coefA_decompM hT hloc hz
  have hx : ∀ k : Fin m, ∃ x : X, x ∈ M' ∧ T x = (θ k : ℂ) • x ∧
      ∀ y ∈ M', T y = (θ k : ℂ) • y → inner ℂ (ι x) (ι y) = inner ℂ (b k) y := by
    intro k
    obtain ⟨Z, hZd, hZ⟩ := hfin (θ k)
    have hmemE : ∀ y, y ∈ M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id) ↔
        y ∈ M' ∧ T y = (θ k : ℂ) • y := by
      intro y
      simp [Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hEZ : M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id) ≤ Z := fun y hy =>
      hZ y ((hmemE y).mp hy).1 ((hmemE y).mp hy).2
    haveI := hZd
    haveI : FiniteDimensional ℂ ↥(M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id)) :=
      Submodule.finiteDimensional_of_le hEZ
    obtain ⟨x, hxE, hxr⟩ := exists_inner_comp_eq_functional_of_injOn ι (fun y hy => hinj y ((hmemE y).mp hy).1)
      (innerₛₗ ℂ (b k))
    refine ⟨x, ((hmemE x).mp hxE).1, ((hmemE x).mp hxE).2, fun y hy hTy => ?_⟩
    rw [hxr y ((hmemE y).mpr ⟨hy, hTy⟩)]
    first
      | rfl
      | simp
  choose x hxM hxT hxr using hx
  refine ⟨ι (∑ k, x k), Submodule.mem_map_of_mem (Submodule.sum_mem _ (fun k _ => hxM k)), ?_⟩
  intro y hy
  obtain ⟨n, c, η, hys, hc⟩ := coefA_decompM hT hloc hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, hzs, hys, sum_inner, sum_inner]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, inner_sum, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hkj : θ k = η j
  · exact hxr k (c j) (hc j).1 (by rw [hkj]; exact (hc j).2)
  · have h1 : inner ℂ (b k) (c j) = 0 := coefA_inner_eq_zero hT (hb k).2 (hc j).2 hkj
    have hTYx : TY (ι (x k)) = (θ k : ℂ) • ι (x k) := by
      rw [← hιT _ (hxM k), hxT k, map_smul]
    have hTYc : TY (ι (c j)) = (η j : ℂ) • ι (c j) := by
      rw [← hιT _ (hc j).1, (hc j).2, map_smul]
    rw [h1, coefA_inner_eq_zero hTY hTYx hTYc hkj]

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefCExpEntrySummable
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem coefC_pow_entry_le (B : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (c d : Fin n) :
    ‖(B ^ j) c d‖ ≤ (∑ a, ∑ b, ‖B a b‖) ^ j := by
  induction j generalizing c d with
  | zero =>
    simp only [pow_zero]
    by_cases h : c = d
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  | succ j ih =>
    rw [pow_succ, Matrix.mul_apply, pow_succ]
    have hN0 : 0 ≤ ∑ a, ∑ b, ‖B a b‖ := by positivity
    have hN : ∑ e, ‖B e d‖ ≤ ∑ a, ∑ b, ‖B a b‖ := by
      refine Finset.sum_le_sum fun e _ => ?_
      exact Finset.single_le_sum (f := fun b => ‖B e b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ d)
    calc ‖∑ e, (B ^ j) c e * B e d‖ ≤ ∑ e, ‖(B ^ j) c e * B e d‖ := norm_sum_le _ _
      _ ≤ ∑ e, (∑ a, ∑ b, ‖B a b‖) ^ j * ‖B e d‖ := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (ih c e) (norm_nonneg _)
      _ = (∑ a, ∑ b, ‖B a b‖) ^ j * ∑ e, ‖B e d‖ := by rw [Finset.mul_sum]
      _ ≤ (∑ a, ∑ b, ‖B a b‖) ^ j * ∑ a, ∑ b, ‖B a b‖ :=
          mul_le_mul_of_nonneg_left hN (pow_nonneg hN0 _)

theorem coefC_exp_entry_summable (B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c d : Fin n) :
    Summable fun j : ℕ => ‖(s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d‖ := by
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (Real.summable_pow_div_factorial (‖(s : ℂ)‖ * ∑ a, ∑ b, ‖B a b‖))
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc ‖(s : ℂ)‖ ^ j / (j.factorial : ℝ) * ‖(B ^ j) c d‖
      ≤ ‖(s : ℂ)‖ ^ j / (j.factorial : ℝ) * (∑ a, ∑ b, ‖B a b‖) ^ j := by
        gcongr
        exact coefC_pow_entry_le B j c d
    _ = (‖(s : ℂ)‖ * ∑ a, ∑ b, ‖B a b‖) ^ j / (j.factorial : ℝ) := by ring

theorem coefC_exp_entry_hasSum (B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c d : Fin n) :
    HasSum (fun j : ℕ => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d)
      ((NormedSpace.exp ((s : ℂ) • B)) c d) := by
  have hterm : ∀ j : ℕ, ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j =
      fun c d => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d := by
    intro j
    ext c d
    simp only [smul_pow, Matrix.smul_apply, smul_eq_mul]
    ring
  have hS : Summable fun j : ℕ => ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j := by
    rw [show (fun j : ℕ => ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j) =
      fun j : ℕ => (fun c d => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d) from funext hterm]
    exact Pi.summable.mpr fun c => Pi.summable.mpr fun d => (coefC_exp_entry_summable B s c d).of_norm
  have hE : NormedSpace.exp ((s : ℂ) • B) = ∑' j : ℕ, ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have h2 := Pi.hasSum.mp (Pi.hasSum.mp hS.hasSum c) d
  rw [hE]
  convert h2 using 1
  funext j
  rw [hterm j]

theorem coefC_hasSum_mul {f g : ℕ → ℂ} {a b : ℂ} (hf : HasSum f a) (hg : HasSum g b)
    (hf' : Summable fun j => ‖f j‖) (hg' : Summable fun j => ‖g j‖) :
    HasSum (fun m => ∑ kl ∈ antidiagonal m, f kl.1 * g kl.2) (a * b) := by
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hf' hg'
  have h := (Summable.of_norm hs).hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf' hg', hf.tsum_eq, hg.tsum_eq] at h
  exact h

theorem coefC_choose_coef (s : ℂ) (j k : ℕ) :
    s ^ (j + k) / ((j + k).factorial : ℂ) * ((j + k).choose j : ℂ) =
      s ^ j / (j.factorial : ℂ) * (s ^ k / (k.factorial : ℂ)) := by
  have h1 : ((j + k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [Nat.cast_choose ℂ (Nat.le_add_right j k), Nat.add_sub_cancel_left, pow_add]
  field_simp <;> ring

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.GelfandSeries
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def gx (l : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0, _ => 1
  | k + 1, r => l r * gx l k r - ∑ s ∈ univ.filter (fun s => r < s), gx l k s

def gelfandSeries (l : Fin n → ℂ) : PowerSeries ℂ :=
  1 - ∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹)

def gval (l : Fin n → ℂ) (k : ℕ) : ℂ := PowerSeries.coeff (k + 1) (gelfandSeries l)

def icShift (μ : Fin n → ℝ) : Fin n → ℂ := fun r => ((μ r + ((n : ℝ) - 1) / 2 : ℝ) : ℂ)

def gxSeries (l : Fin n → ℂ) (r : Fin n) : PowerSeries ℂ := PowerSeries.mk fun k => gx l k r

theorem gxSeries_mul (l : Fin n → ℂ) (r : Fin n) :
    gxSeries l r * (1 - PowerSeries.C (l r) * PowerSeries.X) =
      1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s => r < s), gxSeries l s := by
  ext k
  rcases k with _ | k
  · simp [gxSeries, gx]
  · rw [show gxSeries l r * (1 - PowerSeries.C (l r) * PowerSeries.X) =
        gxSeries l r - PowerSeries.C (l r) * (gxSeries l r * PowerSeries.X) by ring,
      map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, map_sub,
      PowerSeries.coeff_succ_X_mul, map_sum]
    simp [gxSeries, gx, PowerSeries.coeff_one]

theorem oneSubCX_const_ne (a : ℂ) : PowerSeries.constantCoeff (1 - PowerSeries.C a * PowerSeries.X) ≠ 0 := by
  simp

theorem gxSeries_eq (l : Fin n → ℂ) (r : Fin n) :
    gxSeries l r = (1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s => r < s), gxSeries l s) *
      (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹ := by
  rw [← gxSeries_mul, mul_assoc, PowerSeries.mul_inv_cancel _ (oneSubCX_const_ne _), mul_one]

theorem gxSeries_tele (l : Fin n → ℂ) (d : ℕ) : ∀ r : ℕ, n - r = d →
    1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s : Fin n => r ≤ s.val), gxSeries l s =
      ∏ s ∈ univ.filter (fun s : Fin n => r ≤ s.val),
        (1 - PowerSeries.X * (1 - PowerSeries.C (l s) * PowerSeries.X)⁻¹) := by
  induction d with
  | zero =>
    intro r hr
    have : univ.filter (fun s : Fin n => r ≤ s.val) = ∅ := by
      ext s; simp; omega
    simp [this]
  | succ d ih =>
    intro r hr
    have hrn : r < n := by omega
    have hins : univ.filter (fun s : Fin n => r ≤ s.val) =
        insert ⟨r, hrn⟩ (univ.filter (fun s : Fin n => r + 1 ≤ s.val)) := by
      ext s; simp [Fin.ext_iff]; omega
    have hgt : univ.filter (fun s : Fin n => (⟨r, hrn⟩ : Fin n) < s) =
        univ.filter (fun s : Fin n => r + 1 ≤ s.val) := by
      ext s; simp only [mem_filter, mem_univ, true_and, Fin.lt_def]; omega
    have hnot : (⟨r, hrn⟩ : Fin n) ∉ univ.filter (fun s : Fin n => r + 1 ≤ s.val) := by simp
    rw [hins, sum_insert hnot, prod_insert hnot, ← ih (r + 1) (by omega), gxSeries_eq l ⟨r, hrn⟩,
      hgt]
    ring

theorem gelfandSeries_eq (l : Fin n → ℂ) :
    gelfandSeries l = PowerSeries.X * ∑ r, gxSeries l r := by
  have h := gxSeries_tele l n 0 (by simp)
  have e : univ.filter (fun s : Fin n => 0 ≤ s.val) = univ := by ext; simp
  rw [e] at h
  rw [gelfandSeries, ← h]
  ring

theorem sum_gx_eq_gval (l : Fin n → ℂ) (k : ℕ) : ∑ r, gx l k r = gval l k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gval, gelfandSeries_eq, PowerSeries.coeff_succ_X_mul, map_sum]
  simp [gxSeries]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.MomentMatch
section
noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS

theorem moment_poly {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (Q : ℂ[X]) :
    ∑ i, u i * Q.eval (b i) = ∑ s, r s * Q.eval (a s) := by
  simp only [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc ∑ i, u i * (Q.coeff k * b i ^ k) = Q.coeff k * ∑ i, u i * b i ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = Q.coeff k * ∑ s, r s * a s ^ k := by rw [h k]
    _ = ∑ s, r s * (Q.coeff k * a s ^ k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem moment_fibre {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (p : ℂ) :
    ∑ i ∈ univ.filter (fun i => b i = p), u i = ∑ s ∈ univ.filter (fun s => a s = p), r s := by
  classical
  set S : Finset ℂ := (univ.image b ∪ univ.image a).erase p with hS
  have hne : (∏ s ∈ S, (p - s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  let Q : ℂ[X] := C (∏ s ∈ S, (p - s))⁻¹ * ∏ s ∈ S, (X - C s)
  have hQ : ∀ x, x ∈ univ.image b ∪ univ.image a → Q.eval x = if x = p then 1 else 0 := by
    intro x hx
    simp only [Q, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with hxp
    · subst hxp
      exact inv_mul_cancel₀ hne
    · rw [Finset.prod_eq_zero (i := x) (Finset.mem_erase.mpr ⟨hxp, hx⟩) (sub_self x), mul_zero]
  have e := moment_poly b u a r h Q
  rw [Finset.sum_filter, Finset.sum_filter]
  calc ∑ i, (if b i = p then u i else 0) = ∑ i, u i * Q.eval (b i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [hQ (b i) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp
    _ = ∑ s, r s * Q.eval (a s) := e
    _ = _ := Finset.sum_congr rfl fun s _ => by
          rw [hQ (a s) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp

variable {n : ℕ}

end ReciprocityTheory.ChartRestriction.DS
end
end

