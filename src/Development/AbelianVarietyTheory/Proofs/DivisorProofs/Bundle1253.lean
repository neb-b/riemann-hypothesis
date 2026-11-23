module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Decomp
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type}

theorem val_unif_pow_le {ϖ : kˣ} (hϖ : IsUnif ϖ) {n m : ℕ} (h : n ≤ m) :
    valuation k ((ϖ ^ m : kˣ) : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' (show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le) h

theorem box_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) (X : Matrix A D k) {n m : ℕ} (h : n ≤ m) :
    box ϖ X (fun _ => m) ⊆ box ϖ X (fun _ => n) :=
  fun _ hY i j => (hY i j).trans (val_unif_pow_le hϖ h)

theorem mem_box_self (ϖ : kˣ) (X : Matrix A D k) (e : A → ℕ) : X ∈ box ϖ X e :=
  fun i j => by simp

theorem eq_of_forall_mem_box {ϖ : kˣ} (hϖ : IsUnif ϖ) {X Y : Matrix A D k}
    (h : ∀ n : ℕ, Y ∈ box ϖ X (fun _ => n)) : Y = X := by
  ext i j
  by_contra hne
  have h0 : valuation k (Y i j - X i j) ≠ 0 := by simpa [sub_eq_zero] using hne
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (show valuation k (ϖ : k) < 1 from hϖ ▸ uniformizer_lt_one) (Units.mk0 _ h0)
  have := h n i j
  simp only [Units.val_pow_eq_pow_val, map_pow] at this
  exact absurd this (not_le.2 hn)

variable [Fintype A] [Fintype D]

theorem exists_box_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {X : Matrix A D k} {U : Set (Matrix A D k)}
    (hU : U ∈ nhds X) : ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ U := by
  refine exists_subset_nhds_of_isCompact' (V := fun n : ℕ => box ϖ X (fun _ => n))
    (Antitone.directed_ge fun a b h => box_mono hϖ X h) (fun n => isCompact_box ϖ X _)
    (fun n => (isClopen_box ϖ X _).isClosed) ?_
  apply mem_nhdsSet_iff_forall.2
  intro Y hY
  have hYX : Y = X := eq_of_forall_mem_box hϖ (Set.mem_iInter.1 hY)
  simpa only [hYX] using hU

theorem exists_sum_boxFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) :
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k), ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ s : Finset (Matrix A D k),
      Φ = ∑ c ∈ s, Φ c • GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∧
      ∀ c ∈ s, ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Φ X = Φ c := by
  classical
  intro Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  have hrad : ∀ X, ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ {Y | Φ Y = Φ X} := fun X =>
    exists_box_subset hϖ ((hlc.isOpen_fiber (Φ X)).mem_nhds rfl)
  choose n hn using hrad
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover hcs (fun X => box ϖ X (fun _ => n X))
    (fun X => (isClopen_box ϖ X _).isOpen) (fun Y _ => Set.mem_iUnion.2 ⟨Y, mem_box_self ϖ Y _⟩)
  refine ⟨t.sup n, fun m hm => ?_⟩
  have hconst : ∀ Y ∈ tsupport Φ, ∀ Z ∈ box ϖ Y (fun _ => m), Φ Z = Φ Y := by
    intro Y hY Z hZ
    obtain ⟨X, hXt, hYX⟩ := Set.mem_iUnion₂.1 (ht hY)
    have hsub : box ϖ Y (fun _ => m) ⊆ box ϖ X (fun _ => n X) := by
      rw [← box_eq_of_mem hYX]; exact box_mono hϖ Y ((Finset.le_sup hXt).trans hm)
    have h1 : Φ Z = Φ X := hn X (hsub hZ)
    have h2 : Φ Y = Φ X := hn X (hsub (mem_box_self ϖ Y _))
    rw [h1, h2]
  let rep : Set (Matrix A D k) → Matrix A D k := fun B =>
    if h : ∃ Z, box ϖ Z (fun _ => m) = B then h.choose else 0
  have hrep : ∀ Y, box ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m) = box ϖ Y (fun _ => m) := by
    intro Y
    have h : ∃ Z, box ϖ Z (fun _ => m) = box ϖ Y (fun _ => m) := ⟨Y, rfl⟩
    rw [show rep (box ϖ Y (fun _ => m)) = h.choose from dif_pos h]
    exact h.choose_spec
  obtain ⟨s₀, hs₀⟩ := IsCompact.elim_finite_subcover hcs
    (fun Y : tsupport Φ => box ϖ (Y : Matrix A D k) (fun _ => m))
    (fun Y => (isClopen_box ϖ _ _).isOpen) (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, mem_box_self ϖ Y _⟩)
  let s : Finset (Matrix A D k) := s₀.image (fun Y : tsupport Φ => rep (box ϖ (Y : Matrix A D k) (fun _ => m)))
  have hs : ∀ c ∈ s, ∃ Y ∈ tsupport Φ, c = rep (box ϖ Y (fun _ => m)) := by
    intro c hc
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨Y, Y.2, rfl⟩
  have hval : ∀ c ∈ s, ∀ Z ∈ box ϖ c (fun _ => m), Φ Z = Φ c := by
    intro c hc Z hZ
    obtain ⟨Y, hY, rfl⟩ := hs c hc
    rw [hrep] at hZ
    have hcY : rep (box ϖ Y (fun _ => m)) ∈ box ϖ Y (fun _ => m) := by
      have := mem_box_self ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m)
      rwa [hrep] at this
    rw [hconst Y hY Z hZ, hconst Y hY _ hcY]
  have huniq : ∀ c ∈ s, ∀ c' ∈ s, ∀ Z, Z ∈ box ϖ c (fun _ => m) → Z ∈ box ϖ c' (fun _ => m) → c = c' := by
    intro c hc c' hc' Z hZ hZ'
    obtain ⟨Y, -, rfl⟩ := hs c hc
    obtain ⟨Y', -, rfl⟩ := hs c' hc'
    have e1 := box_eq_of_mem hZ
    have e2 := box_eq_of_mem hZ'
    rw [hrep] at e1 e2
    rw [← e1, ← e2]
  have hcov : ∀ Z, Φ Z ≠ 0 → ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m) := by
    intro Z hZ
    obtain ⟨Y, hY, hZY⟩ := Set.mem_iUnion₂.1 (hs₀ (subset_tsupport Φ hZ))
    refine ⟨rep (box ϖ (Y : Matrix A D k) (fun _ => m)), Finset.mem_image_of_mem _ hY, ?_⟩
    rw [hrep]; exact hZY
  refine ⟨s, ?_, hval⟩
  funext Z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, boxFn]
  by_cases h : ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m)
  · obtain ⟨c, hc, hZ⟩ := h
    rw [Finset.sum_eq_single c]
    · rw [Set.indicator_of_mem hZ, Pi.one_apply, mul_one, hval c hc Z hZ]
    · intro c' hc' hne
      rw [Set.indicator_of_notMem (fun hZ' => hne (huniq c' hc' c hc Z hZ' hZ)), mul_zero]
    · intro hcs'; exact absurd hc hcs'
  · push_neg at h
    rw [Finset.sum_eq_zero fun c hc => by rw [Set.indicator_of_notMem (h c hc), mul_zero]]
    by_contra hZ
    obtain ⟨c, hc, hZc⟩ := hcov Z hZ
    exact h c hc hZc

end GlobalTheory.RankCoinv.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmul
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.VacCore

theorem ray_formula {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (k : V → ℂ) (hk : Differentiable ℝ k) (w : V) (ℓ : V →ₗ[ℝ] ℂ)
    (h : ∀ z, fderiv ℝ k z w = ℓ z * k z) : k w = k 0 * Complex.exp (ℓ w / 2) := by
  set c := ℓ w
  let E : ℝ → ℂ := fun s => Complex.exp (((-(s ^ 2) / 2 : ℝ) : ℂ) * c)
  have hE : ∀ s : ℝ, HasDerivAt E (Complex.exp (((-(s ^ 2) / 2 : ℝ) : ℂ) * c) * (((-(2 * s) / 2 : ℝ) : ℂ) * c)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (-(s ^ 2) / 2 : ℝ)) (-(2 * s) / 2) s := by
      have := ((hasDerivAt_pow 2 s).neg).div_const 2
      simpa using this
    exact ((h1.ofReal_comp).mul_const c).cexp
  have hK : ∀ s : ℝ, HasDerivAt (fun s : ℝ => k (s • w)) (fderiv ℝ k (s • w) w) s := by
    intro s
    have := (hk (s • w)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const w)
    rw [one_smul] at this
    exact this
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => k (s • w) * E s) 0 s := by
    intro s
    have := (hK s).mul (hE s)
    refine this.congr_deriv ?_
    rw [h, map_smul]
    simp only [Complex.real_smul, E]
    push_cast
    ring
  have hc := is_const_of_deriv_eq_zero (f := fun s : ℝ => k (s • w) * E s)
    (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) 1 0
  simp only [E, one_smul, zero_smul] at hc
  have : Complex.exp (((-((1:ℝ) ^ 2) / 2 : ℝ) : ℂ) * c) * Complex.exp (c / 2) = 1 := by
    rw [← Complex.exp_add]; push_cast; ring_nf; simp
  calc k w = k w * (Complex.exp (((-((1:ℝ) ^ 2) / 2 : ℝ) : ℂ) * c) * Complex.exp (c / 2)) := by rw [this, mul_one]
    _ = _ := by rw [← mul_assoc, hc]; simp

theorem conj_mul_eq_zero_of_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f g : SchwartzMap V ℂ) (y₀ : V) (hy : y₀ ≠ 0)
    (h : ∀ z, fderiv ℝ f z y₀ * (starRingEnd ℂ) (g z) + f z * (starRingEnd ℂ) (fderiv ℝ g z y₀) = 0) :
    ∀ z, f z * (starRingEnd ℂ) (g z) = 0 := by
  intro z
  let φ : ℝ → ℂ := fun t => f (z + t • y₀) * (starRingEnd ℂ) (g (z + t • y₀))
  have hL : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z + t • y₀) y₀ t := by
    intro t
    have := ((hasDerivAt_id t).smul_const y₀).const_add z
    simpa using this
  have hφ : ∀ t, HasDerivAt φ 0 t := by
    intro t
    have hf := (f.differentiableAt (x := z + t • y₀)).hasFDerivAt.comp_hasDerivAt t (hL t)
    have hg := (g.differentiableAt (x := z + t • y₀)).hasFDerivAt.comp_hasDerivAt t (hL t)
    have hg' := hg.star
    have := hf.mul hg'
    refine this.congr_deriv ?_
    have := h (z + t • y₀)
    simpa [Complex.star_def] using this
  have hc : ∀ t, φ t = φ 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) t 0
  have hlin : Filter.Tendsto (fun t : ℝ => z + t • y₀) (Filter.cocompact ℝ) (Filter.cocompact V) := by
    apply Filter.tendsto_cocompact_cocompact_of_norm
    intro ε
    have hy' : 0 < ‖y₀‖ := norm_pos_iff.mpr hy
    refine ⟨(ε + ‖z‖) / ‖y₀‖, fun t ht => ?_⟩
    have h1 : ‖t • y₀‖ ≤ ‖z + t • y₀‖ + ‖z‖ := by
      calc ‖t • y₀‖ = ‖(z + t • y₀) - z‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul] at h1
    rw [div_lt_iff₀ hy'] at ht
    linarith
  have hf0 : Filter.Tendsto (fun t : ℝ => f (z + t • y₀)) (Filter.cocompact ℝ) (nhds 0) :=
    (f.tendsto_cocompact).comp hlin
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖g x‖ ≤ C := ⟨_, fun x => (g.toBoundedContinuousFunction).norm_coe_le_norm x⟩
  have hφ0 : Filter.Tendsto φ (Filter.cocompact ℝ) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hf0 ⊢
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    have := hf0.mul_const C
    rw [zero_mul] at this
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) this
    simp only [φ, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hconst : Filter.Tendsto φ (Filter.cocompact ℝ) (nhds (φ 0)) := by
    have : φ = fun _ => φ 0 := funext hc
    rw [this]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hconst hφ0
  simpa [φ] using this

noncomputable def lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b : V) : V →ₗ[ℝ] ℂ where
  toFun z := 2 * Real.pi * Complex.I * (B z a : ℂ) + 2 * Real.pi * (B z b : ℂ)
  map_add' x y := by simp only [map_add (f := _), LinearMap.add_apply, Complex.ofReal_add]; ring
  map_smul' c x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring

theorem lin_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b z : V) :
    lin B a b z = 2 * Real.pi * Complex.I * (B z a : ℂ) + 2 * Real.pi * (B z b : ℂ) := rfl

theorem schwartz_vacuum_eq_smul : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ y, (∀ x, B x y = 0) → y = 0) →
    ∀ (J e : (V × V) →ₗ[ℝ] (V × V)) (e' : V →ₗ[ℝ] V), (∀ y, J (J y) = -y) → (∀ y, e (e y) = e y) →
    (∀ y, J (e y) = e (J y)) → (∀ y, (e y).1 = e' y.1) → (∀ y x, B x (e y).2 = B (e' x) y.2) →
    ∀ (f g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ y x, fderiv ℝ g x (J y).1 - 2 * Real.pi * Complex.I * (B x (J y).2 : ℝ) * g x =
      Complex.I * (fderiv ℝ g x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * g x)) →
    (∀ y x, fderiv ℝ f x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I * (B x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f x =
      Complex.I * (fderiv ℝ f x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * f x)) →
    ∃ z : ℂ, f = z • g := by
  intro V _ _ _ B hB J e e' hJ he hJe he1 he2 f g hg0 hg hf

  have hinj : ∀ y, (J y).1 = 0 → y.1 = 0 → y = 0 := by
    intro y hJy hy1
    have key : ∀ x, g x ≠ 0 → B x y.2 = 0 := by
      intro x hx
      have h := hg y x
      simp only [hJy, hy1, map_zero] at h
      have h2 : g x * (2 * Real.pi * (B x y.2 : ℂ) + 2 * Real.pi * Complex.I * (B x (J y).2 : ℂ)) = 0 := by
        linear_combination (-1 : ℂ) * h + (2 * Real.pi * (B x y.2 : ℂ) * g x) * Complex.I_sq
      have h3 := (mul_eq_zero.mp h2).resolve_left hx
      have h4 := congrArg Complex.re h3
      simpa [Real.pi_ne_zero] using h4
    have hy2 : y.2 = 0 := by
      apply hB
      by_contra hne
      push_neg at hne
      obtain ⟨x₀, hx₀⟩ := hne
      apply hg0
      ext x
      simp only [SchwartzMap.zero_apply]
      set t₀ : ℝ := -(B x y.2) / B x₀ y.2
      have hS : IsClosed {t : ℝ | g (x + t • x₀) = 0} :=
        isClosed_eq (g.continuous.comp (continuous_const.add (continuous_id.smul continuous_const)))
          continuous_const
      have hsub : ({t₀}ᶜ : Set ℝ) ⊆ {t : ℝ | g (x + t • x₀) = 0} := by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
        simp only [Set.mem_setOf_eq]
        by_contra hgt
        have := key _ hgt
        rw [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
        apply ht
        simp only [t₀]
        field_simp
        linarith
      have hcl := hS.closure_subset_iff.mpr hsub
      rw [(dense_compl_singleton t₀).closure_eq] at hcl
      have := hcl (Set.mem_univ 0)
      simpa using this
    exact Prod.ext hy1 hy2
  let T : (V × V) →ₗ[ℝ] (V × V) := (LinearMap.fst ℝ V V ∘ₗ J).prod (LinearMap.fst ℝ V V)
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hinj y (congrArg Prod.fst hy) (congrArg Prod.snd hy)
  have hTs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTi

  choose yx hyx using fun x : V => hTs (x, 0)
  have hyx1 : ∀ x, (J (yx x)).1 = x := fun x => by simpa [T] using congrArg Prod.fst (hyx x)
  have hyx2 : ∀ x, (yx x).1 = 0 := fun x => by simpa [T] using congrArg Prod.snd (hyx x)
  have hray : ∀ k : SchwartzMap V ℂ, (∀ (y : V × V) (z : V), fderiv ℝ k z (J y).1 -
      2 * Real.pi * Complex.I * (B z (J y).2 : ℝ) * k z =
      Complex.I * (fderiv ℝ k z y.1 - 2 * Real.pi * Complex.I * (B z y.2 : ℝ) * k z)) →
      ∀ x, k x = k 0 * Complex.exp (lin B (J (yx x)).2 (yx x).2 x / 2) := by
    intro k hk x
    apply ray_formula k k.differentiable x (lin B (J (yx x)).2 (yx x).2)
    intro z
    have h := hk (yx x) z
    rw [hyx1, hyx2, map_zero] at h
    rw [lin_apply]
    linear_combination h - (2 * Real.pi * (B z (yx x).2 : ℂ) * k z) * Complex.I_sq
  have hg_ray := hray g hg
  have hg00 : g 0 ≠ 0 := by
    intro h0; apply hg0; ext x; rw [hg_ray x, h0]; simp
  have hgne : ∀ x, g x ≠ 0 := fun x => by
    rw [hg_ray x]; exact mul_ne_zero hg00 (Complex.exp_ne_zero _)
  have he'2 : ∀ v, e' (e' v) = e' v := by
    intro v
    have := congrArg Prod.fst (he (v, 0))
    simp only [he1] at this
    simpa using this
  by_cases hz : ∀ v, e' v = 0
  · have he0 : ∀ y, e y = 0 := by
      intro y; apply Prod.ext
      · rw [he1, hz]; rfl
      · apply hB; intro x; rw [he2, hz, map_zero, LinearMap.zero_apply]
    have hf' : ∀ (y : V × V) (z : V), fderiv ℝ f z (J y).1 -
        2 * Real.pi * Complex.I * (B z (J y).2 : ℝ) * f z =
        Complex.I * (fderiv ℝ f z y.1 - 2 * Real.pi * Complex.I * (B z y.2 : ℝ) * f z) := by
      intro y z; have := hf y z; rwa [he0, smul_zero, sub_zero] at this
    have hf_ray := hray f hf'
    refine ⟨f 0 / g 0, ?_⟩
    ext x
    rw [SchwartzMap.smul_apply, smul_eq_mul, hf_ray x, hg_ray x]
    field_simp
  · push_neg at hz
    obtain ⟨v, hv⟩ := hz
    set y₀ := e' v with hy₀def
    have hy₀ : e' y₀ = y₀ := he'2 v
    obtain ⟨u, hu⟩ := hTs (y₀, 0)
    have hu1 : (J u).1 = y₀ := by simpa [T] using congrArg Prod.fst hu
    have hu2 : u.1 = 0 := by simpa [T] using congrArg Prod.snd hu
    have heu : e u = u := by
      have : e u - u = 0 := hinj _
        (by rw [map_sub, Prod.fst_sub, hJe, he1, hu1, hy₀, sub_self])
        (by rw [Prod.fst_sub, he1, hu2, map_zero, sub_self])
      exact sub_eq_zero.mp this
    have hfu : ∀ z, fderiv ℝ f z y₀ = (2 * Real.pi * Complex.I * (B z (J u).2 : ℂ)
        - 2 * Real.pi * (B z u.2 : ℂ)) * f z := by
      intro z
      have h := hf u z
      rw [heu, two_smul, sub_add_cancel_left, map_neg, Prod.fst_neg, Prod.snd_neg, map_neg,
        map_neg, hu1, hu2, map_zero, Complex.ofReal_neg] at h
      linear_combination (-1 : ℂ) * h + (2 * Real.pi * (B z u.2 : ℂ) * f z) * Complex.I_sq
    have hgu : ∀ z, fderiv ℝ g z y₀ = (2 * Real.pi * Complex.I * (B z (J u).2 : ℂ)
        + 2 * Real.pi * (B z u.2 : ℂ)) * g z := by
      intro z
      have h := hg u z
      rw [hu1, hu2, map_zero] at h
      linear_combination h - (2 * Real.pi * (B z u.2 : ℂ) * g z) * Complex.I_sq
    have hk := conj_mul_eq_zero_of_line f g y₀ hv (fun z => by
      rw [hfu z, hgu z]
      simp only [map_add (f := _), map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring)
    refine ⟨0, ?_⟩
    ext z
    rw [zero_smul, SchwartzMap.zero_apply]
    exact (mul_eq_zero.mp (hk z)).resolve_right ((map_ne_zero _).mpr (hgne z))

end GlobalTheory.VacCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzLocallyConstantSupport
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical

noncomputable section
open Filter Topology

namespace GlobalTheory.SBBounds

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tendsto_pow_zero {x : k} (h : valuation k x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem sb_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : k),
    t ≠ 0 → valuation k t < 1 → ∀ φ : Matrix (Fin n) (Fin n) k → ℂ, φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    ∃ N M : ℕ, (∀ X, φ X ≠ 0 → t ^ N • X ∈ intM k (Fin n) (Fin n)) ∧
      ∀ X E, E ∈ intM k (Fin n) (Fin n) → φ (X + t ^ M • E) = φ X := by
  intro k _ _ _ _ n t _ ht φ hφ
  obtain ⟨hlc, hcs⟩ := hφ
  have hU : IsOpen (intM k (Fin n) (Fin n)) := isOpen_intMatrix
  have hUc : IsCompact (intM k (Fin n) (Fin n)) := isCompact_intMatrix
  have h0 : (0 : Matrix (Fin n) (Fin n) k) ∈ intM k (Fin n) (Fin n) := fun i j => (𝒪[k]).zero_mem
  have htO : t ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 ht.le
  have hT := tendsto_pow_zero ht

  have hmono : Monotone fun N : ℕ => {X : Matrix (Fin n) (Fin n) k | t ^ N • X ∈ intM k (Fin n) (Fin n)} := by
    intro N N' hNN' X hX i j
    have e : t ^ N' • X = t ^ (N' - N) • (t ^ N • X) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hNN']
    rw [e]
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact (𝒪[k]).mul_mem ((𝒪[k]).pow_mem htO _) (hX i j)
  obtain ⟨N, hN⟩ := hcs.isCompact.elim_directed_cover
    (fun N : ℕ => {X : Matrix (Fin n) (Fin n) k | t ^ N • X ∈ intM k (Fin n) (Fin n)})
    (fun N => hU.preimage (f := fun X : Matrix (Fin n) (Fin n) k => t ^ N • X) (continuous_const_smul _))
    (fun X _ => by
      have h1 : Tendsto (fun N : ℕ => t ^ N • X) atTop (𝓝 ((0 : k) • X)) := hT.smul_const X
      rw [zero_smul] at h1
      obtain ⟨N, hN⟩ := (h1.eventually (hU.mem_nhds h0)).exists
      exact Set.mem_iUnion.2 ⟨N, hN⟩)
    hmono.directed_le

  have hZ : IsOpen {p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k |
      φ (p.2.1 + p.1 • p.2.2) = φ p.2.1} := by
    have c1 : Continuous fun p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k =>
        p.2.1 + p.1 • p.2.2 := by fun_prop
    have c2 : Continuous fun p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.2.1 := by fun_prop
    have := ((hlc.comp_continuous c1).comp₂ (hlc.comp_continuous c2) fun a b => a - b).isOpen_fiber 0
    simpa [Function.comp_def, sub_eq_zero] using this
  have hKU : IsCompact (tsupport φ ×ˢ intM k (Fin n) (Fin n)) := hcs.isCompact.prod hUc
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ q ∈ tsupport φ ×ˢ intM k (Fin n) (Fin n), φ (q.1 + c • q.2) = φ q.1 := by
    refine hKU.eventually_forall_of_forall_eventually fun q _ => ?_
    have hm : ((0 : k), q) ∈ {p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k |
      φ (p.2.1 + p.1 • p.2.2) = φ p.2.1} := by simp
    exact hZ.mem_nhds hm
  obtain ⟨M, hM⟩ := (hT.eventually hev).exists
  refine ⟨N, M, fun X hX => hN (subset_tsupport _ hX), fun X E hE => ?_⟩
  by_cases hX : X ∈ tsupport φ
  · exact hM (X, E) ⟨hX, hE⟩
  by_cases hX' : X + t ^ M • E ∈ tsupport φ
  · have hE' : -E ∈ intM k (Fin n) (Fin n) := fun i j => (𝒪[k]).neg_mem (hE i j)
    have := hM (X + t ^ M • E, -E) ⟨hX', hE'⟩
    simp only [smul_neg, add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

end GlobalTheory.SBBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementRealComponentsOfFrame
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusDict

open GlobalTheory.AdelicU

theorem compAt_mt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (a : GA D V) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) =
      GlobalTheory.Orb.archMat D.sp.cm.sig V.gram (embOverOf D τ) (projArch D.sp.cm.sig V.gram (placeOf D τ) a) := by
  refine Matrix.ext fun i j => ?_
  change θ τ (infPart D (Formalism.L2.Theta.mt V a i j)) = _
  rw [eq_infProj hθ (embOverOf D τ) rfl]
  exact GlobalTheory.Doubling.infProj_fst (embOverOf D τ) _

theorem torus_dict : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Fin r → ℝ) (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a).map (finPart D) = 1 ∧ ∀ τ, Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * X.map (tauE D τ) = X.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) ∧ Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Y.map (tauE D τ) = Y.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) ∧ ∀ z : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) *ᵥ z = 0 → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) *ᵥ z = 0 → Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *ᵥ (fun i => tauE D τ (z i)) = fun i => tauE D τ (z i) := by
  intro D θ hθ V r X Y t a ha
  refine ⟨congrArg Units.val (MonoidHom.mem_ker.1 ha.1), fun τ => ?_⟩
  rw [compAt_mt hθ V a τ]
  exact ha.2 (placeOf D τ) (embOverOf D τ)

end GlobalTheory.TorusDict
end

