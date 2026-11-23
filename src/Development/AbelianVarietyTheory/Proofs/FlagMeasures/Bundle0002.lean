module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardQuotPow
section
namespace GlobalTheory.CardQuotientPow

open Module Submodule

theorem card_quot_pow {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by
  have key : ∀ I : Ideal R, Nat.card (R ⧸ I) = I.toAddSubgroup.index := fun I => rfl
  induction k with
  | zero => rw [key]; simp
  | succ k ih =>
    rw [pow_succ (Nat.card (R ⧸ Ideal.span {p})) k, ← ih, key, key, key]
    have hle : (Ideal.span {p ^ (k+1)}).toAddSubgroup ≤ (Ideal.span {p ^ k}).toAddSubgroup := by
      intro x hx
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p (Nat.le_succ k)) hx
    rw [← AddSubgroup.relIndex_mul_index hle, mul_comm]
    congr 1
    let f : R →+ R := AddMonoidHom.mulLeft (p ^ k)
    have hr : f.range = (Ideal.span {p ^ k}).toAddSubgroup := by
      ext x
      simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton', f,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
    have hc : (Ideal.span {p ^ (k+1)}).toAddSubgroup.comap f = (Ideal.span {p}).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, f,
        AddMonoidHom.coe_mulLeft]
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
    rw [← hr, ← AddSubgroup.index_comap, hc]

theorem main {R M ι : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Module.Basis ι R M) {p : R}
    (hp : Irreducible p) (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    ∃ m : ℕ, Associated (LinearMap.det φ) (p ^ m) ∧
      Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {p}) ^ m := by
  classical
  set N := LinearMap.range φ with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hφ
  have h : finrank R N = finrank R M := e.finrank_eq.symm
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  let f : M →ₗ[R] M := N.subtype ∘ₗ (b'.equiv ab (Equiv.refl _) : M →ₗ[R] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, b'.equiv_apply, Equiv.refl_apply,
      Submodule.subtype_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hφf : Associated (LinearMap.det φ) (LinearMap.det f) := by
    have : φ = N.subtype ∘ₗ (e : M →ₗ[R] N) := by ext x; rfl
    rw [this]
    exact LinearMap.associated_det_comp_equiv _ _ _
  choose k hk using fun i =>
    IsDiscreteValuationRing.associated_pow_irreducible (smithNormalFormCoeffs_ne_zero b h i) hp
  refine ⟨∑ i, k i, ?_, ?_⟩
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine hφf.trans ?_
    rw [hdetf]
    exact Associated.prod _ _ _ fun i _ => hk i
  · rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← card_quot_pow hp, Ideal.span_singleton_eq_span_singleton.mpr (hk i)]

end GlobalTheory.CardQuotientPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CauchySchwarz
section
open scoped ComplexOrder

namespace GlobalTheory.HermitianCauchySchwarz

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem herm (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hI : ∀ x : V, (0 : ℂ) ≤ I x x) (x y : V) :
    I y x = starRingEnd ℂ (I x y) := by
  have h1 := hI (x + y)
  have h2 := hI (x + Complex.I • y)
  have hx := hI x
  have hy := hI y
  rw [Complex.nonneg_iff] at h1 h2 hx hy
  simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im, RingHom.id_apply] at h1 h2
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> linarith [h1.2, h2.2, hx.2, hy.2]

theorem cauchy_schwarz (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hI : ∀ x : V, (0 : ℂ) ≤ I x x) (x y : V) :
    ‖I x y‖ ^ 2 ≤ (I x x).re * (I y y).re := by
  set b := I x y with hb
  have hyx := herm I hI x y
  have hx := (Complex.nonneg_iff.mp (hI x))
  have hy := (Complex.nonneg_iff.mp (hI y))
  have hq : ∀ s : ℝ, 0 ≤ ((I y y).re * (b.re * b.re + b.im * b.im)) * (s * s)
      + (-2 * (b.re * b.re + b.im * b.im)) * s + (I x x).re := by
    intro s
    have h := (Complex.nonneg_iff.mp (hI (x + ((-(s : ℂ)) * starRingEnd ℂ b) • y))).1
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply] at h
    rw [hyx] at h
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, map_mul, map_neg,
      Complex.conj_ofReal, RingHom.map_neg, Complex.conj_conj, ← hb, Complex.add_im, mul_zero,
      sub_zero, neg_zero, zero_mul, add_zero] at h
    rw [← hy.2] at h
    nlinarith [h, hx.2, hy.2]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  rw [Complex.sq_norm, Complex.normSq_apply]
  set n := b.re * b.re + b.im * b.im
  have hn : 0 ≤ n := by nlinarith [mul_self_nonneg b.re, mul_self_nonneg b.im]
  have hac : 0 ≤ (I x x).re * (I y y).re := mul_nonneg hx.1 hy.1
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hac
  · nlinarith

end GlobalTheory.HermitianCauchySchwarz

theorem GlobalTheory.HermitianCauchySchwarz.main : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ (x : V), (0 : ℂ) ≤ ((I : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x) → ∀ (x y : V), ‖((I : V → V →ₗ[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤ Complex.re (((I : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x) * Complex.re (((I : V → V →ₗ[ℂ] ℂ) y : V → ℂ) y) :=
  fun I hI x y => GlobalTheory.HermitianCauchySchwarz.cauchy_schwarz I hI x y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeFnSumSmulAeEq
section
namespace GlobalTheory.SumSmulAeEq

open MeasureTheory

theorem coeFn_sum_smul_ae_eq {X ι : Type} [MeasurableSpace X] (μ : Measure X) (s : Finset ι)
    (c : ι → ℂ) (y : ι → Lp ℂ (2 : ENNReal) μ) (F : ι → X → ℂ)
    (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i) :
    ((∑ i ∈ s, c i • y i : Lp ℂ (2 : ENNReal) μ) : X → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • y a) (∑ i ∈ s, c i • y i), Lp.coeFn_smul (c a) (y a),
      h a, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h4, Finset.sum_insert ha, Pi.smul_apply, h3, smul_eq_mul]

end GlobalTheory.SumSmulAeEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeSmulMem
section
namespace GlobalTheory.IntegralMultiple

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ a : 𝓞 E, (a : E) = (m : E) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y, hy, ⟨y • c, hint⟩, ?_⟩
  simp [zsmul_eq_mul]

theorem coe_smul_mem {E : Type} [Field E] [NumberField E] {j : ℕ}
    (Λ : Submodule (𝓞 E) (Fin j → E)) (r : 𝓞 E) {v : Fin j → E} (hv : v ∈ Λ) :
    (r : E) • v ∈ Λ := by
  have := Λ.smul_mem r hv
  rwa [← algebraMap_smul E r v] at this

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {j : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin j → E)),
    Submodule.IsFullLattice E Λ → ∀ (x : Fin j → E), ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ (↑n : E) • x ∈ Λ := by
  intro E _ _ j Λ hΛ x
  let S : Submodule E (Fin j → E) :=
    { carrier := {x | ∃ n : ℤ, n ≠ 0 ∧ (n : E) • x ∈ Λ}
      add_mem' := by
        rintro a b ⟨n, hn, ha⟩ ⟨m, hm, hb⟩
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        have h1 := coe_smul_mem Λ (m : 𝓞 E) ha
        have h2 := coe_smul_mem Λ (n : 𝓞 E) hb
        convert Λ.add_mem h1 h2 using 1
        simp only [smul_add, smul_smul, map_intCast, Int.cast_mul]
        push_cast
        rw [mul_comm (m : E) (n : E)]
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c v ⟨n, hn, hv⟩
        obtain ⟨m, hm, a, ha⟩ := exists_int_mul_integral c
        refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
        have h := coe_smul_mem Λ a hv
        convert h using 1
        rw [smul_smul, smul_smul, ha]
        push_cast
        ring_nf }
  have hle : Submodule.span E (Λ : Set (Fin j → E)) ≤ S := by
    rw [Submodule.span_le]
    intro v hv
    exact ⟨1, one_ne_zero, by simpa using hv⟩
  rw [hΛ.span_eq_top] at hle
  exact hle Submodule.mem_top

end GlobalTheory.IntegralMultiple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DecayOfMemSpan
section
namespace GlobalTheory.DecayOfMemSpan

theorem decay_of_mem_span {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {u : H}
    (h : ∀ v ∈ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))) :
    ∀ v ∈ Submodule.span ℂ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g)) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    refine ⟨A + B, fun g => ?_⟩
    rw [inner_add_left, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hA g) (hB g))
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    refine ⟨‖a‖ * A, fun g => ?_⟩
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA g) (norm_nonneg a)

end GlobalTheory.DecayOfMemSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionExponents
section
open Matrix Finset Real

namespace GlobalTheory

theorem deep_exponent_core (X τ be n g : ℝ) (q : ℕ) (hX : 16 ≤ X) (hq : 1 ≤ q) (hτ : 0 < τ)
    (hτX : τ ≤ X⁻¹ ^ (11 * q)) (hbe0 : 0 ≤ be) (hbe : be ≤ X ^ 6) (hn0 : 0 ≤ n) (hn : n ≤ X)
    (hg0 : 0 ≤ g) (hg : g ≤ X) :
    (X ^ (96 * q) * (2 * τ) ^ 16) * ((6 * be) * Real.exp 1 * (289 * n / τ ^ 4)) * g ^ 2 * X
      ≤ Real.exp (-1) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = X ^ q := ⟨_, rfl⟩
  have hXY : X ≤ Y := by
    rw [hYdef]; simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ X) hq
  have hY16 : 16 ≤ Y := le_trans hX hXY
  have hY0 : 0 < Y := by linarith
  have hτY : τ * Y ^ 11 ≤ 1 := by
    have h1 : X⁻¹ ^ (11 * q) * Y ^ 11 = 1 := by
      rw [hYdef, ← pow_mul, inv_pow, mul_comm q 11]
      exact inv_mul_cancel₀ (by positivity)
    calc τ * Y ^ 11 ≤ X⁻¹ ^ (11 * q) * Y ^ 11 := by gcongr
      _ = 1 := h1
  have hA : Y ^ 96 * τ ^ 12 * Y ^ 36 ≤ 1 := by
    have e : Y ^ 96 * τ ^ 12 * Y ^ 36 = (τ * Y ^ 11) ^ 12 := by ring
    rw [e]
    exact pow_le_one₀ (by positivity) hτY
  have hB : be * n * g ^ 2 * X ≤ Y ^ 10 :=
    calc be * n * g ^ 2 * X ≤ X ^ 6 * X * X ^ 2 * X := by gcongr
      _ = X ^ 10 := by ring
      _ ≤ Y ^ 10 := by gcongr
  have hC0 : 0 ≤ (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) := by positivity
  have hC : (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) * 16 ^ 26 ≤ 1 :=
    calc (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) * 16 ^ 26
        ≤ (Y ^ 96 * τ ^ 12) * Y ^ 10 * Y ^ 26 := by gcongr
      _ = Y ^ 96 * τ ^ 12 * Y ^ 36 := by ring
      _ ≤ 1 := hA
  have hE : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hE' : 1 / 3 ≤ Real.exp (-1) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos 1) hE.le
    rwa [Real.exp_neg, ← one_div]
  have hXq : X ^ (96 * q) = Y ^ 96 := by rw [hYdef, ← pow_mul, mul_comm]
  have hτ0 : τ ≠ 0 := hτ.ne'
  have e : Y ^ 96 * (2 * τ) ^ 16 * (6 * be * Real.exp 1 * (289 * n / τ ^ 4)) * g ^ 2 * X
      = (2 ^ 16 * 6 * 289) * Real.exp 1 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X)) := by
    field_simp
  rw [hXq, e]
  calc (2 ^ 16 * 6 * 289) * Real.exp 1 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X))
      ≤ (2 ^ 16 * 6 * 289) * 3 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE.le (by norm_num)) hC0
    _ ≤ 1 / 3 := by norm_num at hC ⊢; linarith
    _ ≤ Real.exp (-1) := hE'

theorem deep_region_exponents : ∀ (n f q : ℕ) (rd g b : ℝ) (τ : ℝ), 8 ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → 2 ≤ b → 1 ≤ g → 0 < τ → τ ≤ ((n : ℝ) * f * rd * g * b)⁻¹ ^ (11 * q) → let N : ℕ := n ^ 2 * f; let rh : ℝ := (n : ℝ) ^ 2 * Real.sqrt f * g * rd * (2 * τ) ^ ((1 : ℝ) / q) / 4; let be : ℝ := Real.sqrt n * b ^ 2 + 1.5 * (n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ); rh ≤ Real.log 2 ∧ (2 * rh * Real.sqrt f * be) ^ (2 * (8 * q * N)) * ((6 * be) ^ N * Real.exp f * (17 * Real.sqrt n / τ ^ 2) ^ (2 * N)) * g ^ (2 * N) * ((n : ℝ) * f * rd * g * b) ^ N ≤ Real.exp (-(N : ℝ)) := by
  intro n f q rd g b τ hn hf hq hqn hrd hb hg hτ hτP N rh be
  have hN : N = n ^ 2 * f := rfl
  have hrh : rh = (n : ℝ) ^ 2 * Real.sqrt f * g * rd * (2 * τ) ^ ((1 : ℝ) / q) / 4 := rfl
  have hbe : be = Real.sqrt n * b ^ 2 + 1.5 * (n : ℝ) ^ ((3 : ℝ) / 2)
      + 3 * ((8 * q * N + N : ℕ) : ℝ) := rfl
  clear_value N rh be
  generalize hPdef : ((n : ℝ) * f * rd * g * b) = P at hτP ⊢
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hqn' : (q : ℝ) ≤ n := by
    have h : q ≤ n := le_trans (by nlinarith) hqn
    exact_mod_cast h
  have hq0 : q ≠ 0 := by omega
  have hNr : (N : ℝ) = (n : ℝ) ^ 2 * f := by rw [hN]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hrd0 : 0 ≤ rd := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hnf : (n : ℝ) ≤ n * f := le_mul_of_one_le_right hn0 hf1
  have hnfr : (n : ℝ) * f ≤ n * f * rd := le_mul_of_one_le_right (by positivity) hrd
  have hnfrg : (n : ℝ) * f * rd ≤ n * f * rd * g := le_mul_of_one_le_right (by positivity) hg
  have hmP : (n : ℝ) * f * rd * g ≤ P := by
    rw [← hPdef]; exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hP16 : (16 : ℝ) ≤ P := by
    rw [← hPdef]
    linarith [mul_le_mul (by linarith : (8 : ℝ) ≤ n * f * rd * g) hb (by norm_num) (by positivity)]
  have hP0 : 0 ≤ P := by linarith
  have hnP : (n : ℝ) ≤ P := by linarith
  have hnfP : (n : ℝ) * f ≤ P := by linarith
  have hgP : g ≤ P := by
    have h : g ≤ n * f * rd * g := le_mul_of_one_le_left hg0 (by linarith)
    linarith
  have hbP : b ≤ P := by
    rw [← hPdef]; exact le_mul_of_one_le_left hb0 (by linarith)
  have hnbP : (n : ℝ) * b ≤ P := by
    rw [← hPdef]; exact mul_le_mul_of_nonneg_right (by linarith) hb0
  have hnmP : (n : ℝ) * (n * f * rd * g) ≤ P ^ 2 := by
    rw [sq]; exact mul_le_mul hnP hmP (by positivity) hP0
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have hs1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsn : Real.sqrt n ≤ n :=
    calc Real.sqrt n = Real.sqrt n * 1 := by ring
      _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hs1 (Real.sqrt_nonneg n)
      _ = n := Real.mul_self_sqrt hn0
  have hfs : Real.sqrt f * Real.sqrt f = f := Real.mul_self_sqrt hf0
  have hf1s : 1 ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hf1
  have hsf : Real.sqrt f ≤ f :=
    calc Real.sqrt f = Real.sqrt f * 1 := by ring
      _ ≤ Real.sqrt f * Real.sqrt f := mul_le_mul_of_nonneg_left hf1s (Real.sqrt_nonneg f)
      _ = f := hfs
  have h32 : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ 2 := by
    rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hcast : ((8 * q * N + N : ℕ) : ℝ) ≤ 9 * (n : ℝ) ^ 3 * f := by
    push_cast
    rw [hNr]
    linarith [mul_nonneg (sub_nonneg.2 hqn') (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f),
      mul_nonneg (by linarith : (0 : ℝ) ≤ n - 1) (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f)]
  have t1 : Real.sqrt n * b ^ 2 ≤ P ^ 2 :=
    calc Real.sqrt n * b ^ 2 ≤ n * b ^ 2 := by gcongr
      _ = (n * b) * b := by ring
      _ ≤ P * P := mul_le_mul hnbP hbP hb0 hP0
      _ = P ^ 2 := by ring
  have t2 : (n : ℝ) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hn0 hnP 2
  have t3 : (n : ℝ) ^ 3 * f ≤ P ^ 3 :=
    calc (n : ℝ) ^ 3 * f = n * n * (n * f) := by ring
      _ ≤ P * P * P := by gcongr
      _ = P ^ 3 := by ring
  have hP23 : P ^ 2 ≤ P ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hbe0 : 0 ≤ be := by rw [hbe]; positivity
  have hbeP : be ≤ 30 * P ^ 3 := by rw [hbe]; linarith
  have hP3 : (30 : ℝ) ≤ P ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hP16 3
    norm_num at h; linarith
  have hbe6 : be ≤ P ^ 6 := by linarith [mul_le_mul_of_nonneg_right hP3 (by positivity : (0 : ℝ) ≤ P ^ 3)]
  have hK : (n : ℝ) ^ 2 * f * g * rd * be / 2 ≤ P ^ 6 := by
    have e : (n : ℝ) ^ 2 * f * g * rd * be / 2 = (n * (n * f * rd * g)) * be / 2 := by ring
    rw [e]
    have h : (n * (n * f * rd * g)) * be ≤ P ^ 2 * (30 * P ^ 3) :=
      mul_le_mul hnmP hbeP hbe0 (by positivity)
    linarith [mul_nonneg (pow_nonneg hP0 5) (by linarith : (0 : ℝ) ≤ P - 15)]
  have hsq : ((2 * τ) ^ ((1 : ℝ) / q)) ^ q = 2 * τ := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow (by positivity) hq0
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (2 * τ) ^ ((1 : ℝ) / q) := ⟨_, rfl⟩
  rw [← hsdef] at hsq hrh
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hτP' : τ * P ^ (11 * q) ≤ 1 := by
    have h1 : P⁻¹ ^ (11 * q) * P ^ (11 * q) = 1 := by
      rw [inv_pow]; exact inv_mul_cancel₀ (by positivity)
    calc τ * P ^ (11 * q) ≤ P⁻¹ ^ (11 * q) * P ^ (11 * q) := by gcongr
      _ = 1 := h1
  have hu : (s * P ^ 11) ^ q ≤ 2 ^ q :=
    calc (s * P ^ 11) ^ q = s ^ q * P ^ (11 * q) := by rw [mul_pow, ← pow_mul]
      _ = 2 * (τ * P ^ (11 * q)) := by rw [hsq]; ring
      _ ≤ 2 * 1 := by gcongr
      _ = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  have hsP : s * P ^ 11 ≤ 2 := (pow_le_pow_iff_left₀ (by positivity) (by norm_num) hq0).1 hu
  have hrh0 : 0 ≤ rh := by rw [hrh]; positivity
  constructor
  · have hP211 : P ^ 2 ≤ P ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hA1 : (n : ℝ) ^ 2 * Real.sqrt f * g * rd ≤ P ^ 2 :=
      calc (n : ℝ) ^ 2 * Real.sqrt f * g * rd ≤ (n : ℝ) ^ 2 * f * g * rd := by gcongr
        _ = n * (n * f * rd * g) := by ring
        _ ≤ P ^ 2 := hnmP
    have h : (n : ℝ) ^ 2 * Real.sqrt f * g * rd * s ≤ P ^ 11 * s :=
      calc (n : ℝ) ^ 2 * Real.sqrt f * g * rd * s ≤ P ^ 2 * s := mul_le_mul_of_nonneg_right hA1 hs0
        _ ≤ P ^ 11 * s := mul_le_mul_of_nonneg_right hP211 hs0
    have hl := Real.log_two_gt_d9
    rw [hrh]
    linarith
  · have hAeq : 2 * rh * Real.sqrt f * be = ((n : ℝ) ^ 2 * f * g * rd * be / 2) * s := by
      rw [hrh]; linear_combination ((n : ℝ) ^ 2 * g * rd * s * be / 2) * hfs
    have hA16 : (2 * rh * Real.sqrt f * be) ^ (16 * q) ≤ P ^ (96 * q) * (2 * τ) ^ 16 := by
      rw [hAeq]
      calc (((n : ℝ) ^ 2 * f * g * rd * be / 2) * s) ^ (16 * q) ≤ (P ^ 6 * s) ^ (16 * q) :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hK hs0) _
        _ = P ^ (96 * q) * (2 * τ) ^ 16 := by
          rw [mul_pow, ← pow_mul, show 6 * (16 * q) = 96 * q by ring,
            show 16 * q = q * 16 by ring, pow_mul s q 16, hsq]
    have hW := deep_exponent_core P τ be n g q hP16 hq hτ hτP hbe0 hbe6 hn0 hnP hg0 hgP
    have hsq17 : (17 * Real.sqrt n / τ ^ 2) ^ 2 = 289 * (n : ℝ) / τ ^ 4 := by
      rw [div_pow, mul_pow, hs2, ← pow_mul]; norm_num
    have hexp : Real.exp f ≤ Real.exp 1 ^ N := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rw [hNr]
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 :=
        le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) (by linarith : (1 : ℝ) ≤ n) 2)
      linarith [mul_le_mul_of_nonneg_right h1 hf0]
    have e1 : (2 * rh * Real.sqrt f * be) ^ (2 * (8 * q * N))
        = ((2 * rh * Real.sqrt f * be) ^ (16 * q)) ^ N := by
      rw [← pow_mul]; congr 1; ring
    have e2 : (17 * Real.sqrt n / τ ^ 2) ^ (2 * N) = (289 * (n : ℝ) / τ ^ 4) ^ N := by
      rw [pow_mul, hsq17]
    have e3 : g ^ (2 * N) = (g ^ 2) ^ N := pow_mul g 2 N
    rw [e1, e2, e3]
    calc ((2 * rh * Real.sqrt f * be) ^ (16 * q)) ^ N
          * ((6 * be) ^ N * Real.exp f * (289 * (n : ℝ) / τ ^ 4) ^ N) * (g ^ 2) ^ N * P ^ N
        ≤ (P ^ (96 * q) * (2 * τ) ^ 16) ^ N
          * ((6 * be) ^ N * Real.exp 1 ^ N * (289 * (n : ℝ) / τ ^ 4) ^ N) * (g ^ 2) ^ N * P ^ N := by
          gcongr
      _ = ((P ^ (96 * q) * (2 * τ) ^ 16) * ((6 * be) * Real.exp 1 * (289 * (n : ℝ) / τ ^ 4))
            * g ^ 2 * P) ^ N := by
          simp only [mul_pow]
      _ ≤ Real.exp (-1) ^ N := pow_le_pow_left₀ (by positivity) hW N
      _ = Real.exp (-(N : ℝ)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRealSubmoduleBlockFinrankLe
section
open Finset

namespace GlobalTheory

theorem exists_real_submodule_block_finrank_le :
    ∀ (n : ℕ) (E E' : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ 2 * Module.finrank ℂ E' * Module.finrank ℂ E ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        E'.starProjection ∘L T ∘L E.starProjection ∈ U := by
  intro n E E'
  let f : (E →L[ℂ] E') →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E'.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun M N => by ext; simp
      map_smul' := fun c M => by ext; simp }
  refine ⟨LinearMap.range f, ?_, fun T => ⟨E'.orthogonalProjection ∘L T ∘L E.subtypeL, rfl⟩⟩
  refine (LinearMap.finrank_range_le f).trans (le_of_eq ?_)
  have h1 : Module.finrank ℂ (E →L[ℂ] E') = Module.finrank ℂ E * Module.finrank ℂ E' := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := E) (F' := E')).finrank_eq,
      Module.finrank_linearMap]
  rw [← Module.finrank_mul_finrank ℝ ℂ (E →L[ℂ] E'), Complex.finrank_real_complex, h1]
  ring

end GlobalTheory
end

