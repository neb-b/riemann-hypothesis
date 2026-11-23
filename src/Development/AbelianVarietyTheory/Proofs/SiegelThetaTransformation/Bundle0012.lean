module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExOfPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClassesSelfDualOfSelfDual
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace SelfDualClasses

open ShortVectors

noncomputable def hermRat (n : ℕ) : (Fin n → E) →ₗ[ℚ] (Fin n → E) →ₗ[ℚ] E :=
  LinearMap.mk₂ ℚ (fun x y => herm 1 x y)
    (fun x x' y => by simp [DualFamily.herm_one_eq, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [DualFamily.herm_one_eq, Finset.smul_sum])
    (fun x y y' => by simp [DualFamily.herm_one_eq, cc, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp [DualFamily.herm_one_eq, Finset.smul_sum, cc, Rat.smul_def, mul_left_comm])

theorem hermRat_apply {n : ℕ} (x y : Fin n → E) : hermRat n x y = herm 1 x y := rfl

theorem exists_isometry {n : ℕ} {ι : Type} (b b' : Basis ι ℚ (Fin n → E))
    (h : ∀ i j, herm 1 (b' i) (b' j) = herm 1 (b i) (b j)) :
    ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧
      ∀ i, γ (b i) = b' i := by
  let g : (Fin n → E) ≃ₗ[ℚ] (Fin n → E) := b.equiv b' (Equiv.refl ι)
  have hg : ∀ x y, herm 1 (g x) (g y) = herm 1 x y := by
    have : (hermRat n).compl₁₂ g.toLinearMap g.toLinearMap = hermRat (E := E) n :=
      LinearMap.ext_basis b b fun i j => by simp [g, hermRat_apply, h]
    intro x y
    exact LinearMap.congr_fun₂ this x y
  have hs : ∀ (c : E) x, g (c • x) = c • g x := by
    intro c x
    rw [← sub_eq_zero]
    refine (traceHerm_nondegenerate n).1 _ fun z => ?_
    obtain ⟨y, rfl⟩ := g.surjective z
    rw [map_sub, LinearMap.sub_apply, traceHerm_apply, traceHerm_apply, hg,
      TraceDualMin.herm_smul_left, TraceDualMin.herm_smul_left, hg, sub_self]
  exact ⟨{ g.toAddEquiv with map_smul' := hs }, hg, fun i => by simp [g]⟩

theorem finite_integral_of_basis {n : ℕ} {ι : Type} [Fintype ι] (b : Basis ι ℚ (Fin n → E)) :
    {Λ : Submodule (𝓞 E) (Fin n → E) | (∀ i, b i ∈ Λ) ∧
      ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)}.Finite := by
  classical
  let L₀ : Submodule ℤ (Fin n → E) := span ℤ (Set.range b)
  let L₁ : Submodule ℤ (Fin n → E) := (traceHerm n).dualSubmodule L₀
  have hfg : L₁.FG := by
    simp only [L₁, L₀]
    rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ (traceHerm_nondegenerate n)]
    exact fg_span (Set.finite_range _)
  have : Module.Finite ℤ L₁ := Module.Finite.iff_fg.mpr hfg
  have : Finite (L₁ ⧸ L₀.submoduleOf L₁) := Module.finite_of_fg_torsion _ fun q => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hx : (x : Fin n → E) ∈ span ℚ (Set.range b) := b.mem_span _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors ℤ) ℚ _ _ hx
    refine ⟨t, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ht
  have h0 : ∀ Λ : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) → ∀ x ∈ L₀, x ∈ Λ := by
    intro Λ hΛ
    have : L₀ ≤ Λ.restrictScalars ℤ := span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hΛ i)
    exact this
  have h1 : ∀ Λ : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → ∀ x ∈ Λ, x ∈ L₁ := by
    intro Λ hΛ hint x hx y hy
    have := Algebra.isIntegral_trace (L := ℚ) (hint x hx y (h0 Λ hΛ y hy))
    rw [Submodule.mem_one]
    exact IsIntegrallyClosed.isIntegral_iff.mp this
  let F : Submodule (𝓞 E) (Fin n → E) → Set (L₁ ⧸ L₀.submoduleOf L₁) :=
    fun Λ => {q | ∃ x : L₁, (x : Fin n → E) ∈ Λ ∧ Submodule.Quotient.mk x = q}
  have key : ∀ Λ Λ' : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → (∀ i, b i ∈ Λ') → F Λ = F Λ' → Λ ≤ Λ' := by
    intro Λ Λ' hΛ hint hΛ' hF x hx
    have : Submodule.Quotient.mk ⟨x, h1 Λ hΛ hint x hx⟩ ∈ F Λ := ⟨_, hx, rfl⟩
    rw [hF] at this
    obtain ⟨y, hy, hq⟩ := this
    rw [Submodule.Quotient.eq] at hq
    have h2 : (y : Fin n → E) - x ∈ Λ' := h0 Λ' hΛ' _ hq
    simpa using Λ'.sub_mem hy h2
  refine Set.Finite.of_finite_image (f := F) (Set.toFinite _) ?_
  rintro Λ ⟨hΛ, hi⟩ Λ' ⟨hΛ', hi'⟩ hF
  exact le_antisymm (key _ _ hΛ hi hΛ' hF) (key _ _ hΛ' hi' hΛ hF.symm)

theorem norm_herm_le {n : ℕ} (τ : E →+* ℂ) (x y : Fin n → E) (C : ℝ)
    (hx : ∑ k, ‖τ (x k)‖ ^ 2 ≤ C) (hy : ∑ k, ‖τ (y k)‖ ^ 2 ≤ C) : ‖τ (herm 1 x y)‖ ≤ C := by
  have h : ‖τ (herm 1 x y)‖ ≤ ∑ k, (‖τ (x k)‖ ^ 2 + ‖τ (y k)‖ ^ 2) / 2 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [DualFamily.herm_one_eq, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have : ‖τ (cc (y k))‖ = ‖τ (y k)‖ := by
      simp [cc, IsCMField.complexEmbedding_complexConj]
    rw [map_mul, norm_mul, this]
    nlinarith [sq_nonneg (‖τ (x k)‖ - ‖τ (y k)‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at h
  linarith

theorem finite_linearMap {R M T : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup T] [Module R T] [Module.Finite R M] [Finite T] : Finite (M →ₗ[R] T) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R M
  refine Finite.of_injective
    (fun (g : M →ₗ[R] T) (i : Fin m) => g (f (Pi.basisFun R (Fin m) i))) fun g g' h => ?_
  rw [← LinearMap.cancel_right hf]
  exact (Pi.basisFun R (Fin m)).ext fun i => congrFun h i

end SelfDualClasses


open SelfDualClasses in
theorem finite_classes_selfDual_of_selfDual (n : ℕ) :
    ∃ S : Finset (Submodule (𝓞 E) (Fin n → E)),
    (∀ Λ ∈ S, Λ.FG ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) →
    ∃ Λ₀ ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∀ x, x ∈ Λ₀ ↔ γ x ∈ Λ := by
  classical
  set C : ℝ := (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) ^ 2 with hC
  let ι := Fin (2 * fdeg E * n)
  let A : Set E := {x | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C}
  have hA : A.Finite := Embeddings.finite_of_norm_le E ℂ C
  let gram : Basis ι ℚ (Fin n → E) → ι → ι → E := fun b i j => herm 1 (b i) (b j)
  let B : Set (Basis ι ℚ (Fin n → E)) := {b | ∀ i j, gram b i j ∈ A}
  have hG : (gram '' B).Finite := by
    refine (Set.Finite.pi' fun _ : ι => Set.Finite.pi' fun _ : ι => hA).subset ?_
    rintro _ ⟨b, hb, rfl⟩
    exact hb
  obtain ⟨B₀, -, hB₀fin, hB₀⟩ := Set.exists_subset_image_finite_and.mp
    (⟨gram '' B, subset_rfl, hG, rfl⟩ : ∃ t ⊆ gram '' B, t.Finite ∧ t = gram '' B)
  have hS : {Λ : Submodule (𝓞 E) (Fin n → E) | (∃ b ∈ B₀, ∀ i, b i ∈ Λ) ∧ Λ.FG ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ}.Finite := by
    refine (hB₀fin.biUnion fun b _ => finite_integral_of_basis b).subset ?_
    rintro Λ ⟨⟨b, hb, hbΛ⟩, -, hi, -⟩
    exact Set.mem_biUnion hb ⟨hbΛ, hi⟩
  refine ⟨hS.toFinset, fun Λ hΛ => (hS.mem_toFinset.mp hΛ).2, fun Λ hfg hint hdual => ?_⟩
  obtain ⟨v, hv, hli, hsp, hle⟩ := exists_short_vectors Λ hfg hint hdual
  let b : Basis ι ℚ (Fin n → E) := Basis.mk hli hsp.ge
  have hb : ∀ i, b i = v i := fun i => Basis.mk_apply _ _ i
  have hbB : gram b ∈ gram '' B₀ := by
    rw [hB₀]
    refine ⟨b, fun i j => ?_, rfl⟩
    simp only [gram, hb]
    exact ⟨hint _ (hv i) _ (hv j), fun φ => norm_herm_le φ _ _ C (hle i φ) (hle j φ)⟩
  obtain ⟨b₀, hb₀, hgram⟩ := hbB
  obtain ⟨γ, hγ, hγb⟩ := exists_isometry b₀ b fun i j => (congrFun₂ hgram i j).symm
  let γ' : (Fin n → E) ≃ₗ[𝓞 E] (Fin n → E) := γ.restrictScalars (𝓞 E)
  refine ⟨Λ.comap γ'.toLinearMap, hS.mem_toFinset.mpr ⟨⟨b₀, hb₀, fun i => ?_⟩, ?_, ?_, ?_⟩,
    γ, hγ, fun x => Iff.rfl⟩
  · change γ (b₀ i) ∈ Λ
    rw [hγb, hb]
    exact hv i
  · rw [Submodule.comap_equiv_eq_map_symm]
    exact hfg.map _
  · intro x hx y hy
    rw [← hγ]
    exact hint _ hx _ hy
  · intro x hx
    refine hdual (γ x) fun y hy => ?_
    obtain ⟨z, rfl⟩ := γ.surjective y
    rw [hγ]
    exact hx z hy

theorem finite_classes_selfDual_pairs (n : ℕ) (T : Type) [AddCommGroup T] [Module (𝓞 E) T]
    [Finite T] :
    ∃ S : Finset (Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T),
    (∀ P ∈ S, P.1.FG ∧ (∀ x ∈ P.1, ∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) → x ∈ P.1) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) → ∀ f : Λ →ₗ[𝓞 E] T,
    ∃ P ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∃ h : ∀ x, x ∈ P.1 ↔ γ x ∈ Λ,
        ∀ x : P.1, P.2 x = f ⟨γ x, (h x).mp x.2⟩ := by
  classical
  obtain ⟨S, hS, hcl⟩ := finite_classes_selfDual_of_selfDual (E := E) n
  have hfin : {P : Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T | P.1 ∈ S}.Finite := by
    refine (S.finite_toSet.biUnion (t := fun Λ => Set.range
      fun f : Λ →ₗ[𝓞 E] T => (⟨Λ, f⟩ : Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T))
      fun Λ hΛ => ?_).subset ?_
    · have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr (hS Λ hΛ).1
      have : Finite (Λ →ₗ[𝓞 E] T) := SelfDualClasses.finite_linearMap
      exact Set.finite_range _
    · rintro ⟨Λ, f⟩ h
      exact Set.mem_biUnion h ⟨f, rfl⟩
  refine ⟨hfin.toFinset, fun P hP => hS _ (hfin.mem_toFinset.mp hP), fun Λ h1 h2 h3 f => ?_⟩
  obtain ⟨Λ₀, hΛ₀, γ, hγ, h⟩ := hcl Λ h1 h2 h3
  exact ⟨⟨Λ₀, f ∘ₗ (γ.restrictScalars (𝓞 E)).toLinearMap.restrict fun x hx => (h x).mp hx⟩,
    hfin.mem_toFinset.mpr hΛ₀, γ, hγ, h, fun x => rfl⟩

theorem finite_classes_selfDual_level (n N : ℕ) (hN : N ≠ 0) :
    ∃ S : Finset (Σ Λ : Submodule (𝓞 E) (Fin n → E),
      Λ →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})),
    (∀ P ∈ S, P.1.FG ∧ (∀ x ∈ P.1, ∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) → x ∈ P.1) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) →
    ∀ f : Λ →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}),
    ∃ P ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∃ h : ∀ x, x ∈ P.1 ↔ γ x ∈ Λ,
        ∀ x : P.1, P.2 x = f ⟨γ x, (h x).mp x.2⟩ := by
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  exact finite_classes_selfDual_pairs n _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualVacuumGaussianShapeRootOfUnityPhases
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.VacShape

open GlobalTheory.SW.Vac

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, pow_mul' b, hb, ← pow_mul,
    ← pow_mul, mul_comm n m]

theorem isMu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [mul_pow, pow_mul a, ha, pow_mul' b, hb]; simp

theorem ph_of_isMu {a : ℂ} (ha : IsMu a) : Ph a := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [← Complex.ofReal_pow, ← norm_pow, ha]; simp

theorem isMu_ex (q : ℚ) : IsMu (ex q) := by
  refine ⟨2 * q.den, Nat.mul_pos two_pos q.den_pos, ?_⟩
  rw [ex, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨q.num, ?_⟩
  have : (q.den : ℂ) * (q : ℂ) = q.num := by exact_mod_cast Rat.den_mul_eq_num q
  rw [← this]; push_cast; ring

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}

omit [DecidableEq ι] in
theorem semi' (h : VacS A ε φ) : ∀ y ∈ A, ∀ y' ∈ A,
    ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2) := by
  intro y hy y' hy'
  rw [h.semi y hy y' hy', om, om_eq, ex]

omit [DecidableEq ι] in
theorem isMu_eps (h : VacS A ε φ) {y} (hy : y ∈ A) : IsMu (ε y) := by
  obtain ⟨m, hm, hm'⟩ := h.ord
  have h0 : ε 0 = 1 := by simpa using hm' 0 A.zero_mem
  have hpow : ∀ n : ℕ, ε (n • y) = ε y ^ n := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact h0
    | succ n ih =>
      rw [succ_nsmul, semi' h _ (A.nsmul_mem hy n) _ hy, ih, pow_succ, Prod.smul_fst, Prod.smul_snd,
        ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, pr_smul_left, pr_smul_right,
        sub_self, ex_zero, mul_one]
  exact ⟨m, hm, by rw [← hpow, hm' y hy]⟩

theorem shape_at (h : VacS A ε φ) (a : Matrix κ ι ℚ) (ha : φ a ≠ 0) :
    ∃ (S : AddSubgroup (Matrix κ ι ℚ)) (f : Matrix κ ι ℚ → ℂ), Quad S f ∧
      ∀ x, (x - a ∈ S → φ x = φ a * f (x - a)) ∧ (x - a ∉ S → φ x = 0) := by
  have hfix : ∀ y ∈ A, ∀ x, fac ε y x * φ (x - y.2) = φ x := fun y hy =>
    (fixed_iff ε y φ).1 (h.fix y hy)
  let f : Matrix κ ι ℚ → ℂ := fun b => φ (a + b) / φ a
  have hf : ∀ y ∈ A, f y.2 = fac ε y (a + y.2) := by
    intro y hy
    simp only [f]
    rw [← hfix y hy (a + y.2), add_sub_cancel_right, mul_div_cancel_right₀ _ ha]
  have hadd : ∀ y ∈ A, ∀ y' ∈ A, f (y.2 + y'.2) = f y.2 * f y'.2 * ex (2 * pr y'.2 y.1) := by
    intro y hy y' hy'
    have := hf _ (A.add_mem hy hy')
    rw [Prod.snd_add, fac_add (semi' h y hy y' hy')] at this
    rw [this, hf y hy, hf y' hy', show a + (y.2 + y'.2) - y.2 = a + y'.2 by abel, mul_right_comm]
    congr 1
    unfold fac
    rw [mul_assoc, ← ex_add]
    congr 2
    simp only [pr_add_left]; ring
  refine ⟨A.map (AddMonoidHom.snd _ _), f, ⟨?_, ?_⟩, fun x => ⟨fun _ => ?_, fun hx => ?_⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    change IsMu (f y.2)
    rw [hf y hy]
    exact isMu_mul (isMu_eps h hy) (isMu_ex _)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    change f (x.2 + y.2 + z.2) * f x.2 * f y.2 * f z.2 =
      f (x.2 + y.2) * f (y.2 + z.2) * f (x.2 + z.2) * f 0
    have h0 : f 0 = 1 := by simp [f, ha]
    have h1 := hadd _ (A.add_mem hx hy) z hz
    rw [Prod.snd_add, Prod.fst_add, pr_add_right, mul_add, ex_add] at h1
    rw [h1, hadd y hy z hz, hadd x hx z hz, h0]
    ring
  · simp only [f]
    rw [add_sub_cancel, mul_div_cancel₀ _ ha]
  · by_contra hne
    apply hx
    have hd : ∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, pr y.1 y'.2 - pr y'.1 y.2 = m := by
      intro y
      simpa only [om, om_eq] using h.dual y
    have key : ∀ b, (b, 0) ∈ A → ∀ w, φ w ≠ 0 → ε (b, 0) * ex (2 * pr w b) = 1 := by
      intro b hb w hw
      have h1 := hfix _ hb w
      simp only [sub_zero, fac, pr_zero_right] at h1
      apply mul_right_cancel₀ hw; rw [h1, one_mul]
    obtain ⟨b, hb⟩ := exists_lift A h.fg hd (x - a) fun b hb => by
      have h2 := key b hb x hne
      have h3 := key b hb a ha
      apply ex_two_eq_one
      calc _ = ε (b, 0) * ex (2 * pr a b) * ex (2 * pr (x - a) b) := by rw [h3, one_mul]
        _ = ε (b, 0) * ex (2 * pr x b) := by
          rw [mul_assoc, ← ex_add, pr_sub_left]; congr 2; ring
        _ = 1 := h2
    exact ⟨_, hb, rfl⟩

theorem vac_smul (h : VacS A ε φ) (u : ℂ) : VacS A ε (u • φ) := by
  refine ⟨h.fg, h.dual, h.norm, h.semi, h.ord, ?_, fun y hy => ?_⟩
  · obtain ⟨R, hR, h1, h2⟩ := h.sb
    refine ⟨R, hR, fun x hx => h1 x fun e => hx (by simp [e]), fun x z hz => ?_⟩
    simp only [Pi.smul_apply, h2 x z hz]
  · rw [fixed_iff]
    intro x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, (fixed_iff ε y φ).1 (h.fix y hy) x]

theorem pv_of_ph (h : VacS A ε φ) (a : Matrix κ ι ℚ) (ha : φ a ≠ 0) (hp : Ph (φ a)) : PV φ := by
  refine ⟨⟨A, ε, h⟩, fun x => ?_⟩
  obtain ⟨S, f, hq, hx⟩ := shape_at h a ha
  by_cases hS : x - a ∈ S
  · rw [(hx x).1 hS]; exact ph_mul hp (ph_of_isMu (hq.1 _ hS))
  · rw [(hx x).2 hS]; exact ph_zero

theorem vacuum_shape : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, (∀ A ε, VacS A ε φ → ∀ a, φ a ≠ 0 → ∃ (S : AddSubgroup (Matrix κ ι ℚ)) (f : Matrix κ ι ℚ → ℂ), Quad S f ∧ ∀ x, (x - a ∈ S → φ x = φ a * f (x - a)) ∧ (x - a ∉ S → φ x = 0)) ∧ (PV φ → Shape φ) ∧ (∀ A ε, VacS A ε φ → ∃ u : ℂ, ‖u‖ = 1 ∧ PV (u • φ)) ∧ (PV φ → ∀ u : ℂ, Ph u → PV (u • φ)) ∧ ∀ A ε, VacS A ε φ → ∀ a, φ a ≠ 0 → Ph (φ a) → PV φ := by
  intro κ ι _ _ _ φ
  refine ⟨fun A ε h a ha => shape_at h a ha, ?_, fun A ε h => ?_, ?_,
    fun A ε h a ha hp => pv_of_ph h a ha hp⟩
  · rintro ⟨⟨A, ε, h⟩, hp⟩
    refine ⟨h.sb, ?_⟩
    by_cases h0 : ∃ a, φ a ≠ 0
    · obtain ⟨a, ha⟩ := h0
      obtain ⟨S, f, hq, hx⟩ := shape_at h a ha
      refine ⟨φ a, a, S, f, hp a, hq, fun x => ?_⟩
      split_ifs with hS
      · exact (hx x).1 hS
      · exact (hx x).2 hS
    · push Not at h0
      exact ⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩,
        fun x => by simp [h0]⟩
  · by_cases h0 : ∃ a, φ a ≠ 0
    · obtain ⟨a, ha⟩ := h0
      have hn : ‖φ a‖ ≠ 0 := norm_ne_zero_iff.2 ha
      have e : ((((‖φ a‖ : ℝ) : ℂ) / φ a) • φ) a = ((‖φ a‖ : ℝ) : ℂ) := by
        rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ ha]
      refine ⟨((‖φ a‖ : ℝ) : ℂ) / φ a, by simp [hn], pv_of_ph (vac_smul h _) a ?_ ?_⟩
      · rw [e]; exact_mod_cast hn
      · rw [e]; exact ⟨1, one_pos, by simp⟩
    · push Not at h0
      exact ⟨1, norm_one, ⟨A, ε, vac_smul h _⟩, fun x => by simpa [h0] using ph_zero⟩
  · rintro ⟨⟨A, ε, h⟩, hp⟩ u hu
    exact ⟨⟨A, ε, vac_smul h _⟩, fun x => ph_mul hu (hp x)⟩

end GlobalTheory.Phase.VacShape
end

