module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.AlmostSelfdual
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.almost_selfdual_swap {A : Type} [CommRing A] {F V : Type} [Field F]
    [Algebra A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V]
    (Bf : LinearMap.BilinForm F V) (hs : Bf.IsSymm) {M N : Submodule A V}
    (h : M ≤ Bf.dualSubmodule N) : N ≤ Bf.dualSubmodule M := by
  intro x hx
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  have h1 := (Bf.mem_dualSubmodule).1 (h hy) x hx
  rwa [hs.eq] at h1

private theorem UpperTheory.V.AlgebraTools.almost_selfdual_move {A : Type} [CommRing A] {F V : Type} [Field F]
    [Algebra A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V]
    (Bf : LinearMap.BilinForm F V) (I : Ideal A) {M N : Submodule A V}
    (h : I • M ≤ Bf.dualSubmodule N) : M ≤ Bf.dualSubmodule (I • N) := by
  intro x hx
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro z hz
  refine Submodule.smul_induction_on (p := fun z => Bf x z ∈ (1 : Submodule A F)) hz ?_ ?_
  · intro a ha n hn
    have h1 := (Bf.mem_dualSubmodule).1 (h (Submodule.smul_mem_smul ha hx)) n hn
    have e1 : Bf x (a • n) = algebraMap A F a * Bf x n := by
      rw [← algebraMap_smul F a n, map_smul, smul_eq_mul]
    have e2 : Bf (a • x) n = algebraMap A F a * Bf x n := by
      rw [← algebraMap_smul F a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
    show Bf x (a • n) ∈ (1 : Submodule A F)
    rw [e1, ← e2]
    exact h1
  · intro y z hy hz
    show Bf x (y + z) ∈ (1 : Submodule A F)
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz

private theorem UpperTheory.V.AlgebraTools.almost_selfdual_smul {A : Type} [CommRing A] {F V : Type} [Field F]
    [Algebra A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V]
    (f : Module.End F V) (I : Ideal A) {M : Submodule A V} (h : ∀ y ∈ M, f y ∈ M) :
    ∀ y ∈ I • M, f y ∈ I • M := by
  intro y hy
  refine Submodule.smul_induction_on (p := fun y => f y ∈ I • M) hy ?_ ?_
  · intro a ha n hn
    show f (a • n) ∈ I • M
    rw [← algebraMap_smul F a n, map_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul ha (h n hn)
  · intro y z hy hz
    show f (y + z) ∈ I • M
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz

private theorem UpperTheory.V.AlgebraTools.map_mem_dualSubmodule_of_bilinForm_similitude {A : Type} [CommRing A] {F V G : Type} [Field F]
    [Algebra A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Group G]
    (Bf : LinearMap.BilinForm F V) (r : G →* Module.End F V) (σ : G → G) (u : G → A)
    (hr : ∀ g y z, Bf (r g y) (r (σ g) z) = algebraMap A F (u g) * Bf y z)
    {Y : Submodule A V} (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) :
    ∀ g, ∀ y ∈ Bf.dualSubmodule Y, r g y ∈ Bf.dualSubmodule Y := by
  intro g y hy
  rw [LinearMap.BilinForm.mem_dualSubmodule] at hy ⊢
  intro z hz
  have hz' : r (σ g) (r (σ g)⁻¹ z) = z := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hy _ (hY _ _ hz))
  rw [← hz', hr, ← ha, ← map_mul]
  exact Submodule.mem_one.mpr ⟨_, rfl⟩

private theorem UpperTheory.V.AlgebraTools.end_apply_mem_sup_of_apply_mem {A : Type} [CommRing A] {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] [Module A V] (f : Module.End F V) {P Q : Submodule A V}
    (hP : ∀ y ∈ P, f y ∈ P) (hQ : ∀ y ∈ Q, f y ∈ Q) : ∀ y ∈ P ⊔ Q, f y ∈ P ⊔ Q := by
  intro y hy
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hP p hp) (hQ q hq)

private theorem UpperTheory.V.AlgebraTools.almost_selfdual_dual_full {A : Type} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] {F V : Type} [Field F] [Algebra A F]
    [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V]
    [Module.Finite F V] (Bf : LinearMap.BilinForm F V) (hnd : Bf.Nondegenerate)
    (Y : Submodule A V) (hY : Submodule.IsFullLattice F Y) :
    Submodule.IsFullLattice F (Bf.dualSubmodule Y) := by
  classical
  haveI : Module.Free A Y := Submodule.IsLattice.free F Y
  haveI : Module.Finite A Y := Submodule.IsLattice.finite F Y
  let b0 := Module.Free.chooseBasis A Y
  let b := b0.extendOfIsFullLattice F
  have hb : Submodule.span A (Set.range b) = Y := by
    have : (b : _ → V) = Y.subtype ∘ b0 := by
      funext i; simp [b]
    rw [this, Set.range_comp, ← Submodule.map_span, b0.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis Bf hnd b]
  exact { toIsLattice := Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range _))
          span_eq_top := by rw [Submodule.span_span_of_tower, Module.Basis.span_eq] }

theorem UpperTheory.V.AlgebraTools.almost_selfdual :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F V G : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Module.Finite F V] [Group G] (Bf : LinearMap.BilinForm F V) (r : G →* Module.End F V) (σ : G → G) (u : G → A), Bf.IsSymm → Bf.Nondegenerate → Function.Surjective σ → (∀ g y z, Bf (r g y) (r (σ g) z) = algebraMap A F (u g) * Bf y z) → ∀ Y₀ : Submodule A V, Submodule.IsFullLattice F Y₀ → (∀ g, ∀ y ∈ Y₀, r g y ∈ Y₀) → ∃ Y : Submodule A V, Submodule.IsFullLattice F Y ∧ (∀ g, ∀ y ∈ Y, r g y ∈ Y) ∧ (∀ g, ∀ y ∈ Bf.dualSubmodule Y, r g y ∈ Bf.dualSubmodule Y) ∧ Y ≤ Bf.dualSubmodule Y ∧ maximalIdeal A • Bf.dualSubmodule Y ≤ Y := by
  intro A _ _ _ F V G _ _ _ _ _ _ _ _ _ Bf r σ u hs hnd hσ hr Y₀ hY₀ hst₀
  classical
  have anti : ∀ {P Q : Submodule A V}, P ≤ Q → Bf.dualSubmodule Q ≤ Bf.dualSubmodule P :=
    fun hPQ x hx => (Bf.mem_dualSubmodule).2 fun y hy => (Bf.mem_dualSubmodule).1 hx y (hPQ hy)
  have dst : ∀ Y : Submodule A V, (∀ g, ∀ y ∈ Y, r g y ∈ Y) →
      ∀ g, ∀ y ∈ Bf.dualSubmodule Y, r g y ∈ Bf.dualSubmodule Y :=
    fun Y hY => UpperTheory.V.AlgebraTools.map_mem_dualSubmodule_of_bilinForm_similitude Bf r σ u hr hY
  have key : ∀ n : ℕ, ∀ Y : Submodule A V, Submodule.IsFullLattice F Y → (∀ g, ∀ y ∈ Y, r g y ∈ Y) →
      Y ≤ Bf.dualSubmodule Y → maximalIdeal A ^ n • Bf.dualSubmodule Y ≤ Y →
      ∃ Y : Submodule A V, Submodule.IsFullLattice F Y ∧ (∀ g, ∀ y ∈ Y, r g y ∈ Y) ∧
        (∀ g, ∀ y ∈ Bf.dualSubmodule Y, r g y ∈ Bf.dualSubmodule Y) ∧ Y ≤ Bf.dualSubmodule Y ∧
        maximalIdeal A • Bf.dualSubmodule Y ≤ Y := by
    intro n
    induction n with
    | zero =>
      intro Y hY hst hle hn
      refine ⟨Y, hY, hst, dst Y hst, hle, le_trans Submodule.smul_le_right ?_⟩
      simpa using hn
    | succ n ih =>
      intro Y hY hst hle hn
      rcases n with _ | k
      · exact ⟨Y, hY, hst, dst Y hst, hle, by simpa using hn⟩
      · have hDY := UpperTheory.V.AlgebraTools.almost_selfdual_dual_full Bf hnd Y hY
        have hDDY : Y ≤ Bf.dualSubmodule (Bf.dualSubmodule Y) :=
          UpperTheory.V.AlgebraTools.almost_selfdual_swap Bf hs le_rfl
        have hsm : maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y ≤ Bf.dualSubmodule Y :=
          Submodule.smul_le_right
        have hYW : Y ≤ Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y := le_sup_left
        have hWD : Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y ≤ Bf.dualSubmodule Y :=
          sup_le hle hsm
        have hWl : Submodule.IsFullLattice F (Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y) := by
          haveI := hY
          haveI := hDY
          refine Submodule.IsFullLattice.of_le_of_fg F hYW ?_
          haveI : Module.Finite A ↥(Bf.dualSubmodule Y) := Submodule.IsLattice.finite F _
          have : IsNoetherian A ↥(Bf.dualSubmodule Y) := inferInstance
          have : IsNoetherian A
              ↥(Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y : Submodule A V) :=
            isNoetherian_of_le hWD
          exact Module.Finite.iff_fg.mp inferInstance
        have hWst : ∀ g, ∀ y ∈ Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y,
            r g y ∈ Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y := fun g =>
          UpperTheory.V.AlgebraTools.end_apply_mem_sup_of_apply_mem (r g) (hst g)
            (UpperTheory.V.AlgebraTools.almost_selfdual_smul (r g) _ (dst Y hst g))
        have hsq : maximalIdeal A ^ (k + 1) • (maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y) ≤
            Bf.dualSubmodule (Bf.dualSubmodule Y) := by
          rw [← Submodule.mul_smul, ← pow_add]
          refine le_trans (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl)
            (le_trans hn hDDY)
        have hWW : Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y ≤
            Bf.dualSubmodule (Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y) := by
          refine sup_le (UpperTheory.V.AlgebraTools.almost_selfdual_swap Bf hs hWD) ?_
          refine UpperTheory.V.AlgebraTools.almost_selfdual_swap Bf hs (sup_le ?_ ?_)
          · exact UpperTheory.V.AlgebraTools.almost_selfdual_swap Bf hs hsm
          · exact UpperTheory.V.AlgebraTools.almost_selfdual_move Bf _ hsq
        have hWdual : maximalIdeal A ^ (k + 1) •
            Bf.dualSubmodule (Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y) ≤
            Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y :=
          le_trans (Submodule.smul_mono le_rfl (anti hYW)) le_sup_right
        exact ih _ hWl hWst hWW hWdual
  have hD₀ := UpperTheory.V.AlgebraTools.almost_selfdual_dual_full Bf hnd Y₀ hY₀
  haveI := hY₀
  haveI := hD₀
  have hY₁ : Submodule.IsFullLattice F (Y₀ ⊓ Bf.dualSubmodule Y₀) := inferInstance
  have hst₁ : ∀ g, ∀ y ∈ Y₀ ⊓ Bf.dualSubmodule Y₀, r g y ∈ Y₀ ⊓ Bf.dualSubmodule Y₀ :=
    fun g y hy => Submodule.mem_inf.mpr
      ⟨hst₀ g y (Submodule.mem_inf.mp hy).1, dst Y₀ hst₀ g y (Submodule.mem_inf.mp hy).2⟩
  have hle₁ : Y₀ ⊓ Bf.dualSubmodule Y₀ ≤ Bf.dualSubmodule (Y₀ ⊓ Bf.dualSubmodule Y₀) :=
    le_trans inf_le_right (anti inf_le_left)
  have hbound : ∀ Z : Submodule A V, Submodule.IsLattice F Z →
      ∃ s : ℕ, maximalIdeal A ^ s • Z ≤ Y₀ ⊓ Bf.dualSubmodule Y₀ := by
    first
    | exact (UpperTheory.V.AlgebraTools.dual_lattice Bf hs hnd _ hY₁).2.2
    | exact (UpperTheory.V.AlgebraTools.dual_lattice Bf hs hnd _ hY₁.toIsLattice).2.2
  have hdual : Submodule.IsFullLattice F (Bf.dualSubmodule (Y₀ ⊓ Bf.dualSubmodule Y₀)) :=
    UpperTheory.V.AlgebraTools.almost_selfdual_dual_full Bf hnd _ hY₁
  obtain ⟨s, hs'⟩ := hbound _ hdual.toIsLattice
  exact key s _ hY₁ hst₁ hle₁ hs'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplCo
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.isCO :
    ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (p₀ : Ideal R₀) (p : Ideal R)
      (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] [Algebra R₀ O] [Algebra R B]
      [Algebra O B] [Algebra R₀ B] [IsScalarTower R₀ R B] [IsScalarTower R₀ O B],
      IsCplAt R₀ p₀ O → IsCplAt R p B → p.comap (algebraMap R₀ R) = p₀ →
      (∀ x : R, ∃ a : R₀, x - algebraMap R₀ R a ∈ p) → UpperTheory.V.Alg.IsCO O B := by
  intro R₀ R _ _ _ p₀ p O B _ _ _ _ _ _ _ _ _ _ hO hB hp hsurj
  have hRB : ∀ r : R, algebraMap R B r ∈ maximalIdeal B ↔ r ∈ p := by
    intro r
    rw [← hB.comap_eq, Ideal.mem_comap]
  have h0B : ∀ c : R₀, algebraMap R₀ B c ∈ maximalIdeal B ↔ c ∈ p₀ := by
    intro c
    rw [IsScalarTower.algebraMap_apply R₀ R B, hRB, ← hp, Ideal.mem_comap]
  have hmO : Ideal.map (algebraMap O B) (maximalIdeal O) ≤ maximalIdeal B := by
    have hm := IsCplAt.map_pow_eq R₀ p₀ O hO 1
    rw [pow_one, pow_one] at hm
    rw [← hm, Ideal.map_map, ← IsScalarTower.algebraMap_eq R₀ O B, Ideal.map_le_iff_le_comap]
    intro c hc
    exact (h0B c).2 hc
  have hloc : IsLocalHom (algebraMap O B) := by
    refine ⟨fun o ho => ?_⟩
    by_contra hn
    exact (IsLocalRing.mem_maximalIdeal _).1
      (hmO (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hn))) ho
  have e : ∀ c : R₀, algebraMap O B (algebraMap R₀ O c) = algebraMap R B (algebraMap R₀ R c) := by
    intro c
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hres : ∀ x : B, ∃ o : O, x - algebraMap O B o ∈ maximalIdeal B := by
    intro x
    obtain ⟨a, s, hs, hx⟩ := hB.dense 1 x
    rw [pow_one] at hx
    obtain ⟨s₀, hs₀⟩ := hsurj s
    obtain ⟨a₀, ha₀⟩ := hsurj a
    have h1 : algebraMap R B s - algebraMap O B (algebraMap R₀ O s₀) ∈ maximalIdeal B := by
      rw [e, ← map_sub]
      exact (hRB _).2 hs₀
    have h2 : algebraMap R B a - algebraMap O B (algebraMap R₀ O a₀) ∈ maximalIdeal B := by
      rw [e, ← map_sub]
      exact (hRB _).2 ha₀
    have hsu : IsUnit (algebraMap O B (algebraMap R₀ O s₀)) := by
      by_contra hn
      have hm : algebraMap O B (algebraMap R₀ O s₀) ∈ maximalIdeal B :=
        (IsLocalRing.mem_maximalIdeal _).2 hn
      have hsum := Ideal.add_mem _ h1 hm
      rw [sub_add_cancel] at hsum
      exact hs ((hRB s).1 hsum)
    obtain ⟨u, hu⟩ := hloc.map_nonunit _ hsu
    refine ⟨↑u⁻¹ * algebraMap R₀ O a₀, ?_⟩
    have key : algebraMap O B (algebraMap R₀ O s₀) * x - algebraMap O B (algebraMap R₀ O a₀)
        ∈ maximalIdeal B := by
      have hid : algebraMap O B (algebraMap R₀ O s₀) * x - algebraMap O B (algebraMap R₀ O a₀) =
          (algebraMap R B s * x - algebraMap R B a)
            - (algebraMap R B s - algebraMap O B (algebraMap R₀ O s₀)) * x
            + (algebraMap R B a - algebraMap O B (algebraMap R₀ O a₀)) := by ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.sub_mem _ hx (Ideal.mul_mem_right _ _ h1)) h2
    have hinv : algebraMap O B ↑u⁻¹ * algebraMap O B ↑u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hid2 : x - algebraMap O B (↑u⁻¹ * algebraMap R₀ O a₀) = algebraMap O B ↑u⁻¹ *
        (algebraMap O B (algebraMap R₀ O s₀) * x - algebraMap O B (algebraMap R₀ O a₀)) := by
      rw [← hu, map_mul]
      linear_combination (-x) * hinv
    rw [hid2]
    exact Ideal.mul_mem_left _ _ key
  haveI := hB.noeth
  exact UpperTheory.V.Alg.IsCO.mk hB.complete hloc hres
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift
section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem level_map {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) (n : ℕ) {D : Type} [CommRing D]
    (g : R →+* D) (hu : ∀ s, s ∉ p → IsUnit (g s)) (hz : ∀ a, a ∈ p ^ n → g a = 0) :
    ∃ f : B →+* D, ∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g s * f b = g a := by
  have hP := h.isPrime
  choose A S hS hAS using h.dense n
  have wd : ∀ (b : B) (a s a' s' : R), s ∉ p → s' ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n →
      algebraMap R B s' * b - algebraMap R B a' ∈ maximalIdeal B ^ n → g s * g a' = g s' * g a := by
    intro b a s a' s' _ hs' h1 h2
    have hm : algebraMap R B (s * a' - s' * a) ∈ maximalIdeal B ^ n := by
      have hid : algebraMap R B (s * a' - s' * a) = algebraMap R B s' *
          (algebraMap R B s * b - algebraMap R B a) - algebraMap R B s *
          (algebraMap R B s' * b - algebraMap R B a') := by
        simp only [map_sub, map_mul]
        ring
      rw [hid]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    obtain ⟨t, ht, hta⟩ := h.strict n _ hm
    have h0 := hz _ hta
    rw [map_mul, (hu t ht).mul_right_eq_zero, map_sub, map_mul, map_mul, sub_eq_zero] at h0
    exact h0
  let F : B → D := fun b => ↑(hu _ (hS b)).unit⁻¹ * g (A b)
  have hF0 : ∀ b, g (S b) * F b = g (A b) := by
    intro b
    simp only [F, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have spec : ∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g s * F b = g a := by
    intro b a s hs hb
    apply (hu _ (hS b)).mul_left_cancel
    rw [← mul_assoc, mul_comm (g (S b)), mul_assoc, hF0, wd b (A b) (S b) a s (hS b) hs (hAS b) hb]
  have eq_of : ∀ (b : B) (y : D) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g a = g s * y → F b = y := by
    intro b y a s hs hb hy
    exact (hu s hs).mul_left_cancel ((spec b a s hs hb).trans hy)
  have hprod : ∀ x y : B, S x * S y ∉ p := fun x y hm => (hP.mem_or_mem hm).elim (hS x) (hS y)
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, spec⟩
  · refine eq_of 1 1 1 1 ?_ ?_ (by simp)
    · intro h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · simp
  · intro x y
    refine eq_of (x * y) _ (A x * A y) (S x * S y) (hprod x y) ?_ ?_
    · have hid : algebraMap R B (S x * S y) * (x * y) - algebraMap R B (A x * A y) =
          algebraMap R B (S x) * x * (algebraMap R B (S y) * y - algebraMap R B (A y)) +
          algebraMap R B (A y) * (algebraMap R B (S x) * x - algebraMap R B (A x)) := by
        simp only [map_mul]
        ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hAS y)) (Ideal.mul_mem_left _ _ (hAS x))
    · show g (A x * A y) = g (S x * S y) * (F x * F y)
      rw [map_mul, map_mul, ← hF0 x, ← hF0 y]
      ring
  · refine eq_of 0 0 0 1 ?_ ?_ (by simp)
    · intro h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · simp
  · intro x y
    refine eq_of (x + y) _ (S y * A x + S x * A y) (S x * S y) (hprod x y) ?_ ?_
    · have hid : algebraMap R B (S x * S y) * (x + y) - algebraMap R B (S y * A x + S x * A y) =
          algebraMap R B (S y) * (algebraMap R B (S x) * x - algebraMap R B (A x)) +
          algebraMap R B (S x) * (algebraMap R B (S y) * y - algebraMap R B (A y)) := by
        simp only [map_mul, map_add (f := _)]
        ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hAS x)) (Ideal.mul_mem_left _ _ (hAS y))
    · show g (S y * A x + S x * A y) = g (S x * S y) * (F x + F y)
      rw [map_add (f := _), map_mul, map_mul, map_mul, ← hF0 x, ← hF0 y]
      ring

theorem UpperTheory.V.AlgebraTools.IsCplAt.existsUnique_lift :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B →
      ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C] (φ : R →+* C),
      (maximalIdeal C).comap φ = p → ∃! ψ : B →+* C, ψ.comp (algebraMap R B) = φ := by
  intro R _ p B _ _ _ hB C _ _ _ φ hφ
  have hpI : ∀ n, ∀ a ∈ p ^ n, φ a ∈ maximalIdeal C ^ n := by
    intro n a ha
    have hle : Ideal.map φ p ≤ maximalIdeal C := by
      rw [← hφ]
      exact Ideal.map_comap_le
    have hmap : Ideal.map φ (p ^ n) ≤ maximalIdeal C ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hle n
    exact hmap (Ideal.mem_map_of_mem φ ha)
  have hunit : ∀ s, s ∉ p → IsUnit (φ s) := by
    intro s hs
    by_contra hn
    apply hs
    rw [← hφ, Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).2 hn
  let g : ∀ n, R →+* C ⧸ maximalIdeal C ^ n := fun n => (Ideal.Quotient.mk (maximalIdeal C ^ n)).comp φ
  have hu : ∀ n s, s ∉ p → IsUnit (g n s) := fun n s hs =>
    (hunit s hs).map (Ideal.Quotient.mk (maximalIdeal C ^ n))
  have hz : ∀ n a, a ∈ p ^ n → g n a = 0 := fun n a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hpI n a ha)
  choose f hf using fun n => level_map hB n (g n) (hu n) (hz n)
  have lvl : ∀ n (k : B → C ⧸ maximalIdeal C ^ n), (∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g n s * k b = g n a) →
      ∀ b, k b = f n b := by
    intro n k hk b
    obtain ⟨a, s, hs, hb⟩ := hB.dense n b
    exact (hu n s hs).mul_left_cancel ((hk b a s hs hb).trans (hf n b a s hs hb).symm)
  have compat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal C) hle).comp (f n) = f m := by
    intro m n hle
    ext b
    obtain ⟨a, s, hs, hb⟩ := hB.dense n b
    have hbm : algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ m :=
      Ideal.pow_le_pow_right hle hb
    apply (hu m s hs).mul_left_cancel
    show g m s * Ideal.Quotient.factorPow (maximalIdeal C) hle (f n b) = g m s * f m b
    rw [hf m b a s hs hbm]
    have hc := congrArg (Ideal.Quotient.factorPow (maximalIdeal C) hle) (hf n b a s hs hb)
    rw [map_mul] at hc
    have hg : ∀ x, Ideal.Quotient.factorPow (maximalIdeal C) hle (g n x) = g m x := by
      intro x
      simp [g]
    rw [hg, hg] at hc
    exact hc
  have h1p : (1 : R) ∉ p := fun h1 => hB.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hmk : ∀ n b, Ideal.Quotient.mk (maximalIdeal C ^ n)
      (IsAdicComplete.liftRingHom (maximalIdeal C) f compat b) = f n b :=
    fun n b => IsAdicComplete.mk_liftRingHom (maximalIdeal C) f compat n b
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal C) f compat, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.funext' (maximalIdeal C)
    intro n r
    rw [RingHom.comp_apply, hmk]
    apply (hu n 1 h1p).mul_left_cancel
    rw [hf n (algebraMap R B r) r 1 h1p (by simp), map_one, one_mul]
    rfl
  · intro ψ' hψ'
    apply IsAdicComplete.eq_liftRingHom (maximalIdeal C) f compat ψ'
    intro n
    ext b
    rw [RingHom.comp_apply]
    refine lvl n (fun b => Ideal.Quotient.mk (maximalIdeal C ^ n) (ψ' b)) ?_ b
    intro b a s hs hb
    have hmap : Ideal.map ψ' (maximalIdeal B ^ n) ≤ maximalIdeal C ^ n := by
      rw [← IsCplAt.map_pow_eq R p B hB n, Ideal.map_map, hψ', Ideal.map_le_iff_le_comap]
      intro c hc
      exact hpI n c hc
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 (hmap (Ideal.mem_map_of_mem _ hb))
    have e : ∀ x, ψ' (algebraMap R B x) = φ x := fun x => by rw [← RingHom.comp_apply, hψ']
    rw [map_sub, map_mul, e, e, map_sub, map_mul, sub_eq_zero] at h0
    exact h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaFlatReg
section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem flat_regular_cotangent_extension
    (A B : Type) [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B))]
    (κ : Type) [Fintype κ] (x : κ → A) (hx : CotInd A x) :
    ∃ (s t : ℕ) (z : (κ ⊕ Fin s) ⊕ Fin t → B), (∀ k, z (Sum.inl (Sum.inl k)) = algebraMap A B (x k)) ∧
      Ideal.span (Set.range z) = maximalIdeal B ∧
      ((Fintype.card ((κ ⊕ Fin s) ⊕ Fin t) : ℕ) : WithBot ℕ∞) = ringKrullDim B := by
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  obtain ⟨s, y, -, hy, hs⟩ := cotInd_extend A κ x hx
  obtain ⟨t, w, -, hw, ht⟩ := cotInd_extend (B ⧸ I) Empty (fun e => e.elim)
    ⟨fun e => e.elim, fun _ _ e => e.elim⟩
  choose v hv using fun j => Ideal.Quotient.mk_surjective (w j)
  have hw' : Ideal.span (Set.range w) = maximalIdeal (B ⧸ I) := by
    rw [← hw, Set.Sum.elim_range, Set.range_eq_empty (ι := Empty), Set.empty_union]
  have hmap : (maximalIdeal B).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hIle : I ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le _
  refine ⟨s, t, Sum.elim (fun i => algebraMap A B (Sum.elim x y i)) v, fun k => rfl, ?_, ?_⟩
  · rw [Set.Sum.elim_range, Ideal.span_union]
    have h1 : Ideal.span (Set.range fun i => algebraMap A B (Sum.elim x y i)) = I := by
      rw [hI, ← hy, Ideal.map_span, ← Set.range_comp]
      rfl
    have h2 : (Ideal.span (Set.range v)).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) := by
      rw [Ideal.map_span, ← Set.range_comp, ← hw']
      congr 2
      funext j
      exact hv j
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk I)) (h2.trans hmap.symm)
    rw [Ideal.comap_map_quotientMk, Ideal.comap_map_quotientMk, sup_eq_right.2 hIle] at h3
    rw [h1, h3]
  · haveI : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
    have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
    rw [← hI, hmap] at H
    have H' := congrArg (fun a : ℕ∞ => (a : WithBot ℕ∞)) H
    simp only [WithBot.coe_add, IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at H'
    rw [H', ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A),
      ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := B ⧸ I), ← hs, ← ht]
    simp

theorem UpperTheory.V.AlgebraTools.regular_of_flat_fibre :
    ∀ (A B : Type) [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
      [IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B))],
      IsRegularLocalRing B ∧ ∀ (κ : Type) [Fintype κ] (x : κ → A), CotInd A x → CotInd B (fun k => algebraMap A B (x k)) := by
  intro A B _ _ _ _ _ _ _ _ _
  constructor
  · obtain ⟨s, t, z, -, hz, hc⟩ := flat_regular_cotangent_extension A B Empty (fun e => e.elim)
      ⟨fun e => e.elim, fun _ _ e => e.elim⟩
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hc, ← hz, Nat.cast_le]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
    rw [← Set.image_univ, ← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_image_le
  · intro κ _ x hx
    obtain ⟨s, t, z, hzx, hz, hc⟩ := flat_regular_cotangent_extension A B κ x hx
    have h1 := ringKrullDim_le_spanFinrank_maximalIdeal B
    rw [← hc, Nat.cast_le] at h1
    have h2 := (cotInd_of_span B _ z hz h1).comp (fun k : κ => Sum.inl (Sum.inl k))
      (Sum.inl_injective.comp Sum.inl_injective)
    have h3 : (z ∘ fun k : κ => Sum.inl (Sum.inl k)) = fun k => algebraMap A B (x k) := funext hzx
    rwa [h3] at h2
end

