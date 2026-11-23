module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsLatticeEqAddSmulOfStableFgSubmodule
section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule :
    ∀ {G O LL V : Type} [Group G] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (ρ : Representation LL G V)
      (Λ : Lattice (O := O) ρ) (A : Submodule O V), A.FG → (∀ g, ∀ a ∈ A, ρ g a ∈ A) → ∀ μ : O, μ ≠ 0 →
      ∃ L : Lattice (O := O) ρ, ∀ v, v ∈ L.T ↔ ∃ a ∈ A, ∃ u ∈ Λ.T, v = a + μ • u := by
  intro G O LL V _ _ _ _ _ _ _ _ _ _ _ ρ Λ A hA hst μ hμ
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have hmem : ∀ v, v ∈ A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)) ↔
      ∃ a ∈ A, ∃ u ∈ Λ.T, v = a + μ • u := by
    intro v
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, z, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨a, ha, u, hu, by simp⟩
    · rintro ⟨a, ha, u, hu, rfl⟩
      exact ⟨a, ha, μ • u, ⟨u, hu, by simp⟩, rfl⟩
  have hfg : (A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))).FG := hA.sup (Λ.fg.map _)
  have htf : Module.IsTorsionFree O V := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r m h
    rw [← algebraMap_smul LL r m, smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h
  refine ⟨⟨A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)), ?_, hfg, ?_, ?_⟩, hmem⟩
  · intro g x hx
    obtain ⟨a, ha, u, hu, rfl⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨ρ g a, hst g a ha, ρ g u, Λ.stable g u hu, ?_⟩
    rw [map_add (f := _), ← algebraMap_smul LL μ u, map_smul, algebraMap_smul]
  · haveI : Module.Finite O ↥(A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))) :=
      Module.Finite.iff_fg.2 hfg
    infer_instance
  · rw [eq_top_iff, ← Λ.span, Submodule.span_le]
    intro u hu
    have hne : algebraMap O LL μ ≠ 0 := fun h => hμ (hinj (by rw [h, map_zero]))
    have : u = (algebraMap O LL μ)⁻¹ • (μ • u) := by
      rw [← algebraMap_smul LL μ u, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hmem _).2 ⟨0, A.zero_mem, u, hu, by simp⟩))
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsPowUniformizerSmulEqZeroQuotientLattice
section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.exists_pow_uniformizer_smul_eq_zero_quotient_lattice :
    ∀ {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      (lam : O), Irreducible lam → ∀ {k : ℕ} {Y : Type} [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
      (φ : Y →ₗ[O] ((Fin k → LL) ⧸ stdG O LL k)), ∃ a : ℕ, ∀ y, lam ^ a • φ y = 0 := by
  classical
  intro O LL _ _ _ _ _ _ lam hlam k Y _ _ _ φ
  have hz : ∀ z : LL, ∃ a : ℕ, ∃ r : O, algebraMap O LL r = lam ^ a • z := by
    intro z
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) z
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hlam
    refine ⟨m, r * ↑u⁻¹, ?_⟩
    have hU : algebraMap O LL ↑u⁻¹ * algebraMap O LL ↑u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hU0 : algebraMap O LL ↑u ≠ 0 := right_ne_zero_of_mul_eq_one hU
    have hinv : algebraMap O LL ↑u⁻¹ = (algebraMap O LL ↑u)⁻¹ := eq_inv_of_mul_eq_one_left hU
    have hL0 : algebraMap O LL (lam ^ m) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ fun h => hlam.ne_zero ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
    rw [Algebra.smul_def, map_mul, map_mul, hinv]
    field_simp
  have hq : ∀ x : (Fin k → LL) ⧸ stdG O LL k, ∃ a : ℕ, lam ^ a • x = 0 := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    choose a r hr using fun i => hz (v i)
    refine ⟨∑ i, a i, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, stdG, LinearMap.mem_range]
    refine ⟨fun i => lam ^ (∑ j, a j - a i) * r i, funext fun i => ?_⟩
    have hle : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    show algebraMap O LL (lam ^ (∑ j, a j - a i) * r i) = lam ^ (∑ j, a j) • v i
    rw [map_mul, hr i, ← Algebra.smul_def, smul_smul, pow_sub_mul_pow lam hle]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := Y)
  choose a ha using fun y => hq (φ y)
  refine ⟨∑ y ∈ s, a y, fun y => ?_⟩
  have hmem : y ∈ Submodule.span O (s : Set Y) := hs ▸ Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    rw [← pow_sub_mul_pow lam (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hx), mul_smul, ha x,
      smul_zero]
  | zero => rw [map_zero, smul_zero]
  | add x z _ _ h1 h2 => rw [map_add (f := _), smul_add, h1, h2, add_zero]
  | smul c x _ h => rw [map_smul, smul_comm, h, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresOfInjectiveEquivariant
section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.hasPres_of_injective_equivariant :
    ∀ {G O LL : Type} [Group G] [CommRing O] [IsNoetherianRing O] [Field LL] [Algebra O LL] {Xs : Type} {n : ℕ}
      (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) {P Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
      (actP : G → P → P) (actQ : G → Q → Q) (ι : P →ₗ[O] Q) (f' : G → P) (f : G → Q),
      Function.Injective ι → (∀ g u, ι (actP g u) = actQ g (ι u)) → (∀ g, ι (f' g) = f g) →
      HasPres LL N actQ f → HasPres LL N actP f' := by
  intro G O LL _ _ _ _ _ Xs n N P Q _ _ _ _ actP actQ ι f' f hinj heq hf h
  obtain ⟨a, x, E, Y, hfg, hst, hE, φ, hφ, hfφ⟩ := h
  let Y' : Submodule O (Fin a → Fin n → LL) := ((LinearMap.range ι).comap φ).map Y.subtype
  have hle : Y' ≤ Y := Submodule.map_subtype_le _ _
  have hmem : ∀ y : Y, (y : Fin a → Fin n → LL) ∈ Y' ↔ φ y ∈ LinearMap.range ι := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      subst this
      exact hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hfg' : Y'.FG := by
    haveI : IsNoetherian O Y := isNoetherian_of_fg_of_noetherian Y hfg
    exact Submodule.FG.map _ (IsNoetherian.noetherian _)
  have hst' : ∀ g, ∀ y ∈ Y', actN LL (fun j => N (x j)) g y ∈ Y' := by
    intro g y hy
    have h1 := (hmem ⟨y, hle hy⟩).1 hy
    obtain ⟨u, hu⟩ := h1
    refine (hmem ⟨_, hst g y (hle hy)⟩).2 ⟨actP g u, ?_⟩
    rw [heq, hu]
    exact (hφ g ⟨y, hle hy⟩).symm
  have hE' : ∀ g, actN LL (fun j => N (x j)) g E - E ∈ Y' := by
    intro g
    exact (hmem ⟨_, hE g⟩).2 ⟨f' g, by rw [hf, hfφ]⟩
  let ψ : Y' →ₗ[O] LinearMap.range ι :=
    LinearMap.codRestrict _ (φ ∘ₗ Submodule.inclusion hle)
      (fun y => (hmem ⟨y.1, hle y.2⟩).1 y.2)
  let φ' : Y' →ₗ[O] P := (LinearEquiv.ofInjective ι hinj).symm.toLinearMap ∘ₗ ψ
  have key : ∀ y : Y', ι (φ' y) = φ ⟨y.1, hle y.2⟩ := by
    intro y
    have h2 : ((LinearEquiv.ofInjective ι hinj) (φ' y)) = ψ y :=
      (LinearEquiv.ofInjective ι hinj).apply_symm_apply (ψ y)
    exact congrArg Subtype.val h2
  refine ⟨a, x, E, Y', hfg', hst', hE', φ', ?_, ?_⟩
  · intro g y
    apply hinj
    rw [heq, key, key]
    exact hφ g ⟨y.1, hle y.2⟩
  · intro g
    apply hinj
    rw [key, hf]
    exact hfφ g
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IsLocallyConstantTorsionPushOfContinuous
section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.isLocallyConstant_torsion_push_of_continuous :
    ∀ {G O LL Q : Type} [TopologicalSpace G] [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field LL] [TopologicalSpace LL]
      [IsTopologicalRing LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup Q] [Module O Q] {a n : ℕ}
      (Y : Submodule O (Fin a → Fin n → LL)) (φ : ↥Y →ₗ[O] Q) (u : G → Fin a → Fin n → LL) (hu : ∀ g, u g ∈ Y) (c : O),
      IsOpen (Set.range (algebraMap O LL)) → Continuous u → c ≠ 0 → (∀ y, c • φ y = 0) →
      IsLocallyConstant fun g => φ ⟨u g, hu g⟩ := by
  classical
  intro G O LL Q _ _ _ _ _ _ _ _ _ _ _ a n Y φ u hu c hopen hcont hc hkill
  let Lmap : (Fin a → Fin n → O) →ₗ[O] (Fin a → Fin n → LL) :=
    ((Algebra.linearMap O LL).compLeft (Fin n)).compLeft (Fin a)
  let Λ := LinearMap.range Lmap
  have hΛ : Λ.FG := by
    show (LinearMap.range Lmap).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  obtain ⟨μ, hμ0, hμ⟩ := admissible_lattices_commensurable (LL := LL) Λ Y hΛ c hc
  have hμL : algebraMap O LL μ ≠ 0 := fun h =>
    hμ0 ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
  let W : Set LL := (fun x => (algebraMap O LL μ)⁻¹ * x) ⁻¹' Set.range (algebraMap O LL)
  have hW : IsOpen W := hopen.preimage (continuous_const.mul continuous_id)
  let U : Set (Fin a → Fin n → LL) := {v | ∀ j m, v j m ∈ W}
  have hU : IsOpen U := by
    have hUe : U = ⋂ j, ⋂ m, (fun v : Fin a → Fin n → LL => v j m) ⁻¹' W := by
      ext v; simp [U]
    rw [hUe]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun m =>
      hW.preimage ((continuous_apply m).comp (continuous_apply j))
  have key : ∀ v ∈ Y, v ∈ U → ∃ y ∈ Y, v = c • y := by
    intro v hvY hvU
    simp only [U, W, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range] at hvU
    choose x hx using hvU
    have hxΛ : Lmap x ∈ Λ := LinearMap.mem_range_self _ _
    have hmul : μ • Lmap x = v := by
      funext j m
      show μ • algebraMap O LL (x j m) = v j m
      rw [Algebra.smul_def, hx j m, ← mul_assoc, mul_inv_cancel₀ hμL, one_mul]
    obtain ⟨y, hy, hyeq⟩ := hμ _ hxΛ (hmul ▸ hvY)
    exact ⟨y, hy, hmul ▸ hyeq⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have hnhds : {g | u g - u g0 ∈ U} ∈ nhds g0 := by
    refine (hU.preimage (hcont.sub continuous_const)).mem_nhds ?_
    intro j m
    refine ⟨0, ?_⟩
    simp
  filter_upwards [hnhds] with g hg
  obtain ⟨y, hy, hyeq⟩ := key _ (Y.sub_mem (hu g) (hu g0)) hg
  have hsplit : (⟨u g, hu g⟩ : Y) = ⟨u g0, hu g0⟩ + c • ⟨y, hy⟩ := by
    ext1
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [← hyeq]
    abel
  rw [hsplit, map_add (f := _), map_smul, hkill, add_zero]
end

