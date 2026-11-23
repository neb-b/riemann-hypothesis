module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.YPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0020
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmDimQuot
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem pmDim_quot {A B σ M : Type} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module A M] (y : σ → A) :
    Nonempty (((B ⊗[A] M) ⧸ (Ideal.span (Set.range fun i => algebraMap A B (y i)) • ⊤ :
      Submodule B (B ⊗[A] M))) ≃ₗ[B] B ⊗[A] (M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule A M))) := by
  classical
  set I : Ideal A := Ideal.span (Set.range y) with hIdef
  have hI : Ideal.span (Set.range fun i => algebraMap A B (y i)) = I.map (algebraMap A B) := by
    rw [hIdef, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hI]
  refine ⟨(TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := A) B A B
    (I • ⊤ : Submodule A M) ≪≫ₗ Submodule.quotEquivOfEq _ _ ?_).symm⟩
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      obtain ⟨m, hm⟩ := m
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
        Submodule.coe_subtype]
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro a ha m' _
        rw [← TensorProduct.smul_tmul, algebra_compatible_smul B a, ← TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
      · intro u v hu hv
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hu hv
    | add x z hx hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hz
  · rw [Submodule.smul_le]
    intro r hr x hx
    clear hx
    induction hr using Submodule.span_induction generalizing x with
    | mem r hr =>
      obtain ⟨a, ha, rfl⟩ := hr
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b m =>
        refine ⟨b ⊗ₜ[A] (⟨a • m, Submodule.smul_mem_smul ha Submodule.mem_top⟩ : (I • ⊤ : Submodule A M)), ?_⟩
        simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
          Submodule.coe_subtype]
        rw [← TensorProduct.smul_tmul, algebra_compatible_smul B a, TensorProduct.smul_tmul']
      | add u v hu hv =>
        rw [smul_add]
        exact Submodule.add_mem _ hu hv
    | zero => simp
    | add r s _ _ hr hs =>
      rw [add_smul]
      exact Submodule.add_mem _ (hr x) (hs x)
    | smul c r _ hr =>
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ c (hr x)

private theorem pmDim_step {L B σ M N : Type} [CommRing L] [IsRegularLocalRing L] [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [Algebra L B] [IsLocalHom (algebraMap L B)] [Fintype σ]
    [AddCommGroup M] [Module B M] [Module.Finite B M] [AddCommGroup N] [Module B N] [Module L N]
    [IsScalarTower L B N] [Module.Free L N] [Module.Finite L N] (d : ℕ) (y : σ → B)
    (hd : ringKrullDim L = d) (hy : ∀ i, y i ∈ maximalIdeal B) (hq : GlobalTheory.IsQuasiRegularSeq M y)
    (e : (M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule B M)) ≃ₗ[B] N) :
    ∀ Z ∈ (Module.annihilator B M).minimalPrimes,
      ringKrullDim (B ⧸ Z) = ((d + Fintype.card σ : ℕ) : WithBot ℕ∞) := by
  classical
  intro Z hZ
  rcases subsingleton_or_nontrivial M with hM | hM
  · have htop : Module.annihilator B M = ⊤ := Module.annihilator_eq_top_iff.mpr hM
    rw [htop] at hZ
    exact absurd (top_le_iff.mp hZ.1.2) hZ.1.1.ne_top
  · letI : Module L M := Module.compHom M (algebraMap L B)
    haveI : IsScalarTower L B M := ⟨fun a b m => by
      show (a • b) • m = algebraMap L B a • (b • m)
      rw [Algebra.smul_def, mul_smul]⟩
    let eσ : Fin (Fintype.card σ) ≃ σ := (Fintype.equivFin σ).symm
    have hq' := hq.comp_equiv eσ
    have hspan : Ideal.span (Set.range (y ∘ eσ)) = Ideal.span (Set.range y) := by
      rw [Set.range_comp, EquivLike.range_eq_univ, Set.image_univ]
    let e' : (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) ≃ₗ[L] N :=
      ((Submodule.quotEquivOfEq _ _ (by rw [hspan])) ≪≫ₗ e).restrictScalars L
    have hfree : Module.Free L (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) :=
      Module.Free.of_equiv e'.symm
    have hfin : Module.Finite L (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) :=
      Module.Finite.equiv e'.symm
    have h := (UpperTheory.V.AlgebraTools.patched_depth_dim L B M (Fintype.card σ) d (y ∘ eσ) hd
      (fun i => hy _) hq' hfree hfin).2 Z hZ
    rw [h, Nat.add_comm]

theorem UpperTheory.V.Pa.Core.pmDim :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Fintype σ] (c : Λ →+* R) (y : σ → R) (f : R) (ii : Ideal R) (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Free Λ X] [Module.Finite Λ X] (P : PMod y f ii X) (q : Ideal R) (d : ℕ) (La B : Type) [CommRing La] [IsLocalRing La] [Algebra Λ La] [CommRing B] [IsLocalRing B] [Algebra P.BB B], (∀ (a : Λ) (x : X), a • x = c a • x) → q.IsPrime → f ∉ q → (∀ a, y a ∈ q) → IsCplAt Λ (q.comap c) La → IsRegularLocalRing La → ringKrullDim La = d → IsCplAt P.BB (q.map (algebraMap R P.BB)) B → ∀ Z ∈ (Module.annihilator B (B ⊗[P.BB] P.MM)).minimalPrimes, ringKrullDim (B ⧸ Z) = ((d + Fintype.card σ : ℕ) : WithBot ℕ∞) := by
  intro Λ R σ _ _ _ _ _ c y f ii X _ _ _ _ _ P q d La B _ _ _ _ _ _ hc hq hf hy hLa hreg hdim hB
  classical
  have hYP := UpperTheory.V.Pa.Core.yPrime R σ y f P.BB P.cpl q hq hf hy
  haveI : IsNoetherianRing P.BB := P.cpl.noeth
  haveI : IsNoetherianRing B := hB.noeth
  haveI : Module.Finite P.BB P.MM := P.fin
  haveI : IsAdicComplete (maximalIdeal B) B := hB.complete
  letI : Algebra R B := ((algebraMap P.BB B).comp (algebraMap R P.BB)).toAlgebra
  haveI : IsScalarTower R P.BB B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRB : IsCplAt R q B := hYP.2.2.2 B hB
  haveI : Module.Flat P.BB B := UpperTheory.V.AlgebraTools.IsCplAt.flat P.BB _ B hB
  let φ : Λ →+* B := (algebraMap R B).comp c
  have hφ : Ideal.comap φ (maximalIdeal B) = q.comap c := by
    show Ideal.comap ((algebraMap P.BB B).comp ((algebraMap R P.BB).comp c)) (maximalIdeal B) = q.comap c
    rw [← Ideal.comap_comap, ← Ideal.comap_comap, hB.comap_eq, hYP.2.1]
  obtain ⟨ψ, hψ, -⟩ := UpperTheory.V.AlgebraTools.IsCplAt.existsUnique_lift Λ (q.comap c) La hLa B φ hφ
  letI : Algebra La B := ψ.toAlgebra
  haveI : IsLocalHom (algebraMap La B) := by
    show IsLocalHom ψ
    refine ((IsLocalRing.local_hom_tfae ψ).out 1 4).mpr ?_
    have hm : maximalIdeal La = (q.comap c).map (algebraMap Λ La) := by
      simpa using (UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq Λ (q.comap c) La hLa 1).symm
    rw [hm, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hψ, hφ]
  letI : Algebra Λ R := c.toAlgebra
  letI : Algebra Λ B := φ.toAlgebra
  haveI : IsScalarTower Λ R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Λ La B :=
    IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun hψ x).symm)
  haveI : IsScalarTower Λ R X := ⟨fun a r x => by
    show (c a * r) • x = a • (r • x)
    rw [mul_smul, hc]⟩
  obtain ⟨hfin, hfree⟩ :=
    UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange Λ R (q.comap c) q La B X hLa hRB rfl
  haveI := hfin
  haveI := hfree
  let y' : σ → B := fun i => algebraMap P.BB B (algebraMap R P.BB (y i))
  obtain ⟨e1⟩ := pmDim_quot (A := P.BB) (B := B) (M := P.MM) (fun a => algebraMap R P.BB (y a))
  let e : ((B ⊗[P.BB] P.MM) ⧸ (Ideal.span (Set.range y') • ⊤ : Submodule B (B ⊗[P.BB] P.MM))) ≃ₗ[B]
      B ⊗[R] X :=
    e1 ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) P.fib ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R P.BB B B X
  have hy' : ∀ i, y' i ∈ maximalIdeal B := by
    intro i
    have h : algebraMap R P.BB (y i) ∈ Ideal.comap (algebraMap P.BB B) (maximalIdeal B) := by
      rw [hB.comap_eq]
      exact Ideal.mem_map_of_mem _ (hy i)
    exact h
  have hqr : GlobalTheory.IsQuasiRegularSeq (B ⊗[P.BB] P.MM) y' := P.qr.baseChange B
  exact pmDim_step (L := La) (B := B) (M := B ⊗[P.BB] P.MM) (N := B ⊗[R] X) d y' hdim hy' hqr e
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmodEx
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem loc_of_pair {R X Y Z : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] [AddCommGroup Z] [Module R Z] (f : R) (h : X →ₗ[R] Y) [IsLocalizedModule (Submonoid.powers f) h]
    (Φ : X →ₗ[R] Z) (Ψ : Z →ₗ[R] X) (h1 : ∀ z, Φ (Ψ z) = f • z) (h2 : ∀ z, Ψ (Φ z) = f • z) :
    IsLocalizedModule (Submonoid.powers f) (h ∘ₗ Ψ) := by
  have hf : f ∈ Submonoid.powers f := Submonoid.mem_powers f
  refine ⟨fun c => IsLocalizedModule.map_units h c, fun y => ?_, fun {z₁ z₂} hz => ?_⟩
  · obtain ⟨⟨x, m⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers f) h y
    refine ⟨⟨Φ x, ⟨f, hf⟩ * m⟩, ?_⟩
    simp only [LinearMap.comp_apply, h2, LinearMap.map_smul]
    rw [← hm, mul_smul]
    rfl
  · obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := h) hz
    refine ⟨c * ⟨f, hf⟩, ?_⟩
    have hc' := congrArg Φ hc
    simp only [Submonoid.smul_def, LinearMap.map_smul, h1] at hc'
    simp only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    exact hc'

theorem UpperTheory.V.Pa.Core.pmodEx :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] [IsLocalRing R] [IsNoetherianRing R] (U : Ultrafilter ℕ) (f : R) (ii : Ideal R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (U : Filter ℕ) ≤ atTop → (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ k j, ∀ᶠ N in (U : Filter ℕ), ∃ (r : ℕ) (e : (M N ⧸ ((kjIdeal Λ σ k j).map s • ⊤ : Submodule R (M N))) ≃+ (Fin r → MvPowerSeries σ Λ ⧸ kjIdeal Λ σ k j)), ∀ a m, e (s a • m) = a • e m) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → (∃ (e : ℕ) (Gs : Set R), Ideal.span Gs = ii ∧ ∀ r ∈ Gs, ∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ a : R, (f * r) ^ e - a ∈ maximalIdeal R ^ j ∧ ∀ m : M N, a • m = 0) → Nonempty (PMod (fun a => s (MvPowerSeries.X a)) f ii X) := by
  intro Λ R σ _ _ _ _ s _ _ _ _ _ U f ii M _ _ X _ _ _ _ hU hΛ hX hk hpair hnil
  classical
  let y : σ → R := fun a => s (MvPowerSeries.X a)
  let m : Ideal R := Ideal.map (s.comp MvPowerSeries.C) (maximalIdeal Λ)
  have hq : ∀ a j, ∀ᶠ N in (U : Filter ℕ), QRegAt (M N) y (m ^ j) a := by
    intro a j
    filter_upwards [hk (a + 1) j] with N hN
    obtain ⟨r, e, he⟩ := hN
    exact quotientRegularAt_of_quotient_free_over_powerSeries Λ R σ s (M N) a j r e he
  have hXR : Module.Finite R X := by
    obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule Λ X).FG)
    refine ⟨⟨T, ?_⟩⟩
    rw [eq_top_iff]
    rintro x -
    have hx : x ∈ Submodule.span Λ (T : Set X) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact zero_mem _
    | add _ _ _ _ ha hb => exact add_mem ha hb
    | smul a z _ hz => rw [hΛ]; exact Submodule.smul_mem _ _ hz
  obtain ⟨Φ, Ψ, h1, h2⟩ := exists_ultraLimit_pair_of_eventual_quotient_maps Λ R σ s U f M X hU hΛ hX hpair
  let S := Localization.Away f
  let g := (TensorProduct.mk R S X 1) ∘ₗ Ψ
  haveI : IsLocalizedModule (Submonoid.powers f) g :=
    loc_of_pair f (TensorProduct.mk R S X 1) Φ Ψ h1 h2
  obtain ⟨MM, i1, i2, i3, i4, q, hfin, hsurj, hker, hqr, hann⟩ :=
    exists_patched_module R σ (U : Filter ℕ) hU y m f M S _ rfl hq (S ⊗[R] X) g inferInstance
  let BB := AdicCompletion (Ideal.map (algebraMap R S) (Ideal.span (Set.range y))) S
  have hy : ∀ a (x : X), y a • x = 0 := hX
  obtain ⟨fibE⟩ := fibEquiv R σ y f S BB X MM q (yCpl R σ y f) hy hsurj hker
  have hqr' : GlobalTheory.IsQuasiRegularSeq MM fun a => algebraMap R BB (y a) := by
    rw [isQuasiRegularSeq_iff_qRegAt] at hqr ⊢
    intro a
    have := ((qRegAt_map S BB σ (fun b => algebraMap R S (y b)) ⊥ a).1 MM).1 (hqr a)
    simpa [Ideal.map_bot, ← IsScalarTower.algebraMap_apply] using this
  have hnil' : ii ≤ Ideal.comap (algebraMap R BB) (Module.annihilator BB MM).radical := by
    obtain ⟨e, Gs, hGs, hG⟩ := hnil
    rw [← hGs, Ideal.span_le]
    intro r hr
    have key : ∀ x : MM, algebraMap R S ((f * r) ^ e) • x = 0 := by
      apply hann
      intro k
      refine ⟨k, fun j => ?_⟩
      obtain ⟨c, hc⟩ := finite_quotient_of_ultrafilter_limit_module Λ R σ s U f M X hΛ hX hpair k j
      filter_upwards [hc, hG r hr c] with N hN hN'
      obtain ⟨a, ha, ha0⟩ := hN'
      intro x
      have hmem := hN _ ha x
      have heq : (f ^ k * (f * r) ^ e) • x = (f ^ k * ((f * r) ^ e - a)) • x := by
        rw [mul_sub, sub_smul, mul_smul (f ^ k) a, ha0, smul_zero, sub_zero]
      rw [heq]
      exact hmem
    rw [SetLike.mem_coe, Ideal.mem_comap]
    refine ⟨e, ?_⟩
    rw [Module.mem_annihilator]
    intro x
    have hu : IsUnit ((algebraMap R S f) ^ e) := (IsLocalization.Away.algebraMap_isUnit f).pow e
    have hx : (algebraMap R BB r) ^ e • x = ((algebraMap R S r) ^ e) • x := by
      rw [IsScalarTower.algebraMap_apply R S BB, ← map_pow, algebraMap_smul]
    rw [hx, ← hu.smul_eq_zero, smul_smul, ← mul_pow, ← map_mul, ← map_pow]
    exact key x
  exact ⟨⟨BB, yCpl R σ y f, MM, hfin, hqr', fibE, hnil'⟩⟩
end

