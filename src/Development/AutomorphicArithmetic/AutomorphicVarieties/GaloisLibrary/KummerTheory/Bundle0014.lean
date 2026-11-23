module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.pullEq :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] [Normal F K] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω) (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ρ : Representation R (G F Ω) M), N ≠ 0 → galOf F K Ω ≤ U → (IsTotallyComplex K ∨ ∀ m : M, 2 • m = 0 → m = 0) →
    (ClEq K N ρ).map (clPull K hU R M) = EqHom N U ρ ∧ ∀ (τ : K ≃+* K) (σ : Ω ≃+* Ω) (s : R), IsLift τ σ → (ClEig K N ρ σ s).map (clPull K hU R M) = EqEig N U ρ σ s := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ _ U hU N R M _ _ _ ρ hN hU' hM
  have hO := pullOnto F Ω K U hU N R M hN hU' hM
  have hL : ∀ g : G F Ω, IsLift (AlgEquiv.restrictNormal g K).toRingEquiv g.toRingEquiv := fun g x =>
    (AlgEquiv.restrictNormal_commutes g K x).symm
  have hC : ∀ (g : G F Ω) (θ : ClassGroup (𝓞 K) → M),
      θ ∈ clCond K g.toRingEquiv (ρ g) ↔ clPull K hU R M θ ∈ conjCond U g.toRingEquiv (ρ g) := fun g θ =>
    pullCond F Ω K U hU R M _ _ (ρ g) θ hU' (hL g)
  have h1 : (ClEq K N ρ).map (clPull K hU R M) = EqHom N U ρ := by
    apply le_antisymm
    · rintro _ ⟨θ, ⟨hθ, hθ'⟩, rfl⟩
      refine ⟨hO ▸ Submodule.mem_map_of_mem hθ, (Submodule.mem_iInf _).2 fun g => (hC g θ).1 ((Submodule.mem_iInf _).1 hθ' g)⟩
    · rintro φ ⟨hφ, hφ'⟩
      have hφ2 : φ ∈ (ClDual K N R M).map (clPull K hU R M) := by rw [hO]; exact hφ
      obtain ⟨θ, hθ, rfl⟩ := hφ2
      exact ⟨θ, ⟨hθ, (Submodule.mem_iInf _).2 fun g => (hC g θ).2 ((Submodule.mem_iInf _).1 hφ' g)⟩, rfl⟩
  refine ⟨h1, fun τ σ s h => le_antisymm ?_ ?_⟩
  · rintro _ ⟨θ, ⟨hθ, hθ'⟩, rfl⟩
    have h2 : clPull K hU R M θ ∈ EqHom N U ρ := by rw [← h1]; exact Submodule.mem_map_of_mem hθ
    exact ⟨h2, (pullCond F Ω K U hU R M τ σ _ θ hU' h).1 hθ'⟩
  · rintro φ ⟨hφ, hφ'⟩
    have hφ2 : φ ∈ (ClEq K N ρ).map (clPull K hU R M) := by rw [h1]; exact hφ
    obtain ⟨θ, hθ, rfl⟩ := hφ2
    exact ⟨θ, ⟨hθ, (pullCond F Ω K U hU R M τ σ _ θ hU' h).2 hφ'⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ShaFrom
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open Pointwise

private theorem hom_one {Γ M : Type} [Group Γ] [AddCommGroup M] {f : Γ → M} (hf : ∀ a b, f (a * b) = f a + f b) :
    f 1 = 0 := by
  have := hf 1 1
  rw [one_mul] at this
  exact left_eq_add.1 this

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem zm_triv (D : LData F Ω l) (r : ℕ) (g) (m : ZMod (l ^ r)) : zmTw D r 0 g m = m := by simp [zmTw]

private theorem mem_iff (D : LData F Ω l) (r : ℕ) (z : Z1 (zmTw D r 0)) :
    (Submodule.Quotient.mk z : H1 (zmTw D r 0)) ∈ ShaZm D r 0 ↔
      ∀ v : D.S, ∀ g ∈ Dec (F := F) (D.A v), z.1 (toGS Ω _ g) = 0 := by
  refine (Submodule.mem_iInf _).trans (forall_congr' fun v => ?_)
  refine ((Submodule.Quotient.mk_eq_zero _).trans (mem_coboundaries1 _ _)).trans ⟨fun ⟨m, hm⟩ g hg => ?_, fun h => ⟨0, fun g => ?_⟩⟩
  · exact (hm ⟨g, hg⟩).trans (sub_eq_zero.2 (zm_triv D r _ m))
  · exact (h g.1 g.2).trans (sub_eq_zero.2 (zm_triv D r _ 0)).symm

end
end

