module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GlRelationsHasUniversalProperty

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FinsumQuotientNormsOfNonsplit
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

theorem UpperTheory.finsum_quotient_norms_of_nonsplit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ¬ IsSquare (τ ^ 2 - 4) → (∃ g : Kˣ, g ∉ NE τ) ∧ ∀ f : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, f (t * x) = f x) → ∀ g : Kˣ, g ∉ NE τ → (∑ᶠ t : Kˣ ⧸ NE τ, f t.out) = f 1 + f g := by
  intro O K _ _ _ _ _ Δ τ L hτ hs0
  classical
  have hN := hsNE O K Δ τ L hτ
  refine ⟨?_, fun f hf g hg => ?_⟩
  · obtain ⟨x, hx, h⟩ := (hsLaw O K Δ L).2.2.1 _ hτ hs0
    exact ⟨Units.mk0 x hx, fun h' => by have := (hN _).1 h'; rw [Units.val_mk0, h] at this; norm_num at this⟩
  have neg : ∀ t : Kˣ, t ∉ NE τ → hs (τ ^ 2 - 4) (t : K) = -1 := fun t ht => by
    have := mt (hN t).2 ht
    unfold hs at this ⊢
    split_ifs at this ⊢ with h
    · exact absurd rfl this
    · rfl
  have out : ∀ x : Kˣ, f (x : Kˣ ⧸ NE τ).out = f x := fun x => by
    have : x⁻¹ * (x : Kˣ ⧸ NE τ).out ∈ NE τ := QuotientGroup.eq.1 (by simp)
    rw [← hf _ this x, mul_comm _ x, mul_inv_cancel_left]
  have hne : ((1 : Kˣ) : Kˣ ⧸ NE τ) ≠ (g : Kˣ ⧸ NE τ) := fun h => hg (by simpa using QuotientGroup.eq.1 h)
  rw [finsum_eq_sum_of_support_subset (s := {((1 : Kˣ) : Kˣ ⧸ NE τ), (g : Kˣ ⧸ NE τ)}) _ fun t _ => ?_, Finset.sum_pair hne, out, out]
  induction t using QuotientGroup.induction_on with
  | H t =>
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases ht : t ∈ NE τ
    · exact .inl (QuotientGroup.eq.2 (by simpa using ht))
    · refine .inr (QuotientGroup.eq.2 ((hN _).2 ?_))
      rw [Units.val_mul, hsMul O K Δ L _ _ _ hτ (Units.ne_zero _) g.ne_zero, neg _ hg, neg _ fun h => ht (by simpa using h)]
      norm_num
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MapCenterEnvelopingProductGLMemCapelliAlgebra
section
attribute [local instance 100] LieRing.ofAssociativeRing

open UpperTheory.V.Af.CuspFin in
theorem UpperTheory.map_center_envelopingProductGL_mem_capelliAlgebra :
    ∀ (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (ι : Type) [Fintype ι] (n : ℕ) (b : Module.Basis (ι × Fin n × Fin n) ℝ 𝔤), (∀ v i j k l, ⁅b (v, i, j), b (v, k, l)⁆ = (if j = k then b (v, i, l) else 0) - (if l = i then b (v, k, j) else 0)) → (∀ v v', v ≠ v' → ∀ i j k l, ⁅b (v, i, j), b (v', k, l)⁆ = 0) → ∀ (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (ψ : UniversalEnvelopingAlgebra ℝ 𝔤 →ₐ[ℝ] A), ∀ z ∈ Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ 𝔤), ψ z ∈ UpperTheory.V.Af.CuspFin.capAlg fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) := by
  intro 𝔤 _ _ ι _ n b h1 h2 A _ _ _ _ ψ z hz
  obtain ⟨T, _, _, E, hE⟩ := hasUniv_of_sum (UpperTheory.glRelations_hasUniversalProperty n) (UpperTheory.capelliAlgebra_map_of_glRelations n) ι
  letI : Algebra ℝ T := Algebra.compHom T (algebraMap ℝ ℂ)
  haveI : IsScalarTower ℝ ℂ T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let l : 𝔤 →ₗ[ℝ] T := b.constr ℝ fun p => E p.1 p.2.1 p.2.2
  have hl : ∀ v i j, l (b (v, i, j)) = E v i j := fun v i j => b.constr_basis ℝ _ _
  have hlie : ∀ x y, l ⁅x, y⁆ = l x * l y - l y * l x := by
    have key : (LieModule.toEnd ℝ 𝔤 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).compr₂ l =
        (LinearMap.mul ℝ T).compl₁₂ l l - ((LinearMap.mul ℝ T).compl₁₂ l l).flip := by
      refine LinearMap.ext_basis b b ?_
      rintro ⟨v, i, j⟩ ⟨v', k, m⟩
      change l ⁅b (v, i, j), b (v', k, m)⁆ =
        l (b (v, i, j)) * l (b (v', k, m)) - l (b (v', k, m)) * l (b (v, i, j))
      rw [hl, hl]
      by_cases hv : v = v'
      · subst hv
        rw [h1, hE.rel.1 v i j k m, map_sub]
        congr 1 <;> split_ifs <;> simp [hl]
      · rw [h2 v v' hv, map_zero, (hE.rel.2 v v' hv i j k m).eq, sub_self]
    intro x y
    exact LinearMap.congr_fun₂ key x y
  let L : 𝔤 →ₗ⁅ℝ⁆ T := { l with map_lie' := fun {x y} => hlie x y }
  let f : UniversalEnvelopingAlgebra ℝ 𝔤 →ₐ[ℝ] T := UniversalEnvelopingAlgebra.lift ℝ L
  have hf : ∀ v i j, f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) = E v i j := fun v i j => by
    rw [← hl]
    exact UniversalEnvelopingAlgebra.lift_ι_apply ℝ L _
  have hcen : f z ∈ Subalgebra.center ℂ T := by
    rw [Subalgebra.mem_center_iff]
    intro t
    have ht : t ∈ Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j} := hE.gen ▸ Algebra.mem_top
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ht ?_).symm.eq
    rintro _ ⟨v, i, j, rfl⟩
    rw [← hf, Commute, SemiconjBy, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]
  have hbr : ∀ x y : 𝔤,
      ψ (UniversalEnvelopingAlgebra.ι ℝ x) * ψ (UniversalEnvelopingAlgebra.ι ℝ y) -
        ψ (UniversalEnvelopingAlgebra.ι ℝ y) * ψ (UniversalEnvelopingAlgebra.ι ℝ x) =
      ψ (UniversalEnvelopingAlgebra.ι ℝ ⁅x, y⁆) := fun x y => by
    rw [LieHom.map_lie, Ring.lie_def, map_sub, map_mul, map_mul]
  have hrel : MultiRel fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) := by
    refine ⟨fun v i j k m => ?_, fun v v' hv i j k m => ?_⟩
    · rw [hbr, h1, map_sub, map_sub]
      congr 1 <;> split_ifs <;> simp
    · rw [Commute, SemiconjBy, ← sub_eq_zero, hbr, h2 v v' hv, map_zero, map_zero]
  obtain ⟨ρ, hρ⟩ := hE.univ A _ hrel
  have hcomp : (ρ.restrictScalars ℝ).comp f = ψ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => LinearMap.congr_fun (f := LieHom.toLinearMap _)
      (g := LieHom.toLinearMap _) (b.ext ?_) x
    rintro ⟨v, i, j⟩
    change ρ (f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))) =
      ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))
    rw [hf, hρ]
  have hψ : ψ z = ρ (f z) := by rw [← hcomp]; rfl
  rw [hψ]
  have hle : capAlg E ≤ (capAlg fun v i j =>
      ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))).comap ρ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    refine Algebra.subset_adjoin ⟨v, u, ?_⟩
    refine (map_qdet ρ _ _).trans ?_
    simp only [hρ]
  exact hle (hE.centre hcen)
end

