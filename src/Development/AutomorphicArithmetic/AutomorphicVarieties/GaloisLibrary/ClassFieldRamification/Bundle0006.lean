module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0005
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
section
open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kwAbs :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Subgroup (G ℚ Ω)), IsOpen (V : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ V → ∃ N : ℕ, 0 < N ∧ ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) → g ∈ V := by
  intro Ω _ alg hc V hV hcomm
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : alg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hcl : IsClosed (V : Set (Ω ≃ₐ[ℚ] Ω)) := Subgroup.isClosed_of_isOpen V hV
  set L : IntermediateField ℚ Ω := IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[ℚ] Ω)) with hL
  have hfix : L.fixingSubgroup = V := InfiniteGalois.fixingSubgroup_fixedField ⟨V, hcl⟩
  have hnorm : V.Normal := ⟨fun n hn g => by
    have h : g * n * g⁻¹ * n⁻¹ ∈ V :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have := mul_mem h hn
    rwa [inv_mul_cancel_right] at this⟩
  haveI hfin : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hfix]; exact hV)
  haveI hgal : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hfix]; exact hnorm)
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker = V :=
    (@IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ L hgal.to_normal).trans hfix
  haveI hab : IsAbelianGalois ℚ L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := hsurj a
        obtain ⟨b, rfl⟩ := hsurj b
        have h : a * b * a⁻¹ * b⁻¹ ∈ V :=
          hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
          mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
        exact h⟩ }
  obtain ⟨N, ζ, hN, hζ, hle⟩ := UpperTheory.V.CF.kw Ω L
  refine ⟨N, hN, fun g hg => ?_⟩
  rw [← hfix]
  refine IntermediateField.fixingSubgroup_le hle ?_
  have h1 : ℚ⟮ζ⟯ ≤ IntermediateField.fixedField (Subgroup.zpowers (g : Ω ≃ₐ[ℚ] Ω)) := by
    rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers (g : Ω ≃ₐ[ℚ] Ω) ≤ MulAction.stabilizer _ ζ :=
      Subgroup.zpowers_le.2 (hg ζ hζ.pow_eq_one)
    exact this hf
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (h1 hx) g (Subgroup.mem_zpowers g)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kwHom :
    ∀ (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L], ∃ N : ℕ, 0 < N ∧ Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ) := by
  intro L _ _ _
  let f : L →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : L ≃ₐ[ℚ] f.fieldRange := AlgEquiv.ofInjectiveField f
  haveI : IsAbelianGalois ℚ f.fieldRange := IsAbelianGalois.of_algHom e.symm.toAlgHom
  haveI : FiniteDimensional ℚ f.fieldRange := e.toLinearEquiv.finiteDimensional
  obtain ⟨N, ζ, hN, hζ, hle⟩ := UpperTheory.V.CF.kw (AlgebraicClosure ℚ) f.fieldRange
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI hNQ : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI hC : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    @CyclotomicField.isCyclotomicExtension N _ ℚ _ hNQ
  refine ⟨N, hN, ⟨?_⟩⟩
  exact ((IsCyclotomicExtension.algEquiv {N} ℚ ℚ⟮ζ⟯ (CyclotomicField N ℚ)).toAlgHom.comp
    (IntermediateField.inclusion hle)).comp e.toAlgHom
end

