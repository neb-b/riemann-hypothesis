module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0038
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0032

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.AutQIso
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

private theorem irr_of_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : IsIrr r)
    (e : RepIso r r') : IsIrr r' :=
  _root_.UpperTheory.Reformulated.B.IrreducibleSubrep.irr_of_iso h e

theorem UpperTheory.V.Z.Bc.autQIso :
    AutQIso := by
  intro F Ω _ _ _ _ l _ ι n r r' e H hc K _ _ _ _ _ _ hK hi
  have e' : RepIso (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))
      (r'.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) := by
    obtain ⟨g, hg⟩ := e
    exact ⟨g, fun s => hg _⟩
  obtain ⟨π, h1, -, h3⟩ := H (continuous_of_iso hc e) K hK (irr_of_iso hi e')
  refine ⟨π, h1, (UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n _).2.1 hi, h3.mono fun w hw => ?_⟩
  obtain ⟨B, hB, hE⟩ := hw
  exact ⟨B, hB, hE.of_iso e'.symm'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.BiQuad
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

namespace UpperTheory.V.Z.Bc

private theorem mem_range_resG_iff (k L Ω : Type) [Field k] [Field L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω]
    [IsScalarTower k L Ω] (s : G k Ω) :
    s ∈ (resG k L Ω).range ↔ ∀ x : L, s (algebraMap L Ω x) = algebraMap L Ω x := by
  constructor
  · rintro ⟨t, rfl⟩ x
    exact t.commutes x
  · intro h
    exact ⟨{ s.toRingEquiv with commutes' := h }, AlgEquiv.ext fun _ => rfl⟩

private theorem comm_on (k K M : Type) [Field k] [Field K] [Field M] [Algebra k K] [Algebra k M] [Algebra K M]
    [IsScalarTower k K M] [h : IsAbelianGalois k K] (σ τ : M ≃ₐ[k] M) (x : K) :
    (σ * τ) (algebraMap K M x) = (τ * σ) (algebraMap K M x) := by
  rw [← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]
  change algebraMap K M (AlgEquiv.restrictNormalHom K (σ * τ) x) = algebraMap K M (AlgEquiv.restrictNormalHom K (τ * σ) x)
  rw [map_mul, map_mul, h.is_comm.comm]

private theorem exists_compositum (k K K' Ω : Type) [Field k] [Field K] [Field K'] [Field Ω] [Algebra k K] [Algebra k K']
    [Algebra k Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower k K Ω] [IsScalarTower k K' Ω]
    [FiniteDimensional k K] [FiniteDimensional k K'] [IsAbelianGalois k K] [IsAbelianGalois k K'] :
    ∃ (M : Type) (_ : Field M) (_ : Algebra k M) (_ : Algebra K M) (_ : Algebra K' M) (_ : Algebra M Ω)
      (_ : IsScalarTower k K M) (_ : IsScalarTower k K' M) (_ : IsScalarTower K M Ω) (_ : IsScalarTower K' M Ω),
      FiniteDimensional k M ∧ IsAbelianGalois k M ∧
      ∀ s : Ω ≃ₐ[k] Ω, (∀ x : K, s (algebraMap K Ω x) = algebraMap K Ω x) → (∀ x : K', s (algebraMap K' Ω x) = algebraMap K' Ω x) →
        ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := by
  let a := IsScalarTower.toAlgHom k K Ω
  let b := IsScalarTower.toAlgHom k K' Ω
  let M : IntermediateField k Ω := a.fieldRange ⊔ b.fieldRange
  have hM : M = IntermediateField.adjoin k ((a.fieldRange : Set Ω) ∪ b.fieldRange) := IntermediateField.sup_def _ _
  have ha : ∀ x, a x ∈ M := fun x => (le_sup_left : a.fieldRange ≤ M) ⟨x, rfl⟩
  have hb : ∀ x, b x ∈ M := fun x => (le_sup_right : b.fieldRange ≤ M) ⟨x, rfl⟩
  letI iK : Algebra K M := (a.toRingHom.codRestrict M ha).toAlgebra
  letI iK' : Algebra K' M := (b.toRingHom.codRestrict M hb).toAlgebra
  haveI t1 : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (a.commutes x).symm
  haveI t2 : IsScalarTower k K' M := IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (b.commutes x).symm
  haveI t3 : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI t4 : IsScalarTower K' M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hext : ∀ f g : M →ₐ[k] Ω, (∀ x : K, f (algebraMap K M x) = g (algebraMap K M x)) →
      (∀ x : K', f (algebraMap K' M x) = g (algebraMap K' M x)) → f = g := by
    intro f g h1 h2
    refine IntermediateField.algHom_ext_of_eq_adjoin k hM ?_
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact h1 y
    · exact h2 y
  haveI : FiniteDimensional k a.fieldRange := a.equivFieldRange.toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional k b.fieldRange := b.equivFieldRange.toLinearEquiv.finiteDimensional
  haveI : IsGalois k a.fieldRange := IsGalois.of_algEquiv a.equivFieldRange
  haveI : IsGalois k b.fieldRange := IsGalois.of_algEquiv b.equivFieldRange
  haveI : FiniteDimensional k M := IntermediateField.finiteDimensional_sup _ _
  haveI : Normal k M := IntermediateField.normal_sup k Ω _ _
  haveI : Algebra.IsSeparable k M := inferInstance
  haveI : IsGalois k M := ⟨⟩
  refine ⟨M, inferInstance, inferInstance, iK, iK', inferInstance, t1, t2, t3, t4, inferInstance, ?_, ?_⟩
  · refine { is_comm := ⟨fun σ τ => ?_⟩ }
    have := hext (M.val.comp (σ * τ : M ≃ₐ[k] M)) (M.val.comp (τ * σ : M ≃ₐ[k] M))
      (fun x => congrArg Subtype.val (comm_on k K M σ τ x)) (fun x => congrArg Subtype.val (comm_on k K' M σ τ x))
    exact AlgEquiv.ext fun x => Subtype.ext (DFunLike.congr_fun this x)
  · intro s h1 h2 x
    exact DFunLike.congr_fun (hext ((s : Ω →ₐ[k] Ω).comp M.val) M.val h1 h2) x

private theorem abelian_of_two (K : Type) [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) : IsAbelianGalois ℚ K := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  haveI : IsCyclic (K ≃ₐ[ℚ] K) := inferInstance
  exact IsAbelianGalois.of_isCyclic ℚ K

end UpperTheory.V.Z.Bc

theorem UpperTheory.V.Z.Bc.biQuad :
    BiQuad := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ h h'
  haveI := abelian_of_two K h
  haveI := abelian_of_two K' h'
  obtain ⟨M, fM, iQ, iK, iK', iΩ, t1, t2, t3, t4, hfin, hab, hfix⟩ := exists_compositum ℚ K K' Ω
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  obtain rfl : iQ = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI nM : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  haveI cM : IsCMField M := IsCMField.of_isAbelianGalois M
  haveI a1 : IsAbelianGalois K M := IsAbelianGalois.tower_top ℚ K M
  haveI a2 : IsAbelianGalois K' M := IsAbelianGalois.tower_top ℚ K' M
  refine ⟨M, fM, nM, cM, iK, iK', iΩ, t3, t4, a1.toIsGalois, a2.toIsGalois,
    isSolvable_of_comm a1.is_comm.comm, isSolvable_of_comm a2.is_comm.comm, fun s => ?_, fun s => ?_⟩
  · rw [mem_range_resG_iff, mem_range_resG_iff]
    constructor
    · intro hs x
      rw [IsScalarTower.algebraMap_apply K' M Ω]
      exact hs _
    · intro hs
      exact hfix (resG ℚ K Ω s) s.commutes hs
  · rw [mem_range_resG_iff, mem_range_resG_iff]
    constructor
    · intro hs x
      rw [IsScalarTower.algebraMap_apply K M Ω]
      exact hs _
    · intro hs
      exact hfix (resG ℚ K' Ω s) hs s.commutes
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.EqOfRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

private theorem eq_of_res {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (φ : Γ' →* Γ) (ε : Γ →* kˣ)
    (h1 : ∀ s, ε s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, ε s = 1 ∨ ε s = -1) (t : Γ) (ht : ε t ≠ 1) (a b : Γ →* kˣ)
    (hab : a.comp φ = b.comp φ) (hc : a t = b t) : a = b := by
  have h0 : ∀ s, ε s = 1 → a s = b s := fun s hs => by
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact DFunLike.congr_fun hab x
  refine MonoidHom.ext fun s => ?_
  rcases h2 s with hs | hs
  · exact h0 s hs
  · have e := h0 (t⁻¹ * s) (by simp [hs, (h2 t).resolve_left ht])
    rw [map_mul, map_mul, map_inv, map_inv, hc] at e
    exact mul_left_cancel e

open Classical in
private theorem card_bad {Γ Γ' k I : Type} [Group Γ] [Group Γ'] [Field k] [Fintype I] {n : ℕ} (φ : Γ' →* Γ) (ε : Γ →* kˣ)
    (h1 : ∀ s, ε s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, ε s = 1 ∨ ε s = -1) (h3 : ε ≠ 1) (δ : I → Γ →* kˣ)
    (hi : Function.Injective δ) (hδ : ∀ i s, δ i s = 1 ∨ δ i s = -1) (r : Γ' →* GL (Fin n) k) (hr : IsIrr r) :
    (Finset.univ.filter fun i => RepIso r (tw r ((δ i).comp φ))).card ≤ 2 * n ^ 2 := by
  obtain ⟨t, ht⟩ : ∃ t, ε t ≠ 1 := by
    by_contra h
    exact h3 (MonoidHom.ext fun s => by_contra fun hs => h ⟨s, hs⟩)
  have key : ∀ c : kˣ,
      ((Finset.univ.filter fun i => RepIso r (tw r ((δ i).comp φ))).filter fun i => δ i t = c).card ≤ n ^ 2 := by
    intro c
    rw [← Finset.card_image_of_injOn (f := fun i => (δ i).comp φ)]
    · refine Br.twCard _ _ n r hr _ fun d hd => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
    · intro i hi' j hj hij
      exact hi (eq_of_res φ ε h1 h2 t ht _ _ hij
        ((Finset.mem_filter.1 hi').2.trans (Finset.mem_filter.1 hj).2.symm))
  refine le_trans (Finset.card_le_card (t := _ ∪ _) ?_) ((Finset.card_union_le _ _).trans
    ((add_le_add (key 1) (key (-1))).trans (two_mul _).ge))
  intro i hi
  exact Finset.mem_union.2 ((hδ i t).imp (fun h => Finset.mem_filter.2 ⟨hi, h⟩) fun h => Finset.mem_filter.2 ⟨hi, h⟩)

private theorem irr_inf {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} (φ : Γ' →* Γ)
    (H : Subgroup Γ) (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ H) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r : Γ →* GL (Fin n) k)
    (hr : IsIrr (r.comp φ)) (hn : ¬ RepIso (r.comp φ) (tw (r.comp φ) (δ.comp φ))) :
    IsIrr (r.comp (φ.range ⊓ H).subtype) := by
  have h := (Br.resTwo _ _ k n (δ.comp φ).ker.subtype (δ.comp φ) (fun s => by rw [Subgroup.range_subtype]; rfl)
    (fun s => h2 _) (r.comp φ)).1 hr hn
  refine ⟨h.1, fun _ _ _ => trivial, fun W hW hst => h.2.2 W hW fun s v hv => ?_⟩
  exact hst ⟨φ s, ⟨s, rfl⟩, (h1 _).1 s.2⟩ v hv

theorem UpperTheory.V.Z.Bc.third :
    Third := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ hK hK' l _ n r hr hr'
  classical
  obtain ⟨K₀, _, _, _, hK2, hKc⟩ := Br.quadFam (4 * n ^ 2 + 1)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let emb : ∀ i, K₀ i →ₐ[ℚ] Ω := fun i => IsAlgClosed.lift
  letI alg : ∀ i, Algebra (K₀ i) Ω := fun i => (emb i).toRingHom.toAlgebra
  haveI tow : ∀ i, IsScalarTower ℚ (K₀ i) Ω := fun i =>
    IsScalarTower.of_algebraMap_eq fun x => ((emb i).commutes x).symm
  haveI clo : ∀ i, IsAlgClosure (K₀ i) Ω := fun i => ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsAlgClosure K' Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  choose δ _ _ hδ _ using fun i => UpperTheory.exists_quadratic_sign_character ℚ (K₀ i) Ω l (hK2 _)
  have hδi : Function.Injective δ := fun i j hij => by
    by_contra hne
    refine Br.signNe (K₀ i) (K₀ j) Ω (hK2 _) (hKc _ _ hne) (Subgroup.ext fun s => ?_)
    rw [← (hδ i).1, ← (hδ j).1, hij]
  obtain ⟨ε, -, e0, he, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  obtain ⟨ε', -, e0', he', -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K' Ω l hK'
  have c1 := card_bad (resG ℚ K Ω) ε he.1 he.2 e0 δ hδi (fun i => (hδ i).2) _ hr
  have c2 := card_bad (resG ℚ K' Ω) ε' he'.1 he'.2 e0' δ hδi (fun i => (hδ i).2) _ hr'
  have c3 := (Finset.card_union_le _ _).trans (add_le_add c1 c2)
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (c3.trans_lt (by rw [Finset.card_univ, Fintype.card_fin]; omega))
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
  exact ⟨K₀ i, inferInstance, inferInstance, inferInstance, alg i, tow i, hK2 i,
    irr_inf _ _ (δ i) (hδ i).1 (hδ i).2 r hr hi.1, irr_inf _ _ (δ i) (hδ i).1 (hδ i).2 r hr' hi.2⟩
end

