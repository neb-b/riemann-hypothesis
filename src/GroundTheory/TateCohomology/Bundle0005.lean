module

public import Mathlib
public import GroundTheory.TateCohomology.DimensionShift
public import GroundTheory.TateCohomology.TateLow
public import GroundTheory.TateCohomology.Bundle0004
public import GroundTheory.TateCohomology.Bundle0003
public import GroundTheory.TateCohomology.CoindOne

@[expose] public section

-- bundled from GroundTheory.TateCohomology.Annihilation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

theorem norm_apply_of_mem_invariants (A : Rep.{u} R G) {a : A} (ha : a ∈ A.ρ.invariants) :
    A.ρ.norm a = Fintype.card G • a := by
  rw [Representation.mem_invariants] at ha
  simp [Representation.norm, LinearMap.sum_apply, ha]

theorem card_smul_tateCohomology_zero (A : Rep.{u} R G) (x : tateCohomology A 0) :
    Fintype.card G • x = 0 := by
  let e := ((tateCohomologyZeroIso (R := R) (G := G)).app A).toLinearEquiv
  apply e.injective
  rw [map_nsmul, map_zero]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (normRangeInvariants A) (e x)
  rw [← hy]
  have h : (Submodule.Quotient.mk (Fintype.card G • y) :
      A.ρ.invariants ⧸ normRangeInvariants A) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, mem_normRangeInvariants_iff]
    exact ⟨y, by rw [norm_apply_of_mem_invariants A y.2]; rfl⟩
  rw [Submodule.Quotient.mk_smul] at h
  exact h

private theorem card_smul_succ {n : ℤ}
    (h : ∀ (A : Rep.{u} R G) (x : tateCohomology A n), Fintype.card G • x = 0)
    (A : Rep.{u} R G) (x : tateCohomology A (n + 1)) : Fintype.card G • x = 0 := by
  let e := (coindShiftIso A n).toLinearEquiv
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← map_nsmul, h, map_zero]

private theorem card_smul_pred {n : ℤ}
    (h : ∀ (A : Rep.{u} R G) (x : tateCohomology A (n + 1)), Fintype.card G • x = 0)
    (A : Rep.{u} R G) (x : tateCohomology A n) : Fintype.card G • x = 0 := by
  let e := (indShiftIso A n).toLinearEquiv
  apply e.injective
  rw [map_nsmul, map_zero, h]

theorem card_smul_tateCohomology (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology A n) :
    Fintype.card G • x = 0 := by
  induction n using Int.induction_on generalizing A with
  | zero => exact card_smul_tateCohomology_zero A x
  | succ n ih => exact card_smul_succ (fun A x => ih A x) A x
  | pred n ih =>
    refine card_smul_pred ?_ A x
    rw [sub_add_cancel]
    exact ih

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.Characters
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

section Exactness

universe u

variable {k G : Type u} [CommRing k] [Group G]

theorem shortComplex_exact_of_forall {S : ShortComplex (Rep.{u} k G)}
    (h : ∀ x : S.X₂, S.g.hom x = 0 → ∃ y : S.X₁, S.f.hom y = x) : S.Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
    ShortComplex.moduleCat_exact_iff]
  exact h

end Exactness

section Sequence

variable (G : Type) [Group G]

noncomputable def intToRat : Rep.trivial ℤ G ℤ ⟶ Rep.trivial ℤ G ℚ :=
  Rep.ofHom ⟨(Int.castAddHom ℚ).toIntLinearMap, fun _ => rfl⟩

noncomputable def ratToRatModInt : Rep.trivial ℤ G ℚ ⟶ Rep.trivial ℤ G (AddCircle (1 : ℚ)) :=
  Rep.ofHom ⟨(QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap, fun _ => rfl⟩

noncomputable def ratSES : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (intToRat G) (ratToRatModInt G) (by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun n => ?_))
    change ((n : ℚ) : AddCircle (1 : ℚ)) = 0
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩)

theorem ratSES_shortExact : (ratSES G).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine shortComplex_exact_of_forall fun q hq => ?_
    have hq' : ((show ℚ from q) : AddCircle (1 : ℚ)) = 0 := hq
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 hq'
    exact ⟨n, by change ((n : ℤ) : ℚ) = (show ℚ from q); rw [← hn, zsmul_one]⟩
  · exact (Rep.mono_iff_injective (intToRat G)).2 (Int.cast_injective (α := ℚ))
  · exact (Rep.epi_iff_surjective (ratToRatModInt G)).2 QuotientAddGroup.mk_surjective

end Sequence

section H2

variable (G : Type) [Group G] [Fintype G]

noncomputable def h1RatModIntIso :
    H1 (Rep.trivial ℤ G (AddCircle (1 : ℚ))) ≅ ModuleCat.of ℤ (Additive G →+ AddCircle (1 : ℚ)) :=
  H1IsoOfIsTrivial _


omit [Fintype G] in
theorem h1RatModIntIso_inv_apply (χ : Additive G →+ AddCircle (1 : ℚ)) :
    (h1RatModIntIso G).inv χ =
      H1π _ ((cocycles₁IsoOfIsTrivial (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv χ) :=
  rfl

theorem isIso_δ_ratSES : IsIso (groupCohomology.δ (ratSES_shortExact G) 1 2 rfl) :=
  isIso_δ_of_isZero (ratSES_shortExact G) 1 (isZero_groupCohomology_trivial_rat 1)
    (isZero_groupCohomology_trivial_rat 2)

noncomputable def h1RatModIntIsoH2Int :
    H1 (Rep.trivial ℤ G (AddCircle (1 : ℚ))) ≅ H2 (Rep.trivial ℤ G ℤ) :=
  @asIso _ _ _ _ (groupCohomology.δ (ratSES_shortExact G) 1 2 rfl) (isIso_δ_ratSES G)

noncomputable def h2IntIsoHom :
    H2 (Rep.trivial ℤ G ℤ) ≅ ModuleCat.of ℤ (Additive G →+ AddCircle (1 : ℚ)) :=
  (h1RatModIntIsoH2Int G).symm ≪≫ h1RatModIntIso G

noncomputable def h2IntAddEquiv :
    H2 (Rep.trivial ℤ G ℤ) ≃+ (Additive G →+ AddCircle (1 : ℚ)) :=
  (h2IntIsoHom G).toLinearEquiv.toAddEquiv

theorem h2IntAddEquiv_symm_apply (χ : Additive G →+ AddCircle (1 : ℚ)) :
    (h2IntAddEquiv G).symm χ =
      groupCohomology.δ (ratSES_shortExact G) 1 2 rfl ((h1RatModIntIso G).inv χ) :=
  rfl

theorem h2IntAddEquiv_symm_apply_eq_H2_class (χ : Additive G →+ AddCircle (1 : ℚ)) (y : G → ℚ)
    (hy : ∀ g : G, (y g : AddCircle (1 : ℚ)) = χ (Additive.ofMul g)) (x : G × G → ℤ)
    (hx : ∀ g h : G, (x (g, h) : ℚ) = y g + y h - y (g * h)) :
    ∃ hc : x ∈ cocycles₂ (Rep.trivial ℤ G ℤ),
      (h2IntAddEquiv G).symm χ = H2π (Rep.trivial ℤ G ℤ) ⟨x, hc⟩ := by
  have hfx : (ratSES G).f.hom ∘ x = d₁₂ (ratSES G).X₂ y := by
    funext p
    change ((x p : ℤ) : ℚ) = y p.2 - y (p.1 * p.2) + y p.1
    rw [hx]; ring
  refine ⟨mem_cocycles₂_of_comp_eq_d₁₂ (ratSES_shortExact G) hfx, ?_⟩
  rw [h2IntAddEquiv_symm_apply, h1RatModIntIso_inv_apply]
  refine δ₁_apply (ratSES_shortExact G)
    ((cocycles₁IsoOfIsTrivial (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv χ) y ?_ x hfx
  funext g
  change ((y g : ℚ) : AddCircle (1 : ℚ)) = χ (Additive.ofMul g)
  exact hy g

end H2

section Cyclic

variable {G : Type} [Group G] [Fintype G] (σ : G) (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)



include hσ in
theorem orderOf_ofAdd_div_card_dvd :
    orderOf (Multiplicative.ofAdd (((1 : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ))) ∣
      orderOf σ := by
  have : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  rw [orderOf_ofAdd_eq_addOrderOf, AddCircle.addOrderOf_period_div Nat.card_pos,
    orderOf_eq_card_of_forall_mem_zpowers hσ]

noncomputable def cyclicChar : Additive G →+ AddCircle (1 : ℚ) :=
  MonoidHom.toAdditiveLeft (monoidHomOfForallMemZpowers hσ (orderOf_ofAdd_div_card_dvd σ hσ))

theorem cyclicChar_apply_gen :
    cyclicChar σ hσ (Additive.ofMul σ) = (((1 : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ)) := by
  change Multiplicative.toAdd
    (monoidHomOfForallMemZpowers hσ (orderOf_ofAdd_div_card_dvd σ hσ) σ) = _
  rw [monoidHomOfForallMemZpowers_apply_gen]
  rfl


end Cyclic

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.CohTrivialBasic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep
open scoped MonoidAlgebra

universe u

section Def

variable {k G : Type u} [CommRing k] [Group G]

def CohTrivial (A : Rep.{u} k G) : Prop :=
  ∀ (S : Subgroup G) [Fintype S], TateAcyclic (res S.subtype A)

theorem CohTrivial.of_retract {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : CohTrivial N) : CohTrivial M := fun S _ =>
  (hN S).of_retract ((resFunctor S.subtype).map i) ((resFunctor S.subtype).map r)
    (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id])

theorem CohTrivial.of_iso {M N : Rep.{u} k G} (e : M ≅ N) (hN : CohTrivial N) : CohTrivial M :=
  hN.of_retract e.hom e.inv e.hom_inv_id

end Def

section Norm

variable {k G : Type u} [CommRing k] [Group G]

theorem sum_eq_sum_quotient_sum [Fintype G] (S : Subgroup G) [Fintype S] [Fintype (G ⧸ S)]
    {β : Type*} [AddCommMonoid β] (f : G → β) :
    ∑ g : G, f g = ∑ c : G ⧸ S, ∑ s : S, f (c.out * s) := by
  let e : (G ⧸ S) × S ≃ G :=
    { toFun := fun x => x.1.out * x.2
      invFun := fun g => ((g : G ⧸ S), cosetPart S g)
      left_inv := fun x => by
        obtain ⟨c, s⟩ := x
        ext
        · exact mk_out_mul S c s
        · simp only [cosetPart_out_mul]
      right_inv := fun g => out_mul_cosetPart S g }
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

variable {V : Type*} [AddCommGroup V] [Module k V]

theorem exists_sum_eq_subgroup [Fintype G] (ρ : Representation k G V) (φ : V →ₗ[k] V)
    (hφ : ∀ v, ∑ g : G, ρ g (φ (ρ g⁻¹ v)) = v) (S : Subgroup G) [Fintype S] :
    ∃ ψ : V →ₗ[k] V, ∀ v, ∑ s : S, ρ s (ψ (ρ (s⁻¹ : S) v)) = v := by
  classical
  refine ⟨∑ c : G ⧸ S, ρ c.out⁻¹ ∘ₗ φ ∘ₗ ρ c.out, fun v => ?_⟩
  conv_rhs => rw [← hφ v]
  rw [← Fintype.sum_equiv (Equiv.inv G) (fun h => ρ h⁻¹ (φ (ρ h v))) _ (fun h => by simp),
    sum_eq_sum_quotient_sum S, Finset.sum_comm]
  refine Fintype.sum_equiv (Equiv.inv S) _ _ fun s => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply, map_mul, mul_inv_rev, Module.End.mul_apply]

theorem cohTrivial_of_sum_eq [Fintype G] (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) : CohTrivial M := fun S _ => by
  obtain ⟨ψ, hψ⟩ := exists_sum_eq_subgroup M.ρ φ hφ S
  exact tateAcyclic_of_sum_eq (res S.subtype M) ψ hψ

variable [Fintype G]

theorem cohTrivial_coind_bot (B : Rep.{u} k (⊥ : Subgroup G)) :
    CohTrivial (coind (⊥ : Subgroup G).subtype B) :=
  cohTrivial_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)

theorem cohTrivial_ind_bot (B : Rep.{u} k (⊥ : Subgroup G)) :
    CohTrivial (ind (⊥ : Subgroup G).subtype B) := by
  classical
  exact (cohTrivial_coind_bot B).of_iso (indCoindIso B)

theorem exists_sum_eq_of_basis (M : Rep.{u} k G) {ι : Type*}
    (b : Module.Basis ι k[G] M.ρ.asModule) :
    ∃ φ : M.V →ₗ[k] M.V, ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m := by
  let φ : M.V →ₗ[k] M.V := M.ρ.asModuleEquiv.toLinearMap ∘ₗ
    (b.repr.symm.toLinearMap.restrictScalars k) ∘ₗ Finsupp.mapRange.linearMap coeffOneProj ∘ₗ
    (b.repr.toLinearMap.restrictScalars k) ∘ₗ M.ρ.asModuleEquiv.symm.toLinearMap
  refine ⟨φ, fun m => ?_⟩
  apply M.ρ.asModuleEquiv.symm.injective
  apply b.repr.injective
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
    Representation.asModuleEquiv_symm_map_rho, map_smul, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]
  generalize b.repr (M.ρ.asModuleEquiv.symm m) = c
  ext i : 1
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, coeffOneProj_apply, smul_eq_mul,
    MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.single_mul_single,
    mul_one, one_mul, inv_inv]
  conv_rhs => rw [← MonoidAlgebra.sum_coeff_single (c i)]
  exact (Finsupp.sum_fintype _ _ (by simp)).symm

theorem cohTrivial_of_free (M : Rep.{u} k G) [Module.Free k[G] M.ρ.asModule] : CohTrivial M := by
  obtain ⟨φ, hφ⟩ := exists_sum_eq_of_basis M (Module.Free.chooseBasis k[G] M.ρ.asModule)
  exact cohTrivial_of_sum_eq M φ hφ

theorem cohTrivial_free (α : Type u) : CohTrivial (free k G α) := by
  have := Representation.free_asModule_free k G α
  exact cohTrivial_of_free _

end Norm

section ShortExact

variable {k G : Type u} [CommRing k] [Group G]

theorem TateAcyclic.of_shortExact_X₃ [Fintype G] {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₃ : TateAcyclic S.X₃) : TateAcyclic S.X₁ :=
  fun n => by
    have e := @asIso _ _ _ _ (TateCohomology.δ hS (n - 1)) (isIso_δ_of_tateAcyclic hS h₂ (n - 1))
    have h := (h₃ (n - 1)).of_iso e.symm
    rwa [sub_add_cancel] at h

theorem TateAcyclic.of_shortExact_X₁ [Fintype G] {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₁ : TateAcyclic S.X₁) : TateAcyclic S.X₃ :=
  fun n => (h₁ (n + 1)).of_iso
    (@asIso _ _ _ _ (TateCohomology.δ hS n) (isIso_δ_of_tateAcyclic hS h₂ n))

theorem CohTrivial.of_shortExact_X₃ {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h₂ : CohTrivial S.X₂) (h₃ : CohTrivial S.X₃) : CohTrivial S.X₁ := by
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have a : TateAcyclic (S.map (resFunctor H.subtype)).X₂ := by
    rw [ShortComplex.map_X₂]; exact h₂ H
  have b : TateAcyclic (S.map (resFunctor H.subtype)).X₃ := by
    rw [ShortComplex.map_X₃]; exact h₃ H
  have c := TateAcyclic.of_shortExact_X₃ hS' a b
  rw [ShortComplex.map_X₁] at c
  exact c

theorem CohTrivial.of_shortExact_X₁ {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h₂ : CohTrivial S.X₂) (h₁ : CohTrivial S.X₁) : CohTrivial S.X₃ := by
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have a : TateAcyclic (S.map (resFunctor H.subtype)).X₂ := by
    rw [ShortComplex.map_X₂]; exact h₂ H
  have b : TateAcyclic (S.map (resFunctor H.subtype)).X₁ := by
    rw [ShortComplex.map_X₁]; exact h₁ H
  have c := TateAcyclic.of_shortExact_X₁ hS' a b
  rw [ShortComplex.map_X₃] at c
  exact c

end ShortExact

section Rat

variable {G : Type} [Group G]

end Rat

end GroundTheory.GroupCoh
end

