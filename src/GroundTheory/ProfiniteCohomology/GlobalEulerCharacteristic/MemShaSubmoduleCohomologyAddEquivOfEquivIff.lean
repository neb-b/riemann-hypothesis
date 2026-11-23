module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShaTwist
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerShaOpen
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Kummer
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Coprime
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
public import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global Representation

universe u

noncomputable section

section Scalars

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsDiscreteRep A] [IsDiscreteRep A'] (e : A ≃+ A')
  (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

theorem mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv e he n x ∈ shaSubmodule φ A' n ↔ x ∈ shaSubmodule φ A n := by
  refine forall_congr' fun v => ?_
  have key := cohomologyAddEquivOfEquiv_mapAlong e he (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
    (B := Rep.res (φ v).toMonoidHom A) (B' := Rep.res (φ v).toMonoidHom A') e (fun _ a => he _ a) (𝟙 _) (𝟙 _)
    (fun _ => rfl) n x
  rw [← key]
  constructor
  · intro h
    exact (cohomologyAddEquivOfEquiv (A := Rep.res (φ v).toMonoidHom A) (A' := Rep.res (φ v).toMonoidHom A')
      e (fun _ a => he _ a) n).injective (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

end Scalars

section Card

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (ℓ : ℕ) [Fact ℓ.Prime]
  (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] (hM : ∀ m : M, ℓ • m = 0)

end Card

section KummerZMod

attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
  {T O : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep T] [IsDiscreteRep O] {ℓ : ℕ} {f : T ⟶ O}
  {w : f ≫ (ℓ • 𝟙 O) = 0} (hS : (ShortComplex.mk f (ℓ • 𝟙 O) w).ShortExact) (hT : ∀ t : T, ℓ • t = 0)

def kummerModNZMod (i : ℕ) :
    ModN (cohomology (Rep.res N.subtype O) i) ℓ →ₗ[ZMod ℓ]
      cohomology (Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (i + 1) :=
  ((cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T) (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT))
    (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1)).toAddMonoidHom.comp
      (kummerModNHom N hS i)).toZModLinearMap ℓ

theorem kummerModNZMod_apply (i : ℕ) (y : ModN (cohomology (Rep.res N.subtype O) i) ℓ) :
    kummerModNZMod N hS hT i y =
      cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T) (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT))
        (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1) (kummerModNHom N hS i y) :=
  rfl

theorem kummerModNZMod_injective (i : ℕ) : Function.Injective (kummerModNZMod N hS hT i) :=
  (cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T) (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT))
    (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1)).injective.comp (kummerModNHom_injective N hS i)

variable [N.Normal] [CompactSpace N]

theorem isIntertwiningMap_kummerModNZMod (i : ℕ) :
    (letI := conjActionOf N (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N).le O i;
      modNRep (G ⧸ N) (cohomology (Rep.res N.subtype O) i) ℓ).IsIntertwiningMap
      (cohomologyConjRep (zmodRepOfTorsion ℓ T hT) N (i + 1)) (kummerModNZMod N hS hT i) := by
  let _ := conjActionOf N (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N).le O i
  refine ⟨fun q x => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      have hs : (g : G ⧸ N) • y = (cohomologyConj O N i g).hom y :=
        conjActionOf_smul N (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N).le O i g y
      rw [modNRep_mk, hs, cohomologyConjRep_mk, kummerModNZMod_apply, kummerModNZMod_apply,
        kummerModNHom_cohomologyConj]
      exact cohomologyAddEquivOfEquiv_cohomologyConj (A := T) (A' := zmodRepOfTorsion ℓ T hT)
        (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) N (i + 1) g _


omit [N.Normal] [CompactSpace N] in
theorem mem_shaSubmodule_iff_mem_range_kummerModNZMod {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)]
    [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] (ψ : ∀ v, Hv v →ₜ* N) (i : ℕ)
    (hsha : ∀ x : cohomology (Rep.res N.subtype T) (i + 1),
      x ∈ ptSha ψ (Rep.res N.subtype T) (i + 1) ↔ ∃ y, kummerModNHom N hS i y = x)
    (y : cohomology (Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (i + 1)) :
    y ∈ shaSubmodule ψ (Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (i + 1) ↔
      y ∈ LinearMap.range (kummerModNZMod N hS hT i) := by
  set E := cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T)
    (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1)
  obtain ⟨y', rfl⟩ := E.surjective y
  refine (mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff ψ (A := Rep.res N.subtype T)
    (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl)
    (i + 1) y').trans ?_
  refine (mem_ptSha_iff_mem_shaSubmodule ψ _ y').symm.trans ((hsha y').trans ⟨?_, ?_⟩)
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [kummerModNZMod_apply, hz]⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, E.injective (by rw [← hz, kummerModNZMod_apply])⟩

end KummerZMod

section GS

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ℓ : ℕ) [Fact ℓ.Prime]

abbrev gsRootsZMod : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S) :=
  zmodRepOfTorsion ℓ (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ)

theorem finrank_gsRootsZMod {S} (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hcard : Nat.card (gsRootsZMod S ℓ) = ℓ ^ 1 := by
    rw [pow_one]
    obtain ⟨f⟩ := nonempty_addEquiv_gsRoots_of_mem S (n := ℓ) (fun v hv =>
      by_contra fun h => hℓS v h hv)
    exact (Nat.card_congr f.toEquiv).trans (Nat.card_zmod ℓ)
  have : Finite (gsRootsZMod S ℓ) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  exact finrank_eq_of_natCard_zmod ℓ hcard

variable {S} (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]

abbrev gsH1SUnitsModRep :
    Representation (ZMod ℓ)
      (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
      (ModN (cohomology (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (galSUnitsMax K.1 ℚ̄ S)) 1) ℓ) :=
  letI := conjActionOf (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le (galSUnitsMax K.1 ℚ̄ S) 1
  modNRep _ _ ℓ

theorem finrank_shaSubmodule_two_eq_finrank_invariants (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hK : Odd ℓ ∨ IsTotallyComplex L.1)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hT : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (t : gsRootsZMod S ℓ),
      (gsRootsZMod S ℓ).ρ g t = t)
    (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
    (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m) :
    Module.finrank (ZMod ℓ) (shaSubmodule (gsFinFamily S ιs) M 2) =
      Module.finrank (ZMod ℓ) ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M hT hM))).invariants := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hP : (((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index : ℕ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).1 hcop.symm
  let P := gsOpenSubgroup S hL
  let N : Subgroup (galUnramifiedOutside K.1 ℚ̄ S) := P
  have hS := gsKummer_shortExact S ℓ hℓS
  have hTorsion := nsmul_gsRoots S ℓ
  refine finrank_shaSubmodule_eq_finrank_invariants (gsFinFamily S ιs) P (gsRootsZMod S ℓ) M
    hT hM (finrank_gsRootsZMod ℓ hℓS) hP 2 (gsH1SUnitsModRep ℓ hL)
    (kummerModNZMod N hS hTorsion 1) ?_ ?_ ?_
  · exact isIntertwiningMap_kummerModNZMod N hS hTorsion 1
  · exact kummerModNZMod_injective N hS hTorsion 1
  · exact mem_shaSubmodule_iff_mem_range_kummerModNZMod N hS hTorsion
      (mackeyFamily P (gsFinFamily S ιs)) 1
      (mem_ptSha_mackey_iff_exists_kummerModN hL ιs hℓ hℓS hK)

end GS

end

end GroundTheory.ProfCoh
