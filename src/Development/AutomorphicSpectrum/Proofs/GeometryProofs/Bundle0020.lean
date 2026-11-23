module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordNoeth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

lemma genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U)
    (h : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq s) = secVal ξ U h s := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes _ _ _
  simp only [genMap, secVal, ← e]
  rfl

lemma secVal_res (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (h : genPt ξ ∈ V)
    (s : Γ(X, U)) : secVal ξ V h (X.presheaf.map i.op s) = secVal ξ U (leOfHom i h) s := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply i (genPt ξ) h s)

lemma secVal_injective {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (U : X.Opens)
    (h : genPt ξ ∈ U) (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) : Function.Injective (secVal ξ U h) := by
  intro s t e
  refine TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => ?_
  apply hg.inj ⟨q, hU q hq⟩
  exact (genMap_germ ξ ⟨q, hU q hq⟩ U hq h s).trans (e.trans (genMap_germ ξ ⟨q, hU q hq⟩ U hq h t).symm)

lemma exists_secVal_eq {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (U : X.Opens)
    (h : genPt ξ ∈ U) (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω)
    (ha : ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) : ∃ s, secVal ξ U h s = a := by
  have key : ∀ q : U, ∃ (W : X.Opens) (_ : q.1 ∈ W) (_ : W ⟶ U) (hW : genPt ξ ∈ W) (s : Γ(X, W)),
      secVal ξ W hW s = a := by
    intro q
    obtain ⟨t, ht⟩ := ha ⟨q.1, hU _ q.2⟩ q.2
    obtain ⟨V, hqV, s, rfl⟩ := X.presheaf.germ_exist t
    have hqW : q.1 ∈ V ⊓ U := ⟨hqV, q.2⟩
    have hW : genPt ξ ∈ V ⊓ U := (hU _ q.2).mem_open (V ⊓ U).isOpen hqW
    refine ⟨V ⊓ U, hqW, homOfLE inf_le_right, hW, X.presheaf.map (homOfLE inf_le_left).op s, ?_⟩
    rw [secVal_res, ← genMap_germ ξ ⟨q.1, hU _ q.2⟩ V hqV]
    exact ht
  choose W hq i hW s hs using key
  have comp : TopCat.Presheaf.IsCompatible X.sheaf.1 W s := by
    intro p q
    apply secVal_injective hg (W p ⊓ W q) ⟨hW p, hW q⟩ (fun r hr => hU r (leOfHom (i p) hr.1))
    refine (secVal_res ξ _ _ _).trans (Eq.trans ?_ (secVal_res ξ _ _ _).symm)
    rw [hs, hs]
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W U i
    (fun r hr => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r, hr⟩, hq _⟩) s comp
  refine ⟨t, ?_⟩
  rw [← hs ⟨_, h⟩, ← ht ⟨_, h⟩]
  exact (secVal_res ξ _ _ _).symm

lemma mem_regAt_self {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨t, ht⟩ := hg.bij.2 a
  refine ⟨t, ?_⟩
  simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact ht

lemma isNoetherianRing_chart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type} [CommRing o]
    [IsNoetherianRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (tie : CoordTie o ξ x)
    (c : κ) (hc : x c ≠ 0) (U : X.Opens) (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩)
    (h : genPt ξ ∈ U) : IsNoetherianRing Γ(X, U) := by
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hU q).1 hq).elim fun h _ => h
  have hA : IsNoetherianRing (Algebra.adjoin o (Set.range fun j => x j / x c)) := by
    have : Algebra.FiniteType o (Algebra.adjoin o (Set.range fun j => x j / x c)) :=
      (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => x j / x c).toFinset, by simp⟩
    exact Algebra.FiniteType.isNoetherianRing o _
  have mem : ∀ a, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ ∃ s, secVal ξ U h s = a := by
    intro a
    rw [tie.ring c hc a]
    constructor
    · intro H
      refine exists_secVal_eq tie.gen U h hsp a fun q hq => ?_
      obtain ⟨_, hc'⟩ := (hU q.1).1 hq
      exact H q hc'
    · rintro ⟨s, rfl⟩ p hp
      have hpU : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
      exact ⟨_, genMap_germ ξ p U hpU h s⟩
  let g : Γ(X, U) →+* Algebra.adjoin o (Set.range fun j => x j / x c) :=
    (secVal ξ U h).codRestrict _ fun s => (mem _).2 ⟨s, rfl⟩
  have hb : Function.Bijective g := by
    constructor
    · intro s t e
      exact secVal_injective tie.gen U h hsp (congrArg Subtype.val e)
    · rintro ⟨a, ha⟩
      obtain ⟨s, rfl⟩ := (mem a).1 ha
      exact ⟨s, rfl⟩
  exact isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective g hb).symm

theorem noetherian_of_coordTie (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω)
    (tie : CoordTie o ξ x) :
    (∀ p : Cpt ξ, IsNoetherianRing (regAt ξ p)) ∧ ((∀ q : X, genPt ξ ⤳ q) → IsNoetherian X ∧ IsIntegral X) := by
  refine ⟨fun p => ?_, fun hall => ?_⟩
  · obtain ⟨c, hcp⟩ := tie.cover p
    obtain ⟨U, hUa, hU⟩ := tie.affine c hcp.1
    have hp : p.1 ∈ U := (hU p.1).2 ⟨p.2, hcp⟩
    have h : genPt ξ ∈ U := p.2.mem_open U.isOpen hp
    haveI := isNoetherianRing_chart tie c hcp.1 U hU h
    letI := X.presheaf.algebra_section_stalk (⟨p.1, hp⟩ : U)
    haveI := hUa.isLocalization_stalk ⟨p.1, hp⟩
    haveI : IsNoetherianRing (X.presheaf.stalk p.1) :=
      IsLocalization.isNoetherianRing (hUa.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl _ ‹_›
    exact isNoetherianRing_of_surjective _ _ (genMap ξ p).rangeRestrict
      (genMap ξ p).rangeRestrict_surjective
  · have ex : ∀ c : {c // x c ≠ 0}, ∃ U : X.affineOpens,
        ∀ q : X, q ∈ (U : X.Opens) ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c.1 ⟨q, h⟩ := fun c => by
      obtain ⟨U, hUa, hU⟩ := tie.affine c.1 c.2
      exact ⟨⟨U, hUa⟩, hU⟩
    choose S hS using ex
    have hcov : (⨆ c, (S c : X.Opens)) = ⊤ := by
      refine eq_top_iff.2 fun q _ => ?_
      obtain ⟨c, hc⟩ := tie.cover ⟨q, hall q⟩
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨c, hc.1⟩, (hS _ q).2 ⟨hall q, hc⟩⟩
    have hgen : ∀ c, genPt ξ ∈ (S c : X.Opens) := fun c =>
      (hS c _).2 ⟨specializes_rfl, c.2, fun _ => mem_regAt_self tie.gen _⟩
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_affine_cover hcov fun c =>
      isNoetherianRing_chart tie c.1 c.2 _ (hS c) (hgen c)
    haveI : CompactSpace X := by
      refine ⟨?_⟩
      have e : (Set.univ : Set X) = ⋃ c, ((S c : X.Opens) : Set X) := by
        have := congrArg (fun V : X.Opens => (V : Set X)) hcov
        simpa using this.symm
      rw [e]
      exact isCompact_iUnion fun c => (S c).2.isCompact
    have hcl : closure {genPt ξ} = (Set.univ : Set X) :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (hall q)
    have hirr : IsIrreducible (Set.univ : Set X) := hcl ▸ isIrreducible_singleton.closure
    haveI : IrreducibleSpace X := (irreducibleSpace_def X).2 hirr
    haveI : ∀ q : X, _root_.IsReduced (X.presheaf.stalk q) := fun q =>
      isReduced_of_injective (genMap ξ ⟨q, hall q⟩) (tie.gen.inj _)
    haveI : AlgebraicGeometry.IsReduced X := isReduced_of_isReduced_stalk X
    exact ⟨{}, isIntegral_of_irreducibleSpace_of_isReduced X⟩

end GlobalTheory.CompanionTheory.Ar.CoordNoeth

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToToStalk
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory CptModel

namespace CoordInhab

variable {o K : Type} [CommRing o] [Field K] [Algebra o K]

theorem inv_mem_of_span_eq_top {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (S : Subring K) (h1 : ∀ a : o, algebraMap o K a ∈ S)
    (h2 : ∀ j, algebraMap o K (x j) / algebraMap o K (x c) ∈ S) : (algebraMap o K (x c))⁻¹ ∈ S := by
  have h1mem : (1 : o) ∈ Submodule.span o (Set.range x) := by
    have h : (1 : o) ∈ Ideal.span (Set.range x) := by
      rw [hx]
      exact Submodule.mem_top
    exact h
  have key : ∀ y ∈ Submodule.span o (Set.range x),
      algebraMap o K y / algebraMap o K (x c) ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact h2 j
    | zero =>
      rw [map_zero, zero_div]
      exact S.zero_mem
    | add y z _ _ hy hz =>
      rw [map_add (f := _), add_div]
      exact S.add_mem hy hz
    | smul r y _ hy =>
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact S.mul_mem (h1 r) hy
  have h := key 1 h1mem
  rwa [map_one, one_div] at h

theorem algebraMap_mem_regAt (p : Cpt (pt (algebraMap o K))) (a : o) :
    algebraMap o K a ∈ regAt (pt (algebraMap o K)) p :=
  RingHom.mem_range.2 ⟨tS p.1 a, genMap_toStalk _ p a⟩

variable [IsFractionRing o K]

theorem inChart_iff {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (p : Cpt (pt (algebraMap o K))) :
    InChart (pt (algebraMap o K)) (fun j => algebraMap o K (x j)) c p ↔ x c ∉ p.1.asIdeal := by
  have hinj := IsFractionRing.injective o K
  constructor
  · rintro ⟨hne, hrat⟩ hmem
    have hne' : algebraMap o K (x c) ≠ 0 := hne
    have hinv : (algebraMap o K (x c))⁻¹ ∈ regAt (pt (algebraMap o K)) p :=
      inv_mem_of_span_eq_top x hx c _ (algebraMap_mem_regAt p) hrat
    obtain ⟨b, s, hs, -, hbs⟩ := (mem_regAt_iff _ p _).1 hinv
    apply hs
    have hsb : algebraMap o K s = algebraMap o K (b * x c) := by
      rw [map_mul, ← hbs, mul_comm ((algebraMap o K (x c))⁻¹) (algebraMap o K s), mul_assoc,
        inv_mul_cancel₀ hne', mul_one]
    rw [hinj hsb]
    exact p.1.asIdeal.mul_mem_left b hmem
  · intro hnot
    have hne : algebraMap o K (x c) ≠ 0 := by
      intro h0
      apply hnot
      rw [(map_eq_zero_iff _ hinj).1 h0]
      exact p.1.asIdeal.zero_mem
    exact ⟨hne, fun c' => (mem_regAt_iff _ p _).2 ⟨x c', x c, hnot, hne, div_mul_cancel₀ _ hne⟩⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

end CoordInhab

open CoordInhab

theorem ValAt.unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (hξ : IsCptGen ξ) (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hs, s, hsa, rfl⟩ := h
  obtain ⟨hs', s', hsa', rfl⟩ := h'
  exact congrArg (Scheme.stalkClosedPointTo z).hom (hξ.inj ⟨centre z, hs⟩ (hsa.trans hsa'.symm))

namespace CoordInhab

end CoordInhab

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeRing

variable {X : Scheme.{0}} {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']

theorem centre_specializes (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) ⤳ centre z := by
  have h := (IsLocalRing.specializes_closedPoint
    (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint R'))).map z.continuous
  exact h


set_option backward.isDefEq.respectTransparency false in
theorem stalkSpecializes_stalkClosedPointTo (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalkSpecializes (centre_specializes ψ z) ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ) ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (Spec.map (CommRingCat.ofHom ψ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_change : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (R R' : Type)
    [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ψ : R →+* R')
    (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R), ValAt ξ z a r →
    genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) →
    ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  intro X Ω _ ξ R R' _ _ _ _ ψ z a r h h'
  obtain ⟨h1, s, rfl, rfl⟩ := h
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalkSpecializes_stalkClosedPointTo ψ z)

end GlobalTheory.CompanionTheory.Ar.ChangeRing
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZarhinBundleKernelFirstCoordEquations
section
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

namespace ProjCoord

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

def push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) : Cpt (η ≫ f) :=
  ⟨f p.1, p.2.map f.continuous⟩

theorem genMap_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) :
    genMap (η ≫ f) (push η f p) = (genMap η p).comp (f.stalkMap p.1).hom := by
  have h1 := Scheme.stalkClosedPointTo_comp η f
  have h2 := Scheme.Hom.stalkSpecializes_stalkMap f _ _ p.2
  have h3 : X.presheaf.stalkSpecializes (push η f p).2 ≫ Scheme.stalkClosedPointTo (η ≫ f) =
      f.stalkMap p.1 ≫ (Y.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo η) :=
    (congrArg (X.presheaf.stalkSpecializes (push η f p).2 ≫ ·) h1).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo η) h2).trans
        (Category.assoc _ _ _)))
  exact congrArg (fun g => g.hom) h3

theorem regAt_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f] (p : Cpt η) :
    regAt (η ≫ f) (push η f p) = regAt η p := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  unfold regAt
  rw [genMap_push]
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := hb.2 s
    exact ⟨t, rfl⟩

theorem genMap_push_injective (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]
    (p : Cpt η) (h : Function.Injective (genMap η p)) :
    Function.Injective (genMap (η ≫ f) (push η f p)) := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  rw [genMap_push]
  exact h.comp hb.1

end OpenImm

section Chart

variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]

end Chart

section Away

open HomogeneousLocalization

variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]

end Away

section Poly

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem aeval_mul_of_isHomogeneous {B : Type} [CommRing B] [Algebra o B] (x : κ → B) (t : B)
    {g : MvPolynomial κ o} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun j => t * x j) g = t ^ n * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h : ∑ i ∈ d.support, d i = n := by
    have := hg (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

end Poly

end ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

end GlobalTheory.CompanionTheory.Ar
end
end

