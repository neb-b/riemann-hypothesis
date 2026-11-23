module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem eq_of_regAt_eq_of_coordTie :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω),
      CoordTie o ξ x → ∀ p q : Cpt ξ, regAt ξ p = regAt ξ q → p = q := by
  intro X Ω _ ξ o _ _ κ x h p q e
  obtain ⟨c, hc⟩ := h.cover p
  have hq : InChart ξ x c q := ⟨hc.1, fun c' => e ▸ hc.2 c'⟩
  haveI hloc : IsLocalRing (regAt ξ p) :=
    (regAt_isLocalRing_isFractionRing_stalk X Ω ξ h.gen p).1
  have hmem : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c), (s : Ω) ∈ regAt ξ p :=
    fun s => (h.ring c hc.1 s).1 s.2 p hc
  let f : Algebra.adjoin o (Set.range fun j => x j / x c) →+* regAt ξ p :=
    ((Algebra.adjoin o (Set.range fun j => x j / x c)).val :
      Algebra.adjoin o (Set.range fun j => x j / x c) →+* Ω).codRestrict (regAt ξ p) hmem
  have hI : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hp' : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hq' : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ q (s : Ω) := by
    intro s
    rw [hp' s]
    simp only [unitAt, e]
  exact (_root_.GlobalTheory.CompanionTheory.Ar.chart_point_of_prime X Ω ξ o κ x h c hc.1 _ hI).unique ⟨hc, hp'⟩ ⟨hq, hq'⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingsEqualImagesEqual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_prime_nonunitAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hg : IsCptGen ξ) (p : Cpt ξ) {o : Type} [CommRing o] [Algebra o Ω] (A : Subalgebra o Ω)
    (hA : ∀ s ∈ A, s ∈ regAt ξ p) :
    ∃ I : Ideal A, I.IsPrime ∧ ∀ s : A, s ∉ I ↔ unitAt ξ p (s : Ω) := by
  haveI : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).1
  let φ : A →+* regAt ξ p := RingHom.codRestrict A.val.toRingHom (regAt ξ p) (fun s => hA s s.2)
  refine ⟨Ideal.comap φ (IsLocalRing.maximalIdeal _), inferInstance, fun s => ?_⟩
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h.exists_right_inv
    have e : (s : Ω) * (t : Ω) = 1 := congrArg Subtype.val ht
    refine ⟨left_ne_zero_of_mul_eq_one e, hA s s.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right e]
    exact t.2
  · rintro ⟨h0, -, h2⟩
    refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, h2⟩ : regAt ξ p) (Subtype.ext ?_)
    exact mul_inv_cancel₀ h0

theorem unitAt_of_le {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (p : Cpt ξ) (p' : Cpt ξ') (h : regAt ξ p ≤ regAt ξ' p') {a : Ω}
    (ha : unitAt ξ p a) : unitAt ξ' p' a :=
  ⟨ha.1, h ha.2.1, h ha.2.2⟩

theorem image_eq_of_regAt_eq :
    ∀ (P X₁ X₂ : Scheme.{0}) (Ω : Type) [Field Ω] (ξ₀ : Sp Ω ⟶ P) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (f₁ : X₁ ⟶ P)
      (f₂ : X₂ ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → IsCptGen ξ₁ →
      IsCptGen ξ₂ → ξ₁ ≫ f₁ = ξ₀ → ξ₂ ≫ f₂ = ξ₀ → ∀ (p₁ : Cpt ξ₁) (p₂ : Cpt ξ₂), regAt ξ₁ p₁ = regAt ξ₂ p₂ →
      f₁ p₁.1 = f₂ p₂.1 := by
  intro P X₁ X₂ Ω _ ξ₀ ξ₁ ξ₂ f₁ f₂ o _ _ κ u hu g₁ g₂ e₁ e₂ p₁ p₂ hR
  have dom : ∀ {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ P), ξ ≫ f = ξ₀ →
      Dominates ξ ξ₀ f (RingHom.id Ω) := by
    intro X ξ f e
    have : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _ := by
      rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id]
    show ξ ≫ f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ₀
    rw [this, Category.id_comp, e]
  obtain ⟨h₁, r₁, n₁⟩ := RegAtDom.regAt_dominates P Ω ξ₀ X₁ Ω ξ₁ f₁ (RingHom.id Ω) (dom ξ₁ f₁ e₁) p₁
  obtain ⟨h₂, r₂, n₂⟩ := RegAtDom.regAt_dominates P Ω ξ₀ X₂ Ω ξ₂ f₂ (RingHom.id Ω) (dom ξ₂ f₂ e₂) p₂
  set a₁ : Cpt ξ₀ := ⟨f₁ p₁.1, h₁⟩ with ha₁
  set a₂ : Cpt ξ₀ := ⟨f₂ p₂.1, h₂⟩ with ha₂
  have l₁ : regAt ξ₀ a₁ ≤ regAt ξ₁ p₁ := fun a ha => r₁ a ha
  have l₂ : regAt ξ₀ a₂ ≤ regAt ξ₁ p₁ := fun a ha => hR ▸ r₂ a ha
  have m₁ : ∀ a ∈ regAt ξ₀ a₁, unitAt ξ₁ p₁ a → unitAt ξ₀ a₁ a := n₁ g₁
  have m₂ : ∀ a ∈ regAt ξ₀ a₂, unitAt ξ₁ p₁ a → unitAt ξ₀ a₂ a := fun a ha h =>
    n₂ g₂ a ha ⟨h.1, hR ▸ h.2.1, hR ▸ h.2.2⟩
  obtain ⟨c₁, hc₁⟩ := hu.cover a₁
  obtain ⟨c, hc⟩ := hu.cover a₂

  have hq : unitAt ξ₀ a₁ (u c / u c₁) := by
    refine m₁ _ (hc₁.2 c) ⟨div_ne_zero hc.1 hc₁.1, l₁ (hc₁.2 c), ?_⟩
    rw [inv_div]
    exact l₂ (hc.2 c₁)
  have hin : InChart ξ₀ u c a₁ := by
    refine ⟨hc.1, fun j => ?_⟩
    have : u j / u c = u j / u c₁ * (u c / u c₁)⁻¹ := by
      have := hc₁.1
      have := hc.1
      field_simp
    rw [this]
    exact mul_mem (hc₁.2 j) hq.2.2
  set A := Algebra.adjoin o (Set.range fun j => u j / u c) with hA
  have A₁ : ∀ s ∈ A, s ∈ regAt ξ₀ a₁ := fun s hs => (hu.ring c hc.1 s).1 hs a₁ hin
  have A₂ : ∀ s ∈ A, s ∈ regAt ξ₀ a₂ := fun s hs => (hu.ring c hc.1 s).1 hs a₂ hc
  obtain ⟨I, hI, hI₁⟩ := exists_prime_nonunitAt ξ₀ hu.gen a₁ A A₁
  have hI₂ : ∀ s : A, s ∉ I ↔ unitAt ξ₀ a₂ (s : Ω) := fun s => by
    rw [hI₁ s]
    exact ⟨fun h => m₂ _ (A₂ s s.2) (unitAt_of_le ξ₀ ξ₁ a₁ p₁ l₁ h),
      fun h => m₁ _ (A₁ s s.2) (unitAt_of_le ξ₀ ξ₁ a₂ p₁ l₂ h)⟩
  have e := (_root_.GlobalTheory.CompanionTheory.Ar.chart_point_of_prime P Ω ξ₀ o κ u hu c hc.1 I hI).unique ⟨hin, hI₁⟩ ⟨hc, hI₂⟩
  exact congrArg Subtype.val e

end GlobalTheory.CompanionTheory.Ar.SncBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothOpenImmersionRange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem smoothOfRelativeDimension_opensRange_ι_comp
    (A B T : Scheme.{0}) (j : A ⟶ B) [IsOpenImmersion j] (g : B ⟶ T) (n : ℕ)
    (h : SmoothOfRelativeDimension n (j ≫ g)) :
    SmoothOfRelativeDimension n (j.opensRange.ι ≫ g) := by
  have e : j.opensRange.ι = j.isoOpensRange.inv ≫ j :=
    (Iso.eq_inv_comp _).mpr j.isoOpensRange_hom_ι
  rw [e, Category.assoc, ← zero_add n]
  exact smoothOfRelativeDimension_comp 0 n _ _

end GlobalTheory.CompanionTheory.Ar.SncBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothSchemeStalksDomains
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem isDomain_and_isIntegrallyClosed_stalk_sp_field (K : Type) [Field K] (y : Sp K) :
    IsDomain ((Sp K).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp K).presheaf.stalk y) := by
  let p : PrimeSpectrum K := y
  have hle : p.asIdeal.primeCompl ≤ IsUnit.submonoid K := fun x hx =>
    isUnit_iff_ne_zero.2 fun h0 => hx (h0 ▸ p.asIdeal.zero_mem)
  let e₁ : K ≃+* Localization.AtPrime p.asIdeal :=
    (IsLocalization.atUnits K p.asIdeal.primeCompl hle).toRingEquiv
  let e₂ : (Sp K).presheaf.stalk y ≃+* Localization.AtPrime p.asIdeal :=
    (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of K) p).commRingCatIsoToRingEquiv
  let e : K ≃+* (Sp K).presheaf.stalk y := e₁.trans e₂.symm
  haveI := Field.instIsIntegrallyClosed K
  exact ⟨(MulEquiv.isField (Field.toIsField K) e.symm.toMulEquiv).isDomain, IsIntegrallyClosed.of_equiv e⟩

theorem isDomain_stalk_of_smoothOfRelativeDimension_field (K : Type) [Field K] (e : ℕ)
    (X : Scheme.{0}) (g : X ⟶ Sp K) (hg : SmoothOfRelativeDimension e g) (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  haveI : Smooth g := SmoothOfRelativeDimension.smooth e g
  exact (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g
    (isDomain_and_isIntegrallyClosed_stalk_sp_field K) x).1

end GlobalTheory.CompanionTheory.Ar.SncBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenTangentsPullback
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Transfer

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left} {R : Type} [CommRing R]

def pushAt (h : IsGrpPullback G' G f φ) {T : Over S'} (v : T ⟶ G') : Over.mk (T.hom ≫ f) ⟶ G :=
  Over.homMk (v.left ≫ φ) (by
    change (v.left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w v])

theorem pushAt_one (h : IsGrpPullback G' G f φ) (T : Over S') : pushAt h (1 : T ⟶ G') = 1 := by
  have e : pushAt h (1 : T ⟶ G') * pushAt h (1 : T ⟶ G') = pushAt h (1 : T ⟶ G') := by
    apply Over.OverMorphism.ext
    have := h.2 T 1 1 (pushAt h 1) (pushAt h 1) rfl rfl
    rw [this, _root_.mul_one]
    rfl
  exact mul_eq_left.mp e

def tanMap (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (v : epsAt y ⟶ G') : epsAt (y ≫ f) ⟶ G :=
  Over.homMk (v.left ≫ φ) (by
    change (v.left ≫ φ) ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ y ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc]
    have := Over.w v
    change v.left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ y at this
    rw [this, Category.assoc])

@[simp] theorem tanMap_left (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (v : epsAt y ⟶ G') :
    (tanMap h y v).left = v.left ≫ φ := rfl

def rebase₂ (y : Sp R ⟶ S') (f : S' ⟶ S) : epsAt (y ≫ f) ⟶ Over.mk ((epsAt y).hom ≫ f) :=
  Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ (spMap (algebraMap R (DualNumber R)) ≫ y) ≫ f = spMap (algebraMap R (DualNumber R)) ≫ y ≫ f
    rw [Category.id_comp, Category.assoc])

theorem tanMap_eq (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (v : epsAt y ⟶ G') :
    tanMap h y v = rebase₂ y f ≫ pushAt h v := by
  apply Over.OverMorphism.ext
  change v.left ≫ φ = 𝟙 _ ≫ v.left ≫ φ
  rw [Category.id_comp]

theorem tanMap_mul (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (a b : epsAt y ⟶ G') :
    tanMap h y (a * b) = tanMap h y a * tanMap h y b := by
  rw [tanMap_eq, tanMap_eq, tanMap_eq, ← MonObj.comp_mul]
  congr 1
  apply Over.OverMorphism.ext
  exact (h.2 _ a b (pushAt h a) (pushAt h b) rfl rfl).symm

theorem left_eq_of_comp (h : IsGrpPullback G' G f φ) {Z : Scheme.{0}} {a b : Z ⟶ G'.left}
    (h₁ : a ≫ φ = b ≫ φ) (h₂ : a ≫ G'.hom = b ≫ G'.hom) : a = b :=
  h.1.hom_ext h₁ h₂

theorem tanMap_injective (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') : Function.Injective (tanMap h y) := by
  intro a b e
  apply Over.OverMorphism.ext
  refine left_eq_of_comp h (congrArg (fun z => z.left) e) ?_
  rw [Over.w a, Over.w b]

theorem tanMap_surjective (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') : Function.Surjective (tanMap h y) := by
  intro w
  have hw : w.left ≫ G.hom = (spMap (algebraMap R (DualNumber R)) ≫ y) ≫ f := by
    rw [Category.assoc]; exact Over.w w
  refine ⟨Over.homMk (h.1.lift _ _ hw) (h.1.lift_snd _ _ hw), ?_⟩
  apply Over.OverMorphism.ext
  exact h.1.lift_fst _ _ hw

def tanEquiv (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') : (epsAt y ⟶ G') ≃* (epsAt (y ≫ f) ⟶ G) :=
  { Equiv.ofBijective (tanMap h y) ⟨tanMap_injective h y, tanMap_surjective h y⟩ with
    map_mul' := tanMap_mul h y }

theorem one_left_comp (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') :
    (1 : Over.mk y ⟶ G').left ≫ φ = (1 : Over.mk (y ≫ f) ⟶ G).left :=
  congrArg (fun z => z.left) (pushAt_one h (Over.mk y))

theorem comp_fst_hom (y : Sp R ⟶ S') :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) ≫ y = y := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext a; rfl
  rw [this]
  simp

theorem isTanAt_iff (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (v : epsAt y ⟶ G') :
    IsTanAt G (y ≫ f) (tanMap h y v) ↔ IsTanAt G' y v := by
  unfold IsTanAt
  rw [← one_left_comp h y, tanMap_left]
  constructor
  · intro e
    refine left_eq_of_comp h ?_ ?_
    · rw [Category.assoc]; exact e
    · have h1 : v.left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ y := Over.w v
      have h2 : (1 : Over.mk y ⟶ G').left ≫ G'.hom = y := Over.w _
      rw [Category.assoc, h1, h2]
      exact comp_fst_hom y
  · intro e
    rw [← Category.assoc, e]

theorem epsMul_comp_algebraMap (c : R) : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
  ext a <;> simp [epsMul]

theorem eps_left_iff (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (c : R) (u v : epsAt y ⟶ G') :
    (tanMap h y u).left = spMap (epsMul c) ≫ (tanMap h y v).left ↔ u.left = spMap (epsMul c) ≫ v.left := by
  rw [tanMap_left, tanMap_left]
  constructor
  · intro e
    refine left_eq_of_comp h ?_ ?_
    · rw [Category.assoc]; exact e
    · have h1 : u.left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ y := Over.w u
      have h2 : v.left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ y := Over.w v
      rw [Category.assoc, h1, h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        epsMul_comp_algebraMap]
  · intro e
    rw [e, Category.assoc]

theorem isComb_iff (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') {n : ℕ} (c : Fin n → R)
    (v : Fin n → (epsAt y ⟶ G')) (w : epsAt y ⟶ G') :
    IsComb c (fun i => tanMap h y (v i)) (tanMap h y w) ↔ IsComb c v w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    obtain ⟨u', rfl⟩ : ∃ u' : Fin n → (epsAt y ⟶ G'), u = fun i => tanMap h y (u' i) :=
      ⟨fun i => (tanMap_surjective h y (u i)).choose,
        funext fun i => ((tanMap_surjective h y (u i)).choose_spec).symm⟩
    refine ⟨u', fun i => (eps_left_iff h y _ _ _).1 (hu i), (tanEquiv h y).injective ?_⟩
    have := map_list_prod (tanEquiv h y) (List.ofFn u')
    rw [List.map_ofFn] at this
    rw [this]
    exact hw
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => tanMap h y (u i), fun i => (eps_left_iff h y _ _ _).2 (hu i), ?_⟩
    have := map_list_prod (tanEquiv h y) (List.ofFn u)
    rw [List.map_ofFn] at this
    exact this

variable {O : Type} [CommRing O]

theorem isEigVec_iff (h : IsGrpPullback G' G f φ) (act' : OAct O G') (act : OAct O G)
    (hact : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (y : Sp R ⟶ S') (τ : O →+* R) (v : epsAt y ⟶ G') :
    IsEigVec act (y ≫ f) τ (tanMap h y v) ↔ IsEigVec act' y τ v := by
  have key : ∀ a, tanMap h y v ≫ act.act a = tanMap h y (v ≫ act'.act a) := fun a => by
    apply Over.OverMorphism.ext
    change (v.left ≫ φ) ≫ (act.act a).left = (v.left ≫ (act'.act a).left) ≫ φ
    rw [Category.assoc, Category.assoc, hact]
  unfold IsEigVec
  rw [isTanAt_iff]
  refine and_congr_right fun _ => forall_congr' fun a => ?_
  rw [key]
  exact eps_left_iff h y (τ a) _ _

theorem isEigFrame_iff (h : IsGrpPullback G' G f φ) (act' : OAct O G') (act : OAct O G)
    (hact : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (y : Sp R ⟶ S') (τ : O →+* R) {n : ℕ}
    (v : Fin n → (epsAt y ⟶ G')) :
    IsEigFrame act (y ≫ f) τ (fun i => tanMap h y (v i)) ↔ IsEigFrame act' y τ v := by
  unfold IsEigFrame
  refine and_congr (forall_congr' fun i => isEigVec_iff h act' act hact y τ (v i)) ?_
  constructor
  · intro H w hw
    obtain ⟨c, hc, hu⟩ := H (tanMap h y w) ((isEigVec_iff h act' act hact y τ w).2 hw)
    exact ⟨c, (isComb_iff h y c v w).1 hc, fun c' hc' => hu c' ((isComb_iff h y c' v w).2 hc')⟩
  · intro H w hw
    obtain ⟨w', rfl⟩ := tanMap_surjective h y w
    obtain ⟨c, hc, hu⟩ := H w' ((isEigVec_iff h act' act hact y τ w').1 hw)
    exact ⟨c, (isComb_iff h y c v w').2 hc, fun c' hc' => hu c' ((isComb_iff h y c' v w').1 hc')⟩

end GlobalTheory.CompanionTheory.Ar.LocFn.Transfer

namespace GlobalTheory.CompanionTheory.Ar.LocFn

open Transfer

theorem dualMap_eq_pj {A T : Type} [CommRing A] [CommRing T] (θ : A →+* T) :
    Formalism.L2.Pj.dualMap θ = GlobalTheory.CompanionTheory.Ar.dualMap θ := by
  apply RingHom.ext
  intro a
  rfl

theorem exists_eigFrame_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : Type) [CommRing T] (y : Sp T ⟶ Xo.XF c) (A : Type) [CommRing A] (x₀ : Sp A ⟶ Y.X) (κ : c.F →+* A) (θ : A →+* T) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt x₀ ⟶ Y.t.G)), spMap θ ≫ x₀ = y ≫ Y.j → StableEig Y.t x₀ κ σ e → ∃ V : Fin r → (epsAt (under y) ⟶ Xo.univ.t.G), (∀ i, Tied Y y (V i).left (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left)) ∧ IsEigFrame Xo.univ.t.act (under y) ((θ.comp κ).comp (tauIn c σ)) V := by
  intro E _ _ _ H D l Xo c O _ β Y T _ y A _ x₀ κ θ σ r e hx hst
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  have hover : ∀ i, (spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e i).left) ≫ Y.t.G.hom =
      spMap (algebraMap T (DualNumber T)) ≫ y ≫ Y.j := fun i => by
    have h1 : (e i).left ≫ Y.t.G.hom = spMap (algebraMap A (DualNumber A)) ≫ x₀ := Over.w (e i)
    rw [Category.assoc, h1, ← hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    have : (GlobalTheory.CompanionTheory.Ar.dualMap θ).comp (algebraMap A (DualNumber A)) = (algebraMap T (DualNumber T)).comp θ := by
      have hA : ∀ a : A, algebraMap A (DualNumber A) a = TrivSqZeroExt.inl a := fun _ => rfl
      have hT : ∀ a : T, algebraMap T (DualNumber T) a = TrivSqZeroExt.inl a := fun _ => rfl
      ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, hA, hT]
    rw [this]
  let v : Fin r → (epsAt (y ≫ Y.j) ⟶ Y.t.G) := fun i => Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e i).left) (hover i)
  have hv : IsEigFrame Y.t.act (y ≫ Y.j) ((θ.comp κ).comp (tauIn c σ)) v :=
    hst T θ (y ≫ Y.j) hx v (fun i => rfl)
  let w : Fin r → (epsAt y ⟶ Y.oF.t.G) := fun i => (tanMap_surjective hq y (v i)).choose
  have hw : ∀ i, tanMap hq y (w i) = v i := fun i => (tanMap_surjective hq y (v i)).choose_spec
  have hfr : IsEigFrame Y.oF.t.act y ((θ.comp κ).comp (tauIn c σ)) w := by
    refine (isEigFrame_iff hq Y.oF.t.act Y.t.act Y.m.act y _ w).1 ?_
    simpa only [hw] using hv
  refine ⟨fun i => tanMap hp y (w i), fun i => ⟨(w i).left, Over.w (w i), rfl, ?_⟩,
    (isEigFrame_iff hp Y.oF.t.act Xo.univ.t.act Y.m0.act y _ w).2 hfr⟩
  have := congrArg (fun z => z.left) (hw i)
  rw [dualMap_eq_pj]
  exact this

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

abbrev XQ (X : Scheme.{0}) : Scheme.{0} := pullback (toZ X) (toZ (Sp ℚ))

abbrev XQ.fst (X : Scheme.{0}) : XQ X ⟶ X := pullback.fst _ _

abbrev XQ.snd (X : Scheme.{0}) : XQ X ⟶ Sp ℚ := pullback.snd _ _

def toXQ {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) : Sp F ⟶ XQ X :=
  pullback.lift x (spMap (algebraMap ℚ F)) (specULiftZIsTerminal.hom_ext _ _)

@[simp] theorem toXQ_fst {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) :
    toXQ x ≫ XQ.fst X = x := pullback.lift_fst _ _ _

def evalAt {S : Scheme.{0}} (U : S.Opens) (f : Γ(S, U)) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) : ℂ :=
  (Scheme.stalkClosedPointTo z).hom (S.presheaf.germ U (centre z) hz f)

def anTop (S : Scheme.{0}) : TopologicalSpace (Sp ℂ ⟶ S) :=
  TopologicalSpace.generateFrom
    {A | ∃ (U : S.Opens) (f : Γ(S, U)) (V : Set ℂ), IsOpen V ∧ A = {z | ∃ hz : centre z ∈ U, evalAt U f z hz ∈ V}}

section Good

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  {M : LieModel G ξ Li}

def GoodAt (h : LieMetric M y) (C : ℝ) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) {GK : Over (Sp L)}
    [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) : Prop :=
  letI := τ.addCommGroup
  ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)),
    ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT →
    ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier),
      IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier,
      (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (ε a)).left)) →
      ∀ (σ : L →+* ℂ) (w : Fin r → ℂ),
        C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧
        sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2

end Good

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end
end

