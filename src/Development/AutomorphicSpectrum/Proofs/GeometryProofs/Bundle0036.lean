module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDominatingSurjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

section Surj

variable {X : Scheme.{0}}

theorem germ_closedPoint_eq_appLE {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X) (U : X.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp only [Scheme.Hom.appLE]
  rfl

theorem val_comp_spec {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S] (φ : R ⟶ S) (z : Spec R ⟶ X)
    (w : Spec S ⟶ X) (hw : Spec.map φ ≫ z = w) (U : X.Opens)
    (h1 : z (IsLocalRing.closedPoint R) ∈ U) (h2 : w (IsLocalRing.closedPoint S) ∈ U) (t : Γ(X, U)) :
    φ.hom ((Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ U _ h1).hom t)) =
      (Scheme.stalkClosedPointTo w).hom ((X.presheaf.germ U _ h2).hom t) := by
  subst hw
  have key : (Spec.map φ ≫ z).appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem _ h2).ge ≫
      (Scheme.ΓSpecIso S).hom =
      z.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem z h1).ge ≫ (Scheme.ΓSpecIso R).hom ≫ φ := by
    have e₂ : (⊤ : (Spec S).Opens) ≤ (Spec.map φ) ⁻¹ᵁ ⊤ := by simp
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) z U ⊤ ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem z h1).ge e₂,
      Category.assoc, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have e1 := congrArg (fun g => (g ≫ φ).hom t) (germ_closedPoint_eq_appLE z U h1)
  have e2 := congrArg (fun g => g.hom t) (germ_closedPoint_eq_appLE (Spec.map φ ≫ z) U h2)
  have e3 := congrArg (fun g => g.hom t) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1 e2 e3
  rw [e1, e2, e3]

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Ω' : Type} [Field Ω']

def DomAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω') (A : ValuationSubring Ω') (p : Cpt ξ) : Prop :=
  ∃ ν : X.presheaf.stalk p.1 →+* A, IsLocalHom ν ∧ ∀ s, (ν s : Ω') = i (genMap ξ p s)

theorem DomAt.inv_mem {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p : Cpt ξ} (h : DomAt ξ i A p) {a : Ω}
    (h0 : a ≠ 0) (ha : a ∈ regAt ξ p) (hi : i a⁻¹ ∈ A) : a⁻¹ ∈ regAt ξ p := by
  obtain ⟨ν, hloc, hν⟩ := h
  obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
  have hu : IsUnit (ν s) := by
    refine IsUnit.of_mul_eq_one (a := ν s) ⟨i (genMap ξ p s)⁻¹, hi⟩ ?_
    apply Subtype.ext
    show (ν s : Ω') * i (genMap ξ p s)⁻¹ = 1
    rw [hν s, ← map_mul, mul_inv_cancel₀ h0, map_one]
  have hs : IsUnit s := (isUnit_map_iff ν s).mp hu
  refine RingHom.mem_range.mpr ⟨↑hs.unit⁻¹, ?_⟩
  rw [map_units_inv, IsUnit.unit_spec]

theorem genMap_germ (r : Cpt ξ) {U : X.Opens} (hr : r.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ r ((X.presheaf.germ U r.1 hr).hom t) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr)).hom t) := by
  have e := congrArg (fun g => g.hom t) (X.presheaf.germ_stalkSpecializes hr r.2)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes r.2).hom ((X.presheaf.germ U r.1 hr).hom t)) = _
  rw [e]

theorem DomAt.eq_of_mem_affine {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p p' : Cpt ξ} (h : DomAt ξ i A p)
    (h' : DomAt ξ i A p') {U : X.Opens} (hU : IsAffineOpen U) (hp : p.1 ∈ U) (hp' : p'.1 ∈ U) : p.1 = p'.1 := by
  obtain ⟨ν, hν1, hν⟩ := h
  obtain ⟨ν', hν1', hν'⟩ := h'
  have key : ∀ b : Γ(X, U), p.1 ∈ X.basicOpen b ↔ p'.1 ∈ X.basicOpen b := by
    intro b
    have e : ν ((X.presheaf.germ U p.1 hp).hom b) = ν' ((X.presheaf.germ U p'.1 hp').hom b) := by
      apply Subtype.ext
      simp only [hν, hν', genMap_germ]
    rw [X.mem_basicOpen b p.1 hp, X.mem_basicOpen b p'.1 hp', ← isUnit_map_iff ν, ← isUnit_map_iff ν', e]
  have sp : ∀ {a c : X}, a ∈ U → c ∈ U → (∀ b : Γ(X, U), a ∈ X.basicOpen b → c ∈ X.basicOpen b) → c ⤳ a := by
    intro a c ha hc hab
    rw [specializes_iff_forall_open]
    intro s hs has
    obtain ⟨b, hb, hab'⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨a, has⟩ ha
    exact hb (hab b hab')
  exact ((sp hp' hp (fun b => (key b).2)).antisymm (sp hp hp' (fun b => (key b).1))).eq

theorem domAt_of_spec {i : Ω →+* Ω'} {A : ValuationSubring Ω'} (z : Spec (CommRingCat.of A) ⟶ X)
    (hz : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ z = Spec.map (CommRingCat.ofHom i) ≫ ξ)
    (h : genPt ξ ⤳ z (IsLocalRing.closedPoint A)) :
    DomAt ξ i A ⟨z (IsLocalRing.closedPoint A), h⟩ := by
  refine ⟨(Scheme.stalkClosedPointTo z).hom, inferInstance, fun s => ?_⟩
  obtain ⟨U, hU, t, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg : genPt ξ ∈ U := h.mem_open U.isOpen hU
  have hw : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') ∈ U := by
    rw [← hz]
    exact ((IsLocalRing.specializes_closedPoint _).map z.continuous).mem_open U.isOpen hU
  have e1 := val_comp_spec (CommRingCat.ofHom (algebraMap A Ω')) z _ hz U hU hw t
  have e2 := val_comp_spec (CommRingCat.ofHom i) ξ _ rfl U hg hw t
  have e3 := congrArg i (genMap_germ (ξ := ξ) ⟨z (IsLocalRing.closedPoint A), h⟩ hU t)
  exact e1.trans (e2.symm.trans e3.symm)

private theorem exists_domAt_of_injective_genMap (i : Ω →+* Ω') (p : Cpt ξ) (hinj : Function.Injective (genMap ξ p)) :
    ∃ A : ValuationSubring Ω', DomAt ξ i A p := by
  let g : X.presheaf.stalk p.1 →+* Ω' := i.comp (genMap ξ p)
  have hg : Function.Injective g := i.injective.comp hinj
  obtain ⟨A, hA⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range g)
  obtain ⟨hle, hloc⟩ := hA
  have hmem : ∀ s, g s ∈ A.toSubring := fun s => hle ⟨s, rfl⟩
  refine ⟨A, g.codRestrict A.toSubring hmem, ⟨fun s hs => ?_⟩, fun s => rfl⟩
  obtain ⟨v, hv⟩ := hs.exists_right_inv
  have hv' : g s * (v : Ω') = 1 := congrArg Subtype.val hv
  let y : (LocalSubring.range g).toSubring := ⟨g s, ⟨s, rfl⟩⟩
  have hy : IsUnit y := by
    apply hloc.map_nonunit
    refine IsUnit.of_mul_eq_one ⟨v, v.2⟩ ?_
    exact Subtype.ext hv'
  obtain ⟨w, hw⟩ := hy.exists_right_inv
  obtain ⟨s', hs'⟩ := w.2
  refine IsUnit.of_mul_eq_one s' ?_
  apply hg
  rw [map_mul, map_one, hs']
  exact congrArg Subtype.val hw

private theorem inChart_of_domAt_of_div_mem {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p : Cpt ξ} (h : DomAt ξ i A p)
    {κ : Type} {x : κ → Ω} {c : κ} (hxc : x c ≠ 0) (hA : ∀ c', i (x c' / x c) ∈ A) {c'' : κ}
    (h'' : InChart ξ x c'' p) : InChart ξ x c p := by
  refine ⟨hxc, fun c' => ?_⟩
  have hc'' : x c'' ≠ 0 := h''.1
  have h1 : x c / x c'' ∈ regAt ξ p := h''.2 c
  have h0 : x c / x c'' ≠ 0 := div_ne_zero hxc hc''
  have h2 : (x c / x c'')⁻¹ ∈ regAt ξ p := h.inv_mem h0 h1 (by rw [inv_div]; exact hA c'')
  have e : x c' / x c = (x c' / x c'') * (x c / x c'')⁻¹ := by
    rw [inv_div, div_mul_div_cancel₀ hc'']
  rw [e]
  exact mul_mem (h''.2 c') h2

private theorem div_mem_of_valuation_le {K : Type} [Field K] (A : ValuationSubring K) {a b : K} (hb : b ≠ 0)
    (h : A.valuation a ≤ A.valuation b) : a / b ∈ A := by
  rw [← A.valuation_le_one_iff, map_div₀]
  have hb' : A.valuation b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  exact div_le_one_of_le₀ h zero_le'

theorem surjective_of_dominates (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type)
    [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (s' : X' ⟶ Spec (CommRingCat.of ℤ)) (f : X' ⟶ X) (i : Ω →+* Ω') (hc : CoordTie ℤ ξ x)
    (hg : ∀ q : X, genPt ξ ⤳ q) (hp : IsProper s') (hd : Dominates ξ' ξ f i) : Function.Surjective f := by
  intro q
  obtain ⟨A, hdom⟩ := exists_domAt_of_injective_genMap i ⟨q, hg q⟩ (hc.gen.inj ⟨q, hg q⟩)
  have hex : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s' := by
    rw [← UniversallyClosed.eq_valuativeCriterion]
    infer_instance
  let S : ValuativeCommSq s' :=
    { R := A, K := Ω', i₁ := ξ', i₂ := specZIsTerminal.from _, commSq := ⟨specZIsTerminal.hom_ext _ _⟩ }
  obtain ⟨⟨l, hl1, -⟩⟩ := (hex.1 S).exists_lift
  have hl : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ l = ξ' := hl1
  have hz : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ (l ≫ f) = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
    rw [← Category.assoc, hl]
    exact hd
  have hdom' := domAt_of_spec (i := i) (A := A) (l ≫ f) hz (hg _)
  obtain ⟨c₁, hc₁⟩ := hc.cover ⟨q, hg q⟩
  have : Nonempty κ := ⟨c₁⟩
  obtain ⟨c, hcmax⟩ := Finite.exists_max (fun c => A.valuation (i (x c)))
  have hxc : x c ≠ 0 := by
    intro h0
    have h1 := hcmax c₁
    simp only [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hc₁.1 ((map_eq_zero i).1 h1)
  have hA : ∀ c', i (x c' / x c) ∈ A := fun c' => by
    rw [map_div₀]
    exact div_mem_of_valuation_le A ((map_ne_zero i).2 hxc) (hcmax c')
  obtain ⟨U, hUaff, hUmem⟩ := hc.affine c hxc
  have hq : q ∈ U := (hUmem q).2 ⟨hg q, inChart_of_domAt_of_div_mem hdom hxc hA hc₁⟩
  obtain ⟨c₂, hc₂⟩ := hc.cover ⟨(l ≫ f) (IsLocalRing.closedPoint A), hg _⟩
  have hq' : (l ≫ f) (IsLocalRing.closedPoint A) ∈ U :=
    (hUmem _).2 ⟨hg _, inChart_of_domAt_of_div_mem hdom' hxc hA hc₂⟩
  have e := DomAt.eq_of_mem_affine hdom hdom' hUaff hq hq'
  exact ⟨l (IsLocalRing.closedPoint A), e.symm⟩

end Surj
end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstReg

theorem stalkClosedPointTo_germ_top {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ ⊤ (genPt ξ) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (ξ.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (genPt ξ) trivial ≫ Scheme.stalkClosedPointTo ξ =
      ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
    refine (Scheme.germ_stalkClosedPointTo ξ ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem genMap_germ_const {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) {O : Type} [CommRing O] [Algebra O Ω]
    (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (p : Cpt ξ) (o : O) :
    genMap ξ p ((X.presheaf.germ ⊤ p.1 trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = algebraMap O Ω o := by
  have h1 : genMap ξ p ((X.presheaf.germ ⊤ p.1 trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ ⊤ (genPt ξ) trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, stalkClosedPointTo_germ_top]
  have h2 : ξ.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom (algebraMap O Ω))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hs]; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom o)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O Ω)))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (algebraMap O Ω o) =
      (Spec.map (CommRingCat.ofHom (algebraMap O Ω))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  rw [← h3']
  simp

theorem isUnit_germ_const_iff {X : Scheme.{0}} {O : Type} [CommRing O]
    (s : X ⟶ Spec (CommRingCat.of O)) (x : X) (o : O) :
    IsUnit ((X.presheaf.germ ⊤ x trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) ↔ o ∉ (s x).asIdeal := by
  rw [← Scheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top, Scheme.Hom.mem_preimage,
    basicOpen_eq_of_affine (R := CommRingCat.of O) o]
  exact Iff.rfl

theorem regular_const : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)), ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p ∧ (IsCptGen ξ → (unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal)) := by
  intro X Ω _ ξ O _ _ _ s hs p o
  have hg := genMap_germ_const ξ s hs p o
  refine ⟨⟨_, hg⟩, fun hc => ?_⟩
  rw [← isUnit_germ_const_iff s p.1 o]
  constructor
  · intro hu
    obtain ⟨u, hu, e⟩ := (unitAt_iff_of_isCptGen ξ hc p _).1 hu
    rwa [← hc.inj p (e.trans hg.symm)]
  · intro hu
    rw [← hg]
    exact RegAtMono.unitAt_of_isUnit ξ p hu

end GlobalTheory.CompanionTheory.Ar.Flat.ConstReg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionDivisorEq
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem length_localizedModule_quot_eq {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R}
    (h₁ : ∀ x ∈ J₁, ∃ s, s ∉ W ∧ s * x ∈ J₂) (h₂ : ∀ x ∈ J₂, ∃ s, s ∉ W ∧ s * x ∈ J₁) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₁)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₂)) := by
  have key : ∀ {A B : Ideal R}, (∀ x ∈ A, ∃ s, s ∉ W ∧ s * x ∈ B) →
      Submodule.localized W.primeCompl (M := R) A ≤ Submodule.localized W.primeCompl (M := R) B := by
    intro A B h y hy
    obtain ⟨m, hm, s, rfl⟩ := hy
    obtain ⟨t, ht, htm⟩ := h m hm
    refine ⟨t * m, htm, ⟨t, ht⟩ * s, ?_⟩
    exact IsLocalizedModule.mk'_cancel_left _ _ _ _
  have heq : Submodule.localized W.primeCompl (M := R) J₁ = Submodule.localized W.primeCompl (M := R) J₂ :=
    le_antisymm (key h₁) (key h₂)
  have e₁ := (localizedQuotientEquiv W.primeCompl (M := R) J₁).length_eq
  have e₂ := (localizedQuotientEquiv W.primeCompl (M := R) J₂).length_eq
  have e₃ := (Submodule.quotEquivOfEq _ _ heq).length_eq
  exact e₁.symm.trans (e₃.trans e₂)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem IsUnitSec.symm {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) : IsUnitSec P g f := by
  intro W hW hP hR
  obtain ⟨u, v, hu, hv, hm⟩ := h W hW hP hR
  refine ⟨v, u, hv, hu, ?_⟩
  have := P.neg_mem hm
  rwa [neg_sub] at this

theorem divSupp_subset_of_isUnitSec {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) :
    divSupp P f ⊆ divSupp P g := by
  rintro W ⟨hmin, hrel⟩
  have hWp : W.IsPrime := hmin.1.1
  have hP : P ≤ W := le_sup_left.trans hmin.1.2
  have hf : f ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨u, v, hu, hv, hm⟩ := h W hWp hP hrel
  have hvg : v * g ∈ W := by
    have e : v * g = u * f - (u * f - v * g) := by ring
    rw [e]
    exact W.sub_mem (W.mul_mem_left u hf) (hP hm)
  have hg : g ∈ W := (hWp.mem_or_mem hvg).resolve_left hv
  refine ⟨⟨⟨hWp, sup_le hP ((Ideal.span_singleton_le_iff_mem _).mpr hg)⟩, ?_⟩, hrel⟩
  rintro W' ⟨hW'p, hW'le⟩ hW'W
  have hP' : P ≤ W' := le_sup_left.trans hW'le
  have hg' : g ∈ W' := hW'le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have huf : u * f ∈ W' := by
    have e : u * f = (u * f - v * g) + v * g := by ring
    rw [e]
    exact W'.add_mem (hP' hm) (W'.mul_mem_left v hg')
  have hf' : f ∈ W' := (hW'p.mem_or_mem huf).resolve_left fun hu' => hu (hW'W hu')
  exact hmin.2 ⟨hW'p, sup_le hP' ((Ideal.span_singleton_le_iff_mem _).mpr hf')⟩ hW'W

theorem mul_mem_sup_span_of_sub_mem {R : Type*} [CommRing R] {P : Ideal R} {f g u v x : R}
    (hm : u * f - v * g ∈ P) (hx : x ∈ P ⊔ Ideal.span {f}) : u * x ∈ P ⊔ Ideal.span {g} := by
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have e : u * (p + a * f) = (u * p + a * (u * f - v * g)) + (a * v) * g := by ring
  rw [e]
  exact Ideal.add_mem _
    (Ideal.mem_sup_left (P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left a hm)))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))

theorem multAt_sup_span_eq_of_sub_mem {P W : Ideal (MRing ι)} (hW : W.IsPrime) {f g u v : MRing ι}
    (hu : u ∉ W) (hv : v ∉ W) (hm : u * f - v * g ∈ P) :
    multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  have hm' : v * g - u * f ∈ P := by
    have := P.neg_mem hm
    rwa [neg_sub] at this
  haveI := hW
  unfold multAt
  rw [dite_eq_left hW, dite_eq_left hW,
    length_localizedModule_quot_eq W
      (fun x hx => ⟨u, hu, mul_mem_sup_span_of_sub_mem hm hx⟩)
      (fun x hx => ⟨v, hv, mul_mem_sup_span_of_sub_mem hm' hx⟩)]

theorem cycles_eq_of_isUnitSec :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι),
      IsUnitSec P f g → divSupp P f = divSupp P g ∧
        (∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W) ∧
        ∀ (n : ℕ) (L : Fin n → HermLine ι), vertR P L f = vertR P L g := by
  intro K _ ι _ P f g h
  have hsupp : divSupp P f = divSupp P g :=
    Set.Subset.antisymm (divSupp_subset_of_isUnitSec h) (divSupp_subset_of_isUnitSec h.symm)
  have hmult : ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    rintro W ⟨hmin, hrel⟩
    have hWp : W.IsPrime := hmin.1.1
    obtain ⟨u, v, hu, hv, hm⟩ := h W hWp (le_sup_left.trans hmin.1.2) hrel
    exact multAt_sup_span_eq_of_sub_mem hWp hu hv hm
  refine ⟨hsupp, hmult, fun n L => ?_⟩
  unfold vertR
  rw [← hsupp]
  refine finsum_mem_congr rfl fun W hW => ?_
  rw [hmult W hW]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueAlongStalkSurjection
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat.ValLift

theorem valAt_of_stalkMap_surjective : ∀ (X₀ X' : Scheme.{0}) (Ω R : Type) [Field Ω] [CommRing R] [IsLocalRing R]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀)
    (z : Spec (CommRingCat.of R) ⟶ X') (a : Ω) (r : R), ξ' ≫ π = ξ →
    Function.Surjective (π.stalkMap (centre z)).hom → ValAt ξ' z a r → ValAt ξ (z ≫ π) a r := by
  intro X₀ X' Ω R _ _ _ ξ ξ' π z a r hξ hsurj hv
  subst hξ
  obtain ⟨h', s', hs'a, hs'r⟩ := hv
  obtain ⟨s, hs⟩ := hsurj s'
  have hsp : genPt (ξ' ≫ π) ⤳ centre (z ≫ π) := h'.map π.continuous
  refine ⟨hsp, s, ?_, ?_⟩
  · rw [← hs'a, ← hs]
    have key : X₀.presheaf.stalkSpecializes hsp ≫ AlgebraicGeometry.Scheme.stalkClosedPointTo (ξ' ≫ π) =
        π.stalkMap (centre z) ≫ X'.presheaf.stalkSpecializes h' ≫ AlgebraicGeometry.Scheme.stalkClosedPointTo ξ' := by
      rw [AlgebraicGeometry.Scheme.stalkClosedPointTo_comp]
      exact AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap_assoc π (genPt ξ') (centre z) h'
        (AlgebraicGeometry.Scheme.stalkClosedPointTo ξ')
    show (CommRingCat.Hom.hom (X₀.presheaf.stalkSpecializes hsp ≫
      AlgebraicGeometry.Scheme.stalkClosedPointTo (ξ' ≫ π))) s = _
    rw [key]
    rfl
  · rw [← hs'r, ← hs, AlgebraicGeometry.Scheme.stalkClosedPointTo_comp]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.ValLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGenerator
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem ιMulti_ne_zero {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b : Fin r → E}
    (hb : LinearIndependent Ω b) : exteriorPower.ιMulti Ω r b ≠ 0 := by
  classical
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (Module.Basis.span hb).equivFun.toLinearMap
  have hφb : ∀ j, φ (b j) = Pi.single j 1 := by
    intro j
    have h2 : φ (b j) = (Module.Basis.span hb).equivFun (Module.Basis.span hb j) := by
      rw [Module.Basis.span_apply hb j]
      exact LinearMap.congr_fun hφ ⟨b j, Submodule.subset_span ⟨j, rfl⟩⟩
    rw [h2]
    ext k
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  intro h0
  have h1 := congrArg (exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating (n := Fin r) (R := Ω)).compLinearMap φ)) h0
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at h1
  have h2 : (fun i => φ (b i)) = (1 : Matrix (Fin r) (Fin r) Ω) := by
    ext i j
    simp [hφb, Matrix.one_apply, Pi.single_apply, eq_comm]
  have h3 : Matrix.det (fun i => φ (b i) : Matrix (Fin r) (Fin r) Ω) = 0 := h1
  rw [h2, Matrix.det_one] at h3
  exact one_ne_zero h3

theorem ιMulti_mem_span {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω) {r : ℕ} (b c : Fin r → E)
    (hc : ∀ i, c i ∈ Submodule.span R (Set.range b)) :
    exteriorPower.ιMulti Ω r c ∈ Submodule.span R {exteriorPower.ιMulti Ω r b} := by
  classical
  choose m hm using fun i => (Submodule.mem_span_range_iff_exists_fun R).1 (hc i)
  have hc' : c = fun i => ∑ j, ((m i j : R) : Ω) • b j := by
    funext i
    rw [← hm i]
    rfl
  have hsum : exteriorPower.ιMulti Ω r (fun i => ∑ j, ((m i j : R) : Ω) • b j) =
      ∑ σ : Fin r → Fin r, exteriorPower.ιMulti Ω r (fun i => ((m i (σ i) : R) : Ω) • b (σ i)) :=
    (exteriorPower.ιMulti Ω r).toMultilinearMap.map_sum (fun i j => ((m i j : R) : Ω) • b j)
  rw [hc', hsum]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hsm : exteriorPower.ιMulti Ω r (fun i => ((m i (σ i) : R) : Ω) • b (σ i)) =
      (∏ i, ((m i (σ i) : R) : Ω)) • exteriorPower.ιMulti Ω r (b ∘ σ) :=
    (exteriorPower.ιMulti Ω r).toMultilinearMap.map_smul_univ _ _
  have hR : (∏ i, ((m i (σ i) : R) : Ω)) ∈ R := prod_mem fun i _ => (m i (σ i)).2
  rw [hsm]
  by_cases hσ : Function.Injective σ
  · have hperm := (exteriorPower.ιMulti Ω r).map_perm b (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ))
    have hco : b ∘ (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ)) = b ∘ σ := rfl
    rw [hco] at hperm
    rw [hperm]
    refine Submodule.smul_mem _ (⟨_, hR⟩ : R) ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ))) with h | h
    · rw [h, one_smul]
      exact Submodule.mem_span_singleton_self _
    · rw [h, Units.neg_smul, one_smul]
      exact neg_mem (Submodule.mem_span_singleton_self _)
  · have h0 : exteriorPower.ιMulti Ω r (b ∘ σ) = 0 :=
      (exteriorPower.ιMulti Ω r).map_eq_zero_of_not_injective _ fun h => hσ h.of_comp
    rw [h0, smul_zero]
    exact zero_mem _

theorem wedge_eq_span_ιMulti : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p → L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} ∧ exteriorPower.ιMulti Ω r b ≠ 0 := by
  intro X Ω _ ξ E _ _ L r b p ⟨hb, hL⟩
  refine ⟨le_antisymm ?_ ?_, ιMulti_ne_zero hb⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact ιMulti_mem_span (regAt ξ p) b c (fun i => hL ▸ hc i)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨b, fun i => by rw [hL]; exact Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame
end
end

