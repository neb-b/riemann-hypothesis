module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FirstOrderPointsCommute
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCoordsComplexPoint
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFraction
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_local_mono_frac : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) :=
  @PositivityTheory.HtPt.Ma.reg_local

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditive
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SqAdd

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S : Scheme.{0}} {C B : Type} [CommRing C] [CommRing B]

theorem dualMap_comp_algebraMap (φ : C →+* B) :
    (dualMap φ).comp (algebraMap C (DualNumber C)) = (algebraMap B (DualNumber B)).comp φ := by
  refine RingHom.ext fun c => ?_
  apply TrivSqZeroExt.ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : C →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMap φ) =
      φ.comp (TrivSqZeroExt.fstHom C C C).toRingHom := by
  refine RingHom.ext fun c => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

def epsIdeal (B : Type) [CommRing B] : Ideal (DualNumber B) :=
  RingHom.ker (TrivSqZeroExt.fstHom B B B).toRingHom

theorem epsIdeal_sq : epsIdeal B ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : a.fst = 0 := ha
  have hb' : b.fst = 0 := hb
  rw [Ideal.mem_bot]
  apply TrivSqZeroExt.ext <;> simp [ha', hb']

def redMap (B : Type) [CommRing B] : B →+* DualNumber B ⧸ epsIdeal B :=
  (Ideal.Quotient.mk (epsIdeal B)).comp (algebraMap B (DualNumber B))

theorem mk_eq_redMap_comp :
    Ideal.Quotient.mk (epsIdeal B) = (redMap B).comp (TrivSqZeroExt.fstHom B B B).toRingHom := by
  refine RingHom.ext fun a => ?_
  change Ideal.Quotient.mk (epsIdeal B) a = Ideal.Quotient.mk (epsIdeal B) (algebraMap B (DualNumber B) a.fst)
  rw [Ideal.Quotient.eq]
  change (TrivSqZeroExt.fstHom B B B).toRingHom _ = 0
  simp [TrivSqZeroExt.algebraMap_eq_inl]

def restr (φ : C →+* B) (y : Sp C ⟶ S) :
    Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ epsAt y :=
  Over.homMk (spMap (dualMap φ)) (by
    change spMap _ ≫ spMap _ ≫ y = spMap _ ≫ spMap _ ≫ y
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (dualMap_comp_algebraMap φ))

theorem red_restr (G : Over S) [GrpObj G] (φ : C →+* B) (y : Sp C ⟶ S) (v : epsAt y ⟶ G) (tv : IsTanAt G y v) :
    spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ (restr φ y ≫ v).left =
      spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
        (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left := by
  have hred : spMap (redMap B) = spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (algebraMap B (DualNumber B)) := by
    rw [← Spec.map_comp]; rfl
  have hmk : spMap (Ideal.Quotient.mk (epsIdeal B)) =
      spMap (redMap B) ≫ spMap (TrivSqZeroExt.fstHom B B B).toRingHom := by
    rw [← Spec.map_comp]
    exact congrArg (fun f => spMap f) mk_eq_redMap_comp
  have hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (dualMap φ) =
      spMap φ ≫ spMap (TrivSqZeroExt.fstHom C C C).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => spMap f) (fst_comp_dualMap φ)
  let T : Over S := Over.mk (spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
    spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y)
  let m₁ : T ⟶ Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) :=
    Over.homMk (spMap (Ideal.Quotient.mk (epsIdeal B))) rfl
  let m₂ : T ⟶ Over.mk y := Over.homMk (spMap (redMap B) ≫ spMap φ) (by
    change (spMap (redMap B) ≫ spMap φ) ≫ y = _
    rw [hred]
    simp [T])
  have c : m₁ ≫ (1 : _ ⟶ G) = m₂ ≫ (1 : _ ⟶ G) := by
    rw [MonObj.comp_one, MonObj.comp_one]
  have c' : spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
      (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      (spMap (redMap B) ≫ spMap φ) ≫ (1 : Over.mk y ⟶ G).left := congrArg CommaMorphism.left c
  rw [c']
  have tv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left := tv
  rw [← tv']
  change spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (dualMap φ) ≫ v.left = _
  rw [hmk]
  simp only [Category.assoc]
  rw [reassoc_of% hfst]

theorem top_le_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    ⊤ ≤ (p ≫ k) ⁻¹ᵁ U := fun z _ => by
  change k (p z) ∈ U
  exact h (show p z ∈ (⊤ : Y.Opens) from trivial)

theorem appTop_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (k' : X ⟶ Z) (e : k' = p ≫ k) (U : Z.Opens)
    (h : ⊤ ≤ k ⁻¹ᵁ U) (h' : ⊤ ≤ k' ⁻¹ᵁ U) (s : Γ(Z, U)) :
    p.appTop.hom ((k.appLE U ⊤ h).hom s) = (k'.appLE U ⊤ h').hom s := by
  subst e
  have hle : (⊤ : X.Opens) ≤ p ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  have hp : p.appTop = p.appLE ⊤ ⊤ hle := Scheme.Hom.app_eq_appLE ..
  have : k.appLE U ⊤ h ≫ p.appTop = (p ≫ k).appLE U ⊤ h' := by
    rw [hp]
    exact Scheme.Hom.appLE_comp_appLE ..
  rw [← this]
  rfl

theorem tan_local (G : Over S) [GrpObj G] [IsLocalRing B] (φ : C →+* B) (y : Sp C ⟶ S) (v w : epsAt y ⟶ G)
    (tv : IsTanAt G y v) (tw : IsTanAt G y w) (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U)
    (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U) (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)) :
    (spMap (dualMap φ)).appTop.hom
        (((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s) =
      (spMap (dualMap φ)).appTop.hom ((v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s) := by
  have hmul : ((restr φ y ≫ v) * (restr φ y ≫ w)).left = spMap (dualMap φ) ≫ (v * w).left :=
    congrArg CommaMorphism.left (MonObj.comp_mul (restr φ y) v w).symm
  have hone : (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      spMap (dualMap φ) ≫ (1 : epsAt y ⟶ G).left :=
    congrArg CommaMorphism.left (MonObj.comp_one (restr φ y)).symm
  have hxv : ⊤ ≤ (restr φ y ≫ v).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) v.left U hv
  have hxw : ⊤ ≤ (restr φ y ≫ w).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) w.left U hw
  have hxvw : ⊤ ≤ ((restr φ y ≫ v) * (restr φ y ≫ w)).left ⁻¹ᵁ U := by
    rw [hmul]; exact top_le_comp _ _ U hvw
  have hx1 : ⊤ ≤ (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left ⁻¹ᵁ U := by
    rw [hone]; exact top_le_comp _ _ U h1
  have key := _root_.GlobalTheory.CompanionTheory.Ar.sqzero_add S G B (spMap φ ≫ y) (DualNumber B) (algebraMap B (DualNumber B)) (epsIdeal B)
    epsIdeal_sq (restr φ y ≫ v) (restr φ y ≫ w) (red_restr G φ y v tv) (red_restr G φ y w tw) U hxv hxw hxvw hx1 s
  rw [map_add (f := _), map_add (f := _),
    appTop_appLE (spMap (dualMap φ)) _ _ hmul U hvw hxvw s,
    appTop_appLE (spMap (dualMap φ)) _ _ hone U h1 hx1 s,
    appTop_appLE (spMap (dualMap φ)) v.left (restr φ y ≫ v).left rfl U hv hxv s,
    appTop_appLE (spMap (dualMap φ)) w.left (restr φ y ≫ w).left rfl U hw hxw s]
  exact key

theorem dualMap_fst (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).fst = φ a.fst := by
  simp [dualMap]

theorem dualMap_snd (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).snd = φ a.snd := by
  simp [dualMap]

theorem dual_eq_of_localization (a b : DualNumber C)
    (h : ∀ (q : Ideal C) [q.IsMaximal], dualMap (algebraMap C (Localization.AtPrime q)) a =
      dualMap (algebraMap C (Localization.AtPrime q)) b) : a = b := by
  have h0 : ∀ r r' : C, (∀ (q : Ideal C) [q.IsMaximal], algebraMap C (Localization.AtPrime q) r =
      algebraMap C (Localization.AtPrime q) r') → r = r' := by
    intro r r' hr
    rw [← sub_eq_zero]
    refine eq_zero_of_localization _ fun q hq => ?_
    rw [map_sub, hr q, sub_self]
  apply TrivSqZeroExt.ext
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_fst, ← dualMap_fst, h q]
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_snd, ← dualMap_snd, h q]

theorem gamma_eq_of_localization (a b : Γ(Sp (DualNumber C), ⊤))
    (h : ∀ (q : Ideal C) [q.IsMaximal], (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom a =
      (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom b) : a = b := by
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).commRingCatIsoToRingEquiv.injective
  refine hinj (dual_eq_of_localization _ _ fun q _ => ?_)
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap (algebraMap C (Localization.AtPrime q))))
  have e' : ∀ c : Γ(Sp (DualNumber C), ⊤), dualMap (algebraMap C (Localization.AtPrime q))
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Localization.AtPrime q)))).hom
        ((spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom c) := fun c =>
    (congrArg (fun f => f.hom c) e).symm
  rw [e', e', h q]

theorem tan_mul_add : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S)
    (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
    ∀ (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U) (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U)
      (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)),
      ((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s =
        (v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s := by
  intro S G _ C _ y v w tv tw U hv hw hvw h1 s
  exact gamma_eq_of_localization _ _ fun q _ =>
    tan_local G (algebraMap C (Localization.AtPrime q)) y v w tv tw U hv hw hvw h1 s

end GlobalTheory.CompanionTheory.Ar.SqAdd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistObjMapFunctorial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem objMap_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' : Scheme.{0}) (s' : S' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (f : S' ⟶ S) (m : ObjMap o' o f) (g : HostAut H) (a : TwIso D g) (h : TwOK o g a) (h' : TwOK o' g a), ∃ n : ObjMap (twistObj o' g a h') (twistObj o g a h) f, n.toSABMap = twistMap m.toSABMap g  := by
  intro E _ _ _ H D l B _ b S s S' s' o o' f m g a h h'
  exact ⟨{ toSABMap := twistMap m.toSABMap g
           eta := fun x => m.eta (a.a l.M x)
           etaA := fun x => m.etaA (a.a l.A x) }, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionAvoidPrime
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_rep_avoiding : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ), IsMultiProjPrime P → IsMultiProjPrime W → P ≤ W → IsMultiHomog f df → IsMultiHomog g dg → g ∉ P → IsUnitSec P f g → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = (df k : ℤ) - dg k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * g - g' * f ∈ P ∧ IsUnitSec P f' g' :=
  @PositivityTheory.Xgn.exists_representative_avoiding_ideal

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionDivisorEqStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_section_divisor_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), IsUnitSec P f g → divSupp P f = divSupp P g ∧ (∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W) ∧ ∀ (n : ℕ) (L : Fin n → HermLine ι), vertR P L f = vertR P L g := by
  intro K _ ι _ P f g h
  have length_localizedModule_quot_eq {R : Type} [CommRing R] (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R}
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

  have unitSec_symm {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) : IsUnitSec P g f := by
    intro W hW hP hR
    obtain ⟨u, v, hu, hv, hm⟩ := h W hW hP hR
    refine ⟨v, u, hv, hu, ?_⟩
    have := P.neg_mem hm
    rwa [neg_sub] at this

  have divSupp_subset_of_isUnitSec {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) :
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

  have mul_mem_sup_span_of_sub_mem {R : Type} [CommRing R] {P : Ideal R} {f g u v x : R}
      (hm : u * f - v * g ∈ P) (hx : x ∈ P ⊔ Ideal.span {f}) : u * x ∈ P ⊔ Ideal.span {g} := by
    obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e : u * (p + a * f) = (u * p + a * (u * f - v * g)) + (a * v) * g := by ring
    rw [e]
    exact Ideal.add_mem _
      (Ideal.mem_sup_left (P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left a hm)))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))

  have multAt_sup_span_eq_of_sub_mem {P W : Ideal (MRing ι)} (hW : W.IsPrime) {f g u v : MRing ι}
      (hu : u ∉ W) (hv : v ∉ W) (hm : u * f - v * g ∈ P) :
      multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    have hm' : v * g - u * f ∈ P := by
      have := P.neg_mem hm
      rwa [neg_sub] at this
    haveI := hW
    unfold multAt
    rw [dite_eq_left hW, dite_eq_left hW,
      length_localizedModule_quot_eq W (J₁ := P ⊔ Ideal.span {f}) (J₂ := P ⊔ Ideal.span {g})
        (fun x hx => ⟨u, hu, mul_mem_sup_span_of_sub_mem hm hx⟩)
        (fun x hx => ⟨v, hv, mul_mem_sup_span_of_sub_mem hm' hx⟩)]

  have hsupp : divSupp P f = divSupp P g :=
    Set.Subset.antisymm (divSupp_subset_of_isUnitSec h) (divSupp_subset_of_isUnitSec (unitSec_symm h))
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
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCentreRegularUnit
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_centre_of_isProper : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a :=
  @PositivityTheory.Xgn.valuation_centre_exists

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCoordsComplexPointStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_coords_complex_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (w : (Σ k, ι k) → ℂ), w ∈ Small.ptsOver ℂ (mCoordIdeal y) → ∃ (W : Subring Ω) (φ : W →+* ℂ), (∀ a : W, φ a ≠ 0 → IsUnit a) ∧ (∀ (k : K) (c e : ι k), w ⟨k, c⟩ ≠ 0 → ∃ h : y ⟨k, e⟩ / y ⟨k, c⟩ ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) ∧ ∀ (a : K → ℤ) (s : Ω) (v : ℂ) (C : ∀ k, ι k), Small.HasVal y a s w v → (∀ k, w ⟨k, C k⟩ ≠ 0) → ∃ h : s * ∏ k, y ⟨k, C k⟩ ^ (-a k) ∈ W, φ ⟨_, h⟩ * ∏ k, w ⟨k, C k⟩ ^ a k = v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val | exact GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val | (intros; apply GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_lattice_generator : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p → L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} ∧ exteriorPower.ιMulti Ω r b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti | exact GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundle
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lineLat_isVBOn_gen_frames : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (T : Set (Cpt ξ)) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E), A.IsVBOn T p V → B.IsVBOn T q V' → a ≠ 0 → b ≠ 0 → (∃ x ∈ T, ∃ f, IsCoeffAt A B p q a b x f) → (lineLat A B p q a b).IsVBOn T 1 ⊤ ∧ (∀ x ∈ T, ∀ t : Ω, (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹) ∧ ∀ x ∈ T, ∀ (v : Fin p → E) (w : Fin q → E) (α β : Ω), A.IsFrameAt v x → B.IsFrameAt w x → exteriorPower.ιMulti Ω p v = α • a → exteriorPower.ιMulti Ω q w = β • b → (lineLat A B p q a b).IsGenAt x (α / β) :=
  @PositivityTheory.Xgn.line_lattice_vector_bundle

end GlobalTheory.CompanionTheory.Ar.Flat
end

