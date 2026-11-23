module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemOfUniversalSectionBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRingRegularAtExtensionPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep

variable {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem Tower.map_mem_O (𝔗 : GlobalTheory.GSep.Tower X₁ act) {w : 𝔗.X₂.M.Z} {x : X₁.Ω₁} (hx : x ∈ X₁.M.O (𝔗.p w)) :
    algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ x ∈ 𝔗.X₂.M.O w := by
  obtain ⟨U, f, hz, rfl⟩ := hx
  refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, hz, ?_⟩
  refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
  rw [𝔗.p_pt]
  exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hz⟩) f

theorem Tower.stalkHom_stalkMap (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z) (x : X₁.M.Z.presheaf.stalk (𝔗.p z₂)) :
    𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) := by
  obtain ⟨U, hz, f, rfl⟩ := X₁.M.Z.presheaf.exists_germ_eq x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ hz]
  refine (RatModel.stalkHom_germ (U := 𝔗.p ⁻¹ᵁ U) hz _).trans ?_
  refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
  rw [𝔗.p_pt]
  exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hz⟩) f

theorem Tower.regAt : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective io → 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.RegAt X₁ z₁ ev → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂ := by
  intro I X₁ act 𝔗 z₁ z₂ hz V V' _ _ _ _ ev io ev₂ hio hext hreg
  subst hz
  have key : ev₂.comp (𝔗.p.stalkMap z₂).hom = io.comp ev :=
    RingHom.ext fun x => hext.2 x _ (𝔗.stalkHom_stalkMap z₂ x)
  let fm : FractionRing V →+* FractionRing V' :=
    IsLocalization.map (M := nonZeroDivisors V) (S := FractionRing V) (FractionRing V') io
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hio)
  have e1 : spMap ev₂ ≫ Spec.map (𝔗.p.stalkMap z₂) = spMap io ≫ spMap ev := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg (fun φ : _ →+* V' => φ x) key
  have e2 : jK V' ≫ spMap io = spMap fm ≫ jK V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    show algebraMap V' (FractionRing V') (io x) = fm (algebraMap V (FractionRing V) x)
    exact (IsLocalization.map_eq (M := nonZeroDivisors V) (S := FractionRing V) (T := nonZeroDivisors V')
      (Q := FractionRing V') (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hio) x).symm
  have hm : jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂ ≫ 𝔗.p =
      spMap fm ≫ jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc (spMap ev₂), e1, Category.assoc,
      ← Category.assoc (jK V'), e2, Category.assoc]
  have hpt : 𝔗.p ((jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))) =
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) (closedPoint (FractionRing V)) := by
    refine (Scheme.Hom.comp_apply _ 𝔗.p _).symm.trans ?_
    rw [Category.assoc, Category.assoc, hm]
    refine (Scheme.Hom.comp_apply (spMap fm) _ _).trans (congrArg _ ?_)
    exact Spec_closedPoint
  intro a ha
  set P₂ := (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))
  haveI := 𝔗.X₂.normal.isIntegrallyClosed_stalk P₂
  haveI : IsIntegrallyClosed (𝔗.X₂.M.O P₂) := IsIntegrallyClosed.of_equiv (𝔗.X₂.M.stalkEquiv P₂)
  have hmem : ∀ c : X₁.S.R, ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) c ∈ 𝔗.X₂.M.O P₂ := fun c =>
    𝔗.map_mem_O (by rw [hpt]; exact hreg c.1 c.2)
  let q : X₁.S.R →+* 𝔗.X₂.M.O P₂ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom).codRestrict _ hmem
  obtain ⟨p, hmon, hp⟩ := 𝔗.om_fin.to_isIntegral ⟨a, ha⟩
  have hq : (algebraMap (𝔗.X₂.M.O P₂) 𝔗.X₂.Ω₁).comp q = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om :=
    RingHom.ext fun c => (𝔗.om_eq c).symm
  have hia : IsIntegral (𝔗.X₂.M.O P₂) a := by
    refine ⟨p.map q, hmon.map q, ?_⟩
    rw [Polynomial.eval₂_map, hq]
    have := Polynomial.hom_eval₂ p 𝔗.om 𝔗.X₂.S.R.val.toRingHom ⟨a, ha⟩
    rw [hp, map_zero] at this
    exact this.symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hia
  rw [← hy]
  exact y.2

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRingValuePointLiesOverUnitaryModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.GSep

theorem valPt_lies_over_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ Xo.XF c), GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = y ≫ C.i → ∃ (yK : X₁.S.R →+* FractionRing V₁) (x' : Sp (FractionRing V₁) ⟶ Sp (ratHull X₁.S.R)), (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ x' ≫ spMap (toRat X₁.S.R) = spMap yK ∧ x' ≫ u = y := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hL z₁ V₁ _ _ _ ev y hreg hy
  set yw := jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyw
  set w := yw (IsLocalRing.closedPoint (FractionRing V₁)) with hw
  have hle : X₁.S.R ≤ X₁.M.O w := fun a ha => hreg a ha

  have hπw : π w = C.i (y (IsLocalRing.closedPoint (FractionRing V₁))) := by
    have h1 : yw ≫ π = y ≫ C.i := by simpa only [hyw, Category.assoc] using hy
    have h2 := congrArg (fun f => f (IsLocalRing.closedPoint (FractionRing V₁))) h1
    exact h2
  have hc : ∀ n : ℤ, n ≠ 0 → IsUnit (n : X₁.M.O w) := fun n hn => by
    rw [← map_intCast (X₁.M.stalkEquiv w) n, MulEquiv.isUnit_map, ← map_intCast (π.stalkMap w).hom n,
      isUnit_map_iff, hπw, ← isUnit_map_iff (C.i.stalkMap _).hom, map_intCast]
    have h : IsUnit (n : c.F) := IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
    have h' := ((h.map (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom).map
      ((Sp c.F).presheaf.germ ⊤ ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) (y (IsLocalRing.closedPoint (FractionRing V₁))))
        trivial).hom).map ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F).stalkMap _).hom
    rwa [map_intCast, map_intCast, map_intCast] at h'
  have hle' : ratHull X₁.S.R ≤ X₁.M.O w := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    obtain ⟨h1, h2⟩ := (RatModel.isUnit_O_iff _).1 (hc n hn)
    have e : ((n : X₁.M.O w) : X₁.Ω₁) = n := by simp
    rw [e] at h1 h2
    have := mul_mem h2 (hle h)
    rwa [inv_mul_cancel_left₀ h1] at this
  have hsp : yw (IsLocalRing.closedPoint (FractionRing V₁)) ⤳ w := specializes_rfl
  let ψ : ratHull X₁.S.R →+* X₁.M.Z.presheaf.stalk w :=
    (X₁.M.stalkEquiv w).symm.toRingHom.comp (Subalgebra.inclusion hle').toRingHom
  let φ : X₁.M.Z.presheaf.stalk w →+* FractionRing V₁ := (X₁.M.Z.presheaf.stalkSpecializes hsp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (FractionRing V₁)) yw).hom
  have hK : (RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom =
      (φ.comp ψ).comp (toRat X₁.S.R) :=
    RingHom.ext fun a => (RatModel.valLoc_eq_val yw hsp (Subalgebra.inclusion hle a)).symm
  refine ⟨(RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom,
    spMap (φ.comp ψ), fun a => rfl, ?_, ?_⟩
  · rw [hK]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI := C.isPreimmersion_i
  haveI : IsProper C.z := GlobalTheory.ThetaDescent.isProper_of_isProjOver C.proj
  haveI : C.Z.IsSeparated := by
    constructor
    rw [← terminal.comp_from C.z]
    infer_instance
  haveI : IsDominant (spMap (X₁.M.stalkHom w)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (X₁.M.stalkHom w))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (X₁.M.stalkHom_injective w)]
    exact bot_le
  have hfs : ∀ {B : Type} [CommRing B] [IsLocalRing B] (q : Sp B ⟶ X₁.M.Z) (h : q (IsLocalRing.closedPoint B) ⤳ w),
      spMap (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of B) q).hom ≫
        X₁.M.Z.fromSpecStalk w = q := by
    intro B _ _ q h
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of B) q
  have e1 : spMap (X₁.M.stalkHom w) ≫ spMap ψ = spMap (ratHull X₁.S.R).val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => congrArg Subtype.val ((X₁.M.stalkEquiv w).apply_symm_apply (Subalgebra.inclusion hle' a))
  have e2 : spMap (X₁.M.stalkHom w) ≫ X₁.M.Z.fromSpecStalk w = X₁.M.pt :=
    hfs X₁.M.pt (X₁.M.pt_specializes _ w)
  have hab : spMap ψ ≫ u ≫ C.i = X₁.M.Z.fromSpecStalk w ≫ π := by
    refine ext_of_isDominant (spMap (X₁.M.stalkHom w)) ?_
    rw [reassoc_of% e1, reassoc_of% e2, hL.2.2.2]
  have e3 : spMap φ ≫ X₁.M.Z.fromSpecStalk w = yw := hfs yw hsp
  rw [← cancel_mono C.i, Category.assoc]
  rw [show spMap (φ.comp ψ) = spMap φ ≫ spMap ψ by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp], Category.assoc, hab, reassoc_of% e3, ← hy]
  simp only [hyw, Category.assoc]

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemUniversalUnitaryDeepTowers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.GSep.UTower

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem lbIso_pull_comp_of_eq {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isMonHom_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) (e : G ⟶ G) [IsMonHom e] (e' : G' ⟶ G')
    (he : e'.left ≫ φ = φ ≫ e.left) : IsMonHom e' := by
  have push_comp : ∀ {T₁ : Over S'} (x : T₁ ⟶ G'), pushPt hφ.1.w (x ≫ e') = pushPt hφ.1.w x ≫ e :=
    fun x => Over.OverMorphism.ext (by
      show (x.left ≫ e'.left) ≫ φ = (x.left ≫ φ) ≫ e.left
      rw [Category.assoc, he, Category.assoc])
  have pm : ∀ {T₁ : Over S'} (x y : T₁ ⟶ G'), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have inj : ∀ {T₁ : Over S'} {x y : T₁ ⟶ G'}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun h => GlobalTheory.SiegelPull.push_injective hφ _ h
  refine isMonHom_of_mul _ fun T₁ x y => inj ?_
  rw [push_comp, pm, pm, push_comp, push_comp]
  exact MonObj.mul_comp _ _ _

theorem deep_of_uLink : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → GlobalTheory.GSep.Deep X₁ act := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hU N₀
  have hact : IsAct X₁ act := hU.1
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j₀, hk, hBk, hj₀, big⟩ := GlobalTheory.Poinc.GSetup.exists_big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 N₀
  have hun1 : IsUnit (X₁.ρ.n : X₁.o₁) := by
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [hL₁]; exact dvd_pow_self _ (by omega)
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) X₁.S.unit
  haveI : CharZero X₁.Ω₁ := ArithBase.char (o := X₁.o₁)
  have hM : 0 < X₁.S.r * X₁.S.N := by rw [hL₁]; exact pow_pos hℓp.pos _
  have hζ₀ : ∃ ζ₀ : X₁.Ω₁, IsPrimitiveRoot ζ₀ (X₁.S.r * X₁.S.N) :=
    ⟨_, (X₁.S.prim.pow (by positivity) (sq _)).map_of_injective (ArithBase.inj (o := X₁.o₁) (Ω := X₁.Ω₁))⟩
  have htors : ∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp X₁.S.R) (z : Over.mk x ⟶ X₁.ρ.P.A),
      z ^ (X₁.S.r * X₁.S.N) = 1 → ∃ y : baseOver (Sp X₁.S.R) ⟶ X₁.ρ.P.A,
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp X₁.S.R)) ≫ y = z := by
    intro E _ _ x z hz
    obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij E x z hz
    exact ⟨_, ha⟩
  set j := j₀ + (j₁ + 2 * X₁.ρ.k) with hj
  set K := (X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 with hK
  have hKpos : 0 < K := by have := hℓp.pos; positivity
  obtain ⟨Ω₂, _, _, Q, φQ, ζ, fd, gal, -, hζ, hQg, hQpb, hQlb, ⟨levQ⟩⟩ :=
    _root_.GlobalTheory.LevelPrimePower.exists_level_primePower X₁.S.R.val.toRingHom X₁.ρ.P X₁.ρ.n (X₁.S.r * X₁.S.N) K hℓp hM
      (by rw [hL₁]; exact dvd_pow_self _ (by omega)) ⟨2 * (j + 2 * k), by rw [hK]; ring⟩ hζ₀ htors
  haveI := fd
  obtain ⟨o₂, _, _, _, κ, ze, hκ, hc, hze⟩ :=
    GlobalTheory.Poinc.exists_arithBase_rootOfUnity (o₁ := X₁.o₁) (Ω₁ := X₁.Ω₁) Ω₂ K ζ hKpos hζ
  haveI : CharZero Ω₂ := ArithBase.char (o := o₂)
  obtain ⟨R, h, hfg, hfr, hh, hfin, hic, hstab⟩ := _root_.GlobalTheory.Poinc.NormalClosureRing.exists_integralClosure_finite X₁.S.R X₁.S.fg X₁.S.frac κ hκ hc
  haveI := GlobalTheory.ThetaReal.isNoetherian_of_fg hfg
  haveI := GlobalTheory.GenSpread.isFractionRing_of_forall_div hfr
  have hun2 : IsUnit (X₁.ρ.n : o₂) := by simpa using hun1.map κ
  have hKunit : IsUnit (K : R) := by
    have := (hun2.map (algebraMap o₂ R))
    rw [map_natCast] at this
    rw [hK]; push_cast
    exact ((this.pow _).mul ((this.pow _).pow _)).pow _
  let zeR : (↥R)ˣ := Units.map (algebraMap o₂ R).toMonoidHom ze
  have hzeR : Units.map (algebraMap R Ω₂).toMonoidHom zeR = ζ := by
    rw [← hze]; ext; rfl
  have hQpb' : IsGrpPullback Q.A X₁.ρ.P.A (spMap ((algebraMap R Ω₂).comp h)) φQ := by
    have e : (algebraMap R Ω₂).comp h = (algebraMap X₁.Ω₁ Ω₂).comp X₁.S.R.val.toRingHom := RingHom.ext hh
    rw [e]; exact hQpb
  obtain ⟨P, ψ, hPg, hpb, hlb, ⟨lev⟩⟩ := _root_.GlobalTheory.SympLevelExt.level_extends X₁.ρ.P R Ω₂ h Q φQ K zeR hKpos hKunit hQg hQpb' hQlb
    ⟨by rw [hzeR]; exact levQ⟩
  have hS := GlobalTheory.Poinc.hypS_polAV_pullback X₁.ρ.P P (spMap h) ψ hpb hlb X₁.ρ.hypS
  obtain ⟨th, hth⟩ := _root_.GlobalTheory.SecBasisPull.exists_secBasis_pull X₁.ρ.P P h ψ hpb hlb X₁.ρ.th₁ X₁.ρ.th₁_basis
  obtain ⟨S₂, ρ₂, hR, φ₂, hSR, -, -, hN₂, hr₂, hg₂, hpb₂, hlb₂⟩ :=
    _root_.GlobalTheory.ThetaSBasis.exists_real_of_secBasis o₂ Ω₂ R hfg hfr P X₁.ρ.n k j ze hℓp X₁.ρ.n_odd hk (by omega) hun2 hS th hth lev
  set om : X₁.S.R →+* S₂.R := (Subalgebra.inclusion hR).toRingHom.comp h with hom
  have hval : ∀ a, ((om a : S₂.R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => hh a
  have hcart : IsGrpPullback ρ₂.P.A X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) := by
    rw [hom, ← spMap_comp_ring]
    exact hpb₂.comp hpb
  have hlbc : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ₂ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (lbIso_pull_comp_of_eq hlb φ₂ rfl)

  have hφp := hcart.1
  have wε : ∀ a, ((φ₂ ≫ ψ) ≫ (act a).left) ≫ X₁.ρ.P.A.hom = ρ₂.P.A.hom ≫ spMap om := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let act₂ : 𝓞 E → (ρ₂.P.A ⟶ ρ₂.P.A) := fun a =>
    Over.homMk (hφp.lift ((φ₂ ≫ ψ) ≫ (act a).left) ρ₂.P.A.hom (wε a)) (hφp.lift_snd _ _ _)
  have hact₂ : ∀ a, (act₂ a).left ≫ (φ₂ ≫ ψ) = (φ₂ ≫ ψ) ≫ (act a).left := fun a => hφp.lift_fst _ _ _
  have hmon : ∀ a, IsMonHom (act₂ a) := fun a => by
    haveI := hact a
    exact isMonHom_of_isGrpPullback hcart (act a) (act₂ a) (hact₂ a)

  haveI : IsDedekindDomain X₁.o₁ := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  have hp : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt) ≫ X₁.M.s = spMap ((algebraMap o₂ Ω₂).comp κ) := by
    rw [Category.assoc, X₁.M.pt_s, hc]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap X₁.o₁ X₁.Ω₁))
      (CommRingCat.ofHom (algebraMap X₁.Ω₁ Ω₂))).symm
  have hst : ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt).stalkMap (genericPoint (Sp Ω₂))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (GlobalTheory.Poinc.stalkMap_spMap_finite _ (RingHom.finite_algebraMap.2 inferInstance) _)
      (RingHom.Finite.of_surjective _ (GlobalTheory.Poinc.RatModel.stalkMap_pt_surjective X₁.M _))
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := GlobalTheory.Poinc.exists_ratModel_normalization X₁.o₁ o₂ Ω₂ κ hκ X₁.M.Z X₁.M.s X₁.M.lft
    X₁.M.qc X₁.M.sep _ hp hst
  have hs : M₂.s ≫ spMap κ = q ≫ X₁.M.s := by
    refine ext_of_isDominant M₂.pt ?_
    rw [← Category.assoc, M₂.pt_s, spMap_comp_ring, ← Category.assoc, hqgen, hp]
  have hproj : IsProjOver M₂.s :=
    _root_.GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over X₁.o₁ o₂ κ M₂.Z X₁.M.Z X₁.M.s q M₂.s X₁.projM hq inferInstance hs

  have hrat : ∀ x : ratHull X₁.S.R, algebraMap X₁.Ω₁ Ω₂ (x : X₁.Ω₁) ∈ ratHull S₂.R := fun x => by
    obtain ⟨n, hn, hx⟩ := mem_ratHull.1 x.2
    refine mem_ratHull.2 ⟨n, hn, ?_⟩
    have h₀ := (om ⟨_, hx⟩).2
    rw [hval] at h₀
    simpa using h₀
  let rh : ratHull X₁.S.R →+* ratHull S₂.R :=
    ((algebraMap X₁.Ω₁ Ω₂).comp (ratHull X₁.S.R).val.toRingHom).codRestrict (ratHull S₂.R) hrat
  have hrv : spMap (ratHull S₂.R).val.toRingHom ≫ spMap rh =
      spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap (ratHull X₁.S.R).val.toRingHom := by
    rw [spMap_comp_ring, spMap_comp_ring]
    rfl
  have hUO₂ : UOver Xo c ρ₂.P (toRat S₂.R) (spMap rh ≫ u) := by
    refine (uOver_baseChange_iff hcart hlbc (toRat S₂.R)).2 ?_
    have e : (toRat S₂.R).comp om = rh.comp (toRat X₁.S.R) := RingHom.ext fun a => Subtype.ext (hval a)
    rw [e]
    exact hU.uOver.comp rh
  have hgen₂ : ∀ w, (spMap (ratHull S₂.R).val.toRingHom ≫ spMap rh ≫ u) w ∈ genericPoints (Xo.XF c) := fun w => by
    rw [← Category.assoc, hrv, Category.assoc, Scheme.Hom.comp_apply]
    exact hU.2.2.1 _
  have hcomp₂ : M₂.pt ≫ q ≫ π = spMap (ratHull S₂.R).val.toRingHom ≫ (spMap rh ≫ u) ≫ C.i := by
    rw [← Category.assoc, hqgen, Category.assoc, hU.2.2.2, ← Category.assoc (spMap (ratHull S₂.R).val.toRingHom),
      ← Category.assoc (spMap (ratHull S₂.R).val.toRingHom), hrv]
    simp only [Category.assoc]
  have hMn' : GlobalTheory.IsNormalScheme M₂.Z := GlobalTheory.IsNormalScheme.of_pred hMn
  have hdiv : M₂.HasDiv S₂.th :=
    C.thetaInt o₂ Ω₂ S₂ ρ₂ (spMap rh ≫ u) hUO₂ hgen₂ M₂ (q ≫ π) hMn' hcomp₂
  have hbig : S₂.Big := big j (by omega) o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : GSet :=
    { o₁ := o₂, Ω₁ := Ω₂, S := S₂, ρ := ρ₂, big := hbig, M := M₂, normal := hMn', projM := hproj, div := hdiv }
  set d := X₁.ρ.n ^ (j₀ + 2 * k) with hd
  have hlev : S₂.r * S₂.N = X₁.S.r * X₁.S.N * d := by
    rw [hr₂, hN₂, hL₁, hd, hj, ← pow_mul, ← pow_add, ← pow_add, mul_comm k 2]
    ring_nf
  obtain ⟨lam, hlam, hlamr⟩ := _root_.GlobalTheory.Poinc.PullLab.exists_lab_of_isGrpPullback X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) d hcart hlev
  have hRS : ∀ x : Ω₂, x ∈ S₂.R ↔ x ∈ R := fun x => by rw [hSR]
  let sR : (Ω₂ ≃ₐ[X₁.Ω₁] Ω₂) → (S₂.R →+* S₂.R) := fun σ =>
    RingHom.codRestrict (((σ : Ω₂ ≃+* Ω₂) : Ω₂ →+* Ω₂).comp S₂.R.val.toRingHom) S₂.R
      (fun x => (hRS _).2 (hstab σ x ((hRS _).1 x.2)))
  have hsR : ∀ σ, (sR σ).comp om = om := fun σ => RingHom.ext fun a => Subtype.ext
    ((congrArg σ (hval a)).trans ((σ.commutes _).trans (hval a).symm))
  choose gl hgl using fun σ => _root_.GlobalTheory.Poinc.labelHom_of_comp_eq X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) hcart (sR σ) (hsR σ)
  have hgll : ∀ σ a, gl σ (lam a) = lam a := fun σ a => _root_.GlobalTheory.Poinc.Sep.realPt_inj_of_grpPullback S₂ ρ₂ X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) hcart _ _ (by
      rw [hgl, hlam, ← Category.assoc, spMap_comp_ring, hsR])
  let 𝔗 : Tower X₁ act :=
    { X₂ := X₂
      act₂ := act₂
      isAct := hmon
      alg := inferInstance
      fd := fd
      gal := gal
      d := d
      lev := hlev
      om := om
      om_eq := hval
      om_fin := RingHom.Finite.comp (RingHom.Finite.of_surjective _ fun x => ⟨⟨x.1, (hRS _).1 x.2⟩, rfl⟩) hfin
      sR := sR
      sR_eq := fun σ a => rfl
      p := q
      p_fin := hq
      p_pt := hqgen
      φ := φ₂ ≫ ψ
      cart := hcart
      lb := hlbc
      act_eq := hact₂
      lam := lam
      lam_pt := hlam
      lam_range := hlamr
      gl := gl
      gl_pt := hgl
      gl_lam := hgll }
  refine ⟨𝔗, ?_⟩
  show N₀ ≤ S₂.r * S₂.N
  rw [hN₂, hr₂]
  exact hBk.trans (Nat.le_mul_of_pos_left _ (by have := hℓp.pos; positivity))

end GlobalTheory.GSep.UTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameValueLocalUnitsMulSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open GlobalTheory.Poinc.Sep.Coef

noncomputable section

namespace GlobalTheory.USep.EvG

theorem frame_ev : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)),
      (t.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val t r z J ^ (N₁ ^ 2) * val κ (r ≫ b.left) z J = 1) →
    ∃ c ∈ k₀, (val t (spMap ev) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ N₁ hN b hb hbdef t ht
  obtain ⟨-, hM₀, hβ, hw, -⟩ := hFB
  have HD : DescV ib β ev k₀ w := ⟨hk₀, ptsVia_of hβ, hk, hM₀, hw, fun _ _ _ h _ => h⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.FamPull.exists_kap D N₁
  let y : Over.mk (spMap ev) ⟶ D.P.A := toUnit (Over.mk (spMap ev)) ≫ b
  have hy : y ^ N₁ = 1 := by rw [← MonObj.comp_pow, hb, MonObj.comp_one]
  have hyd : RatPV β k₀ y.left := by
    show DefOver k₀ ((spMap ev ≫ b.left) ≫ β)
    rw [Category.assoc]
    exact hbdef
  obtain ⟨c, hc, ec⟩ := kap_memV HD κ hκ y hyd z J J₀ hJ hJ₀
  rw [hy] at ec
  have h1 : val t (spMap ev) z J ^ (N₁ ^ 2) * val (Z := Sp K) κ y.left z J = 1 := ht.2 κ hκ (Sp K) (spMap ev) z J hJ
  obtain ⟨c', hc', ec'⟩ := GlobalTheory.Poinc.Sep.Coef.zpow_mem ⟨c, hc, ec⟩ (-1)
  set a := om (Z := Sp K) w z J J₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left with ha
  set bb := om (Z := Sp K) w z J J₀ y.left with hbb
  set T := val t (spMap ev) z J with hT
  set Kv := val (Z := Sp K) κ y.left z J with hKv
  have alg : (T * a * bb⁻¹) ^ (N₁ ^ 2) = (bb ^ ((N₁ : ℤ) ^ 2) * a⁻¹ * a ^ (1 - (N₁ : ℤ) ^ 2) * Kv) ^ (-1 : ℤ) := by
    have hK : Kv = (T ^ (N₁ ^ 2))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hK]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    rw [← natCast_zsmul, ← natCast_zsmul]
    push_cast
    module
  obtain ⟨c'', hc'', ec''⟩ := GlobalTheory.Poinc.Sep.Coef.root_mem hk₀ (z := z) (s := (T * a * bb⁻¹).val) (n := N₁ ^ 2) (Nat.one_le_pow _ _ (by omega))
    ⟨c', hc', by rw [← Units.val_pow_eq_pow_val, alg]; exact ec'⟩
  refine ⟨c'', hc'', ?_⟩
  have e : T = (a⁻¹ * bb) * (T * a * bb⁻¹) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e, Units.val_mul, ← ec'']
  rfl

end GlobalTheory.USep.EvG
end
end

