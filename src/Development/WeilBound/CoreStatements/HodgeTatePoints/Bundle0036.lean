module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0034
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0032
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GfCurve
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem curve_sec_nef : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (W : Ideal (MRing J)) (a : K → ℤ) (r : (∀ k, J k) → Ω), IsMultiProjPrime W → mCoordIdeal y ≤ W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) → (∀ s, mseg y s ≠ 0 → r s ∈ chartRing o (mseg y) s) → (∀ s t, mseg y s ≠ 0 → mseg y t ≠ 0 → ∃ (n : ℕ) (z : Ω), z ∈ chartRing o (mseg y) t ∧ (mseg y s / mseg y t) ^ n * (r s * chartMon y s a / chartMon y t a - r t) = p * z) → (∃ (s : ∀ k, J k) (n d : ℕ) (g : MRing J), (∀ k, (X ⟨k, s k⟩ : MRing J) ∉ W) ∧ ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ g ∉ W ∧ n * r s * mseg y s ^ d = aeval y g) → 0 ≤ geoNum 1 W (fun _ => a) := by
  intro Ω _ _ K _ J _ y p _ o _ _ ho W a r hW hle hch hdim hr hov ⟨s, n, d, g, hs, hn, hg, hgW, hgy⟩
  have hp := natCast_mem_of_charOf hch
  have hP := hW.1
  have hs0 := mseg_ne_zero hle hs
  let ap : K → ℕ := fun k => (a k).toNat
  let am : K → ℕ := fun k => (-a k).toNat
  refine geoNum_nonneg_of_regular p hW hp hdim (hom_mul hg (hom_mon s ap))
    (hom_mul (hom_mon s fun _ => d) (hom_mon s am)) (fun k => ?_)
    (fun h => (hP.mem_or_mem h).elim hgW (mon_not_mem hP hs _))
    (fun h => (hP.mem_or_mem h).elim (mon_not_mem hP hs _) (mon_not_mem hP hs _)) fun t ht => ?_
  · simp only [Pi.add_apply, ap, am]
    omega
  have ht0 := mseg_ne_zero hle ht
  obtain ⟨m, z, hz, hrel⟩ := hov s t hs0 ht0
  obtain ⟨n₁, e₁, g₁, hn₁, hg₁, hy₁⟩ := exists_rep ho ht0 (hr t ht0)
  obtain ⟨n₂, e₂, g₂, hn₂, hg₂, hy₂⟩ := exists_rep ho ht0 hz
  refine ⟨n₁ * n₂, (fun _ => e₁ + e₂) + am, n * (n₂ * (g₁ * mon t (fun _ => e₂) * mon t ap)),
    fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hn₁ hn₂, ?_⟩
  have hsplit : mon t ((fun _ => e₁ + e₂) + am) = mon t (fun _ => e₁ + e₂) * mon t am := by
    simp [mon, pow_add, Finset.prod_mul_distrib]
  have hz0 : mon s (fun _ => m) * (((n₁ * n₂ : ℕ) : MRing J) * (mon t (fun _ => e₁ + e₂) * mon t am * (g * mon s ap)) -
      n * (n₂ * (g₁ * mon t (fun _ => e₂) * mon t ap * (mon s (fun _ => d) * mon s am)))) -
      p * (n * (n₁ * (g₂ * mon t (fun _ => e₁ + m) * mon s (fun _ => d) * mon s am * mon t ap))) ∈
        mCoordIdeal y := by
    refine mem_mCoordIdeal (d := fun k => m + e₁ + e₂ + d + ap k + am k) (hom_sub (hom_of_eq (hom_mul (hom_mon _ _)
      (hom_sub (hom_nat_mul _ (hom_mul (hom_mul (hom_mon _ _) (hom_mon _ _)) (hom_mul hg (hom_mon _ _))))
        (hom_nat_mul _ (hom_nat_mul _ (hom_of_eq (hom_mul (hom_mul (hom_mul hg₁ (hom_mon _ _)) (hom_mon _ _))
          (hom_mul (hom_mon _ _) (hom_mon _ _))) fun k => ?_))))) fun k => ?_)
      (hom_nat_mul _ (hom_nat_mul _ (hom_nat_mul _ (hom_of_eq (hom_mul (hom_mul (hom_mul (hom_mul hg₂ (hom_mon _ _))
        (hom_mon _ _)) (hom_mon _ _)) (hom_mon _ _)) fun k => ?_))))) ?_
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.add_apply]; omega
    rw [chartMon_eq_div hs0, chartMon_eq_div ht0] at hrel
    have hne : ∀ {u : ∀ k, J k}, mseg y u ≠ 0 → ∀ c, aeval y (mon u c) ≠ 0 := fun hu c => by
      rw [aeval_mon]
      exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (Finset.prod_ne_zero_iff.1 hu k (Finset.mem_univ k))
    have h1 := hne hs0 am
    have h2 := hne ht0 am
    have h3 := hne ht0 ap
    simp only [map_sub, map_mul, map_natCast, aeval_mon_const, ← hgy, ← hy₁, ← hy₂]
    change (mseg y s / mseg y t) ^ m * (r s * (aeval y (mon s ap) / aeval y (mon s am)) /
      (aeval y (mon t ap) / aeval y (mon t am)) - r t) = p * z at hrel
    generalize aeval y (mon s ap) = A at *
    generalize aeval y (mon s am) = B at *
    generalize aeval y (mon t ap) = A' at *
    generalize aeval y (mon t am) = B' at *
    rw [div_pow] at hrel
    field_simp at hrel
    push_cast
    linear_combination (n * n₁ * n₂ * mseg y t ^ (e₁ + e₂) * mseg y s ^ d) * hrel
  have h1 := (Ideal.add_mem_iff_left W (W.neg_mem (W.mul_mem_right _ hp))).1 (by
    rw [← sub_eq_add_neg]; exact hle hz0)
  have h2 := (hP.mem_or_mem h1).resolve_left (mon_not_mem hP hs _)
  rw [hsplit]
  convert h2 using 1
  ring

end PositivityTheory.HtPt.Gf
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatReg
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem chart_le_regAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    (s : ∀ k, J k) (q : Cpt 𝔐.ξ) (hs : InChart 𝔐.ξ (mseg y) s q) (hq : OverZp 𝔐 p q)
    (a : chartRing o (mseg y) s) : (a : Ω) ∈ regAt 𝔐.ξ q := by
  have ha : (a : Ω) ∈ Algebra.adjoin o (Set.range fun j => mseg y j / mseg y s) :=
    (Hcptgen.chartRing_mseg (o := o) y s hs.1).le a.2
  obtain ⟨b, hb, h⟩ := Hcptgen.mem_adjoin_loc Fact.out ho _ ha
  have h3 := (𝔐.tie.ring s hs.1 _).1 h q hs
  have h4 := (Hcptgen.overZp_iff Fact.out q).1 hq b hb
  have := mul_mem h3 h4.2.2
  rwa [mul_assoc, mul_inv_cancel₀ h4.1, mul_one] at this

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Imports
section
namespace PositivityTheory.HtPt.Ktw

theorem a1 :
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.Statement.{0, 0} :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Swarm.GradedCech.proof).mpr
    GroundTheory.Heights₂.Heights.KeyFormula.serreVanishing_graded_holds

theorem a2 :
    GroundTheory.Heights₂.Heights.Kleiman.TildeVanish.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.TildeVanish.proof a1

theorem a3 :
    GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed.proof
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof
    GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily.proof a2

theorem a4 :
    GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict.proof a3
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof

theorem a5 :
    GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict.proof a4

end PositivityTheory.HtPt.Ktw
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MfBase
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

noncomputable section

namespace PositivityTheory.HtPt.Mf


set_option maxHeartbeats 1000000 in
theorem xr_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ IsNormalScheme X) := by
  intro X Ω _ ξ hgen hall
  have hdom : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x =>
    Function.Injective.isDomain (genMap ξ ⟨x, hall x⟩) (hgen.inj ⟨x, hall x⟩)
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := hdom x
    infer_instance
  haveI : AlgebraicGeometry.IsReduced X := isReduced_of_isReduced_stalk X
  haveI : IrreducibleSpace X := by
    rw [irreducibleSpace_def]
    have hcl : closure {GlobalTheory.CompanionTheory.Ar.genPt ξ} = (Set.univ : Set X) :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI hI : AlgebraicGeometry.IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  refine ⟨hI, ?_⟩
  have key : ∀ p : Cpt ξ, IsIntegrallyClosedIn (regAt ξ p) Ω ↔ IsIntegrallyClosed (X.presheaf.stalk p.1) := by
    intro p
    let ψ : X.functionField →+* Ω :=
      (X.presheaf.stalkSpecializes (hall (genericPoint X)) ≫ Scheme.stalkClosedPointTo ξ).hom
    letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
    have hcomm : ∀ r : X.presheaf.stalk p.1, ψ (algebraMap _ X.functionField r) = algebraMap _ Ω r := by
      intro r
      have hc : X.presheaf.stalkSpecializes (genericPoint_specializes p.1) ≫
          X.presheaf.stalkSpecializes (hall (genericPoint X)) = X.presheaf.stalkSpecializes p.2 :=
        TopCat.Presheaf.stalkSpecializes_comp _ _ _
      have h1 : algebraMap (X.presheaf.stalk p.1) X.functionField r =
          (X.presheaf.stalkSpecializes (genericPoint_specializes p.1)).hom r := rfl
      have h2 : algebraMap (X.presheaf.stalk p.1) Ω r =
          (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom r := rfl
      rw [h1, h2]
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom r) hc
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3
    have hsurj : Function.Surjective ψ := by
      intro a
      obtain ⟨g, rfl⟩ := hgen.bij.2 a
      refine ⟨(X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ))).hom g, ?_⟩
      have hc2 : X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)) ≫
          X.presheaf.stalkSpecializes (hall (genericPoint X)) = 𝟙 _ :=
        (TopCat.Presheaf.stalkSpecializes_comp _ _ _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _)
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom g) hc2
      simp only [Category.id_comp, CommRingCat.hom_comp, RingHom.comp_apply] at h3
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3
    let e : X.functionField ≃ₐ[X.presheaf.stalk p.1] Ω :=
      AlgEquiv.ofBijective { ψ with commutes' := hcomm } ⟨ψ.injective, hsurj⟩
    rw [isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField, e.isIntegrallyClosedIn]
    letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
    haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
      Algebra.isIntegral_of_surjective (genMap ξ p).rangeRestrict_surjective
    rw [Subring.isIntegrallyClosedIn_iff, isIntegrallyClosedIn_iff]
    constructor
    · intro h
      refine ⟨hgen.inj p, fun {x} hx => ?_⟩
      exact RingHom.mem_range.mp (h hx.tower_top)
    · rintro ⟨-, h⟩ x hx
      exact RingHom.mem_range.mpr (h (isIntegral_trans x hx))
  constructor
  · intro h x
    exact ⟨inferInstance, (key ⟨x, hall x⟩).mp
      (Subring.isIntegrallyClosedIn_iff.mpr (fun a ha => h ⟨x, hall x⟩ a ha))⟩
  · intro h p a ha
    exact Subring.isIntegrallyClosedIn_iff.mp ((key p).mpr (h p.1).2) ha

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem bijective_iff_isIso_stalkMap (ξ : Sp Ω ⟶ X) (x : Sp Ω) :
    Function.Bijective (Scheme.stalkClosedPointTo ξ).hom ↔ IsIso (ξ.stalkMap x) := by
  obtain rfl : x = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  rw [← isIso_comp_right_iff (ξ.stalkMap _) (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of Ω)).hom]
  exact (ConcreteCategory.isIso_iff_bijective _).symm

def push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) (q : Cpt ξ) : Cpt (ξ ≫ f) :=
  ⟨f q.1, q.2.map f.continuous⟩

theorem genMap_push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) (q : Cpt ξ) :
    genMap (ξ ≫ f) (push ξ f q) = (genMap ξ q).comp (f.stalkMap q.1).hom := by
  show (X.presheaf.stalkSpecializes _ ≫ Scheme.stalkClosedPointTo (ξ ≫ f)).hom =
    (W.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ).hom.comp (f.stalkMap q.1).hom
  rw [← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.stalkClosedPointTo_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ q.1 q.2 _

theorem regAt_push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) [SurjectiveOnStalks f] (q : Cpt ξ) :
    regAt (ξ ≫ f) (push ξ f q) = regAt ξ q := by
  ext a
  simp only [regAt, genMap_push, RingHom.mem_range, RingHom.comp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := f.stalkMap_surjective q.1 y
    exact ⟨x, rfl⟩

theorem isCptGen_of_comp {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) [SurjectiveOnStalks f]
    (h : IsCptGen (ξ ≫ f)) : IsCptGen ξ := by
  have key : ∀ {A B C : Type} (g : B → C) (s : A → B), Function.Injective (g ∘ s) →
      Function.Surjective s → Function.Injective g := by
    intro A B C g s hi hs y y' hy
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨x', rfl⟩ := hs y'
    exact congrArg s (hi hy)
  have hb : Function.Bijective ((Scheme.stalkClosedPointTo ξ).hom ∘ (f.stalkMap (ξ (closedPoint Ω))).hom) := by
    have hb0 := h.bij
    rw [Scheme.stalkClosedPointTo_comp] at hb0
    exact hb0
  refine ⟨⟨key _ _ hb.1 (f.stalkMap_surjective _), Function.Surjective.of_comp hb.2⟩, fun p => ?_⟩
  have hi : Function.Injective ((genMap ξ p) ∘ (f.stalkMap p.1).hom) := by
    have hi0 := h.inj (push ξ f p)
    rw [genMap_push] at hi0
    exact hi0
  exact key _ _ hi (f.stalkMap_surjective p.1)

end PositivityTheory.HtPt.Mf
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MgLevel
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Mg

abbrev extPt {X : Scheme.{0}} {k K : Type} [Field k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) :
    Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl

theorem epi_spMap {k K : Type} [Field k] [Field K] (i : k →+* K) : Epi (spMap i) := by
  have : Surjective (spMap i) :=
    ⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem extPt_inj {X : Scheme.{0}} {k K : Type} [Field k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) {G : Over X}
    {a b : Over.mk x ⟶ G} (h : extPt i x ≫ a = extPt i x ≫ b) : a = b := by
  have := epi_spMap i
  have h' : spMap i ≫ a.left = spMap i ≫ b.left := congrArg (fun q => q.left) h
  exact Over.OverMorphism.ext ((cancel_epi (spMap i)).1 h')

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {X : Scheme.{0}}
  {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} {z : Ωˣ} {ev : D.La → (Over.mk ξ ⟶ t.G)}

theorem full_iso (h : IsFullLevelAt D t ξ N z ev) (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) :
    ∃ I : TateIsoAt D t (spMap i ≫ ξ), I.ζ N = Units.map i.toMonoidHom z ∧ ∀ a, I.ev N a = extPt i ξ ≫ ev a := by
  obtain ⟨I, h1, h2⟩ := h k i
  exact ⟨I, Units.ext h1, fun a => Over.OverMorphism.ext (h2 a)⟩

theorem full_desc (hN : 0 < N) (h : IsFullLevelAt D t ξ N z ev) (k : Type) [Field k] (i : Ω →+* k)
    (g : Over.mk (spMap i ≫ ξ) ⟶ t.G) (hg : g ^ N = 1) : ∃ a, g.left = spMap i ≫ (ev a).left := by
  let j : k →+* AlgebraicClosure k := algebraMap _ _
  obtain ⟨I, -, h2⟩ := h (AlgebraicClosure k) (j.comp i)
  let u : Over.mk (spMap (j.comp i) ≫ ξ) ⟶ Over.mk (spMap i ≫ ξ) :=
    Over.homMk (spMap j) (by simp [spMap_comp])
  obtain ⟨a, ha⟩ := (I.onto N hN (u ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])
  refine ⟨a, ?_⟩
  have := epi_spMap j
  have e : spMap j ≫ g.left = (I.ev N a).left := by rw [ha]; rfl
  rw [← cancel_epi (spMap j), e, h2, spMap_comp, Category.assoc]

theorem level_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) := by
  intro E _ _ _ H D X t Ω _ ξ N hN z ev h
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  obtain ⟨I, h1, h2⟩ := full_iso h (AlgebraicClosure Ω) j
  refine ⟨?_, fun a b => ?_, fun r a => ?_, fun a => ?_, fun g => ?_, fun k _ i g hg => ?_,
    fun k _ _ i a b g g' hg hg' => ?_⟩
  · refine IsPrimitiveRoot.of_map_of_injective (f := Units.map j.toMonoidHom) ?_ (Units.map_injective j.injective)
    rw [← h1]
    exact I.ζ_prim N hN
  · apply extPt_inj j
    rw [MonObj.comp_mul, ← h2, ← h2, ← h2, I.add]
  · apply extPt_inj j
    rw [← h2, I.lin, h2, Category.assoc]
  · rw [← I.ker N hN a, h2]
    exact ⟨fun e => by rw [e, MonObj.comp_one], fun e => extPt_inj j ξ (by rw [e, MonObj.comp_one])⟩
  · constructor
    · intro hg
      obtain ⟨a, ha⟩ := (I.onto N hN (extPt j ξ ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])
      exact ⟨a, extPt_inj j ξ (by rw [← h2, ha])⟩
    · rintro ⟨a, rfl⟩
      apply extPt_inj j
      rw [MonObj.comp_pow, ← h2, MonObj.comp_one]
      exact (I.onto N hN _).2 ⟨a, rfl⟩
  · obtain ⟨a, ha⟩ := full_desc hN h k i g hg
    exact ⟨ev a, ha⟩
  · obtain ⟨J, e1, e2⟩ := full_iso h k i
    have hg1 : g = J.ev N a := by rw [e2]; exact Over.OverMorphism.ext hg
    have hg2 : g' = J.ev N b := by rw [e2]; exact Over.OverMorphism.ext hg'
    rw [hg1, hg2, ← e1]
    exact J.isom N hN a b

theorem finrank_La (D : Datum H) : Module.Free ℤ D.La ∧ Module.Finite ℤ D.La ∧
    Module.finrank ℤ D.La = Module.finrank ℚ E * (D.p + D.q) := by
  have := D.fin
  refine ⟨GlobalTheory.datum_free_int D, Module.Finite.trans (𝓞 E) D.La, ?_⟩
  rw [GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank]

end PositivityTheory.HtPt.Mg
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MiOpen
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace PositivityTheory.HtPt.Mi

theorem flat_of_forall {X Z : Scheme.{0}} (f : X ⟶ Z)
    (h : ∀ x : X, ∃ (W : Scheme.{0}) (g : W ⟶ X) (w : W), g w = x ∧ Flat g ∧ Flat (g ≫ f)) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨W, g, w, rfl, _, _⟩ := h x
  have h := Flat.stalkMap (g ≫ f) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact GlobalTheory.ringHom_flat_of_comp_faithfullyFlat (GlobalTheory.faithfullyFlat_stalkMap_of_flat g w) h

theorem open_crit : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  intro R _ X Y j q _ H
  have key : ∀ x : X, ∃ (U V : Scheme.{0}) (g : U ⟶ X) (u : U) (δ : U ⟶ V) (m : V ⟶ pullback j j),
      g u = x ∧ Flat g ∧ Flat (g ≫ j) ∧ IsOpenImmersion δ ∧ Flat m ∧ δ ≫ m = g ≫ pullback.diagonal j ∧
      ∀ z, pullback.snd j j z = x → ∃ u', m (δ u') = z := by
    intro x
    obtain ⟨R', _, _, _, X', Y', j', q', a, b, U, hfl, hP, hb, ha, hU, hcl⟩ := @H (q (j x)).asIdeal (q (j x)).isPrime
    have hs : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 hfl)
    have hbf : Flat b := MorphismProperty.of_isPullback hb.flip hs
    have haf : Flat a := MorphismProperty.of_isPullback ha.flip hbf
    obtain ⟨x', hx1, hx2⟩ := Scheme.exists_preimage_of_isPullback (ha.paste_vert hb) x
      (IsLocalRing.closedPoint R') (PrimeSpectrum.ext hP.symm)
    have hx2' : q' (j' x') = IsLocalRing.closedPoint R' := by rw [← hx2]; simp
    let u : U.toScheme := ⟨x', hcl x' hx2'⟩
    have hu : U.ι u = x' := rfl
    have hw : (U.ι ≫ a) ≫ j = (U.ι ≫ j') ≫ b := by rw [Category.assoc, ha.w, Category.assoc]
    let δ : U.toScheme ⟶ pullback j' (U.ι ≫ j') := pullback.lift U.ι (𝟙 _) (by simp)
    have hδ : δ ≫ pullback.fst _ _ = U.ι := pullback.lift_fst _ _ _
    have hδ' : δ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hV := (IsPullback.of_hasPullback j' (U.ι ≫ j')).paste_horiz ha
    rw [← hw] at hV
    let m : pullback j' (U.ι ≫ j') ⟶ pullback j j :=
      pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _ ≫ U.ι ≫ a) (by rw [hV.w]; simp only [Category.assoc])
    have hm1 : m ≫ pullback.fst j j = pullback.fst _ _ ≫ a := pullback.lift_fst _ _ _
    have hm2 : m ≫ pullback.snd j j = pullback.snd _ _ ≫ U.ι ≫ a := pullback.lift_snd _ _ _
    have hm : IsPullback m (pullback.snd j' (U.ι ≫ j')) (pullback.snd j j) (U.ι ≫ a) :=
      IsPullback.of_right (by rw [hm1]; exact hV) hm2 (IsPullback.of_hasPullback j j)
    have hg : Flat (U.ι ≫ a) := inferInstance
    have hδo : IsOpenImmersion δ := by
      have : IsOpenImmersion (δ ≫ pullback.fst j' (U.ι ≫ j')) := by rw [hδ]; infer_instance
      exact IsOpenImmersion.of_comp δ (pullback.fst j' (U.ι ≫ j'))
    have hgu : (U.ι ≫ a) u = x := by rw [Scheme.Hom.comp_apply, hu]; exact hx1
    refine ⟨U, _, U.ι ≫ a, u, δ, m, hgu, hg, by rw [hw]; infer_instance, hδo,
      MorphismProperty.of_isPullback hm.flip hg, ?_, fun z hz => ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hm1, reassoc_of% hδ]; simp
      · rw [Category.assoc, hm2, reassoc_of% hδ']; simp
    · obtain ⟨v, hv1, hv2⟩ := Scheme.exists_preimage_of_isPullback hm z u (hz.trans hgu.symm)
      have h1 : j' (pullback.fst j' (U.ι ≫ j') v) = j' x' := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact congrArg (fun t => j' (U.ι t)) hv2
      let u' : U.toScheme := ⟨pullback.fst j' (U.ι ≫ j') v, hcl _ (by rw [h1, hx2'])⟩
      have h2 : δ u' = v := by
        apply (pullback.fst j' (U.ι ≫ j')).isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hδ]
        rfl
      exact ⟨u', by rw [h2]; exact hv1⟩
  have : Flat j := flat_of_forall j fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, h3, -⟩ := key x
    exact ⟨U, g, u, h1, h2, h3⟩
  have : Flat (pullback.diagonal j) := flat_of_forall _ fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, -, h4, h5, h6, -⟩ := key x
    exact ⟨U, g, u, h1, h2, by rw [← h6]; infer_instance⟩
  have : Surjective (pullback.diagonal j) := ⟨fun z => by
    obtain ⟨U, V, g, u, δ, m, -, -, -, -, -, h6, h7⟩ := key (pullback.snd j j z)
    obtain ⟨u', hu'⟩ := h7 z rfl
    exact ⟨g u', by rw [← hu', ← Scheme.Hom.comp_apply, ← h6, Scheme.Hom.comp_apply]⟩⟩
  have : IsClosedImmersion (pullback.diagonal j) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [(pullback.diagonal j).surjective.range_eq]; exact isClosed_univ)
  have : IsIso (pullback.diagonal j) := Flat.isIso_of_surjective_of_mono _
  have : Mono j := (pullback.isIso_diagonal_iff j).1 this
  exact IsOpenImmersion.of_flat_of_mono j

end PositivityTheory.HtPt.Mi
end

