module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFiniteGaloisStableThetaRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.NormalClosureRing

theorem exists_integralClosure_finite : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (κ : o₁ →+* o₂), κ.Finite → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ h.Finite ∧ IsIntegrallyClosed R ∧ ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ x ∈ R, σ x ∈ R := by
  intro o₁ Ω₁ _ _ _ _ R₁ hR₁ hfrac o₂ Ω₂ _ _ _ _ _ _ κ hκ hcomp
  haveI : IsDedekindDomain o₁ := ArithBase.ded (Ω := Ω₁)
  haveI : CharZero Ω₁ := ArithBase.char (o := o₁)
  have hinj₁ : Function.Injective (algebraMap o₁ Ω₁) := ArithBase.inj
  haveI : CharZero o₁ := (algebraMap o₁ Ω₁).charZero
  haveI : Algebra.FiniteType o₁ R₁ := (Subalgebra.fg_iff_finiteType R₁).mp hR₁
  haveI : FaithfulSMul o₁ R₁ := (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b hab => hinj₁ (congrArg Subtype.val hab)
  haveI : FaithfulSMul R₁ Ω₁ := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI : IsFractionRing R₁ Ω₁ := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfrac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  haveI : IsScalarTower R₁ Ω₁ Ω₂ := inferInstance
  let C := integralClosure R₁ Ω₂
  have hmem : ∀ x : o₂, algebraMap o₂ Ω₂ x ∈ C := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hκ.to_isIntegral x
    refine ⟨p.map (algebraMap o₁ R₁), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have := congrArg (algebraMap o₂ Ω₂) hpx
    rw [Polynomial.hom_eval₂, map_zero, hcomp] at this
    exact this
  let R : Subalgebra o₂ Ω₂ :=
    { toSubsemiring := C.toSubsemiring
      algebraMap_mem' := hmem }
  let h : R₁ →+* R := (algebraMap R₁ Ω₂).codRestrict R fun a => (isIntegral_algebraMap : IsIntegral R₁ (algebraMap R₁ Ω₂ a))
  have hh : ∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a := fun a => rfl
  haveI : Module.Finite R₁ C := GlobalTheory.finite_integralClosure_dedekind o₁ R₁ Ω₁ Ω₂
  classical
  have hfg : R.FG := by
    obtain ⟨s, hs⟩ := hR₁
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule R₁ C).FG)
    refine ⟨s.image (algebraMap Ω₁ Ω₂) ∪ t.image Subtype.val, le_antisymm ?_ ?_⟩
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe] at hy
      rcases hy with ⟨a, ha, rfl⟩ | ⟨z, -, rfl⟩
      · have ha' : a ∈ R₁ := hs ▸ Algebra.subset_adjoin ha
        exact (h ⟨a, ha'⟩).2
      · exact z.2
    · set A := Algebra.adjoin o₂ ((s.image (algebraMap Ω₁ Ω₂) ∪ t.image Subtype.val : Finset Ω₂) : Set Ω₂)
      have hR₁A : ∀ z ∈ Algebra.adjoin o₁ (s : Set Ω₁), algebraMap Ω₁ Ω₂ z ∈ A := by
        intro z hz
        induction hz using Algebra.adjoin_induction with
        | mem z hz => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz)))
        | algebraMap r =>
          have := congrArg (fun f => f r) hcomp
          simp only [RingHom.comp_apply] at this
          rw [← this]
          exact A.algebraMap_mem _
        | add x y _ _ hx hy => rw [map_add (f := _)]; exact A.add_mem hx hy
        | mul x y _ _ hx hy => rw [map_mul]; exact A.mul_mem hx hy
      suffices key : ∀ y : C, y ∈ Submodule.span R₁ (t : Set C) → (y : Ω₂) ∈ A from
        fun x hx => key ⟨x, hx⟩ (ht ▸ Submodule.mem_top)
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy)))
      | zero => exact A.zero_mem
      | add y z _ _ hy hz => exact A.add_mem hy hz
      | smul r y _ hy =>
        convert A.mul_mem (hR₁A r.1 (hs ▸ r.2)) hy using 1
        first | rfl | exact Algebra.smul_def r (y : Ω₂) | simp [Algebra.smul_def]
  letI : Algebra R₁ R := h.toAlgebra
  haveI : IsScalarTower R₁ R Ω₂ := .of_algebraMap_eq fun a => rfl
  haveI : IsIntegralClosure R R₁ Ω₂ :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := fun {x} => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩ }
  have hfin : h.Finite := GlobalTheory.finite_of_isIntegralClosure_dedekind o₁ R₁ Ω₁ Ω₂ R
  have hic : IsIntegrallyClosed R := integralClosure.isIntegrallyClosedOfFiniteExtension (R := R₁) Ω₁ (L := Ω₂)
  refine ⟨R, h, hfg, ?_, hh, hfin, hic, ?_⟩
  · intro x
    have hxi : IsIntegral Ω₁ x := Algebra.IsIntegral.isIntegral x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors R₁) x hxi
    have hm0 : algebraMap R₁ Ω₂ (m : R₁) ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply R₁ Ω₁ Ω₂]
      exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors m.2)
    refine ⟨_, hm, algebraMap R₁ Ω₂ (m : R₁), isIntegral_algebraMap, ?_⟩
    rw [Submonoid.smul_def, Algebra.smul_def, mul_div_cancel_left₀ _ hm0]
  · intro σ x hx
    exact (show IsIntegral R₁ x from hx).map (σ.toAlgHom.restrictScalars R₁)

end GlobalTheory.Poinc.NormalClosureRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelComparisonGeneratorOfUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem exists_level_gen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∃ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1]), ν.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG (maximalIdeal R) e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hab A₂ D₂ U₂ wL hwL β hβm hβ w hw
  have hab' : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left :=
    fun e ae h1 h2 => (hab e ae h1 h2).1
  obtain ⟨W, hW, HW⟩ := _root_.GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global hR hG U a ha g.b hab' U₂ wL hwL β hβ
  obtain ⟨ν, hν, Hν⟩ := GlobalTheory.T.exists_generator_ratio_translationTwist_isos D₂.toPre D.toPre β.hom g.b w hw W hW
  refine ⟨ν, hν, ?_⟩
  intro e h hh hh' Z r z J J' N N' hJ hJ' hN hN'
  have k0 := lift_comp_pG U a g.b hab' U₂ β hβ e h hh'
  have hm : r ≫ h ≫ (U.gt e).pG.left = (r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
    rw [k0, Category.assoc]
  have hf : r ≫ h ≫ (fstG (maximalIdeal R) e G).left = r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
    rw [hh']
  have hs : (r ≫ (U₂.gt e).pG.left) ≫ D₂.toPre.P.A.hom = r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w]; rfl
  have k2 := Hν Z (r ≫ (U₂.gt e).pG.left) z J (J' (r ≫ (U₂.gt e).pG.left)) hJ (hJ' _)
  have m1 : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0)) := by
    have m1' : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J (r ≫ h ≫ (U.gt e).pG.left)) := by
      simpa using hJ (r ≫ h ≫ (U.gt e).pG.left)
    rw [hm] at m1'
    exact m1'
  have m2 : (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U (J' (r ≫ (U₂.gt e).pG.left)) := by
    simpa using hJ' (r ≫ (U₂.gt e).pG.left)
  have m3 : ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
    simpa using hN (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)
  have m4 : (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U (N' (r ≫ (fstG (maximalIdeal R) e G).left)) := by
    simpa using hN' (r ≫ (fstG (maximalIdeal R) e G).left)
  have k1 := HW e h hh hh' Z r z _ _ _ _ m1 m2 m3 m4
  rw [k2, hs, mul_right_comm, k1, hm, hf]

end GlobalTheory.MumCmp.LevelCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleAlgebraisationGeneratedSystem
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

theorem exists_lb_of_generated_system_proper : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → (∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤) → ∃ (M : LB X.left) (s' : Fin (n + 1) → LB.Sec M) (w : ∀ e, LB.Iso (H e) (M.pull (b e))), M.IsLB ∧ ∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j) := by
  intro R _ _ I hcI X hX Y β b hb hbb H v hH n s hs hgen
  obtain ⟨P, f, O, t, hO, hva, hP⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose c w hc' hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy R P f O n t hO hva _
    ((Y e).hom ≫ thick R I e) (H e) (s e) (hH e).1 (hgen e) (fun d F hF h k => by
      obtain ⟨m, hm⟩ := (hP d F hF).1 h 0
      have : F = 0 := by
        rw [Ideal.mem_bot] at hm
        exact ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1)))).pow m).left (by simpa using hm)
      rw [this, map_zero])
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← (hb (e + 1)).w, ← Category.assoc, hbb, (hb e).w]
  have hcc : ∀ e, β e ≫ c (e + 1) = c e := fun e => by
    have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hO (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections R P f O n t hO hva _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hc', hc', c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
  haveI hPp : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R P f ⟨O, hO, n, t, hva⟩
  obtain ⟨g, hg, -⟩ := _root_.GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms R I hcI X (Over.mk f) hX (inferInstanceAs (IsSeparated f))
    (inferInstanceAs (LocallyOfFiniteType f)) (inferInstanceAs (QuasiCompact f)) Y β b hb hbb
    c hc' hcc
  have hM : (O.pull g.left).IsLB := LB.isLB_pull hO _
  obtain ⟨s', hs'⟩ := GlobalTheory.MorAlg.exists_isPull g.left hO t
  have key : ∀ e, GlobalTheory.MorAlg.IsPull (b e) s' (s e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hO hM (hH e).1 hs' (by rw [hg e]; exact ⟨w e, hw e, hr e⟩)
  choose w' hw' cw using key
  exact ⟨O.pull g.left, s', w', hM, fun e => ⟨hw' e, fun j => cw e j⟩⟩

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionThetaQuotientProjChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThBdl

theorem exists_locSec_of_openImmersion (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (ξ : Sp K ⟶ S)
    (e : spMap (algebraMap R K) ≫ χ = ξ) (θ : SecAt t.G t.PP.L ξ) (pt : Fin N → (Over.mk ξ ⟶ t.G)) (c : Fin N → R)
    (hodd : Odd m) (hm3 : 3 ≤ m) (hm : IsUnit (m : R)) (hpol : PolFib t.G t.PP.L g ξ)
    (hth : ThList t.G t.PP.L t.PP.rig m ξ θ pt (fun a => algebraMap R K (c a))) (hu : ∃ a, IsUnit (c a)) :
    ∃ s : LocSec t.G t.PP.L χ.opensRange, IsLocSec s ∧ GenIs ξ s (SecM.ofSec t.G θ) ∧ FibNz s χ.opensRange := by
  subst e
  have hlft : LocallyOfFiniteType t.G.hom := by
    haveI := t.semi.smooth
    infer_instance
  obtain ⟨σ, hσ, hσnz⟩ := _root_.GlobalTheory.UMin.ExtFrac.ext_any_frac E H S t g m N R K χ θ pt c hodd hm3 hm hpol hth hu
  obtain ⟨s, hs, hsgen, hsfib⟩ := _root_.GlobalTheory.UMin.LocSecOfImm.exists_locSec S t.G t.PP.L R χ σ hlft hσnz
  refine ⟨s, hs, ?_, hsfib⟩
  have := hsgen K (algebraMap R K)
  rw [hσ] at this
  exact this

theorem exists_locSec_theta_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G)),
    Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt →
    IsGenSec t.G t.PP.L _ θ → ThList t.G t.PP.L t.PP.rig m M.pt θ pt c → PCrd (M.pt ≫ h) c →
    ∀ (a : Fin (n + 1)) (z : M.Z), z ∈ h ⁻¹ᵁ chart k n a → ∃ N : M.Z.Opens, z ∈ N ∧ N ≤ h ⁻¹ᵁ chart k n a ∧
      ∃ s : LocSec t.G t.PP.L N, IsLocSec s ∧
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ) ∧ FibNz s N := by
  intro E _ _ _ H k Ω _ _ _ _ _ M t g m n c h θ pt hN hodd hm3 hmu hpol hgen hth hcrd a z hz
  obtain ⟨hca, hdiv⟩ := _root_.GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O k Ω M n c h a z hcrd hz
  obtain ⟨W, hWa, hzW, hWV, hnoeth, hic⟩ := _root_.GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed k Ω M hN (h ⁻¹ᵁ chart k n a) z hz
  have hne : (W : Set M.Z).Nonempty := ⟨z, hzW⟩
  obtain ⟨χ, hoi, hrange, hgenpt⟩ := GlobalTheory.T.exists_openImmersion_spec_ringOn_affine k Ω M W hWa hne
  haveI := M.isFractionRing_ringOn hWa hne
  let c'' : Fin (n + 1) → M.ringOn W := fun b =>
    ⟨c b / c a, RatModel.mem_ringOn.2 fun z' hz' => hdiv z' (hWV hz') b⟩
  let θ' : SecAt t.G t.PP.L M.pt :=
    SecM.toSec t.G ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ)
  have hmΩ : (m : Ω) ≠ 0 := by
    have := hmu.map (algebraMap k Ω)
    rw [map_natCast] at this
    exact this.ne_zero
  have hth' : ThList t.G t.PP.L t.PP.rig m M.pt θ' pt (fun b => algebraMap (M.ringOn W) Ω (c'' b)) := by
    refine ⟨hth.1, fun b => ?_, hth.2.2⟩
    have key := GlobalTheory.UMin.thG_smul_iff M.Z t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m Ω M.pt θ θ' (pt b)
      (c a)⁻¹ (c b) (c b / c a) hodd hmΩ hpol rfl (hth.2.1 b)
    exact key.2 (by rw [div_eq_inv_mul])
  have hmR : IsUnit (m : M.ringOn W) := by
    have := hmu.map (algebraMap k (M.ringOn W))
    rwa [map_natCast] at this
  have hunit : ∃ b, IsUnit (c'' b) := ⟨a, by
    have : c'' a = 1 := Subtype.ext (by simp [c'', div_self hca])
    rw [this]; exact isUnit_one⟩
  obtain ⟨s, hs, hsgen, hsfib⟩ := exists_locSec_of_openImmersion E H M.Z t g m (n + 1) (M.ringOn W) Ω χ M.pt hgenpt θ' pt c'' hodd hm3 hmR hpol hth' hunit
  exact ⟨χ.opensRange, by rw [hrange]; exact hzW, by rw [hrange]; exact hWV, s, hs, hsgen, hsfib⟩

end GlobalTheory.UMin.ThBdl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedRepresentsFixedPullbackHoms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixMat

theorem exists_locClosed_homFix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ (N : ℕ) (X : Scheme.{0}) (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (H : Scheme.{0}) (i : H ⟶ X)
    (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left)
    (Φ : AH ⟶ BH), IsClosedImmersion c ∧ IsOpenImmersion i ∧
    IsGrpPullback AH A (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φA ∧ IsGrpPullback BH B (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φB ∧ IsMonHom Φ ∧
    LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))) = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM hrA hrB hamp hk hva hbasA hbasB
  obtain ⟨eA, heA⟩ := hrA
  obtain ⟨eB, heB⟩ := hrB
  obtain ⟨mA, bA, hbA⟩ := hbasA
  obtain ⟨mB, bB, hbB⟩ := hbasB
  have hyp : Hyps L M k bA bB eA eB := ⟨hA, hB, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩

  obtain ⟨X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest, hex, hmat⟩ :=
    GlobalTheory.T.exists_locallyClosed_universal_hom_matrix_scheme Rg A B L M k mA mB bA bB eA eB hyp
  refine ⟨mA * mB, X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest.1, htest.2.1, htest.2.2.1,
    htest.2.2.2, ?_⟩
  intro R _ t A' B' _ _ φA' φB' Φ' h1 h2 h3 h4
  have ht : IsTest A B L M t A' B' φA' φB' Φ' := ⟨h1, h2, h3, h4⟩

  obtain ⟨c, hc'⟩ := GlobalTheory.T.line_bundle_sections_product_base_change Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' ht
  obtain ⟨h, hh, hmatc⟩ := hex R t A' B' φA' φB' Φ' c ht hc'

  obtain ⟨A₂, g₂, B₂, g₂', φA₂, φB₂, Φ₂, ht₂, hp₂⟩ :=
    GlobalTheory.T.exists_isTest_comp_isPullD_of_isTest Rg A B L M H (Sp R) (i ≫ cE ≫ affπ Rg (mA * mB)) h AH BH φA φB Φ htest
  have hm₂ := hmat R h A₂ B₂ φA₂ φB₂ Φ₂ ht₂ hp₂
  rw [hh, hmatc] at hm₂
  rw [hh] at ht₂

  have hpd := _root_.GlobalTheory.HomFixMat.mat_determines Rg A B L M k mA mB bA bB eA eB hyp R t A₂ B₂ φA₂ φB₂ Φ₂ A' B' φA' φB' Φ' c
    ht₂ ht hm₂ hc'
  have hfin := IsPullD.comp hp₂ hpd
  rw [Category.id_comp] at hfin
  refine ⟨h, ⟨hh, hfin⟩, ?_⟩

  rintro h' ⟨hh', hpd'⟩
  have ht' : IsTest A B L M (h' ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' := by
    rw [hh']; exact ht
  have hm' := hmat R h' A' B' φA' φB' Φ' ht' hpd'
  rw [hh'] at hm'
  have heq : matOf (h' ≫ i ≫ cE) = c :=
    _root_.GlobalTheory.HomFixUniq.mat_unique Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' _ _ ht hm' hc'
  have hg : h' ≫ i ≫ cE = h ≫ i ≫ cE := by
    apply hom_ext_affine
    · simp only [Category.assoc]
      rw [hh', hh]
    · intro n
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective n
      exact congrFun (congrFun (heq.trans hmatc.symm) p.1) p.2
  have hg' : h' ≫ i = h ≫ i := by
    rw [← cancel_mono cE]
    simpa only [Category.assoc] using hg
  exact (cancel_mono i).1 hg'

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemGenericPointsClosureEqOfIsClopen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory

theorem exists_mem_genericPoints_closure_eq_of_isClopen :
    ∀ (X Z : Scheme.{0}) (i : X ⟶ Z), IsOpenImmersion i → Dense (Set.range i) → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ η ∈ genericPoints X, closure {i η} = W := by
  intro X Z i hi hd W hWc hWi
  have he : Topology.IsOpenEmbedding i := i.isOpenEmbedding

  have hgen : IsGenericPoint hWi.genericPoint W :=
    hWi.isGenericPoint_genericPoint hWc.isClosed
  have hne : (W ∩ Set.range i).Nonempty :=
    hd.inter_open_nonempty W hWc.isOpen hWi.nonempty
  have hmem : hWi.genericPoint ∈ Set.range i :=
    (hgen.mem_open_set_iff he.isOpen_range).2 hne
  obtain ⟨η, hη⟩ := hmem
  have hcl : closure {i η} = W := by rw [hη]; exact hgen
  refine ⟨η, ?_, hcl⟩

  have hpre : closure ({η} : Set X) = i ⁻¹' W := by
    rw [← hcl, he.isOpenMap.preimage_closure_eq_closure_preimage he.continuous,
      ← Set.image_singleton, he.injective.preimage_image]
  show closure ({η} : Set X) ∈ irreducibleComponents X
  have hirr : IsIrreducible (closure ({η} : Set X)) := isIrreducible_singleton.closure
  have hclo : IsClopen (closure ({η} : Set X)) := by
    rw [hpre]; exact hWc.preimage he.continuous
  refine ⟨hirr, fun T hT hsub => ?_⟩
  refine hT.2.isPreconnected.subset_isClopen hclo ?_
  exact ⟨η, hsub (subset_closure rfl), subset_closure rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMetricShiftIsNefPowTensAmple
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem exists_isNef_shift_pow_tens : GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), L.SemiPos D → NefFib L → IsAmpleLB A.B → A.IsNef D → ∃ t : ℝ, (((L.pow n).tens A).shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hC hN k _ X _ p D hX L A n hL hLf hA hAn
  obtain ⟨m, N, s, hm, hs⟩ := _root_.GlobalTheory.GenFibreGen.exists_secs_generic hN k X p D hX L A n hLf hA
  obtain ⟨t, -, ht⟩ := GlobalTheory.NefOfGen.nef_of_gen hC k X p D hX ((L.pow n).tens A) m N s hm hs
    ((hL.pow n).tens hAn.semiPos) (_root_.GlobalTheory.NefFibTens.nefFib_pow_tens k X p D hX L A n hLf (nefFib_of_isNef hAn))
  exact ⟨t, ht⟩

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveDeRhamClassTorsionCharacterStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_primitive_deRham_class_torsion_character
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ) (hN : (p : R) ^ N = 0)
    (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A) (hP : AllPrim (dp0 R) (𝟙 _) A)
    (hs : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)))
    (G : PDivGroup p R) (t : G.TorsionTower A) (b : Fn0 A) (hb : IsTorsChar (p ^ N) b) :
    ∃ (c : primDR A) (d : Dat t c), ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      x ^ (p ^ N) = 1 → chi (p ^ N) d.g D x = b D x :=
  GlobalTheory.PtExt.exists_dat_chi_eq p R N hN A hA hP hs G t b hb
end

