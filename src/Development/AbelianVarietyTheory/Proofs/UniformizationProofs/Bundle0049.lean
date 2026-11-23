module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompletedPointOfThickenings
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompletedPoint

theorem adicLevelMap_surjective {B : Type} [CommRing B] (J : Ideal B) (n : ℕ) :
    Function.Surjective (adicLevelMap J (Nat.succ_le_succ (Nat.zero_le n))) := by
  intro p
  have : Set.range (PrimeSpectrum.comap (Ideal.Quotient.factorPow J (Nat.succ_le_succ (Nat.zero_le n)))) = _ :=
    range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective _)
  refine this.ge ?_
  refine (PrimeSpectrum.mem_zeroLocus _ _).2 fun a ha => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hb : b ∈ J := by
    have h : Ideal.Quotient.mk (J ^ (0 + 1)) b = 0 := ha
    rwa [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at h
  refine p.isPrime.mem_of_pow_mem (n + 1) ?_
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hb _)]
  exact zero_mem _

theorem hom_ext_spec {B : Type} [CommRing B] (J : Ideal B) [IsHausdorff J B] {S : CommRingCat.{0}}
    {g g' : Spec (CommRingCat.of B) ⟶ Spec S}
    (h : ∀ n, adicLevelι J (n + 1) ≫ g = adicLevelι J (n + 1) ≫ g') : g = g' := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
  congr 1
  ext1
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
  intro n a
  have h1 := h n
  rw [← Spec.map_comp, ← Spec.map_comp] at h1
  exact congr($(Spec.map_injective h1).hom a)

theorem exists_of_isAdicFamily {B : Type} [CommRing B] (J : Ideal B) [IsAdicComplete J B] {X : Scheme.{0}}
    {V : X.Opens} (hV : IsAffineOpen V) {f : ∀ n : ℕ, Spec (CommRingCat.of (B ⧸ J ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily J f) (h₀ : ∀ p, f 0 p ∈ V) :
    ∃ g : Spec (CommRingCat.of B) ⟶ X, (∀ p, g p ∈ V) ∧ ∀ n, adicLevelι J (n + 1) ≫ g = f n := by
  have hr : ∀ n, Set.range (f n) ⊆ Set.range hV.fromSpec := fun n => by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := adicLevelMap_surjective J n p
    rw [hV.range_fromSpec, ← Scheme.Hom.comp_apply, hf.of_le (Nat.zero_le n)]
    exact h₀ q
  have hφ : ∀ n, ∃ φ : Γ(X, V) ⟶ CommRingCat.of (B ⧸ J ^ (n + 1)), Spec.map φ ≫ hV.fromSpec = f n := fun n => by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec (f n) (hr n))
    exact ⟨φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩
  choose φ hφ using hφ
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp
      (φ (m + 1)).hom = (φ m).hom := by
    intro m
    have h1 : adicLevelMap J (Nat.le_succ (m + 1)) ≫ Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono hV.fromSpec, Category.assoc, hφ, hφ, hf m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom)
  refine ⟨Spec.map (CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom J ha (fun n => (φ n).hom) hc)) ≫ hV.fromSpec, fun p => ?_,
    fun n => ?_⟩
  · exact hV.range_fromSpec.le ⟨_, rfl⟩
  · rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha (fun n => (φ n).hom) hc (n := n)]
    exact hφ n

theorem exists_completion {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) :
    ∃ (B : Type) (_ : CommRing B) (ψ : A →+* B), IsAdicComplete (J.map ψ) B ∧ ψ.Flat ∧
      ∀ p : PrimeSpectrum A, J ≤ p.asIdeal → p ∈ Set.range (PrimeSpectrum.comap ψ) := by
  refine ⟨AdicCompletion J A, inferInstance, algebraMap _ _, ?_, ?_, fun p hp => ?_⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete J.fg_of_isNoetherianRing
  · exact RingHom.flat_algebraMap_iff.2 inferInstance
  · have h : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J ^ 1))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus,
        Ideal.mk_ker, pow_one]
      exact hp
    obtain ⟨q, rfl⟩ := h
    refine ⟨PrimeSpectrum.comap (AdicCompletion.evalₐ J 1).toRingHom q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    congr 2


open GlobalTheory.FormalPoint in
theorem exists_completed_point {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (G G' : Over (Spec (CommRingCat.of R))) [Flat G'.hom] [LocallyOfFiniteType G'.hom]
    (j : ∀ e : ℕ, thickObj R I e G' ⟶ thickObj R I e G)
    (hj : ∀ e, thickMap R I e G' ≫ (j (e + 1)).left = (j e).left ≫ thickMap R I e G)
    (x : (thickObj R I 0 G').left) (W : G.left.Opens) (W' : G'.left.Opens)
    (hW : (fstG I 0 G).left ((j 0).left x) ∈ W) (hW' : (fstG I 0 G').left x ∈ W') :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left)
      (g : Spec (CommRingCat.of B) ⟶ G.left), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧
      Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧
      g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
      g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ W' ∧ ⊤ ≤ g ⁻¹ᵁ W ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
        r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).left ≫ (fstG I e G).left = ρ ≫ g := by
  have tf : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      thickMap R I e H ≫ (fstG I (e + 1) H).left = (fstG I e H).left := fun e H =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have fh : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      (fstG I e H).left ≫ H.hom = (thickObj R I e H).hom ≫ thick R I e := fun e H => pullback.condition
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open hW W.isOpen
  have hci : IsClosedImmersion (thick R I 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hci' : IsClosedImmersion (fstG I 0 G').left :=
    inferInstanceAs (IsClosedImmersion (pullback.fst G'.hom (thick R I 0)))
  obtain ⟨O, hO, hO'⟩ := (fstG I 0 G').left.isClosedEmbedding.isInducing.isOpen_iff.1
    (((j 0).left ≫ (fstG I 0 G).left) ⁻¹ᵁ V).isOpen
  have hxO : (fstG I 0 G').left x ∈ O := hO'.ge hxV
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hVO⟩ := G'.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show (fstG I 0 G').left x ∈ O ∩ W' from ⟨hxO, hW'⟩) (hO.inter W'.isOpen)
  replace hV' : IsAffineOpen V' := hV'
  have hln : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hN : IsNoetherianRing Γ(G'.left, V') := IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV'.fromSpec ≫ G'.hom)
  have hφf : φ.hom.Flat := by
    have : Flat (Spec.map φ) := by rw [hφ]; exact Flat.comp _ _
    exact Flat.SpecMap_iff.1 this
  obtain ⟨B, _, ψ, hB, hψ, hs⟩ := exists_completion (I.map φ.hom)
  letI : Algebra R B := (ψ.comp φ.hom).toAlgebra
  have hBc : IsAdicComplete (I.map (algebraMap R B)) B := by
    rw [Ideal.map_map] at hB; exact hB
  let g' : Spec (CommRingCat.of B) ⟶ G'.left := Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec
  have hg' : g' ≫ G'.hom = spMap (algebraMap R B) := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  have hg'V : ∀ p, g' p ∈ V' := fun p => hV'.range_fromSpec.le ⟨_, rfl⟩
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  have hf : IsAdicFamily (I.map (algebraMap R B)) fun e => reduction I y e ≫ (j e).left ≫ (fstG I e G).left := by
    intro e
    have h₁ : adicLevelMap (I.map (algebraMap R B)) (Nat.le_succ (e + 1)) ≫ reduction I y (e + 1) =
        reduction I y e ≫ thickMap R I e G' := by
      rw [← cancel_mono (fstG I (e + 1) G').left, Category.assoc, Category.assoc, hy, tf, hy, adicLevelMap_ι_assoc]
    show _ ≫ _ ≫ _ = _
    rw [reassoc_of% h₁, reassoc_of% (hj e), tf]
  obtain ⟨g, hgV, hg⟩ := exists_of_isAdicFamily _ hV hf fun p => by
    have h₁ : (fstG I 0 G').left (reduction I y 0 p) ∈ O := by
      have : (reduction I y 0 ≫ (fstG I 0 G').left) p ∈ V' := by rw [hy]; exact hg'V _
      exact (hVO this).1
    exact hO'.le h₁
  refine ⟨B, inferInstance, inferInstance, g', g, hBc, RingHom.Flat.comp hφf hψ, ?_, ?_, hg', ?_, fun p _ => (hVO (hg'V p)).2,
    fun p _ => hVW (hgV p), fun e Z ρ r h => ?_⟩
  · have : Flat (Spec.map (CommRingCat.ofHom ψ)) := Flat.SpecMap_iff.2 hψ
    exact Flat.comp _ _
  · obtain ⟨p, hp⟩ := hV'.range_fromSpec.ge hxV'
    obtain ⟨q, hq⟩ := hs p (by
      rw [Ideal.map_le_iff_le_comap]
      have h₁ : Spec.map φ p = thick R I 0 ((thickObj R I 0 G').hom x) := by
        rw [hφ, Scheme.Hom.comp_apply, hp, ← Scheme.Hom.comp_apply, fh]; rfl
      have h₂ : p.asIdeal.comap φ.hom = _ := congrArg PrimeSpectrum.asIdeal h₁
      rw [h₂]
      intro a ha
      show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ PrimeSpectrum.asIdeal _
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [zero_add, pow_one])]
      exact zero_mem _)
    exact ⟨q, (congrArg hV'.fromSpec hq).trans hp⟩
  · refine hom_ext_spec (I.map (algebraMap R B)) fun e => ?_
    rw [reassoc_of% (hg e), fh, ← Category.assoc (j e).left, Over.w, ← Category.assoc, reduction_hom,
      levelMap_thick]
  · have w : ρ ≫ spMap (algebraMap R B) = (r ≫ (thickObj R I e G').hom) ≫ thick R I e := by
      rw [← hg', ← Category.assoc, ← h, Category.assoc, fh, Category.assoc]
    obtain ⟨l, rfl⟩ := exists_factor_level I (algebraMap R B) ρ _ w
    obtain rfl : r = l ≫ reduction I y e := by
      rw [← cancel_mono (fstG I e G').left, Category.assoc, hy]
      exact h.trans (Category.assoc _ _ _)
    rw [Category.assoc, Category.assoc, hg]

end GlobalTheory.CompletedPoint

theorem GlobalTheory.exists_completed_point_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ x : (thickObj R I 0 G').left, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧ Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧ g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' ∧ ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g := by
  intro R _ _ _ I _ _ D D' A A' G G' _ _ _ _ _ hG' U U' hD j hj x
  have := hG'.smooth
  obtain ⟨jL, h⟩ : ∃ i, (fstG I 0 G).left ((j 0).hom.left x) ∈ U.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U.LG.isLB.cover.ge trivial)
  obtain ⟨jL', h'⟩ : ∃ i, (fstG I 0 G').left x ∈ U'.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U'.LG.isLB.cover.ge trivial)
  obtain ⟨B, _, _, g', g, H⟩ := GlobalTheory.CompletedPoint.exists_completed_point I G G' (fun e => (j e).hom)
    (fun e => (hj e).2.1) x _ _ h h'
  exact ⟨B, _, _, g', g, jL, jL', H⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamCoefVal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefUnit
open GlobalTheory.UT.CoefBasic

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem point_ext {X : Scheme.{0}} [X.IsSeparated] (x₁ x₂ : (TWM.TO hϖ hv).left ⟶ X)
    (h : (TWM.ιS hϖ hv).left ≫ x₁ = (TWM.ιS hϖ hv).left ≫ x₂) : x₁ = x₂ := by
  have hU : ValuativeCriterion.Uniqueness (terminal.from X) := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq (terminal.from X) :=
    { R := TWO.Ov v, K := F, i₁ := (TWM.ιS hϖ hv).left ≫ x₁, i₂ := terminal.from _,
      commSq := ⟨terminal.hom_ext _ _⟩ }
  have := (hU S).elim ⟨x₁, rfl, terminal.hom_ext _ _⟩ ⟨x₂, h.symm, terminal.hom_ext _ _⟩
  exact congrArg CommSq.LiftStruct.l this

theorem exists_ratio_nonneg {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, 0 ≤ v x ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨s, hs⟩ := exists_sec hL h (Geo.Tor.genSec t ht)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.TwistUnit.exists_ratio_local (R := TWO.Ov v) hL s t' ht'
  refine ⟨TWM.ιr (v := v) x₀, TWM.v_ιr x₀, fun z J hJ => ?_⟩
  have e := gs_pull (𝟙 _) (TWM.ιS hϖ hv).left z ⊤ trivial x₀
  rw [Category.id_comp] at e
  have e' := e.symm.trans (congrArg (gs (𝟙 _) z ⊤)
    (TWM.appTop_specMap (CommRingCat.ofHom (algebraMap (TWO.Ov v) F)) x₀))
  exact (sval_genSec t ht _ z hJ).symm.trans ((hs _ _ z J hJ).symm.trans
    ((hx₀ _ _ z J hJ).trans (congrArg (· * _) e')))

theorem exists_ratio_zero {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, v x = 0 ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨x, hx, e⟩ := exists_ratio_nonneg hϖ hv hL h t ht t' ht'
  obtain ⟨y, hy, e'⟩ := exists_ratio_nonneg hϖ hv hL (fun U _ g => (h U g).symm) t' ht' t ht
  refine ⟨x, le_antisymm (TWO.le_zero_of_add_eq_zero_nonneg ?_ hy) hx, e⟩
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have a := e z J hJ
  rw [e' z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, ← map_mul] at a
  have b : cstH z (x * y) = 1 := by
    rw [← Units.mul_left_inj (val t (TWM.ιS hϖ hv).left z J), _root_.one_mul]; exact a.symm
  rw [← AddValuation.map_mul, cstH_inj z (b.trans (map_one _).symm), AddValuation.map_one]

theorem v_of_isCoef {D : DegData V (maximalIdeal V)} {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b}
    {χ : D.toPre.X} {l ω : ℚ} (hg : GenV hϖ hv (g.s χ) l) (hw : GenV hϖ hv w ω)
    (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) (hm : TWM.ιS hϖ hv ≫ m = g.b)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)))
    (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => m.left ≫ DegPre.famφB D.toPre χ i) (DegPre.famε k)))
    (hG₀ : G₀.IsGen) (x : F)
    (hs : ∀ z J, Good D.toPre.P.L z J → sval s (lift (𝟙 (TF (R := V) F)) g.b).left z J =
      cst (R := V) F z x * (val G₀ (TWM.ιS hϖ hv).left z J).val) :
    ∃ c, IsCoef k g w χ s c ∧ v c = v x + ((l + ω : ℚ) : WithTop ℚ) := by
  have hL := D.toPre.P.isLB
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨φ₁, h₁, t₁, ht₁, x₁, v₁, e₁⟩ := hg
  obtain ⟨φ₂, h₂, t₂, ht₂, x₂, v₂, e₂⟩ := hw
  have c₁ : TWM.ιS hϖ hv ≫ cP D.toPre _ χ = cP D.toPre _ χ := comp_cP D.toPre _ χ
  have c₂ : TWM.ιS hϖ hv ≫ (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A) = 1 := MonObj.comp_one _
  have c₃ : TWM.ιS hϖ hv ≫ (cP D.toPre _ χ * m) = cP D.toPre _ χ * g.b := by
    rw [MonObj.comp_mul, c₁, hm]
  obtain rfl : φ₁ = TWM.gtφO hϖ hv m χ := funext fun i => point_ext hϖ hv _ _ ((h₁ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₃.symm, congrArg (·.left) c₁.symm, congrArg (·.left) hm.symm,
      congrArg (·.left) c₂.symm]))
  obtain rfl : φ₂ = TWM.lineφO hϖ hv m := funext fun i => point_ext hϖ hv _ _ ((h₂ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₂.symm, congrArg (·.left) hm.symm]))
  obtain ⟨u, hu, eu⟩ := exists_ratio_zero hϖ hv hL (fun U _ h => by
      have p := SectionScalarValuation.prod_famB D.toPre m χ k h
      have q : (TWM.TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left := rfl
      have r : m * SectionScalarValuation.cQ D.toPre _ χ = cP D.toPre _ χ * m := mul_comm _ _
      have r' : SectionScalarValuation.cQ D.toPre (TWM.TO hϖ hv) χ = cP D.toPre _ χ := rfl
      rw [r, r'] at p
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [p, Fintype.prod_unique (_ : PUnit → U), q]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, TWM.gtφO, TWM.lineφO, DegPre.gtε, DegPre.lineε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ G₀ t₁) t₂)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hG₀ ht₁) ht₂)
    (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TWM.TO hϖ hv).hom)
    (DVR.pullGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ D.toPre.rig_gen k) _)
  refine ⟨x * x₁ * x₂ * u, fun z J hJ => ?_, ?_⟩
  · have a := eu z J hJ
    rw [val_mul hJ, val_mul hJ, val_pull hJ, Over.w (TWM.ιS hϖ hv)] at a
    have b : val (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TF (R := V) F).hom z J = rigV D.toPre (TF (R := V) F).hom z J ^ k := map_pow _ _ _
    rw [b, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val] at a
    rw [hs z J hJ, e₁ z J hJ, e₂ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination (-(cstH z x * cstH z x₁ * cstH z x₂)) * a
  · rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hu, v₁, v₂, add_zero, add_assoc,
      WithTop.coe_add]

end

theorem exists_fam_coef_val : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 4 ≤ k → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) l ω, w.IsGen → GtV hϖ hv g l → GenV hϖ hv w ω → ∀ a₀ : D.toPre.X, ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ (∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, (s.s β).f j = 0) ∧ v (coef s g w a₀) = (((Q a₀ : ℚ) / k + l a₀ + ω : ℚ) : WithTop ℚ) := by
  intro hLL hT _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk g w l ω hw hg hω a₀
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv g.b
  obtain ⟨σ, hσ, G₀, hG₀, x, hx, hs⟩ :=
    GlobalTheory.exists_integral_section_unit_at hLL.1 hT V ϖ hϖ D Q hQ F v hv k hk a₀ m
  rw [hm] at hs
  obtain ⟨c, hc, vc⟩ := v_of_isCoef hϖ hv (hg a₀) hω m hm σ G₀ hG₀ x hs
  obtain ⟨s₀, rfl, h₀⟩ := GlobalTheory.FamFree.exists_fam_single hLL.1.globalFns D.tau_bimult (by omega : 1 ≤ k) a₀ σ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : F, v ζ = (((Q a₀ : ℚ) / k : ℚ) : WithTop ℚ) := by
    by_cases h : a₀ = 0
    · exact ⟨1, by rw [h, QForm.Q_zero hϖ D hQ, AddValuation.map_one]; simp⟩
    · have h1 := QForm.Q_pos hϖ D hQ h
      obtain ⟨ζ, -, e⟩ := exists_val_eq hv (r := (Q a₀ : ℚ) / k)
        (div_pos (by exact_mod_cast (by omega : (0 : ℤ) < Q a₀)) (by exact_mod_cast (by omega : 0 < k)))
      exact ⟨ζ, e⟩
  have hsm : Fam.IsSmul D.toPre F ζ s₀ (ζ • s₀) := (isSmul_iff _ _ _).2 rfl
  have hz : ∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, ((ζ • s₀).s β).f j = 0 := fun β hβ j => by
    rw [hsm β j, h₀ β (fun mu e => hβ mu e.symm) j]; exact mul_zero _
  refine ⟨ζ • s₀, fun χ => ?_, hz, ?_⟩
  · by_cases h : ∃ z : D.toPre.X, χ = a₀ + k • z
    · obtain ⟨z, rfl⟩ := h
      have H := SectionScalarValuation.fe_move hϖ hQ hv k z a₀ (ζ • s₀) (hσ.smul hζ.ge (hsm a₀))
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have e : 0 + (Q a₀ : ℚ) / k + ((k * Q z + QForm.bOf D.toPre Q z a₀ : ℤ) : ℚ) =
          0 + (Q (a₀ + k • z) : ℚ) / k := by
        rw [q_shift hϖ hQ a₀ z k]; push_cast; field_simp; ring
      rwa [e] at H
    · exact vge_of_zero (hz χ fun z e => h ⟨z, e⟩) _
  · have e : ζ • s₀ = (ζ - 1) • s₀ + s₀ := by rw [sub_smul, one_smul, sub_add_cancel]
    rw [e, ((coef_basic V D.toPre F k g).2.2 w hw).2.1, coef_eq hc, show (ζ - 1) * c + c = ζ * c by ring,
      AddValuation.map_mul, hζ, vc, hx, ← WithTop.coe_add, ← WithTop.coe_add, zero_add, add_assoc]

end GlobalTheory.UT.CoefUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLeOnFinset
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.AdicValSum

theorem nullV_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) : NullV v x := by
  classical
  intro q
  obtain ⟨S, hS⟩ := h q
  refine S.finite_toSet.subset fun i hi => ?_
  by_contra hiS
  have h1 := hS S subset_rfl
  have h2 := hS (insert i S) (Finset.subset_insert i S)
  have hx : x i = (s - ∑ j ∈ S, x j) - (s - ∑ j ∈ insert i S, x j) := by
    rw [Finset.sum_insert hiS]
    ring
  have h3 : (q : WithTop ℚ) ≤ v (x i) := by
    rw [hx]
    exact le_trans (le_min h1 h2) (AddValuation.map_sub v _ _)
  exact absurd hi (not_lt.mpr h3)

theorem exists_le_on_finset {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (t : Finset F) :
    ∃ c : ℚ, ∀ y ∈ t, (c : WithTop ℚ) ≤ v y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ : ∃ d : ℚ, (d : WithTop ℚ) ≤ v a := by
      by_cases htop : v a = ⊤
      · exact ⟨0, htop ▸ le_top⟩
      · exact ⟨(v a).untop htop, by rw [WithTop.coe_untop]⟩
    refine ⟨min c d, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_right c d)) hd
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_left c d)) (hc y hy)

theorem sumV_of_sumI {V : Type} [CommRing V] (I : Ideal V) {F : Type} [Field F] [Module V F] (φ : V → F)
    (hφ : ∀ (a : V) (y : F), a • y = φ a * y) (v : AddValuation F (WithTop ℚ))
    (hv : ∀ (n : ℕ) (a : V), a ∈ I ^ n → ((n : ℚ) : WithTop ℚ) ≤ v (φ a))
    {Ix : Type} {x : Ix → F} {s : F} (h : SumI I x s) : SumV v x s := by
  obtain ⟨N, hNfg, -, -, hconv⟩ := h
  obtain ⟨G, rfl⟩ := hNfg
  obtain ⟨c, hc⟩ := exists_le_on_finset v G
  have h0 : ∀ a : V, (0 : WithTop ℚ) ≤ v (φ a) := by
    intro a
    have := hv 0 a (by simp)
    simpa using this
  have hN : ∀ y ∈ Submodule.span V (G : Set F), (c : WithTop ℚ) ≤ v y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simp
    | add y z _ _ hy hz => exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
    | smul a y _ hy =>
      rw [hφ, AddValuation.map_mul]
      simpa using add_le_add (h0 a) hy
  have hIN : ∀ n : ℕ, ∀ z ∈ I ^ n • Submodule.span V (G : Set F), (((n : ℚ) + c : ℚ) : WithTop ℚ) ≤ v z := by
    intro n z hz
    refine Submodule.smul_induction_on hz (fun r hr y hy => ?_) (fun y z hy hz => ?_)
    · rw [hφ, AddValuation.map_mul, WithTop.coe_add]
      exact add_le_add (hv n r hr) (hN y hy)
    · exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
  intro q
  obtain ⟨S, hS⟩ := hconv ⌈q - c⌉₊
  refine ⟨S, fun T hT => le_trans ?_ (hIN _ _ (hS T hT))⟩
  have : q ≤ (⌈q - c⌉₊ : ℚ) + c := by linarith [Nat.le_ceil (q - c)]
  exact WithTop.coe_le_coe.mpr this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (Ix : Type) (x : Ix → F) (s : F), SumF (maximalIdeal V) F x s → SumV v x s ∧ NullV v x := by
  intro V _ _ _ ϖ hϖ F _ _ v hval Ix x s hsum
  letI : Module V F := Module.compHom F (algebraMap V (FractionRing V))
  have hI : SumI (maximalIdeal V) x s := hsum
  have hV : SumV v x s := by
    refine sumV_of_sumI (maximalIdeal V) (fun a => algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a))
      (fun a y => Algebra.smul_def _ _) v ?_ hI
    intro n a ha
    by_cases ha0 : a = 0
    · subst ha0
      simp
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hdvd : ϖ ^ n ∣ ϖ ^ k := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
      exact (Units.dvd_mul_left).mp ha
    have hnk : n ≤ k := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hdvd
    have hhv : HasVal ϖ (algebraMap V (FractionRing V) (↑u * ϖ ^ k)) (k : ℤ) :=
      ⟨u, by rw [map_mul, map_pow, zpow_natCast, mul_comm]⟩
    rw [hval _ _ hhv, WithTop.coe_le_coe]
    exact_mod_cast hnk
  exact ⟨hV, nullV_of_sumV hV⟩

end GlobalTheory.UT.AdicValSum
end

