module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleTrivialOnAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

open GlobalTheory.CechPic

namespace GlobalTheory.DescGalRig

variable {S : Scheme.{0}}

theorem one_left (A : Over S) [GrpObj A] : (1 : A ⟶ A).left = A.hom ≫ eSec A := by
  have hu : (toUnit A).left = A.hom := (Category.comp_id _).symm.trans (Over.w (toUnit A))
  show (toUnit A ≫ η[A]).left = _
  rw [Over.comp_left, hu]
  rfl

theorem eSec_lift_one' (A : Over S) [GrpObj A] : eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left = eSec (A ⊗ A) := by
  apply pullback.hom_ext
  · change eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (fst A A).left = eSec (A ⊗ A) ≫ (fst A A).left
    show (η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) ≫ fst A A).left = (η[A ⊗ A] ≫ fst A A).left
    simp [Hom.one_def]
  · change eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (snd A A).left = eSec (A ⊗ A) ≫ (snd A A).left
    show (η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) ≫ snd A A).left = (η[A ⊗ A] ≫ snd A A).left
    simp [Hom.one_def]

variable {X Y : Scheme.{0}}

theorem one_left_comm {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    (gp : IsGrpPullback A A₀ π φ) : (1 : A ⟶ A).left ≫ φ = φ ≫ (1 : A₀ ⟶ A₀).left := by
  rw [one_left, one_left, Category.assoc, GlobalTheory.PolBaseChange.eSec_comm gp, ← Category.assoc, ← gp.1.w,
    Category.assoc]

theorem lift_one_comm {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left} (gp : IsGrpPullback A A₀ π φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A ⟶ A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (1 : A ⟶ A) (𝟙 A))
  have a₂ := congrArg (fun q => q.left) (lift_snd (1 : A ⟶ A) (𝟙 A))
  have b₁ := congrArg (fun q => q.left) (lift_fst (1 : A₀ ⟶ A₀) (𝟙 A₀))
  have b₂ := congrArg (fun q => q.left) (lift_snd (1 : A₀ ⟶ A₀) (𝟙 A₀))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply GlobalTheory.SquareDescent.square_hom_ext A₀
  · rw [Category.assoc, sq.1, ← Category.assoc, a₁, Category.assoc, b₁, one_left_comm gp]
  · rw [Category.assoc, sq.2, ← Category.assoc, a₂, Category.assoc, b₂, Category.id_comp, Category.comp_id]

theorem lift_one_comm' {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left} (gp : IsGrpPullback A A₀ π φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A) (1 : A ⟶ A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A) (1 : A ⟶ A))
  have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A) (1 : A ⟶ A))
  have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A₀) (1 : A₀ ⟶ A₀))
  have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A₀) (1 : A₀ ⟶ A₀))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply GlobalTheory.SquareDescent.square_hom_ext A₀
  · rw [Category.assoc, sq.1, ← Category.assoc, a₁, Category.assoc, b₁, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, sq.2, ← Category.assoc, a₂, Category.assoc, b₂, one_left_comm gp]

theorem exists_gen_of_side {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {A : Over X} [GrpObj A]
    {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left} {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left}
    {P : LB (A ⊗ A).left} {P₀ : LB (A₀ ⊗ A₀).left} (hG : GlobalTheory.ZM.IsGaloisCover Ga ρ π) (hA₀ : IsAbelianScheme A₀)
    (gp : IsGrpPullback A A₀ π φ) (hP : P.IsLB) (hP₀ : P₀.IsLB) (i : LBIso P (P₀.pull φ₂))
    (h0 : ∃ t : (P₀.pull (eSec (A₀ ⊗ A₀))).Gen, t.IsGen)
    (k : A.left ⟶ (A ⊗ A).left) (k₀ : A₀.left ⟶ (A₀ ⊗ A₀).left) (hk : k ≫ φ₂ = φ ≫ k₀)
    (he : eSec A₀ ≫ k₀ = eSec (A₀ ⊗ A₀)) (hgen : ∃ t : (P.pull k).Gen, t.IsGen) :
    ∃ t : (P₀.pull k₀).Gen, t.IsGen := by
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hN := LB.isLB_pull hP₀ k₀
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π A₀ _ hA₀ hN
    inferInstance inferInstance inferInstance ?_ ?_
  · obtain ⟨t, ht⟩ := h0
    exact gen_chartPull (chartPullOut P₀ (fun _ : PUnit => k₀) (fun _ => 1) (eSec A₀)
      (fun _ => eSec (A₀ ⊗ A₀)) (fun _ => he.symm)) t ht
  · have hiso : LBIso (P.pull k) ((P₀.pull φ₂).pull k) :=
      i.chartPull (chartPullPull P k) (chartPullPull (P₀.pull φ₂) k)
    have htrans : ∀ {U : Scheme.{0}} {L M : LB U}, L.IsLB → M.IsLB → LBIso L M →
        (∃ t : L.Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
      intro U L M hL hM h H
      obtain ⟨w, hw⟩ := h.chartPull (chartPullId L) (chartPullPull M (𝟙 U))
      obtain ⟨t, ht⟩ := H
      obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull L (𝟙 U)) t ht
      obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hM hL a ha
      exact gen_chartPull (chartPullUnpull M _ (Category.id_comp _)) c hc
    obtain ⟨t, ht⟩ := htrans (LB.isLB_pull hP k) (LB.isLB_pull (LB.isLB_pull hP₀ φ₂) k) hiso hgen
    obtain ⟨u, hu⟩ := gen_chartPull (chartPullIn P₀ (fun _ : PUnit => φ₂) (fun _ => 1) k) t ht
    have hc : pullback.fst A₀.hom π ≫ k₀ = (gp.1.isoPullback.inv ≫ k) ≫ φ₂ := by
      rw [Category.assoc, hk, ← Category.assoc, gp.1.isoPullback_inv_fst]
    apply gen_chartPull (chartPullOut P₀ (fun _ : PUnit => k₀) (fun _ => 1) (pullback.fst A₀.hom π)
      (fun _ => gp.1.isoPullback.inv ≫ (k ≫ φ₂)) (fun _ => by rw [← Category.assoc, ← hc]))
      (LB.pullGen P₀ (fun _ : PUnit => k ≫ φ₂) (fun _ => 1) u gp.1.isoPullback.inv)
    exact DVR.pullGen_isGen _ _ _ u hu _

end GlobalTheory.DescGalRig

theorem GlobalTheory.DescGalRig.exists_gen_lift_of_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hG _ hA₀ gp sq hP hP₀ i h0 h₁ h₂
  exact ⟨GlobalTheory.DescGalRig.exists_gen_of_side hG hA₀ gp hP hP₀ i h0 _ _ (GlobalTheory.DescGalRig.lift_one_comm gp sq)
      (GlobalTheory.SquareDescent.eSec_lift_one A₀) h₁,
    GlobalTheory.DescGalRig.exists_gen_of_side hG hA₀ gp hP hP₀ i h0 _ _ (GlobalTheory.DescGalRig.lift_one_comm' gp sq)
      (GlobalTheory.DescGalRig.eSec_lift_one' A₀) h₂⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberMorphismEqOfLocal
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

namespace GlobalTheory.ArLieBase


set_option backward.isDefEq.respectTransparency false in
theorem hom_ext_dualNumber_away : ∀ {L : Type} [CommRing L] {s : Set L}, Ideal.span s = ⊤ → ∀ {Y : Scheme.{0}} {w w' : Sp (DualNumber L) ⟶ Y}, (∀ a : s, spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w = spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w') → w = w' := by
  intro L _ s hs Y w w' h
  have hs' : Ideal.span (Set.range (fun k : s => (TrivSqZeroExt.inl (k : L) : DualNumber L))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom L L)) hs
    rw [Ideal.map_span, Ideal.map_top, Set.image_eq_range] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber L)) _ hs').openCover
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : s) => ?_
  have hd : Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (k : L))) =
      ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  have e : 𝒰.f k = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.toL (k : L))) ≫
      Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ReciprocityTheory.ChartRestriction.G.Chart.toL_comp]
    rfl
  have hk := h k
  rw [hd] at hk
  rw [e, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) hk

end GlobalTheory.ArLieBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DvrDiv

theorem dvd_of_forall_cDvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (a b : R), b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  intro R _ _ _ _ _ a b hb h
  classical
  by_cases ha : a = 0
  · exact ha ▸ dvd_zero b
  let K := FractionRing R
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normal_domain_height_one.{0, 0, 0} R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
  suffices hmem : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      algebraMap R K a / algebraMap R K b ∈ primeLocalSubalgebra K p by
    obtain ⟨r, hr⟩ := (h2 (algebraMap R K a / algebraMap R K b)).2 hmem
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hbK]
  intro p _ hp
  obtain ⟨-, hD, -⟩ := h1 p hp
  let D := primeLocalSubalgebra K p
  haveI : IsDiscreteValuationRing D := hD
  let W := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let iW : D →+* W := algebraMap D W
  let φ : R →+* W := iW.comp (algebraMap R D)
  have hRD : Function.Injective (algebraMap R D) := fun x y hxy =>
    IsFractionRing.injective R K (congrArg Subtype.val hxy)
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr D).comp hRD
  haveI : CharZero W := (RingHom.charZero_iff hφ).1 inferInstance
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨t, ht⟩ := h W hW φ hφ
  have hdvd : algebraMap R D b ∣ algebraMap R D a := by
    rcases ValuationRing.dvd_total (algebraMap R D b) (algebraMap R D a) with hd | ⟨c, hc⟩
    · exact hd
    have ha' : φ a ≠ 0 := (map_ne_zero_iff _ hφ).mpr ha
    have e : φ a * (iW c * t) = φ a * 1 := by
      rw [_root_.mul_one]
      calc φ a * (iW c * t) = iW (algebraMap R D a * c) * t := by
            rw [map_mul, _root_.mul_assoc]; rfl
        _ = φ a := by rw [← hc]; exact ht.symm
    have hu : IsUnit (iW c) := isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit iW c hu
    exact ⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
  obtain ⟨c, hc⟩ := hdvd
  have hcK : algebraMap R K a = algebraMap R K b * (c : K) := congrArg Subtype.val hc
  rw [hcK, mul_div_cancel_left₀ _ hbK]
  exact c.2

end GlobalTheory.DvrDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionLiftPadicAlgClosureNormLeOneIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (i : V →+* OO p), IsLocalHom i → ∀ (hi : Function.Injective ((OO p).subtype.comp i)) (x : FractionRing V), ‖IsFractionRing.lift (K := FractionRing V) hi x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro p _ V _ _ _ i hloc hi x
  have hV : ValuationRing V := inferInstance
  constructor
  · intro hx
    by_contra hnot
    have hx0 : x ≠ 0 := fun h => hnot ⟨0, by simp [h]⟩
    rcases ValuationRing.isInteger_or_isInteger V x with ⟨a, ha⟩ | ⟨w, hw⟩
    · exact hnot ⟨a, ha⟩
    · have hwu : ¬ IsUnit w := by
        intro hu
        apply hnot
        refine ⟨(hu.unit⁻¹ : Vˣ), ?_⟩
        have h1 : algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ) * algebraMap V (FractionRing V) w = 1 := by
          rw [← map_mul]; simp
        rw [hw] at h1
        exact (eq_inv_of_mul_eq_one_left h1).trans (inv_inv x)
      have hiw : ¬ IsUnit (i w) := fun h => hwu (IsLocalHom.map_nonunit w h)
      have hlt : ‖((i w : OO p) : PadicAlgCl p)‖ < 1 := (GlobalTheory.ZH.not_isUnit_OO_iff _).1 hiw
      have hlw : IsFractionRing.lift (K := FractionRing V) hi x⁻¹ = ((i w : OO p) : PadicAlgCl p) := by
        rw [← hw, IsFractionRing.lift_algebraMap]; rfl
      have hprod : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖IsFractionRing.lift (K := FractionRing V) hi x⁻¹‖ = 1 := by
        rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
      rw [hlw] at hprod
      have : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖((i w : OO p) : PadicAlgCl p)‖ < 1 :=
        calc _ ≤ 1 * ‖((i w : OO p) : PadicAlgCl p)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [_root_.one_mul]; exact hlt
      linarith
  · rintro ⟨v, rfl⟩
    rw [IsFractionRing.lift_algebraMap]
    exact (GlobalTheory.ZH.mem_OO_iff _).1 (i v).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

open GlobalTheory.Mum.Pow8

section Pairing

theorem comp_matAct_pr {S : Scheme.{0}} {G₀ : Over S} [GrpObj G₀] [IsCommMonObj G₀] {X : Over S}
    (x : X ⟶ powObj G₀ 8) (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) :
    (x ≫ matAct G₀ a) ≫ powPr G₀ i = ∏ j, (x ≫ powPr G₀ j) ^ a i j := by
  rw [Category.assoc, matAct_pr]
  exact GlobalTheory.Mum.TensAct.comp_prod_zpow x _ _

variable {S : Scheme.{0}} {G₀ : Over S} [GrpObj G₀] [IsCommMonObj G₀] {L : LB G₀.left} (hL : L.IsLB)

def formPair (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) : GlobalTheory.CechPic.Pic X.left :=
  ∑ i, ∑ j, M i j • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ≫ powPr G₀ i) (y ≫ powPr G₀ j)

theorem cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) :
    GlobalTheory.CechPic.cls _ h = formPair hL W (𝟙 _) (𝟙 _) := by
  refine (GlobalTheory.CechPic.cls_linComb hL _ _ h).trans ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  unfold formPair
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, lamPts, negε, GlobalTheory.CechPic.lam, Category.id_comp]
  simp [smul_add, sub_eq_add_neg]

theorem pull_cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) {X : Over S} (u : X ⟶ powObj G₀ 8) :
    GlobalTheory.CechPic.pull u.left (GlobalTheory.CechPic.cls _ h) = formPair hL W u u := by
  rw [cls_e8LB hL W h]
  unfold formPair
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, GlobalTheory.CechPic.pull_lam, Category.id_comp]

variable (hΘ : ∃ t : LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.Theta G₀ L), t.IsGen)
include hΘ

theorem formPair_mul (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (u v : X ⟶ powObj G₀ 8) :
    formPair hL M (u * v) (u * v) = formPair hL M u u + formPair hL M v v + formPair hL (M + M.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ powPr G₀ i = (u ≫ powPr G₀ i) * (v ≫ powPr G₀ i) := fun i => MonObj.mul_comp _ _ _
  have e1 : ∀ i j, GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) ((u * v) ≫ powPr G₀ i) ((u * v) ≫ powPr G₀ j) =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ i) (u ≫ powPr G₀ j) +
        GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (v ≫ powPr G₀ i) (v ≫ powPr G₀ j) +
        (GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ i) (v ≫ powPr G₀ j) +
          GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ j) (v ≫ powPr G₀ i)) := by
    intro i j
    rw [hm, hm, GlobalTheory.CechPic.lam_mul_left hL hΘ, GlobalTheory.Mum.RosatiTens.lam_mul_right hL hΘ,
      GlobalTheory.Mum.RosatiTens.lam_mul_right hL hΘ, GlobalTheory.CechPic.lam_comm _ (v ≫ powPr G₀ i) (u ≫ powPr G₀ j)]
    abel
  unfold formPair
  simp only [e1, smul_add, Finset.sum_add_distrib, Matrix.add_apply, add_smul, Matrix.transpose_apply]
  congr 2
  exact Finset.sum_comm

theorem formPair_one (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} :
    formPair hL M (1 : X ⟶ powObj G₀ 8) 1 = 0 := by
  unfold formPair
  simp [MonObj.one_comp, GlobalTheory.CechPic.lam_one_left]

theorem lam_cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) {X : Over S}
    (x y : X ⟶ powObj G₀ 8) :
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ h) x y = formPair hL (W + W.transpose) x y := by
  unfold GlobalTheory.CechPic.lam
  simp only [pull_cls_e8LB hL W h]
  rw [formPair_mul hL hΘ, formPair_one hL hΘ]
  abel

theorem formPair_act_left (M a : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) :
    formPair hL M (x ≫ matAct G₀ a) y = formPair hL (a.transpose * M) x y := by
  have s3 : ∀ F : Fin 8 → Fin 8 → Fin 8 → GlobalTheory.CechPic.Pic X.left,
      ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := fun F =>
    calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  unfold formPair
  simp only [comp_matAct_pr, GlobalTheory.Mum.RosatiTens.lam_prod_left hL hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  refine (s3 (fun i j k => (M i j * a i k) •
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ≫ powPr G₀ k) (y ≫ powPr G₀ j))).trans ?_
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [mul_comm]

theorem formPair_act_right (M a : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) :
    formPair hL M x (y ≫ matAct G₀ a) = formPair hL (M * a) x y := by
  unfold formPair
  simp only [comp_matAct_pr, GlobalTheory.Mum.RosatiTens.lam_prod_right hL hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end Pairing

theorem unimodular_symmetrised_matrix_adjugate_identities {W : Matrix (Fin 8) (Fin 8) ℤ} (hB : (W + W.transpose).det = 1) :
    (W + W.transpose) * ((W + W.transpose).adjugate * W) = W ∧
      (W + W.transpose).adjugate * W + (W + W.transpose).adjugate * W.transpose = 1 ∧
      ((W + W.transpose).adjugate * W).transpose * (W + W.transpose) =
        (W + W.transpose) * ((W + W.transpose).adjugate * W.transpose) := by
  have hBt : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by
    rw [Matrix.mul_adjugate, hB, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by
    rw [Matrix.adjugate_mul, hB, one_smul]
  have hAt : (W + W.transpose).adjugate.transpose = (W + W.transpose).adjugate := by
    rw [Matrix.adjugate_transpose, hBt]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · rw [← Matrix.mul_add, h2]
  · rw [Matrix.transpose_mul, hAt, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem hypW_e8LB : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀)
    (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → GlobalTheory.LN.HypW (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ P.L.L W) := by
  intro S G₀ _ _ P W hW
  have hL : P.L.L.IsLB := P.L.isLB
  have hΘ : ∃ t : LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.Theta G₀ P.L.L), t.IsGen := ⟨P.c.1, P.c.2⟩
  have hE : (e8LB G₀ P.L.L W).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨h1, h2, h3⟩ := unimodular_symmetrised_matrix_adjugate_identities hW.2
  refine ⟨matAct G₀ ((W + W.transpose).adjugate * W), matAct G₀ ((W + W.transpose).adjugate * W.transpose),
    matAct_hom G₀ _, matAct_hom G₀ _, ?_, ?_, ?_⟩
  · rw [← matAct_one G₀, ← h2]
    refine eighthPowerGroupObj_hom_ext G₀ fun i => ?_
    rw [MonObj.mul_comp, matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
    simp only [Matrix.add_apply, zpow_add]
  · have hC : (cubeLB (powObj G₀ 8) ![𝟙 (powObj G₀ 8), matAct G₀ ((W + W.transpose).adjugate * W)]
        (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hE hC).1 ?_
    rw [GlobalTheory.CechPic.cls_cube_two hE _ _ hC, lam_cls_e8LB hL hΘ W hE, cls_e8LB hL W hE]
    have e := formPair_act_right hL hΘ (W + W.transpose) ((W + W.transpose).adjugate * W)
      (𝟙 (powObj G₀ 8)) (𝟙 (powObj G₀ 8))
    rw [Category.id_comp, h1] at e
    exact e.symm
  · have hC1 : (cubeLB (powObj G₀ 8) ![fst (powObj G₀ 8) (powObj G₀ 8) ≫ matAct G₀ ((W + W.transpose).adjugate * W),
        snd (powObj G₀ 8) (powObj G₀ 8)] (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    have hC2 : (cubeLB (powObj G₀ 8) ![fst (powObj G₀ 8) (powObj G₀ 8),
        snd (powObj G₀ 8) (powObj G₀ 8) ≫ matAct G₀ ((W + W.transpose).adjugate * W.transpose)]
        (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hC1 hC2).1 ?_
    rw [GlobalTheory.CechPic.cls_cube_two hE _ _ hC1, GlobalTheory.CechPic.cls_cube_two hE _ _ hC2, lam_cls_e8LB hL hΘ W hE,
      lam_cls_e8LB hL hΘ W hE, formPair_act_left hL hΘ, formPair_act_right hL hΘ, h3]

end GlobalTheory.PowE8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ProductTorsionSectionBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e8_prod_torsion_section_bound : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (gQ : ℕ) {S : Scheme.{0}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (hP : E8Fibration.IsProd pr) (N : ℕ) {T : Over S}
  (b : Fin gQ ⊕ Fin gQ → (T ⟶ B)), (∀ c, b c ^ N = 1) → ∀ (_hN : 0 < N := by assumption),
  (∀ i, E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ^ N = 1) ∧
  ∀ (act : Fin 2 → (A ⟶ A)), (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) → ∀ (a : Fin 2) (i : Fin (2 * (8 * gQ))),
    E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a =
      Out.linComb (fun i' => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)))
        (fun i' => ((E8Fibration.Lab.labMat W hW.2 gQ a i' i : ZMod N)).val) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act | exact GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMovesTorsionLatticeByAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_moves_torsionLattice_by_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D.toPre K m) (x : TFK (R := R) K ⟶ A.A), 1 ≤ m → QkToAkU U.toUnifPre K m pk x → QkToAkU U.toUnifPre K m pk' (x ≫ E.aA) → CongMod m pk'.y (E'.h pk.y) := by
  first | exact @GlobalTheory.EndLattice.congMod_y_of_end | exact GlobalTheory.EndLattice.congMod_y_of_end | (intros; apply GlobalTheory.EndLattice.congMod_y_of_end <;> assumption)
end

