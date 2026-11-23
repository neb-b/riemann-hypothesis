module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocTrivDescent
open GlobalTheory.CechPic

theorem triv_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) :
    (∃ t : (L.pull f).Gen, t.IsGen) ↔ CechPic.pull f (cls L hL) = 0 := by
  rw [← cls_pull hL f (pull_isLB hL f), cls_eq_zero_iff]

theorem cls_lbPow_eq {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (k : ℕ) (h : (Hecke.lbPow L k).IsLB) :
    cls _ h = k • cls L hL :=
  (cls_linComb hL _ _ h).trans (by simp [pull_id])

theorem one_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (1 : 𝟙_ (Over S') ⟶ G').left ≫ φ = f ≫ (1 : 𝟙_ (Over S) ⟶ G).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) := Over.homMk f (by simp)
  have e2 : (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) = U ≫ 1 := (comp_one U).symm
  exact e.trans (by rw [e2]; rfl)

theorem fibre_triv {R R₁ : Type} [CommRing R] [CommRing R₁] (j : R₁ →+* R) {A : Over (Sp R)} {A₁ : Over (Sp R₁)}
    {ψ : A.left ⟶ A₁.left} (hψ : IsPullback ψ A.hom A₁.hom (spMap j)) {K : Type} [Field K] (g₀ : R →+* K)
    (c : Pic A₁.left) (h : CechPic.pull (pullback.fst A.hom (spMap g₀)) (CechPic.pull ψ c) = 0) :
    CechPic.pull (pullback.fst A₁.hom (spMap (g₀.comp j))) c = 0 := by
  have w : pullback.fst A₁.hom (spMap (g₀.comp j)) ≫ A₁.hom =
      (pullback.snd A₁.hom (spMap (g₀.comp j)) ≫ spMap g₀) ≫ spMap j := by
    rw [pullback.condition, Category.assoc, GlobalTheory.spMap_comp_ring]
  let a := hψ.lift _ _ w
  have ha1 : a ≫ ψ = pullback.fst _ _ := hψ.lift_fst _ _ _
  have ha2 : a ≫ A.hom = pullback.snd _ _ ≫ spMap g₀ := hψ.lift_snd _ _ _
  let n := pullback.lift a (pullback.snd _ _) ha2
  have hn : n ≫ pullback.fst A.hom (spMap g₀) = a := pullback.lift_fst _ _ _
  rw [← ha1, ← hn, Category.assoc, pull_comp, pull_comp, h, map_zero]

theorem basicOpen_triv {R R₁ : Type} [CommRing R] [CommRing R₁] (j : R₁ →+* R) {A : Over (Sp R)}
    {A₁ : Over (Sp R₁)} {ψ : A.left ⟶ A₁.left} (w : ψ ≫ A₁.hom = A.hom ≫ spMap j) (c : Pic A₁.left) (r : R₁)
    (h : CechPic.pull (A₁.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι c = 0) :
    CechPic.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (j r)).ι (CechPic.pull ψ c) = 0 := by
  have le : A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (j r) ≤ ψ ⁻¹ᵁ (A₁.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r) := by
    intro x hx
    have e : A₁.hom.base (ψ.base x) = (spMap j).base (A.hom.base x) := by
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    show A₁.hom.base (ψ.base x) ∈ PrimeSpectrum.basicOpen r
    rw [e]
    exact hx
  rw [← pull_comp, ← Scheme.Hom.resLE_comp_ι ψ le, pull_comp, h, map_zero]

end GlobalTheory.LocTrivDescent

namespace GlobalTheory.LocTrivDescent
open GlobalTheory.CechPic

theorem cls_spread (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀)
    (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (M : LB X₀) (hM : M.IsLB)
    (hp : IsPullback π f f₀ (spMap R₀.subtype)) (h0 : CechPic.pull π (cls M hM) = 0) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁)
      (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → CechPic.pull π₁ (cls M hM) = 0 := by
  have hT := LB.isLB_triv X₀
  have z : cls (LB.triv X₀) hT = 0 := rfl
  have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ X₀),
      CechPic.pull g (cls M hM) = 0 ↔ LBIso (M.pull g) ((LB.triv X₀).pull g) := by
    intro Y g
    rw [← cls_eq_iff (pull_isLB hM g) (pull_isLB hT g), cls_pull hM, cls_pull hT, z, map_zero]
  obtain ⟨F, hF⟩ := GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ X X₀ f f₀ π M (LB.triv X₀) hp hM hT
    ((key π).1 h0)
  exact ⟨F, fun R₁ h hs X₁ f₁ π₁ hp₁ => (key π₁).2 (hF R₁ h hs X₁ f₁ π₁ hp₁)⟩

theorem locTriv_of_noetherian : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  intro H R _ A _ hA M hM h1 k hk h2 K _ g₀ h3
  classical
  obtain ⟨S, G₀, _, φ, L₀, hft, hab, hφ, hL₀, hiso⟩ := GlobalTheory.AmpleFibreMove.exists_fg_model R A hA M hM
  have := hab.proper
  set c₀ := cls L₀ hL₀ with hc₀
  have hc : cls M hM = CechPic.pull φ c₀ := by
    rw [hc₀, ← cls_pull hL₀ φ (pull_isLB hL₀ φ)]
    exact (cls_eq_iff _ _).2 hiso

  let e₀ : Sp S ⟶ G₀.left := (1 : 𝟙_ (Over (Sp S)) ⟶ G₀).left
  have ha : CechPic.pull (spMap S.subtype) (CechPic.pull e₀ c₀) = 0 := by
    rw [← pull_comp, ← one_left_comp hφ, pull_comp, ← hc]
    exact (triv_iff hM _).1 h1
  obtain ⟨F₁, hF₁⟩ := cls_spread R S (Sp R) (Sp S) (𝟙 _) (𝟙 _) (spMap S.subtype) (L₀.pull e₀)
    (pull_isLB hL₀ e₀) (IsPullback.id_vert _) ha

  have hP₀ : (Hecke.lbPow L₀ k).IsLB := LB.isLB_linComb hL₀ _ _
  have hb : CechPic.pull φ (cls _ hP₀) = 0 := by
    obtain ⟨t, ht⟩ := h2
    have hPM : (Hecke.lbPow M k).IsLB := LB.isLB_linComb hM _ _
    have e := (cls_eq_zero_iff hPM).2 ⟨t, ht⟩
    rw [cls_lbPow_eq hM, hc] at e
    rw [cls_lbPow_eq hL₀, map_nsmul]
    exact e
  obtain ⟨F₂, hF₂⟩ := cls_spread R S A.left G₀.left A.hom G₀.hom φ _ hP₀ hφ.1 hb

  obtain ⟨u, hu⟩ : ∃ u : R, (k : R) * u = 1 := ⟨_, hk.mul_val_inv⟩
  obtain ⟨R₁, h, hT, hft₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S (F₁ ∪ F₂ ∪ {u}) hft
  have hT₁ : (F₁ : Set R) ⊆ R₁ := fun x hx => hT (by simp [hx])
  have hT₂ : (F₂ : Set R) ⊆ R₁ := fun x hx => hT (by simp [hx])
  have hu₁ : u ∈ R₁ := hT (by simp)
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  let t : Sp R₁ ⟶ Sp S := spMap (Subring.inclusion h)
  have et : spMap R₁.subtype ≫ t = spMap S.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have := hab.comm
  have := hab.smooth
  have := hab.geomConnected
  letI : GrpObj ((Over.pullback t).obj G₀) := Functor.grpObjObj
  let A₁ : Over (Sp R₁) := (Over.pullback t).obj G₀
  have hab₁ : IsAbelianScheme A₁ :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd G₀.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd G₀.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd G₀.hom t)) }
  have hpb₁ : IsPullback (pullback.fst G₀.hom t) A₁.hom G₀.hom t := IsPullback.of_hasPullback _ _
  have wφ : φ ≫ G₀.hom = (A.hom ≫ spMap R₁.subtype) ≫ t := by
    rw [Category.assoc, et]; exact hφ.1.w
  let ψ : A.left ⟶ A₁.left := pullback.lift φ (A.hom ≫ spMap R₁.subtype) wφ
  have hψ₁ : ψ ≫ pullback.fst G₀.hom t = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hψ : IsGrpPullback A A₁ (spMap R₁.subtype) ψ :=
    (isGrpPullback_pullback G₀ t).cancel (hφ.congr et.symm hψ₁.symm) hψ₂
  let M₁ : LB A₁.left := L₀.pull (pullback.fst G₀.hom t)
  have hM₁ : M₁.IsLB := pull_isLB hL₀ _
  have hc₁ : cls M₁ hM₁ = CechPic.pull (pullback.fst G₀.hom t) c₀ := cls_pull hL₀ _ _
  have hcM : cls M hM = CechPic.pull ψ (cls M₁ hM₁) := by
    rw [hc₁, ← pull_comp, hψ₁, hc]
  obtain ⟨r, hr, hgen⟩ := H R₁ A₁ hab₁ M₁ hM₁
    ((triv_iff hM₁ _).2 (by
      rw [hc₁, ← pull_comp, one_left_comp (isGrpPullback_pullback G₀ t), pull_comp]
      exact hF₁ R₁ h hT₁ (Sp R₁) (𝟙 _) t (IsPullback.id_vert _)))
    k (isUnit_iff_exists_inv.2 ⟨⟨u, hu₁⟩, Subtype.ext (by simpa using hu)⟩)
    (by
      have hPM₁ : (Hecke.lbPow M₁ k).IsLB := LB.isLB_linComb hM₁ _ _
      refine (cls_eq_zero_iff hPM₁).1 ?_
      rw [cls_lbPow_eq hM₁, hc₁, ← map_nsmul, ← cls_lbPow_eq hL₀ k hP₀]
      exact hF₂ R₁ h hT₂ A₁.left A₁.hom _ hpb₁)
    K (g₀.comp R₁.subtype)
    ((triv_iff hM₁ _).2 (fibre_triv R₁.subtype hψ.1 g₀ _ (by rw [← hcM]; exact (triv_iff hM _).1 h3)))
  refine ⟨r, hr, (triv_iff hM _).2 ?_⟩
  rw [hcM]
  exact basicOpen_triv R₁.subtype hψ₂ _ r ((triv_iff hM₁ _).1 hgen)

end GlobalTheory.LocTrivDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchIntegralAdditiveAndDiagonal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixAdd

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem archInt_congr {A B : HermLB q} (h : A.Isometric B) (M : HermLB q) (e : ℕ) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) : A.archInt M e hr = B.archInt M e hr := by
  simp only [HermLB.archInt, h.chernInt_eq]

theorem lin_comb {ι κ : Type} [Fintype ι] [Fintype κ] (m : κ → ι → ℤ) (n : κ → ℤ) :
    (lin fun i => ((∑ j, n j * m j i : ℤ) : ℝ)) = ∑ j, (n j : ℝ) • lin fun i => (m j i : ℝ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, Int.cast_sum, Int.cast_mul, map_sum, map_mul, Finset.sum_mul, smul_eq_C_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lin_add {ι : Type} [Fintype ι] (m n : ι → ℤ) :
    (lin fun i => (((m + n) i : ℤ) : ℝ)) = (lin fun i => (m i : ℝ)) + lin fun i => (n i : ℝ) := by
  simp only [lin, Pi.add_apply, Int.cast_add, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem mixArch_eq {ι : Type} [Fintype ι] {e : ℕ} (F : ι → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hΨ : ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb F n).archInt M e hr)
    (L : Fin e → HermLB q) (m : Fin e → ι → ℤ) (h : ∀ a, (comb F (m a)).Isometric (L a)) :
    mixArch L M hr = Ψ (∏ a, lin fun i => (m a i : ℝ)) := by
  have h₁ : (fun n => (comb L n).archInt M e hr) =
      fun n : Fin e → ℤ => Ψ ((∑ a, (n a : ℝ) • lin fun i => (m a i : ℝ)) ^ e) := by
    funext n
    rw [← lin_comb, hΨ]
    exact (archInt_congr ((isometric_comb_comb F m n).trans (isometric_comb_congr h n)) M e hr).symm
  rw [mixArch, h₁, FibreProj.pol_pow _ Ψ (Fintype.card_fin e), mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.2 e.factorial_ne_zero

theorem mixArch_add_diag : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r),
    (∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ (A B : HermLB q) (L : Fin e → HermLB q),
      mixArch (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr =
        mixArch (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) M hr) ∧
    ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ N : HermLB q,
      mixArch (fun _ : Fin e => N) M hr = N.archInt M e hr := by
  intro hI k _ Y _ q hq M r hr
  classical
  refine ⟨fun e he A B L => ?_, fun e he N => ?_⟩
  · let F : Bool ⊕ Fin e → HermLB q := Sum.elim (fun b => cond b A B) L
    obtain ⟨Ψ, hΨ⟩ := _root_.GlobalTheory.MixFun.exists_functional_archInt k Y q hq (e + 1) _ F M r hr
      fun n => _root_.GlobalTheory.MixHt.archIntegrable_of_isAmb hI k Y q hq (e + 1) he M _ r hr
    let u : Bool ⊕ Fin e → Bool ⊕ Fin e → ℤ := fun j => Pi.single j 1
    have key (C : HermLB q) (c : Bool ⊕ Fin e → ℤ) (hc : (comb F c).Isometric C) :
        mixArch (Fin.cons C L : Fin (e + 1) → HermLB q) M hr =
          Ψ ((lin fun i => (c i : ℝ)) * ∏ a : Fin e, lin fun i => (u (Sum.inr a) i : ℝ)) := by
      rw [mixArch_eq F M hr Ψ hΨ (Fin.cons C L) (Fin.cons c fun a => u (Sum.inr a)) (fun a => by
        cases a using Fin.cases with
        | zero => exact hc
        | succ a => exact isometric_comb_single F (Sum.inr a)), Fin.prod_univ_succ]
      rfl
    have hA : (comb F (u (Sum.inl true))).Isometric A := isometric_comb_single F (Sum.inl true)
    have hB : (comb F (u (Sum.inl false))).Isometric B := isometric_comb_single F (Sum.inl false)
    rw [key A _ hA, key B _ hB, key _ _ ((isometric_comb_add F _ _).trans (hA.tens hB)), lin_add, add_mul, map_add (f := _)]
  · let F : Unit → HermLB q := fun _ => N
    obtain ⟨Ψ, hΨ⟩ := _root_.GlobalTheory.MixFun.exists_functional_archInt k Y q hq e _ F M r hr fun n => _root_.GlobalTheory.MixHt.archIntegrable_of_isAmb hI k Y q hq e he M _ r hr
    have hN : (comb F (Pi.single () 1)).Isometric N := isometric_comb_single F ()
    rw [mixArch_eq F M hr Ψ hΨ _ (fun _ => Pi.single () 1) fun _ => hN, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hΨ]
    exact archInt_congr hN M e hr

end GlobalTheory.MixAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralEqSumEmbeddings
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixPolar

theorem injective_emb {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k] (σ : k →+* ℂ) :
    Function.Injective σ := by
  refine (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  change Ideal.comap (algebraMap ℤ k) (RingHom.ker σ) = ⊥
  rw [RingHom.comap_ker, (RingHom.ext_int _ (Int.castRingHom ℂ) : σ.comp (algebraMap ℤ k) = _)]
  exact (RingHom.injective_iff_ker_eq_bot _).1 Int.cast_injective

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem chernInt_eq (h : IsArithVar p D) (N M : HermLB p) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s)
    (σ : k →+* ℂ) :
    (N.φ σ).chernInt D (offSupp p σ (M.div (isRatSec_ratOfSec s hs))) (logNorm (M.φ σ) (ratOfSec s hs)) =
      Mix.int (fun _ : Fin D => MLine.ofHerm N σ) ((MLine.ofHerm M σ).logSec s) := by
  have := h.isDomain
  have := h.finite
  have hnull (ε : ℤˣ) : (N.φ σ).chernPart D ε (ptsIn p σ (nonzeroLocus s))ᶜ = 0 := by
    have := _root_.GlobalTheory.MixNull.part_compl_null k X p σ (injective_emb σ) h.isProjOver D (fun _ => MLine.ofHerm N σ) ε (nonzeroLocus s) hs
    rwa [part_const] at this
  have key (ε : ℤˣ) : ∫ y in offSupp p σ (M.div (isRatSec_ratOfSec s hs)), logNorm (M.φ σ) (ratOfSec s hs) y
      ∂(N.φ σ).chernPart D ε = ∫ y, (MLine.ofHerm M σ).logSec s y ∂(N.φ σ).chernPart D ε := by
    have hae : ∀ᵐ y ∂(N.φ σ).chernPart D ε, y ∈ ptsIn p σ (nonzeroLocus s) := ae_iff.2 (hnull ε)
    have e : offSupp p σ (M.div (isRatSec_ratOfSec s hs)) = ptsIn p σ (nonzeroLocus s) := offSupp_divOfSec
    rw [e, Measure.restrict_eq_self_of_ae_mem hae]
    exact integral_congr_ae (hae.mono fun y hy => logNorm_ratOfSec _ hy)
  rw [Weight.chernInt, key, key, Mix.int, part_const, part_const]
  rfl

end GlobalTheory.MixPolar

namespace GlobalTheory.MixPolar

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {p : X ⟶ Sp k} {D : ℕ}

theorem pol_int (hP : GlobalTheory.Published.Principalisation) (h : IsArithVar p D) (L : Fin D → HermLB p) (M : HermLB p)
    (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (σ : k →+* ℂ) :
    FibreProj.pol (fun n => Mix.int (fun _ : Fin D => MLine.ofHerm (ArInt.comb L n) σ) ((MLine.ofHerm M σ).logSec s)) =
      D.factorial * Mix.int (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm M σ).logSec s) := by
  haveI := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  have e : ∀ F : (Fin D → ℤ) → ℝ,
      ∑ S : Finset (Fin D), (-1 : ℝ) ^ S.card * F (fun i => if i ∈ S then -1 else 0) = FibreProj.pol F := fun F => by
    unfold FibreProj.pol
    congr!
  let Lj : Option (Finset (Fin D)) → Fin D → MLine p σ := fun j =>
    j.elim (fun i => MLine.ofHerm (L i) σ) (fun S _ => MLine.ofHerm (ArInt.comb L (fun i => if i ∈ S then -1 else 0)) σ)
  let a : Option (Finset (Fin D)) → ℝ := fun j => j.elim (-(D.factorial : ℝ)) (fun S => (-1) ^ S.card)
  have hd : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ∑ j, a j * dens (Lj j) c y = 0 := by
    intro c y hy
    have := _root_.GlobalTheory.Mix.pol_chernDens_comb k X p σ D L c y hy
    rw [← e] at this
    simp only [Fintype.sum_option, a, Lj, Option.elim, dens_const]
    beta_reduce at this
    simp only [MLine.ofHerm] at this ⊢
    linarith
  have hi : ∀ j, Intg (Lj j) ((MLine.ofHerm M σ).logSec s) := fun j =>
    _root_.GlobalTheory.Mix.intg_logSec_of_arithVar hP k X p D h σ (Lj j) (MLine.ofHerm M σ) s hs
  have := _root_.GlobalTheory.Mix.sum_int_eq_zero_of_dens k X p σ D _ a Lj hd _ hi
  simp only [Fintype.sum_option, a, Lj, Option.elim] at this
  rw [← e]
  beta_reduce
  linarith

end GlobalTheory.MixPolar


open GlobalTheory.MixPolar in
theorem GlobalTheory.MixPolar.mixArch_eq_sum : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → HermLB p) (M : HermLB p) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), MixHt.mixArch L M (isRatSec_ratOfSec s hs) = ∑ᶠ σ : k →+* ℂ, Mix.int (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm M σ).logSec s) := by
  intro hP k _ X _ _ p D h L M s hs
  have := h.finite_emb
  haveI := Fintype.ofFinite (k →+* ℂ)
  simp only [MixHt.mixArch, HermLB.archInt, finsum_eq_sum_of_fintype, chernInt_eq h]
  rw [FibreProj.pol_sum]
  simp only [pol_int hP h L M s hs]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ (by positivity)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuLowerBoundLastIndex
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.DefCore

theorem unitE_nonneg {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) : 0 ≤ unitE p := by
  rw [hw.unit]
  have hx : 0 < L.sc.x := by linarith [hh.big.2.1, hh.big.2.2.1]
  have hb : 0 < L.sc.b := lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hx _) _) hh.room
  have := hh.big.2.2.2
  have : (0:ℝ) ≤ L.sc.L := by linarith [hh.big.2.1]
  positivity

end GlobalTheory.CovTop.DefCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierPowerMulPullbackSmallFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.ZmPow

theorem pow_mul_small : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N k : ℕ) (g : ∀ β, SecT D.toPre a N (-1) β) (ρ : ∀ β, SecT D.toPre a 0 k β), Small (maximalIdeal R) (w := id) g → Small (maximalIdeal R) (w := id) ρ → TFE h h' g → TFE h h' ρ → ∃ F : ∀ β, SecT D.toPre a ((N * k : ℕ) : ℤ) 0 β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k), TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ → ∃ τ'' : SecE U.toUnifPre (b e) ((N * k : ℕ) : ℤ) 0, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ k * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  intro R _ _ _ hAdm D a a' h h' hE A G _ _ hG U b hb N k g ρ hgS hρS hgT hρT
  have key : ∀ m : ℕ, ∀ n j : ℤ, n = (N : ℤ) * m → j = (k : ℤ) - m →
      ∃ F : ∀ β, SecT D.toPre a n j β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧
        ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k),
          TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ →
          ∃ τ'' : SecE U.toUnifPre (b e) n j,
            (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'),
              Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ m * sval τ' x z J') ∧
            TExp U.toUnifPre τ'' (w := id) F := by
    intro m
    induction m with
    | zero =>
      intro n j hn hj
      have hn' : n = 0 := by simp [hn]
      have hj' : j = (k : ℤ) := by simp [hj]
      subst hn' hj'
      refine ⟨ρ, hρS, hρT, fun e τ τ' _ hτ' => ⟨τ', fun Z x z J' _ => by simp, hτ'⟩⟩
    | succ m ih =>
      intro n j hn hj
      obtain ⟨Fm, hFS, hFT, hFm⟩ := ih ((N : ℤ) * m) ((k : ℤ) - m) rfl rfl
      obtain ⟨F, hS, hT, hP⟩ := GlobalTheory.T.exists_product_small_twistedFunctionalEqn_family R hAdm D a a' h h' hE A G hG U b hb
        (N : ℤ) (-1) ((N : ℤ) * m) ((k : ℤ) - m) n j (by rw [hn]; push_cast; ring)
        (by rw [hj]; push_cast; ring) g Fm hgS hFS hgT hFT
      refine ⟨F, hS, hT, fun e τ τ' hτ hτ' => ?_⟩
      obtain ⟨τm, hτmv, hτmE⟩ := hFm e τ τ' hτ hτ'
      obtain ⟨τ'', hv, hE''⟩ := hP e τ τm hτ hτmE
      refine ⟨τ'', fun Z x z J' hJ => ?_, hE''⟩
      rw [hv Z x z J' hJ, hτmv Z x z J' hJ]
      ring
  exact key k _ _ (by push_cast; ring) (by simp)

end GlobalTheory.ZmPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentraliseStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C, (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) → (minpoly F c).natDegree = n := by
  first | (exact @GlobalTheory.RegDeg.natDegree_minpoly_eq) | (exact GlobalTheory.RegDeg.natDegree_minpoly_eq) | (intros; apply GlobalTheory.RegDeg.natDegree_minpoly_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointsSimilitudeGLProductBijectiveStatement
section
open GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicPoints_similitude_GL_product_bijective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.bijective_locP) | (exact GlobalTheory.LKTrip.HTGroup.bijective_locP) | (intros; apply GlobalTheory.LKTrip.HTGroup.bijective_locP  <;> assumption)
end

