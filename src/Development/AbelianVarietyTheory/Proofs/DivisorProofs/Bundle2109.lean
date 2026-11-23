module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimOfAxes
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh.PrimForm

variable {R : Type} [CommRing R]

theorem pF_comp {A B C : Over (Sp R)} (f : B ⟶ C) (g : A ⟶ B) (a : GlobForm C.hom) :
    pF g (pF f a) = pF (g ≫ f) a :=
  (GlobalTheory.AbCoh.pull_comp_cup_id.1 R R C.left B.left C.hom B.hom (RingHom.id R) f.left (ovw f) R A.left A.hom
    (RingHom.id R) g.left (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) (fun _ ↦ rfl)).2.2.1 a

theorem pF_id (A : Over (Sp R)) (a : GlobForm A.hom) : pF (𝟙 A) a = a :=
  (GlobalTheory.AbCoh.pull_comp_cup_id.2.2 R A).2.2.1 a

theorem pF_unit {A B : Over (Sp R)} (f : 𝟙_ (Over (Sp R)) ⟶ A) (a : GlobForm A.hom) :
    pF (toUnit B ≫ f) a = 0 := by
  rw [← pF_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).1
  rw [Subsingleton.elim (pF f a) 0, map_zero]

theorem prim_of_axes (A : Over (Sp R)) [GrpObj A]
    (H : ∀ y : GlobForm (A ⊗ A).hom, pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 →
      pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0) : PrimF A := by
  intro x
  have e := H (pF μ[A] x - pF (fst A A) x - pF (snd A A) x) ?_ ?_
  · exact (sub_eq_zero.1 ((sub_sub _ _ _).symm.trans e))
  · rw [map_sub, map_sub, pF_comp, pF_comp, pF_comp, lift_fst, lift_snd, lift_comp_one_right, pF_id, pF_unit,
      sub_self, sub_zero]
  · rw [map_sub, map_sub, pF_comp, pF_comp, pF_comp, lift_fst, lift_snd, lift_comp_one_left, pF_id, pF_unit,
      sub_zero, sub_self]

end GlobalTheory.AbCoh.PrimForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorLiftAlongEtaleMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_lift : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E : DivOver p, E.Through (f y) → ∃ E' : DivOver (f ≫ p), E'.Through y ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hU y hy E hE
  obtain ⟨hfl, hfe, hft⟩ := _root_.GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict M W f U hU y hy
  obtain ⟨V', h, hdvr, hS, hcomap, het, hess⟩ := _root_.GlobalTheory.exists_valuationSubring_extend_of_formallyEtale (K := W.functionField)
    (K' := M.functionField) (R := W.presheaf.stalk (f y)) (S := M.presheaf.stalk y)
    (functionFieldMap f) (f.stalkMap y).hom hfl hfe hft
    (RingHom.ext fun a => functionFieldMap_algebraMap f y a) E.ring E.dvr (fun a => hE _ ⟨a, rfl⟩)
  have hc : ∀ a, Cartier.constFn (f ≫ p) a ∈ V' := fun a => by
    rw [← functionFieldMap_comp_constFn p f]
    exact h _ (E.const_mem a)
  have hess' : ((Cartier.constFn (f ≫ p)).codRestrict V' hc).EssFiniteType := by
    have e : (Cartier.constFn (f ≫ p)).codRestrict V' hc =
        ((functionFieldMap f).restrict E.ring V' h).comp E.const := by
      ext a
      simp [DivOver.const, ← functionFieldMap_comp_constFn p f]
    rw [e]
    exact E.essFiniteType.comp hess
  let E' : DivOver (f ≫ p) := ⟨V', hc, hdvr, hess'⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  have hdim := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hord := _root_.GlobalTheory.EtaleKlt.ord_functionFieldMap_of_formallyEtale M W p f E E' h hcomap het hess
  refine ⟨E', fun g hg => ?_, hord, fun η hη => GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale M W p f n hdim E E' h het hord η hη⟩
  obtain ⟨a, rfl⟩ := hg
  exact hS a

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfClassicalPointSameCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem natCast_prime_not_isUnit_stalk (X : Scheme.{0}) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X) :
    ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y (cPt p))) := by
  intro hu
  have h := hu.map (Scheme.stalkClosedPointTo y).hom
  rw [map_natCast] at h
  refine (not_isUnit_OO_iff ((p : ℕ) : OO p)).2 ?_ h
  have e : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p]) := by simp
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_natCast_lt_one_iff.2 dvd_rfl

theorem dvd_of_not_isUnit_stalk (X : Scheme.{0}) (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ X) (n : ℕ)
    (h : ¬ IsUnit ((n : ℕ) : X.presheaf.stalk (y (cPt q)))) : q ∣ n := by
  have h1 : ¬ IsUnit ((Scheme.stalkClosedPointTo y).hom (n : X.presheaf.stalk (y (cPt q)))) :=
    fun hu => h ((isUnit_map_iff (Scheme.stalkClosedPointTo y).hom _).1 hu)
  rw [map_natCast, not_isUnit_OO_iff] at h1
  have e : (((n : ℕ) : OO q) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) ((n : ℕ) : ℚ_[q]) := by simp
  rw [e, PadicAlgCl.norm_extends] at h1
  exact Padic.norm_natCast_lt_one_iff.1 h1

theorem eq_of_cPt_eq : ∀ (X : Scheme.{0}) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (y : Sp (OO p) ⟶ X)
    (y' : Sp (OO q) ⟶ X), y (cPt p) = y' (cPt q) → p = q := by
  intro X p q hp hq y y' h
  have h1 := natCast_prime_not_isUnit_stalk X p y
  have h2 : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y' (cPt q))) := by
    rw [← h]; exact h1
  have h3 := dvd_of_not_isUnit_stalk X q y' p h2
  exact ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 h3).symm

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsPol

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem polOnAb_genPt : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsOpen (abLocus G) →
    genericPoint S ∈ abLocus G → PolOnAb G L.L → PolOnAb (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)).L := by
  intro S _ G _ _ L hO hg hpol V _
  obtain ⟨U, hU, hp, hUs⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⟨abLocus G, hO⟩) (x := genericPoint S) hg
  obtain ⟨ha, hk⟩ := hpol U hUs
  obtain ⟨f, hf⟩ : ∃ f : V.toScheme ⟶ U.toScheme, f ≫ U.ι = V.ι ≫ KeyVals.genPt S :=
    ⟨IsOpenImmersion.lift U.ι (V.ι ≫ KeyVals.genPt S) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact KeyVals.genPt_le U hp (Set.mem_univ (V.ι y))), IsOpenImmersion.lift_fac _ _ _⟩
  have h := isGrpPullback_pullback G (KeyVals.genPt S)
  have h' := isGrpPullback_pullback (KeyVals.bG G (KeyVals.genPt S)) V.ι
  have h₀ := isGrpPullback_pullback G U.ι
  have h₂ := (h'.comp h).congr hf.symm rfl
  let A' := (Over.pullback V.ι).obj (KeyVals.bG G (KeyVals.genPt S))
  let a : (KeyVals.bG G (KeyVals.genPt S)).left ⟶ G.left := pullback.fst G.hom (KeyVals.genPt S)
  let b : A'.left ⟶ (KeyVals.bG G (KeyVals.genPt S)).left := pullback.fst (KeyVals.bG G (KeyVals.genPt S)).hom V.ι
  let ψ : A'.left ⟶ ((Over.pullback U.ι).obj G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst G.hom U.ι = b ≫ a := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback A' ((Over.pullback U.ι).obj G) f ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hL := pull_isLB (pull_isLB L.isLB a) b
  have hL₀ := pull_isLB L.isLB (pullback.fst G.hom U.ι)
  obtain ⟨w, hw⟩ : LBIso ((L.L.pull a).pull b) ((L.L.pull (pullback.fst G.hom U.ι)).pull ψ) :=
    LBIso.chartPull
      (chartPullLinComb L.L a (fun _ : PUnit => b) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
        fun _ => (Category.id_comp _).symm)
      (chartPullLinComb L.L _ (fun _ : PUnit => ψ) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
        fun _ => hψ.trans (Category.id_comp _).symm)
      (lbIso_self (pull_isLB L.isLB (b ≫ a)))
  have : IsAffine U.toScheme := hU
  exact ⟨relAmple_pull h₃.1 hL₀ hL ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha,
    kTriv_pull h₃ hL₀ hL ((isGen_iff w).1 hw) hk⟩

end GlobalTheory.KeyValsPol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusRestrictAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.PolOpen

section
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem relAmple_pull_of_affine (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w)
    (hf : ∀ U' : S'.Opens, IsAffineOpen U' → ∃ U : S.Opens, IsAffineOpen U ∧ U' ≤ f ⁻¹ᵁ U) (hA : RelAmple A L) :
    RelAmple A' L' := by
  intro U' hU'
  obtain ⟨U, hU, le⟩ := hf U' hU'
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA U hU
  have le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy => (congrArg (fun q => q y ∈ U) h.w).mpr (le hy)
  let ψ := φ.resLE (A.hom ⁻¹ᵁ U) (A'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (A'.hom ∣_ U') (A.hom ∣_ U) (f.resLE U U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict A.hom U).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict A'.hom U').flip.paste_horiz h
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc,
        Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine U := hU
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have hP' := linComb_isLB L' hL' (K := Fin N) (fun _ => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A' L' U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L U N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A' L' U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((f.resLE U U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end

theorem mem_abLocus_of_open {S S' : Scheme.{0}} (j : S' ⟶ S) [IsOpenImmersion j] (G : Over S) (s : S')
    (hs : s ∈ abLocus ((Over.pullback j).obj G)) : j s ∈ abLocus G := by
  rintro K _ _ t ⟨p, hp⟩
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hr : Set.range t ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    exact ⟨s, by rw [Subsingleton.elim q p, hp]⟩
  let t' := IsOpenImmersion.lift j t hr
  have ht : t' ≫ j = t := IsOpenImmersion.lift_fac _ _ _
  have hp' : t' p = s := j.isOpenEmbedding.injective ((congrArg (fun q => q p) ht).trans hp)
  have h₁ : IsProper (pullback.snd (pullback.snd G.hom j) t') := hs K t' ⟨p, hp'⟩
  have h₂ := (IsPullback.of_hasPullback (pullback.snd G.hom j) t').paste_horiz (IsPullback.of_hasPullback G.hom j)
  rw [ht] at h₂
  rw [← h₂.isoPullback_inv_snd]
  infer_instance

theorem polOnAb_open {S S' : Scheme.{0}} (j : S' ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (L : LB G.left)
    (hL : L.IsLB) (h : PolOnAb G L) : PolOnAb ((Over.pullback j).obj G) (L.pull (pullback.fst G.hom j)) := by
  intro W' hW'
  obtain ⟨ha, hK⟩ := h (j ''ᵁ W') (by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_abLocus_of_open j G s (hW' hs))
  have hr : Set.range (W'.ι ≫ j) ⊆ Set.range (j ''ᵁ W').ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  let e := IsOpenImmersion.lift (j ''ᵁ W').ι (W'.ι ≫ j) hr
  have he : e ≫ (j ''ᵁ W').ι = W'.ι ≫ j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (e ≫ (j ''ᵁ W').ι) := by rw [he]; infer_instance
  have : IsOpenImmersion e := IsOpenImmersion.of_comp e (j ''ᵁ W').ι
  have p₀ := isGrpPullback_pullback G (j ''ᵁ W').ι
  have p₁ := (isGrpPullback_pullback ((Over.pullback j).obj G) W'.ι).comp (isGrpPullback_pullback G j)
  have w₁ := p₁.1.w.trans ((congrArg _ he.symm).trans (Category.assoc _ _ _).symm)
  have p₂ := IsGrpPullback.cancel p₀ (p₁.congr he.symm (p₀.1.lift_fst _ _ w₁).symm) (p₀.1.lift_snd _ _ w₁)
  have hL₀ := pull_isLB hL (pullback.fst G.hom (j ''ᵁ W').ι)
  have hL₁ := pull_isLB (pull_isLB hL (pullback.fst G.hom j)) (pullback.fst ((Over.pullback j).obj G).hom W'.ι)
  obtain ⟨w, hw⟩ : LBIso ((L.pull (pullback.fst G.hom j)).pull (pullback.fst ((Over.pullback j).obj G).hom W'.ι))
      ((L.pull (pullback.fst G.hom (j ''ᵁ W').ι)).pull (p₀.1.lift _ _ w₁)) := by
    refine (CechPic.cls_eq_iff hL₁ (pull_isLB hL₀ _)).1 ?_
    rw [CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL]
    exact (CechPic.pull_comp _ _ _).symm.trans ((congrArg (fun q => CechPic.pull q _) (p₀.1.lift_fst _ _ w₁).symm).trans
      (CechPic.pull_comp _ _ _))
  exact ⟨relAmple_pull_of_affine p₂.1 hL₀ hL₁ ((isGen_iff w).1 hw)
    (fun U' hU' => ⟨e ''ᵁ U', hU'.image_of_isOpenImmersion e, fun y hy => ⟨y, hy, rfl⟩⟩) ha,
    kTriv_pull p₂ hL₀ hL₁ ((isGen_iff w).1 hw) hK⟩

theorem polOnAb_affine : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsOpen (abLocus G) → PolOnAb G L.L → PolOnAb (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L :=
  fun _ G _ _ L _ hW _ h => polOnAb_open hW.fromSpec G L.L L.isLB h

end GlobalTheory.KeyVals.PolOpen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelLowerLevelDescendsGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PrincipalDescent

theorem principal_descends : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [IsNoetherianRing o] [CommRing o'] (b : TBase o n) (ζ' : o') (j : o →+* o') (X Y : Scheme.{0}) (s' : X ⟶ Sp o') (π : X ⟶ Y) (sY : Y ⟶ Sp o) (C : SiegPre h N ζ' s') (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ν : Ga → (C.A.left ⟶ C.A.left)), N ≠ 0 → IsUnit (N : o') → n ∣ N → j (b.ζ : o) = ζ' ^ (N / n) → π ≫ sY = s' ≫ spMap j → IsGaloisCover Ga ρ π → IsQProjOver (π ≫ sY) → LocallyOfFiniteType sY → C.Principal → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → (∀ a, SRelBy C C (N / n) (N / n) (ρ a) (ν a)) → ∃ c : SiegPre h n (b.ζ : o) sY, c.Principal ∧ SRel C c (N / n) 1 π := by
  intro h n N o o' _ _ _ b ζ' j X Y s' π sY C Ga _ ρ ν hN hNu hdiv hζ hbase hπ hq hft hP ν1 νm hν
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨c, hCc, -⟩ := _root_.GlobalTheory.SiegLower.exists_lower h n N o o' b.ζ ζ' j X s' C hN hNu hdiv hζ
  have hqA : IsQProjOver (C.A.hom ≫ π ≫ sY) := _root_.GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth o X (π ≫ sY) C.A C.diag hq (pull_isLB C.isLB _) hP.1
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ := _root_.GlobalTheory.abelianScheme_descends_galoisCover_noetherian o X Y π sY Ga ρ C.A ν hπ hqA C.ab (fun a => (hν a).1) ν1 νm
  obtain ⟨P₀, φ₂, hP₀, sq, iso, norm⟩ := _root_.GlobalTheory.SquareDescent.exists_bundle_descent X Y π Ga ρ C.A A₀ φ ν C.P hπ C.ab hA₀ gp hφ (fun a => (hν a).1) ν1 νm
    C.isLB C.rig₁ (fun a => (hν a).2.1)
  have hlev : ∀ a, ∃ x₀ : 𝟙_ (Over Y) ⟶ A₀, (C.lev a ^ (N / n)).left ≫ φ = π ≫ x₀.left := by
    intro a
    obtain ⟨f, hf, -⟩ := hπ.existsUnique_desc ((C.lev a ^ (N / n)).left ≫ φ) (fun g => by
      rw [← Category.assoc, ← (hν g).2.2 a, Category.assoc, hφ.inv g])
    have hf' : f ≫ A₀.hom = 𝟙 Y := by
      have := hπ.fin
      have := hπ.etale
      have := hπ.onto
      have : Epi π := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi π, ← Category.assoc, hf, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
      simp
    exact ⟨Over.homMk f hf', hf.symm⟩
  choose lev₀ hlev₀ using hlev
  obtain ⟨φ', φ₂', gp', sq', iso', hlev'⟩ := _root_.GlobalTheory.SiegLev.descData_transport_id h n N (N / n) o o' b.ζ ζ' X Y (s' ≫ spMap j) s' C c π A₀ φ φ₂ P₀ lev₀
    hCc gp sq hP₀ iso hlev₀
  obtain ⟨c₀, hpb⟩ := _root_.GlobalTheory.exists_siegPre_of_galois_descended_data h n o b.ζ X Y π (s' ≫ spMap j) sY Ga ρ c A₀ φ' φ₂' P₀ lev₀ hbase.symm hπ hA₀ gp' sq' hP₀
    iso' norm hlev'
  have hR : SRel C c₀ (N / n) 1 π := by
    have e := ((_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n N o o o' b.ζ b.ζ ζ' Y X X sY (s' ≫ spMap j) s' c₀ c C π (𝟙 X) 1 1 (N / n)
      ((sRel_one_one_iff c c₀ π).2 hpb)).1).1 hCc
    rwa [Category.id_comp] at e
  exact ⟨c₀, _root_.GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale h N n (N / n) 1 o' o ζ' b.ζ X Y s' sY π C c₀ hπ.fin hπ.etale hπ.onto hR hP, hR⟩

end GlobalTheory.PrincipalDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullInvSymmIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLB

theorem pull_inv_symm_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → LBIso ((LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]).pull (GrpObj.inv : G ⟶ G).left) (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]) := by
  intro S G _ L hL
  have h₁ := LB.isLB_linComb hL (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB h₁ _) h₁).1 ?_
  rw [GlobalTheory.CechPic.cls_pull h₁, GlobalTheory.CechPic.cls_linComb hL _ _ h₁]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, map_add (f := _),
    ← GlobalTheory.CechPic.pull_comp]
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left, Category.comp_id, add_comm]

end GlobalTheory.SymLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullUInjectiveOfFlatSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.EigenDescent
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDescent

theorem app_injective_of_flat_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    (V : Y.Opens) : Function.Injective (π.app V) := by
  intro s t h
  apply TopCat.Presheaf.section_ext Y.sheaf V s t
  intro y hy
  obtain ⟨x, rfl⟩ := π.surjective y
  have hinj : Function.Injective (π.stalkMap x) := by
    have hf := Flat.stalkMap π x
    algebraize [(π.stalkMap x).hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (π x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (π x))
      (B := X.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (π x)) (X.presheaf.stalk x)
  apply hinj
  change π.stalkMap x (Y.presheaf.germ V (π x) hy s) = π.stalkMap x (Y.presheaf.germ V (π x) hy t)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, h]

theorem pullU_injective_of_flat_surjective : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y), Flat π → Surjective π →
    ∀ V : Y.Opens, Function.Injective (pullU π V) := by
  intro X Y π _ _ V u v h
  exact Units.ext (app_injective_of_flat_surjective π V (congrArg Units.val h))

end GlobalTheory.EigenDescent
end

