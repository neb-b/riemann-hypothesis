module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

noncomputable section
namespace GlobalTheory.ZH.LinFrame
open GlobalTheory.ProjSpace

variable {o : Type} [CommRing o] {m : ℕ} {T : Scheme.{0}}

def chartLB (p : T ⟶ PSpace o m) : LB T :=
  ⟨Fin (m + 1), fun i => p ⁻¹ᵁ chart o m i, fun i j =>
    ⟨pullRatio p _ i inf_le_left j, pullRatio p _ j inf_le_right i,
      pullRatio_mul_pullRatio.trans pullRatio_self, pullRatio_mul_pullRatio.trans pullRatio_self⟩⟩

theorem lin_compat (p : T ⟶ PSpace o m) (b : Fin (m + 1) → Γ(T, ⊤)) (i j : Fin (m + 1)) :
    resG T (inf_le_left : p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j ≤ _)
        (∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m i) i le_rfl k) =
      pullRatio p (p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j) i inf_le_left j *
        resG T (inf_le_right : p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j ≤ _)
          (∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m j) j le_rfl k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, resG_pullRatio, resG_pullRatio, mul_left_comm, pullRatio_mul_pullRatio]
  congr 1
  exact (DVR.SecOps.resTop_res _ _).trans (DVR.SecOps.resTop_res _ _).symm

def linSec (p : T ⟶ PSpace o m) (b : Fin (m + 1) → Γ(T, ⊤)) : (chartLB p).Sec where
  f l := ∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m l) l le_rfl k
  compat i j := lin_compat p b i j

variable {K : Type} [Field K]

theorem crd_iff (x : Sp K ⟶ PSpace o m) (v : Fin (m + 1) → K) : Crd (O1 o m) (coord o m) x v ↔
    ∃ (l : Fin (m + 1)) (c : Kˣ), ⊤ ≤ x ⁻¹ᵁ chart o m l ∧
      ∀ j, v j = (c : K) * valR x (chart o m l) (ratio o m l j) := Iff.rfl

theorem valR_pullRatio (x : Sp K ⟶ T) (p : T ⟶ PSpace o m) {W : T.Opens} {l : Fin (m + 1)}
    (hl : W ≤ p ⁻¹ᵁ chart o m l) (h : ⊤ ≤ x ⁻¹ᵁ W) (k : Fin (m + 1)) :
    valR x W (pullRatio p W l hl k) = valR (x ≫ p) (chart o m l) (ratio o m l k) :=
  Points.valR_appLE x p hl h _

theorem valR_linSec (x : Sp K ⟶ T) (p : T ⟶ PSpace o m) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤))
    {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l) (i : Fin (m + 1)) :
    valR x (p ⁻¹ᵁ chart o m l) ((linSec p (b i)).f l) =
      (b.map (valR x ⊤)).mulVec (fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)) i := by
  change valR x (p ⁻¹ᵁ chart o m l) (∑ k, resG T le_top (b i k) * pullRatio p (p ⁻¹ᵁ chart o m l) l le_rfl k) =
    ∑ k, valR x ⊤ (b i k) * valR (x ≫ p) (chart o m l) (ratio o m l k)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CrdCalc.valR_eq x _ h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← CrdCalc.valR_eq x _ h, CrdCalc.valR_mul x _ h, CrdCalc.valR_res x _ h, valR_pullRatio x p _ h]

theorem valR_ratio_self (x : Sp K ⟶ PSpace o m) {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ chart o m l) :
    valR x (chart o m l) (ratio o m l l) = 1 := by
  rw [ratio, ratioOn_self, Points.valR_one x _ h]

theorem exists_isUnit_valR_linSec (x : Sp K ⟶ T) (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det)
    {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l) :
    ∃ i, IsUnit (valR x (p ⁻¹ᵁ chart o m l) ((linSec p (b i)).f l)) := by
  by_contra hn
  have e : b.map (valR x ⊤) = (CrdCalc.valHom x ⊤ le_top).mapMatrix b := by
    ext i j
    exact CrdCalc.valR_eq x ⊤ le_top _
  have hd : (b.map (valR x ⊤)).det ≠ 0 := by
    rw [e, ← RingHom.map_det]
    exact (hb.map _).ne_zero
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hd
    (v := fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)) (funext fun i => by
      rw [← valR_linSec x p b h]
      by_contra hi
      exact hn ⟨i, Ne.isUnit hi⟩)
  have h1 := congrFun h0 l
  rw [valR_ratio_self (x ≫ p) h] at h1
  exact one_ne_zero h1

theorem iSup_nonzeroLocus_linSec (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det) :
    ⨆ i, nonzeroLocus (linSec p (b i)) = ⊤ := by
  refine top_le_iff.1 fun y _ => ?_
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 ((iSup_chart o m).ge (Set.mem_univ (p y)))
  let x : Sp (T.residueField y) ⟶ T := T.fromSpecResidueField y
  have hx : ∀ z, x z = y := fun z => T.fromSpecResidueField_apply y z
  have h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l := fun z _ => by
    change p (x z) ∈ chart o m l
    rw [hx]; exact hl
  obtain ⟨i, hi⟩ := exists_isUnit_valR_linSec x p hb h
  have h2 : x (IsLocalRing.closedPoint _) ∈ T.basicOpen ((linSec p (b i)).f l) :=
    (CrdCalc.isUnit_valR_iff x _ h _).1 hi (Set.mem_univ _)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (congrArg (· ∈ T.basicOpen ((linSec p (b i)).f l)) (hx _)).mp h2⟩⟩

theorem crd_toProj_linSec {A : Type} [CommRing A] (c : T ⟶ Sp A) (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det) (x : Sp K ⟶ T) {v : Fin (m + 1) → K}
    (hv : Crd (O1 o m) (coord o m) (x ≫ p) v) :
    Crd (O1 A m) (coord A m) (x ≫ toProj c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb))
      ((b.map (valR x ⊤)).mulVec v) := by
  obtain ⟨l, u, hl, hv⟩ := (crd_iff _ _).1 hv
  have h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l := hl
  obtain ⟨i, hi⟩ := exists_isUnit_valR_linSec x p hb h
  set g := toProj c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb) with hg
  have h₁ : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ chart A m i := by
    rw [hg, toProj_preimage_chart]
    exact ((CrdCalc.isUnit_valR_iff x _ h _).1 hi).trans
      (x.preimage_mono (le_iSup (fun k => T.basicOpen ((linSec p (b i)).f k)) l))
  have h₂ : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l) := fun z hz => ⟨h₁ hz, h hz⟩
  refine (crd_iff _ _).2 ⟨i, u * hi.unit, h₁, fun j => ?_⟩
  have e := congrArg (valR x _) (sec_eq_pullRatio_toProj_mul c (fun i => linSec p (b i))
    (iSup_nonzeroLocus_linSec p hb) i j l (W := g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l) inf_le_left inf_le_right)
  have r : ∀ t : (chartLB p).Sec, _ = valR x (p ⁻¹ᵁ chart o m l) (t.f l) := fun t =>
    CrdCalc.valR_res x inf_le_right h₂ (t.f l)
  replace e := (r _).symm.trans (e.trans ((CrdCalc.valR_mul x _ h₂ _ _).trans
    (congrArg₂ (· * ·) (valR_pullRatio x _ _ h₂ _) (r _))))
  have ev : v = (u : K) • fun k => valR (x ≫ p) (chart o m l) (ratio o m l k) := funext hv
  rw [ev, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← valR_linSec x p b h, Units.val_mul, IsUnit.unit_spec,
    _root_.mul_assoc]
  exact congrArg (_ * ·) (e.trans (mul_comm _ _))

theorem eq_of_crd {x x' : Sp K ⟶ PSpace o m} (hs : x ≫ PSpace.str o m = x' ≫ PSpace.str o m)
    {w : Fin (m + 1) → K} (h : Crd (O1 o m) (coord o m) x w) (h' : Crd (O1 o m) (coord o m) x' w) : x = x' := by
  obtain ⟨l, c, hl, hw⟩ := (crd_iff _ _).1 h
  obtain ⟨l', c', hl', hw'⟩ := (crd_iff _ _).1 h'
  have h1 : w l = c := by rw [hw, valR_ratio_self x hl, mul_one]
  have h2 : ⊤ ≤ x' ⁻¹ᵁ chart o m l := by
    have hu : IsUnit (valR x' (chart o m l') (ratio o m l' l)) :=
      (Units.isUnit_units_mul c' _).1 ((hw' l).symm.trans h1 ▸ c.isUnit)
    refine ((CrdCalc.isUnit_valR_iff x' _ hl' _).1 hu).trans (x'.preimage_mono ?_)
    rw [ratio, basicOpen_ratioOn]
    exact inf_le_right
  obtain ⟨u, hu⟩ := CrdCalc.exists_unit_charts (O1 o m) x' l' l hl' h2
  have hw'' : ∀ j, w j = (c' : K) * u * valR x' (chart o m l) (ratio o m l j) := fun j => by
    rw [hw', _root_.mul_assoc]
    exact congrArg (_ * ·) (hu (coord o m j))
  have h3 : (c' : K) * u = c := by rw [← h1, hw'', valR_ratio_self x' h2, mul_one]
  refine hom_ext hs fun _ => ⟨⊤, trivial, l, hl, h2, fun j => ?_⟩
  have e := (hw j).symm.trans (hw'' j)
  rw [h3, Units.mul_right_inj, CrdCalc.valR_eq x _ hl, CrdCalc.valR_eq x' _ h2] at e
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e

theorem isImmersion_lift_of_linear_change : ∀ (o : Type) [CommRing o] (Y Z : Scheme.{0}) [IsReduced Y] (s : Z ⟶ Sp o) (f : Y ⟶ Z) (m : ℕ) (π : Y ⟶ PSpace o m) (h : π ≫ PSpace.str o m = f ≫ s), (∀ y : Y, ∃ (W : Z.Opens) (A : Type) (_ : CommRing A) (c : W.toScheme ⟶ Sp A) (ψ : (f ⁻¹ᵁ W).toScheme ⟶ PSpace A m) (a : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(Z, W)) (K : Type) (_ : Field K) (η : Sp K ⟶ (f ⁻¹ᵁ W).toScheme) (v : Fin (m + 1) → K), f y ∈ W ∧ IsImmersion ψ ∧ ψ ≫ PSpace.str A m = (f ∣_ W) ≫ c ∧ IsUnit a.det ∧ IsDominant η ∧ Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (η ≫ (f ⁻¹ᵁ W).ι ≫ π) v ∧ Crd (ProjSpace.O1 A m) (ProjSpace.coord A m) (η ≫ ψ) ((a.map (valF (η ≫ (f ⁻¹ᵁ W).ι ≫ f) W)).mulVec v)) → IsImmersion (pullback.lift π f h) := by
  intro o _ Y Z _ s f m π h H
  choose W A iA c ψ a K iK η v hy hψ hc ha hη h₁ h₂ using H
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  have hj : pullback.lift π f h ≫ pullback.snd (PSpace.str o m) s = f := pullback.lift_snd _ _ _
  have hπ : pullback.lift π f h ≫ pullback.fst (PSpace.str o m) s = π := pullback.lift_fst _ _ _
  generalize pullback.lift π f h = j at hj hπ ⊢
  generalize pullback.fst (PSpace.str o m) s = q at hπ
  generalize pullback.snd (PSpace.str o m) s = r at hj
  subst hj hπ
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (fun y => r ⁻¹ᵁ W y) ?_ fun y => ?_
  · rintro _ ⟨y, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
  have := hψ y
  have := hη y
  have hT : (⊤ : (r ⁻¹ᵁ W y).toScheme.Opens) ≤ ((r ⁻¹ᵁ W y).ι ≫ r) ⁻¹ᵁ W y := (r ⁻¹ᵁ W y).ι_preimage_self.ge
  let b := (((r ⁻¹ᵁ W y).ι ≫ r).appLE (W y) ⊤ hT).hom.mapMatrix (a y)
  have hb : IsUnit b.det := by
    rw [← RingHom.map_det]
    exact (ha y).map _
  let j' : ((j ≫ r) ⁻¹ᵁ W y).toScheme ⟶ (r ⁻¹ᵁ W y).toScheme := j ∣_ (r ⁻¹ᵁ W y)
  have hj' : j' ≫ (r ⁻¹ᵁ W y).ι = ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j := morphismRestrict_ι j _
  let g := toProj ((r ∣_ W y) ≫ c y) (fun i => linSec ((r ⁻¹ᵁ W y).ι ≫ q) (b i)) (iSup_nonzeroLocus_linSec _ hb)
  have hs : (j' ≫ g) ≫ PSpace.str (A y) m = ψ y ≫ PSpace.str (A y) m := by
    rw [Category.assoc, toProj_str, hc, morphismRestrict_comp]
    exact (Category.assoc _ _ _).symm
  have e : j' ≫ g = ψ y := by
    refine ext_of_isDominant_of_isSeparated _ hs (η y) (eq_of_crd ?_ ?_ (h₂ y))
    · rw [Category.assoc, hs, Category.assoc]
    · have k := crd_toProj_linSec ((r ∣_ W y) ≫ c y) ((r ⁻¹ᵁ W y).ι ≫ q) hb (η y ≫ j') (v := v y) (by
        rw [Category.assoc, reassoc_of% hj']
        exact h₁ y)
      have eb : b.map (valR (η y ≫ j') ⊤) = (a y).map (valF (η y ≫ ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j ≫ r) (W y)) := by
        ext i k
        refine (Points.valR_appLE (η y ≫ j') _ hT le_top (a y i k)).trans ?_
        rw [Category.assoc, reassoc_of% hj']
        rfl
      rw [eb, Category.assoc] at k
      exact k
  have : IsImmersion (j' ≫ g) := e ▸ hψ y
  exact IsImmersion.of_comp j' g

end GlobalTheory.ZH.LinFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LbIsoLinCombPull
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.SymExtend

theorem lbIso_linComb_pull {X X' Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) :
    LBIso (LB.LinComb (L.pull F) φ' ε) ((LB.LinComb L φ ε).pull h) :=
  have r : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ ε) := (GlobalTheory.PrimNorm.lbIso_iff hL φ ε φ ε).2 rfl
  LBIso.chartPull (chartPullLinComb L F φ' φ ε h hc) (chartPullPull _ h h rfl) r

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem lbIso_cube_zero (PP : RigLB G) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (z : 𝟙_ (Over S) ⟶ T)
    (hz : ∀ i, z ≫ x i = 1) : LBIso ((cubeLB G x PP.L).pull z.left) (PP.L.pull (eSec G)) := by
  have h1 : GlobalTheory.PrimNorm.cls PP.L (eSec G) = 1 := by
    have := (GlobalTheory.PrimNorm.hasGen_iff PP.isLB (K := PUnit) (fun _ => eSec G) (fun _ => 1)).1 ⟨PP.rig, PP.rigGen⟩
    simpa using this
  have h2 : ∀ I : Finset (Fin n), z.left ≫ (psum G x I).left = eSec G := fun I => by
    have e : z ≫ psum G x I = psum G (fun i => z ≫ x i) I := psum_hom (preHom z) x I
    have e' : psum G (fun i => z ≫ x i) I = 1 := by
      have := psum_hom (1 : (T ⟶ G) →* (𝟙_ (Over S) ⟶ G)) x I
      rw [funext hz]
      exact this.symm
    rw [← Over.comp_left, e, e', ← MonObj.one_eq_one]
    rfl
  exact GlobalTheory.PrimNorm.lbIso_nested PP.isLB _ _ _ _ _ _ (by
    simp only [h2, h1, one_zpow, Finset.prod_const_one])

variable {U : Scheme.{0}} {A : Over U} [GrpObj A] [IsCommMonObj A] {j : U ⟶ S} {a : A.left ⟶ G.left}


omit [IsCommMonObj G] [IsCommMonObj A] in
theorem isPullback_square (h : IsGrpPullback A G j a) :
    IsPullback (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left (A ⊗ A).hom (G ⊗ G).hom j := by
  let l := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have l₁ : l.left ≫ pullback.fst G.hom G.hom = pullback.fst A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have l₂ : l.left ≫ pullback.snd G.hom G.hom = pullback.snd A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have big : IsPullback (pullback.snd A.hom A.hom ≫ a) (pullback.fst A.hom A.hom) G.hom (A.hom ≫ j) :=
    (IsPullback.of_hasPullback A.hom A.hom).flip.paste_horiz h.1
  have h₁ : IsPullback l.left (pullback.fst A.hom A.hom) (pullback.fst G.hom G.hom) a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd G.hom G.hom) (v₁₃ := G.hom) (h₂₂ := G.hom) ?_
      l₁ (IsPullback.of_hasPullback G.hom G.hom).flip
    rw [l₂, h.1.w]
    exact big
  exact h₁.paste_vert h.1

theorem hypS_extend [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S) [Nonempty U] [IsOpenImmersion j]
    [Smooth G.hom] [GeometricallyConnected G.hom] (h : IsGrpPullback A G j a)
    (ext : ∀ α : A ⟶ A, IsMonHom α → ∃! F : G ⟶ G, IsMonHom F ∧ a ≫ F.left = α.left ≫ a)
    (LA : LB A.left) (PP : RigLB G) (hLA : LA.IsLB) (hb : LBIso (PP.L.pull a) LA) (H : GlobalTheory.ZH.HypS A LA) :
    GlobalTheory.ZH.HypS G PP.L := by
  obtain ⟨w', wd', hw', hwd', hs, hp, ha⟩ := H
  obtain ⟨w, ⟨hw, ew⟩, -⟩ := ext w' hw'
  obtain ⟨wd, ⟨hwd, ewd⟩, -⟩ := ext wd' hwd'
  have hL := PP.isLB
  have hB : (PP.L.pull a).IsLB := pull_isLB hL a
  have push : ∀ {u' : A ⟶ A} {u : G ⟶ G}, a ≫ u.left = u'.left ≫ a → ∀ {T : Over U} (x : T ⟶ A),
      pushPt h.1.w (x ≫ u') = pushPt h.1.w x ≫ u := fun e _ x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ← e, Category.assoc])
  have pa := @push _ _ ew
  have pd := @push _ _ ewd
  have cube : ∀ {T : Over S} {T' : Over U} (x : Fin 2 → (T ⟶ G)) (x' : Fin 2 → (T' ⟶ A))
      (V : Over.mk (T'.hom ≫ j) ⟶ T), (∀ i, pushPt h.1.w (x' i) = V ≫ x i) →
      LBIso (cubeLB A x' LA) ((cubeLB G x PP.L).pull V.left) := fun x x' V hx =>
    LBIso.trans (DVR.linComb_isLB _ hLA _ _) (DVR.linComb_isLB _ hB _ _)
      (pull_isLB (DVR.linComb_isLB _ hL _ _) _) (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _)
      (lbIso_linComb_pull hL a _ _ _ V.left fun I => psum_push h _ _ V hx I.down)
  have cl : ∀ {T : Over S} (x : Fin 2 → (T ⟶ G)), (cubeLB G x PP.L).IsLB := fun x => DVR.linComb_isLB _ hL _ _
  have cl' : ∀ {T : Over U} (x : Fin 2 → (T ⟶ A)), (cubeLB A x LA).IsLB := fun x => DVR.linComb_isLB _ hLA _ _
  have w1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ w = 1 := MonObj.one_comp w
  have wd1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ wd = 1 := MonObj.one_comp wd
  refine ⟨w, wd, hw, hwd, ?_, ?_, ?_⟩
  · obtain ⟨F, -, hF⟩ := ext (𝟙 A) inferInstance
    refine (hF _ ⟨GlobalTheory.Serre.isMonHom_mul w wd, ?_⟩).trans (hF _ ⟨inferInstance, by simp⟩).symm
    have b : pushPt h.1.w (w' * wd') = pushPt h.1.w w' * pushPt h.1.w wd' := map_mul (pushHom h A) _ _
    have c := pa (𝟙 A)
    have d := pd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [c, d, ← MonObj.comp_mul, hs] at b
    have e : 𝟙 A.left ≫ a = (𝟙 A.left ≫ a) ≫ (w * wd).left := congrArg (fun z => z.left) b
    simp only [Category.id_comp] at e
    simpa using e.symm
  · let V := pushPt h.1.w (𝟙 A)
    have hV : V.left = a := Category.id_comp _
    have c := cube ![𝟙 G, w] ![𝟙 A, w'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rw [hV] at c
    refine (_root_.GlobalTheory.lbIso_extend_of_normal S hS U G.left A.left j G.hom (eSec G) a A.hom inferInstance
      (GlobalTheory.geometricallyIntegral_of_smooth _) (Over.w η[G]) h.1 _ _ hL (cl _)
      (hb.trans hB hLA (pull_isLB (cl _) _) (hp.trans hLA (cl' _) (pull_isLB (cl _) _) c))).1 ?_
    refine (lbIso_cube_zero PP ![𝟙 G, w] η[G] fun i => ?_).symm
    rw [MonObj.one_eq_one]
    fin_cases i
    · simp
    · exact w1
  · let V := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
    have c₁ := cube ![fst G G ≫ w, snd G G] ![fst A A ≫ w', snd A A] V (fun i => by
      fin_cases i
      · exact (pa _).trans (by simp [V])
      · simp [V])
    have c₂ := cube ![fst G G, snd G G ≫ wd] ![fst A A, snd A A ≫ wd'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (pd _).trans (by simp [V]))
    let z : 𝟙_ (Over S) ⟶ G ⊗ G := lift 1 1
    refine (_root_.GlobalTheory.lbIso_extend_of_normal S hS U (G ⊗ G).left (A ⊗ A).left j (G ⊗ G).hom z.left V.left (A ⊗ A).hom
      (GlobalTheory.smooth_tensorObj_hom G G) (GlobalTheory.geometricallyIntegral_tensorObj_hom G G) (Over.w z)
      (isPullback_square h) _ _ (cl _) (cl _)
      (c₁.symm.trans (pull_isLB (cl _) _) (cl' _) (pull_isLB (cl _) _)
        (ha.trans (cl' _) (cl' _) (pull_isLB (cl _) _) c₂))).1 ?_
    refine LBIso.trans (pull_isLB (cl _) _) (pull_isLB hL _) (pull_isLB (cl _) _)
      (lbIso_cube_zero PP _ z fun i => ?_) (lbIso_cube_zero PP _ z fun i => ?_).symm
    · fin_cases i
      · simpa [z] using w1
      · simp [z]
    · fin_cases i
      · simp [z]
      · simpa [z] using wd1

end GlobalTheory.SymExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoPullbackUniformisedThetaModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.TestBundle

open GlobalTheory.CechPic

theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (P : Over (Spec (CommRingCat.of V))) [Smooth P.hom] [GeometricallyConnected P.hom]
    (e : Spec (CommRingCat.of V) ⟶ P.left) (he : e ≫ P.hom = 𝟙 _) {L M : LB P.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : CechPic.pull (pullback.fst P.hom (jK V)) (cls L hL) =
      CechPic.pull (pullback.fst P.hom (jK V)) (cls M hM)) : LBIso L M := by
  have hN := LB.isLB_div hM hL
  have h₁ : IsPreimmersion (jK V) := IsPreimmersion.of_isLocalization (nonZeroDivisors V)
  have h₂ : Flat (jK V) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors V))
  refine GenericExtend.exists_isGen_of_densePart _ _ (jK V) ((isNormalScheme_iff_pred _).1 inferInstance) h₁ h₂
    DVR.isDominant_jK inferInstance P e (LB.div M L) he ‹_› (geometricallyIntegral_of_smooth P.hom) hN
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hN _)) ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  rw [cls_pull hN, cls_div hM hL, map_sub, h, sub_self]

theorem lbIso_pull_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK _ F ψ ⟨_, h₁, _, h₂⟩
  have := u.semi.smooth
  have := u.semi.geomConnected
  have hL := Q.L.isLB
  have hP := ρ.P.isLB
  have hA := u.A.isLB
  have hG := u.U.LG.isLB
  refine lbIso_of_generic u.G (eSec u.G) (Over.w η[u.G]) (pull_isLB hL F) hG ?_
  have a : CechPic.pull Q.φ (cls _ hL) = CechPic.pull (pullback.fst ρ.P.A.hom Q.u₀) (cls _ hP) :=
    (cls_eq_iff (pull_isLB hL _) (pull_isLB hP _)).2 ⟨Q.w, Q.w_gen⟩
  have b : cls _ hA = CechPic.pull u.φ (cls _ hP) := (cls_eq_iff hA (pull_isLB hP _)).2 u.lb
  have c : CechPic.pull u.U.gen.hom.left (cls _ hA) = CechPic.pull (pullback.fst u.G.hom (jK u.V)) (cls _ hG) :=
    (cls_eq_iff (pull_isLB hA _) (pull_isLB hG _)).2 u.U.ext
  refine Eq.trans ?_ c
  rw [cls_pull hL, ← pull_comp, ← h₂, pull_comp, a, ← pull_comp, h₁, b]
  exact pull_comp _ _ _

end GlobalTheory.ZH.TestBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section

namespace GlobalTheory.RosatiDescent

theorem exists_gen_of_rosatiAdj {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    {f g : A ⟶ A} (h : RosatiAdj A L f g) : ∃ t : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := h (default : PrimeSpectrum k)
  obtain rfl : U = ⊤ := eq_top_iff.2 fun x _ => by
    rwa [Subsingleton.elim (α := PrimeSpectrum k) x default]
  have e : rosatiφ A f g = fun i => (A ⊗ A).left.topIso.inv ≫ ((A ⊗ A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ A f g i :=
    funext fun i => ((A ⊗ A).left.topIso.inv_hom_id_assoc _).symm
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ _ ht _⟩

theorem rosatiAdj_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)} {A : Over (Sp K)}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A₀) {Φ : A.left ⟶ A₀.left}
    (h : IsGrpPullback A A₀ (spMap i) Φ) {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hw : LBIso L (L₀.pull Φ)) {f g : A ⟶ A} {f₀ g₀ : A₀ ⟶ A₀} (hf : f.left ≫ Φ = Φ ≫ f₀.left)
    (hg : g.left ≫ Φ = Φ ≫ g₀.left) (hr : RosatiAdj A L f g) : RosatiAdj A₀ L₀ f₀ g₀ := by
  have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
  let U₂ := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have u₁ : U₂.left ≫ (fst A₀ A₀).left = (fst A A).left ≫ Φ := TripleDescent.lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd A₀ A₀).left = (snd A A).left ≫ Φ := TripleDescent.lift_left_snd _ _
  have P₂ : IsPullback U₂.left (A ⊗ A).hom (A₀ ⊗ A₀).hom (spMap i) :=
    TripleDescent.isPullback_tensor h.1 h.1 _ u₁ u₂
  have v₁ : (fst A A ≫ f).left ≫ Φ = U₂.left ≫ (fst A₀ A₀ ≫ f₀).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, ← u₁, Category.assoc]
  have v₂ : (snd A A ≫ g).left ≫ Φ = U₂.left ≫ (snd A₀ A₀ ≫ g₀).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, ← u₂, Category.assoc]
  have hψ : ∀ k, rosatiφ A f g k ≫ Φ = U₂.left ≫ rosatiφ A₀ f₀ g₀ k := fun k => by
    fin_cases k
    exacts [ArcPull.mul_push h U₂.left v₁ u₂.symm, v₁, u₂.symm, ArcPull.mul_push h U₂.left u₁.symm v₂, u₁.symm, v₂]
  obtain ⟨t, ht⟩ := exists_gen_of_rosatiAdj hr
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hL₀ hL t ht
  obtain ⟨u, hu⟩ := (lb_gen_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom _ _ A₂.smooth A₂.proper A₂.geomConnected P₂).1
    (LB.LinComb L₀ (rosatiφ A₀ f₀ g₀) rosatiε) (DVR.linComb_isLB _ hL₀ _ _)
    (gen_chartPull (chartPullOut L₀ _ _ U₂.left _ hψ) c hc)
  exact fun s => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ _ hu _⟩

end GlobalTheory.RosatiDescent

theorem GlobalTheory.polOAct_descend_of_generators : ∀ (O : Type) [CommRing O] [StarRing O] (J : Type) (gen : J → O), Subring.closure (Set.range gen) = ⊤ → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → LBIso P.L (P₀.L.pull Φ) → ∀ (oa : P.OAct O) (a₀ : J → (P₀.A ⟶ P₀.A)), (∀ j, (oa.act (gen j)).left ≫ Φ = Φ ≫ (a₀ j).left) → ∃ oa₀ : P₀.OAct O, ∀ c, (oa.act c).left ≫ Φ = Φ ≫ (oa₀.act c).left := by
  intro O _ _ J gen hgen K₀ K _ _ i P₀ P Φ h hw oa a₀ ha
  have := P₀.isAb.comm
  have := P.isAb.comm
  obtain ⟨r, -, hr⟩ := oAct_descend_of_generators O J gen K₀ K i P₀.A P.A Φ (ofRingAct oa.toRingAct) a₀ hgen h ha
  exact ⟨⟨r.toRingAct, fun a => RosatiDescent.rosatiAdj_descend i P₀.isAb h P₀.isLB P.isLB hw (hr a) (hr (star a))
    (oa.rosati a)⟩, hr⟩
end
end

