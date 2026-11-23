module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0113
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateEqUnitMulTauCoordinate
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiTauCoordRel

open GlobalTheory.PeriodBalance GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

def kst (ξ : Spec (CommRingCat.of (FractionRing R))) :
    FractionRing R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ :=
  ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

theorem kst_algebraMap (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) :
    kst ξ (algebraMap R (FractionRing R) r) = cst ξ r := rfl

theorem kst_injective (ξ : Spec (CommRingCat.of (FractionRing R))) : Function.Injective (kst (R := R) ξ) :=
  RingHom.injective _

theorem gm_genVal (ξ : Spec (CommRingCat.of (FractionRing R))) {M : LB (TK R).left} (t : LB.Gen M) (j : M.ι)
    (h : ⊤ ≤ M.U j) :
    (gm (𝟙 _) ξ (M.U j) (t.s j)).val = kst ξ (genVal t j h).val := by
  rw [gm_val _ ξ _ (h trivial)]
  simp only [kst, genVal, RingHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, RingHom.toMonoidHom_eq_coe]
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h) ξ trivial _).symm

theorem gm_mulGen {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (y : Y) (j : K ⊕ K' → L.ι) (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    gm (𝟙 Y) y (LB.wchart L (Sum.elim φ φ') j) ((LB.mulGen L φ ε φ' ε' t t').s j) =
      gm (𝟙 Y) y (LB.wchart L φ (j ∘ Sum.inl)) (t.s (j ∘ Sum.inl)) *
        gm (𝟙 Y) y (LB.wchart L φ' (j ∘ Sum.inr)) (t'.s (j ∘ Sum.inr)) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) (gm_res _ y _ hy _))

theorem gm_invGen {Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (y : Y) (j : K → L.ι) :
    gm (𝟙 Y) y (LB.wchart L φ j) ((LB.invGen L φ ε t).s j) = (gm (𝟙 Y) y (LB.wchart L φ j) (t.s j))⁻¹ :=
  map_inv _ _

theorem mem_inl {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {φ' : K' → (Y ⟶ X)} {y : Y} {j : K ⊕ K' → L.ι} (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    y ∈ LB.wchart L φ (j ∘ Sum.inl) :=
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)

theorem mem_inr {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {φ' : K' → (Y ⟶ X)} {y : Y} {j : K ⊕ K' → L.ι} (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    y ∈ LB.wchart L φ' (j ∘ Sum.inr) :=
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)

variable [IsLocalRing R]

theorem val_psi_chart (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (χ : D.X) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D (D.c χ) (j PUnit.unit))
    (hm : ξ ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) :
    ∃ u : Rˣ, val (D.psi χ) (𝟙 _) ξ J = Units.map (cst ξ).toMonoidHom u *
      gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := by
  have hx : D.xK χ = jK R ≫ (D.c χ).left := DVR.QForm.ptK_eq D χ
  have t := gen_trans (D.psi_gen χ) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
    (hJ.mem (fun _ : PUnit => D.xK χ) (𝟙 _)) hm
  obtain ⟨u, hu⟩ := unit_gm' ξ (D.c χ).left (D.P.L.U (J (jK R ≫ (D.c χ).left)) ⊓ D.P.L.U (j PUnit.unit))
    ⟨hJc _ (Over.w _), hj trivial⟩ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit))
  have h2 : trF (L := D.P.L) (fun _ : PUnit => D.xK χ) (fun _ => -1) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (fun _ => J (𝟙 _ ≫ D.xK χ)) j =
        (gm (jK R ≫ (D.c χ).left) ξ _ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, hx]
  refine ⟨u⁻¹, t.trans ?_⟩
  rw [h2, map_inv]
  congr 2
  exact Units.ext hu

theorem val_int {A : Over (Spec (CommRingCat.of R))} {L : LB A.left} (ξ : Spec (CommRingCat.of (FractionRing R)))
    {J : ((Spec (CommRingCat.of (FractionRing R))) ⟶ A.left) → L.ι}
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)))
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (p : Spec (CommRingCat.of R) ⟶ Y) (hp : ∀ k, (p ≫ φ k) ≫ A.hom = 𝟙 _) :
    ∃ w : Rˣ, val t (jK R ≫ p) ξ J = Units.map (cst ξ).toMonoidHom w := by
  obtain ⟨w, hw⟩ := unit_gm' ξ p (LB.wchart L φ (fun k => J ((jK R ≫ p) ≫ φ k)))
    (Set.mem_iInter.2 fun k => by
      have := hJc (p ≫ φ k) (hp k)
      rw [← Category.assoc] at this
      exact this) (t.s _)
  exact ⟨w, Units.ext hw⟩

theorem toUnit_left : (toUnit (TK R)).left = jK R := by
  simpa using Over.w (toUnit (TK R))

theorem gm_rigK (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D η[D.P.A] (j PUnit.unit))
    (hm : ξ ∈ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j) :
    ∃ w : Rˣ, gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j) (D.rigK.s j) =
      Units.map (cst ξ).toMonoidHom w := by
  have e1 := gm_res (𝟙 _) ξ (show LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j ≤
      (toUnit (TK R)).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j from
      fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) hm
    (pullU (toUnit (TK R)).left _ (D.rig.s j))
  have e2 := gm_pull (𝟙 _) (toUnit (TK R)).left ξ (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) (D.rig.s j)
  have e3 : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
  rw [e3] at e2
  obtain ⟨w, hw⟩ := unit_gm' ξ (𝟙 _) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j)
    (Set.mem_iInter.2 fun _ => hj trivial) (D.rig.s j)
  exact ⟨w, (e1.trans e2).trans (Units.ext hw)⟩

theorem alg {G : Type} [CommGroup G] (T G1 G2 G3 c1 c2 c3 c4 c5 c6 c7 Vab Va Vb Vr Vu Kr : G)
    (h1 : T = G1 * G2⁻¹ * G3⁻¹ * c4⁻¹) (h2 : Vab = c1 * G1) (h3 : Va = c2 * G2) (h4 : Vb = c3 * G3)
    (h7 : Vr = c5) (h8 : Vu = c6)
    (h5 : Vab * Va⁻¹ * Vb⁻¹ * Vr⁻¹ * Vu = Va * Vr) (h6 : Va = c7 * Kr) :
    Kr = c1 * c2⁻¹ * c3⁻¹ * c4 * c5⁻¹ * c5⁻¹ * c6 * c7⁻¹ * T := by
  subst h1 h2 h4 h3 h7 h8
  have hK : Kr = c7⁻¹ * (c2 * G2) := by rw [h6]; group
  subst hK
  apply Additive.ofMul.injective
  have h5' := congrArg Additive.ofMul h5
  simp only [ofMul_mul, ofMul_inv] at h5' ⊢
  rw [← sub_eq_zero] at h5' ⊢
  refine Eq.trans ?_ (congrArg Neg.neg h5' |>.trans neg_zero)
  abel

theorem final (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) (h0 : r ≠ 0) (X : (FractionRing R)ˣ) (c : Rˣ)
    (key : Units.map (kst ξ).toMonoidHom (toUnitK r h0) =
      Units.map (cst ξ).toMonoidHom c * Units.map (kst ξ).toMonoidHom X) :
    algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (c : R) * (X : FractionRing R) := by
  have k3 : toUnitK r h0 = Units.map (algebraMap R (FractionRing R)).toMonoidHom c * X := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    rw [key, map_mul]
    rfl
  exact congrArg Units.val k3

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D.X] (oa : D.OAct O) (w0 : O), TraceFormTwistIso D oa w0 → ∀ (y : D.X) (r : R) (x : (FractionRing R)ˣ),
    PsiCoord D y r → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D y (w0 • y) x →
    ∃ u : Rˣ, algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u : R) * (x : FractionRing R) := by
  intro R _ _ _ D O _ _ _ oa w0 hW y r x hr hx
  obtain ⟨u, -, -, hrel⟩ := hW
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := Units.map (cst ξ).toMonoidHom
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom

  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hrel y) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [val_pull hJ] at e
  have e' := (congrArg (· * val u (𝟙 _ ≫ D.xK y) ξ J) (PeriodBalance.val_tau D ξ hJ y (w0 • y))).symm.trans e
  obtain ⟨c6, h6⟩ : ∃ w : Rˣ, val u (𝟙 _ ≫ D.xK y) ξ J = cU w := by
    have : 𝟙 _ ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact DVR.QForm.ptK_eq D y
    rw [this]
    refine val_int ξ hJc u (D.c y).left fun k => ?_
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A, (![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left,
        (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left] : Fin 4 → _) k = q.left := by
      fin_cases k
      · exact ⟨_, rfl⟩
      · exact ⟨𝟙 _, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    rw [hq, Category.assoc, Over.w q, Over.w]; rfl
  obtain ⟨c5, h5⟩ : ∃ w : Rˣ, val D.rigK (𝟙 _) ξ J = cU w := by
    unfold DegPre.rigK
    rw [val_pull hJ]
    have : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
    rw [this]
    exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]

  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau y (w0 • y)) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau y (w0 • y)).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc (y + w0 • y) _ i1 (mem_inl (mem_inl (mem_inl hm)))
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc y _ i2 (mem_inr (mem_inl (mem_inl hm)))
  obtain ⟨c3, g3⟩ := val_psi_chart D ξ hJ hJc (w0 • y) _ i3 (mem_inr (mem_inl hm))
  obtain ⟨c4, g4⟩ := gm_rigK D ξ _ i4 (mem_inr hm)

  have h0 := PsiCoordLocal.ne_zero_of_coord hr
  obtain ⟨jp, hp, ip, ep⟩ := GlobalTheory.PeriodFormCompare.isPsiCoord_toUnitK hr h0
  obtain ⟨c7, g7⟩ := val_psi_chart D ξ hJ hJc y jp ip (hp trivial)
  have eP := gm_genVal ξ (D.psi y) jp hp
  rw [← ep] at eP
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau y (w0 • y)).s j) =
      kU (genVal (D.tau y (w0 • y)) j h) := Units.ext eT
  have eP' : gm (𝟙 _) ξ (LB.wchart D.P.L _ jp) ((D.psi y).s jp) = kU (toUnitK r h0) := Units.ext eP
  have key := alg (h1 := eT'.symm.trans (dT.trans (by rw [g4]))) (h2 := g1) (h3 := g2) (h4 := g3) (h7 := h5)
    (h8 := h6) (h5 := e') (h6 := g7.trans (congrArg (cU c7 * ·) eP'))
  refine ⟨c1 * c2⁻¹ * c3⁻¹ * c4 * c5⁻¹ * c5⁻¹ * c6 * c7⁻¹, final ξ r h0 _ _ (key.trans ?_)⟩
  simp only [cU, kU, map_mul, map_inv]

end GlobalTheory.PsiTauCoordRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcIntegral
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcChartExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabMap_cast_φ {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f₁ f₂ : S' ⟶ S} (h : f₁ = f₂)
    (n : SABMap t' t f₁) : (h ▸ n).φ = n.φ := by
  subst h; rfl

theorem exists_sab_cancel_id {S S' : Scheme.{0}} {t : SAB H S} {t' t'' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t f) : ∃ m' : SABMap t'' t' (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ n)
  exact ⟨m', (sabMap_cast_φ (Category.id_comp f).symm n).symm.trans hm'⟩

end GlobalTheory.ArcChartExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackStalkIsDomainEtale
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGeneric

theorem mem_of_dense_of_maximal {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X] {x : X}
    (hx : ∀ y, y ⤳ x → x ⤳ y) {U : Set X} (hU : IsOpen U) (hd : Dense U) : x ∈ U := by
  obtain ⟨o, ho, hne, hs⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
    (irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨y, hyo, hyU⟩ := hd.inter_open_nonempty o ho hne
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
  have e := hx ξ (hξ.specializes mem_irreducibleComponent)
  exact (e.trans (hξ.specializes (hs hyo))).mem_open hU hyU

end GlobalTheory.TraitGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadOfPolarizedFiber
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolNearAmple

theorem relAmple_near_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (t : SAB H (Sp R)), IsProper t.G.hom → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ s : R, g s ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (h : R →+* R'), IsUnit (h s) → ∀ (t' : SAB H (Sp R')), SABMap t' t (spMap h) → RelAmple t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ t hprop C _ g hpol
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    exact {
      cover := top_le_iff.1 fun y _ => by
        obtain ⟨i, hi⟩ := exists_chart hL (F y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
      g_self := fun J => unit_ext fun y hy => by
        rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
        exact gm_self hL _ y (mem_pull.1 hy)
      cocycle := fun I J K => unit_ext fun y hy => by
        rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy,
          gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
          gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
        exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2) }
  have : Smooth t.G.hom := t.semi.smooth
  have : Flat t.G.hom := inferInstance
  have hL := t.PP.isLB
  let p : Ideal R := RingHom.ker g
  haveI : p.IsPrime := RingHom.ker_isPrime g
  let g₀ := algebraMap R p.ResidueField
  have hf₂ : p.primeCompl ≤ (IsUnit.submonoid C).comap g := fun x hx =>
    show IsUnit (g x) from isUnit_iff_ne_zero.2 fun h0 => hx (RingHom.mem_ker.2 h0)
  let i : p.ResidueField →+* C := Ideal.ResidueField.lift p g le_rfl hf₂
  have hcomp : i.comp g₀ = g := RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap p g le_rfl hf₂ r
  have hsp : spMap i ≫ spMap g₀ = spMap g := by
    rw [← hcomp]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ : IsPullback (pullback.fst t.G.hom (spMap g)) (pullback.snd t.G.hom (spMap g)) t.G.hom
      (spMap i ≫ spMap g₀) := by
    rw [hsp]; exact IsPullback.of_hasPullback _ _
  have hA₁ : RelAmple ((Over.pullback (spMap g₀)).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom (spMap g₀))) :=
    FibreAmple.relAmple_of_fieldExtension (f := t.G.hom) hL i (IsPullback.of_hasPullback t.G.hom (spMap g₀)) h₂
      (pull_isLB hL _) (GlobalTheory.lbIso_refl (pull_isLB hL _)) hpol.2.1
  obtain ⟨s, hs, hAs⟩ := ProperFinite.relAmple_near_fibre t.G hL g₀ (FibreAmple.residueField_fraction p) hA₁
  refine ⟨s, fun h0 => hs (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 h0)), ?_⟩
  intro R' _ h hu t' m
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen s
  have : IsAffine D.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) s
  have hrange : Set.range (spMap h) ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show s ∉ Ideal.comap h y.asIdeal
    exact fun hy => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy hu)
  let u : Sp R' ⟶ D.toScheme := IsOpenImmersion.lift D.ι (spMap h) hrange
  have hu' : u ≫ D.ι = spMap h := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ, Hp⟩ := FibreAmple.exists_isPullback (IsPullback.of_hasPullback t.G.hom D.ι) m.cart.1 u hu'
  have e₀ : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
    exact ⟨w, (isGen_iff w).2 hw⟩
  obtain ⟨w, hw⟩ : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom D.ι)).pull φ) :=
    LBIso.trans t'.PP.isLB (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) e₀
      (FibreAmple.lbIso_pull_comp hφ (GlobalTheory.lbIso_refl (pull_isLB hL _)))
  exact relAmple_pull (A := (Over.pullback D.ι).obj t.G) (A' := t'.G) Hp (pull_isLB hL _) t'.PP.isLB
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hAs

end GlobalTheory.PolNearAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidifiedSymmetricLineBundleGroupPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  first | exact @GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull | exact GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull | (intros; apply GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelChain
section
namespace GlobalTheory.SiegelChain

theorem siegel_chain : ∀ {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ}, GlobalTheory.RedTh.IsSiegel d u →
    ∀ (m : ℕ) (i j : Fin n), (↑j : ℕ) = (↑i : ℕ) + m → d i ≤ (4 : ℝ) ^ m * d j := by
  intro n d u h m
  induction m with
  | zero =>
    intro i j hij
    have : i = j := Fin.ext (by simpa using hij.symm)
    subst this
    simp
  | succ m ih =>
    intro i j hij
    have hk : (i : ℕ) + m < n := by have := j.isLt; omega
    let k : Fin n := ⟨(i : ℕ) + m, hk⟩
    have h1 : d i ≤ 4 ^ m * d k := ih i k rfl
    have h2 : d k ≤ 4 * d j := h.step k j (by simp [k]; omega)
    have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
    calc d i ≤ 4 ^ m * d k := h1
      _ ≤ 4 ^ m * (4 * d j) := mul_le_mul_of_nonneg_left h2 h4
      _ = 4 ^ (m + 1) * d j := by ring

end GlobalTheory.SiegelChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelUnipotentInverseEntriesBounded
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem siegel_unipotent_inv_bounded : ∀ n : ℕ, ∃ c : ℝ, ∀ u : Matrix (Fin n) (Fin n) ℝ, (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ i j, i < j → |u i j| ≤ 1 / 2) → ∃ v : Matrix (Fin n) (Fin n) ℝ, v * u = 1 ∧ u * v = 1 ∧ (∀ i j, j < i → v i j = 0) ∧ ∀ i j, |v i j| ≤ c := by
  intro n
  refine ⟨(Nat.factorial n : ℝ), ?_⟩
  intro u hdiag hlow hup
  have hbt : u.BlockTriangular id := fun i j hij => hlow i j hij
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    simp [hdiag]
  have hunit : IsUnit u.det := by rw [hdet]; exact isUnit_one
  refine ⟨u⁻¹, Matrix.nonsing_inv_mul u hunit, Matrix.mul_nonsing_inv u hunit, ?_, ?_⟩
  · intro i j hij
    letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit
    exact Matrix.blockTriangular_inv_of_blockTriangular hbt hij
  · intro i j
    have hinv : u⁻¹ = u.adjugate := by
      rw [Matrix.inv_def, hdet]; simp
    rw [hinv, Matrix.adjugate_apply]
    have hb : ∀ a b, |(u.updateRow j (Pi.single i 1)) a b| ≤ 1 := by
      intro a b
      by_cases ha : a = j
      · subst ha
        rw [Matrix.updateRow_self]
        by_cases hb : b = i
        · subst hb; simp
        · simp [Pi.single_apply, hb]
      · rw [Matrix.updateRow_ne ha]
        rcases lt_trichotomy a b with h | h | h
        · linarith [hup a b h]
        · subst h; simp [hdiag]
        · simp [hlow a b h]
    have := Matrix.det_le (abv := AbsoluteValue.abs) hb
    simpa using this

end GlobalTheory
end

