module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbPartActIsAdj
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Vert GlobalTheory.LocM
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LocM

open ReciprocityTheory.ChartRestriction.G.Out (RosatiAdj rosatiφ rosatiε)
open GlobalTheory.CechPic

theorem abPartAct_isAdj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (t : SAB H (Sp R)) (U : PELUnif I t) :
    GlobalTheory.HermTensor.IsAdj (abPartAct U) U.D.toPre.P.L := by
  intro c
  have hr : RosatiAdj U.D.toPre.P.A U.D.toPre.P.L ((abPartAct U).act c) ((abPartAct U).act (star c)) := by
    have h : RosatiAdj U.D.toPre.P.A U.D.toPre.P.L ((abPartAct U).act c) ((abPartAct U).act (H.bar c)) := by
      letI := H.starRing
      exact U.oD.onB.rosati c
    rw [← bar_eq_star H]
    exact h
  obtain ⟨V, hV, g, hg⟩ := hr (IsLocalRing.closedPoint R)
  obtain rfl : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hV
  have hL : U.D.toPre.P.L.IsLB := U.D.toPre.P.isLB
  have hgen : ∃ u : LB.Gen (LB.LinComb U.D.toPre.P.L
      (rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c))) rosatiε), u.IsGen := by
    have e : rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c)) = fun i =>
        (U.D.toPre.P.A ⊗ U.D.toPre.P.A).left.topIso.inv ≫ ((U.D.toPre.P.A ⊗ U.D.toPre.P.A).hom ⁻¹ᵁ ⊤).ι ≫
          rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c)) i :=
      funext fun i => ((U.D.toPre.P.A ⊗ U.D.toPre.P.A).left.topIso.inv_hom_id_assoc _).symm
    rw [e]
    exact ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hg _⟩
  obtain ⟨u, hu⟩ := hgen
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨u, hu⟩
  rw [cls_linComb hL, Fin.sum_univ_six] at h0
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1 ?_
  refine (cls_cube_two hL _ _ _).trans (Eq.trans ?_ (cls_cube_two hL _ _ _).symm)
  have pm : ∀ a b : U.D.toPre.P.A ⊗ U.D.toPre.P.A ⟶ U.D.toPre.P.A, padd U.D.toPre.P.A a b = a * b := fun _ _ => rfl
  simp only [rosatiφ, rosatiε, lam, pm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons,
    one_smul, neg_smul, Fin.isValue] at h0 ⊢
  rw [← sub_eq_zero, ← h0]
  abel

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLatticesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt p0 t S' N h
  exact GlobalTheory.Mem.R3.Rw.Up.rows_up K B f T w Z Wt p0 t S' N h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllStepsHoldOfHasDR
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.LieMet GlobalTheory.LocM.FrameBC

namespace GlobalTheory.LocM.StepOfFrame

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

end GlobalTheory.LocM.StepOfFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmChern

theorem antisymm_eq_chernRoots_mul_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ), ∃ R : MvPolynomial (ι × ℕ) ℝ, antisymm Q = chernRoots m R * rootDiscr m := by
  intro ι _ m Q
  classical
  obtain ⟨S, hS⟩ : rootDiscr m ∣ antisymm Q := GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd ι m (antisymm Q) fun τ i j hij =>
    _root_.GlobalTheory.swap_odd_dvd (⟨τ, i⟩ : Root m) ⟨τ, j⟩ (by simp [hij.ne]) _ (_root_.GlobalTheory.AntisymmSwap.rename_swap_antisymm ι m Q τ i j hij.ne)
  have hsym : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S := by
    intro w
    have h1 := _root_.GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight ι m Q w
    rw [hS, map_mul, _root_.GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr ι m w, smul_mul_assoc] at h1
    have hs : ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) ≠ 0 := Units.ne_zero _
    exact mul_left_cancel₀ (_root_.GlobalTheory.GoodMetric.rootDiscr_ne_zero ι m) (smul_right_injective _ hs h1)
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric ι m S hsym
  exact ⟨R, by rw [hS, hR, mul_comm]⟩

end GlobalTheory.AntisymmChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLEEqIffStalk
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtBC

theorem appLE_eq_iff_stalk {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {V : X.Opens} (hV : ∀ y, F y ∈ V) (s : ∀ j, Γ(X, V ⊓ L.U j)) (s' : L'.Sec) :
    (∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ (V ⊓ L.U (j PUnit.unit))),
      (F.appLE _ _ hle).hom (s (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i)) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ (V ⊓ L.U j) := fun y hy => ⟨hV y, mem_pull.1 hy.1⟩
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit _ y _ hy _).symm

theorem mem_of_comm {X X' T T' : Scheme.{0}} {F : X' ⟶ X} {π : X ⟶ T} {π' : X' ⟶ T'} {z : T' ⟶ T}
    (e : F ≫ π = π' ≫ z) {U : T.Opens} (hz : ⊤ ≤ z ⁻¹ᵁ U) (y : X') : F y ∈ π ⁻¹ᵁ U := by
  show π (F y) ∈ U
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hz (Set.mem_univ _)

theorem spMap_comp₀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {M : GChart Y} {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {z : Sp R ⟶ Y.X} {hz : ⊤ ≤ z ⁻¹ᵁ M.U}
  {x : KeyIn R} {x' : KeyIn R'}

theorem keyAt_of_keyPB (h : KeyAt M z hz x) (h' : KeyPB x' x f) :
    KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x' := by
  obtain ⟨φ, he, w, hg, hp, hw, hr, hs, hv⟩ := h
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := h'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x.P.isLB w w' g g' Y.t.PP.isLB x'.P.isLB
  have he'' : eSec x'.P.A ≫ φ' ≫ φ = (spMap f ≫ z) ≫ eSec Y.t.G := by
    rw [← Category.assoc, he', Category.assoc, he, Category.assoc]
  have hF : F' = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [hF']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [hε']
      ext <;> simp [Chart.dualMapR])
  have hq := hp'.comp hp
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, hq, (isGen_iff w'').2 (T.pgen_comp x.P.isLB g g'), ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _
      (rigPull_le φ z he Y.t.PP.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ' (spMap f) he' x.P.L) (fun _ => rfl)).1 hr'
    exact (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
      (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).2
      (T.pmaps_comp x.P.isLB (fun _ => he') r₀ r₁)
  · refine (appLE_eq_iff_stalk w'' (mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ x'.th).2
      fun Z q y j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x.P.isLB (φ' (q y))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.1.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).1 hs' Z q y i k hi hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [← Category.assoc, hv', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
      hF, Category.assoc]
    rfl

theorem keyPB_of_keyAt (h : KeyAt M z hz x) (h' : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x') :
    KeyPB x' x f := by
  obtain ⟨φ, he, w, hg, hc, hw, hr, hs, hv⟩ := h
  obtain ⟨φ'', he'', w'', hg'', hc'', hw'', hr'', hs'', hv''⟩ := h'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x'.P.A.left ⟶ x.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x.P.A.hom = x'.P.A.hom ≫ spMap f :=
    ⟨hp.lift φ'' (x'.P.A.hom ≫ spMap f) (by rw [hc''.1.w, Category.assoc]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x'.P.A ≫ φ' = spMap f ≫ eSec x.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', Category.assoc, Category.assoc, he]
    · have a₁ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      have a₂ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := Over.w η[x.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel Y.t.PP.isLB w w'' g g'' x.P.isLB x'.P.isLB
  have r := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _ (rigPull_le φ z he Y.t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
    (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).1 hr''
  refine ⟨φ', he', w', hg''.trans hg.symm, Chart.dualMapR f, hc.cancel hc'' hw0,
    (isGen_iff w').2 (T.pgen_cancel Y.t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ' (spMap f) he' x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel Y.t.PP.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).2 fun Z q y i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (φ (φ' (q y)))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (appLE_eq_iff_stalk w'' (mem_of_comm hc''.1.w (le_preimage_comp _ hz)) M.θ x'.th).1 hs'' Z q y j k hj hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
        Category.assoc]
      rfl
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyAtBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLESpMapFromSpec
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb

namespace GlobalTheory.FlagEmb.CellOpen

variable {O : Type} [CommRing O] {X P : Scheme.{0}} {N : ℕ} {k : Type} [Field k]

theorem top_le_of_mem {W : (Sp k).Opens} {x : Sp k} (hx : x ∈ W) : ⊤ ≤ W := fun y _ => by
  have : y = x := Subsingleton.elim (α := PrimeSpectrum k) y x
  exact this ▸ hx

theorem mem_basicOpen_fnOn (x : Sp k) (a : k) : x ∈ (Sp k).basicOpen (fnOn ⊤ a) ↔ a ≠ 0 := by
  rw [basicOpen_fnOn, top_inf_eq, mem_spOpen]
  have : x.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum k) x ⊥)
  rw [this, Ideal.mem_bot]

theorem appLE_spMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) {A : Type} [CommRing A] (φ : Γ(X, U) →+* A)
    {x : Sp A ⟶ X} (hx : x = spMap φ ≫ hU.fromSpec) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    (x.appLE U ⊤ h).hom a = fnOn ⊤ (φ a) := by
  subst hx
  have e := appLE_appLE (spMap φ) hU.fromSpec hU.fromSpec_preimage_self.ge (le_rfl : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) a
  refine e.symm.trans ?_
  rw [fromSpec_appLE_self]
  have e2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (R := Γ(X, U)) (S := .of A) (CommRingCat.ofHom φ))
  refine Eq.trans ?_ (congrArg (resG (Sp A) (le_top : (⊤ : (Sp A).Opens) ≤ ⊤)) e2.symm)
  rfl

def sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) (r : Fin (N + 1)) :
    Γ(P, p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r) :=
  ∑ q, (p0.appLE U _ inf_le_left).hom (a q) * pullRatio g _ r inf_le_right q

theorem appLE_sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U) (a : Fin (N + 1) → Γ(X, U))
    (r : Fin (N + 1)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)) :
    v r ≠ 0 ∧ (z.appLE _ ⊤ h).hom (sec p0 g U a r) = fnOn ⊤ ((∑ q, φ (a q) * v q) / v r) := open MvPolynomial GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjFrac in by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := O)
  have pre : pt b v hv ⁻¹ᵁ chart O N r = spOpen (v r) := by
    change ProjPoint.ofHom (grading O N) (eval₂Hom b v) (map_irrelevant_eval₂Hom b hv) ⁻¹ᵁ
      Proj.basicOpen (grading O N) (MvPolynomial.X r) = _
    rw [ProjPoint.ofHom_preimage_basicOpen _ _ _ one_pos (isHomogeneous_X O r), eval₂Hom_X']
    rfl
  have from_chart : (isAffineOpen_chart O N r).fromSpec =
      Spec.map (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos := by
    rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
    refine (Category.id_comp _).symm.trans (congrArg (· ≫ _) ?_)
    exact (Proj.basicOpenIsoSpec (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).hom_inv_id.symm
  have away_ratio (q : Fin (N + 1)) :
      (Proj.awayToSection (grading O N) (MvPolynomial.X r)).hom (ratioAway O N r q) = ratio O N r q := by
    rw [ratioAway, awayToSection_mk]
    exact frac_eq (by ring)
  have h2 : ⊤ ≤ pt b v hv ⁻¹ᵁ chart O N r := hz ▸ h.trans (z.preimage_mono inf_le_right)
  have hr : v r ≠ 0 := by
    have := h2 (Set.mem_univ (IsLocalRing.closedPoint k))
    rw [pre] at this
    intro e
    exact (mem_spOpen.1 this) (e ▸ zero_mem _)
  have ratio_mul (q : Fin (N + 1)) :
      pullRatio (pt b v hv) ⊤ r h2 q * fnOn ⊤ (v r) = fnOn ⊤ (v q) := by
    have hu' : IsUnit (eval₂Hom b v (MvPolynomial.X r)) := by rw [eval₂Hom_X']; exact IsUnit.mk0 _ hr
    have h4 := ProjPoint.awayLift_mk_mul (grading O N) (eval₂Hom b v) hu' (X_mem O N r) 1 (MvPolynomial.X q) (X_mem O N q)
    have he : pt b v hv = spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫ _ :=
      ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem O N r) hu'
    have : IsIso (Proj.awayToSection (grading O N) (MvPolynomial.X r)) :=
      (Proj.basicOpenIsoAway (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).isIso_hom
    have he2 : spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos =
        ofChartHom r (inv (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
          CommRingCat.ofHom (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
          (Scheme.ΓSpecIso (.of k)).inv) := by
      rw [ofChartHom, from_chart, ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
    rw [pullRatio_of_eq he h2 (he ▸ h2), pullRatio_of_eq he2 _ (ofChartHom_preimage _ _),
      pullRatio, ofChartHom_appLE, ← away_ratio, ← CommRingCat.comp_apply, IsIso.hom_inv_id_assoc,
      ]
    change (Scheme.ΓSpecIso (.of k)).inv.hom
      (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu' (ratioAway O N r q)) * _ = _
    rw [← resG_self (X := Sp k) le_top ((Scheme.ΓSpecIso (.of k)).inv.hom _)]
    change fnOn ⊤ _ * fnOn ⊤ _ = fnOn ⊤ _
    rw [← map_mul]
    exact congrArg _ (by simpa only [ratioAway, eval₂Hom_X', pow_one] using h4)
  refine ⟨hr, ((IsUnit.mk0 _ hr).map (fnOn ⊤)).mul_right_cancel ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_mul, div_mul_cancel₀ _ hr, sec, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, map_mul, appLE_appLE, appLE_spMap_fromSpec hU φ hφ, appLE_pullRatio, pullRatio_of_eq hz _ h2, mul_assoc,
    ratio_mul]

def linOpen (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) : P.Opens :=
  ⨆ r, P.basicOpen (sec p0 g U a r)

theorem mem_linOpen_iff (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Fin (N + 1) → Γ(X, U)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (x : Sp k) :
    z x ∈ linOpen p0 g U a ↔ ∑ q, φ (a q) * v q ≠ 0 := by
  have key : ∀ r (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)),
      z x ∈ P.basicOpen (sec p0 g U a r) ↔ ∑ q, φ (a q) * v q ≠ 0 := fun r h => by
    obtain ⟨hr, e⟩ := appLE_sec p0 g hU a r z φ hφ b v hv hz h
    have e2 := Scheme.basicOpen_appLE z ⊤ _ h (sec p0 g U a r)
    rw [top_inf_eq] at e2
    refine (iff_of_eq (congrArg (x ∈ ·) e2)).symm.trans ?_
    refine (iff_of_eq (congrArg (fun t => x ∈ (Sp k).basicOpen t) e)).trans ?_
    rw [mem_basicOpen_fnOn, div_ne_zero_iff, and_iff_left hr]
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := Opens.mem_iSup.1 hx
    exact (key r (top_le_of_mem (x := x) (P.basicOpen_le _ hr))).1 hr
  · intro hx
    obtain ⟨r, hr⟩ := exists_mem_chart O N (g (z x))
    refine Opens.mem_iSup.2 ⟨r, (key r (top_le_of_mem (x := x) ⟨?_, hr⟩)).2 hx⟩
    change x ∈ (z ≫ p0) ⁻¹ᵁ U
    rw [hφ, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    trivial

theorem exists_isCellOpen (O : Type) [CommRing O] (X P : Scheme.{0}) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ)
    (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (U : X.affineOpens)
    (D : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) : ∃ W : P.Opens, IsCellOpen p0 p U D w W := by
  let F : (Σ τ : T, Fin (m τ + 1)) → P.Opens := fun i =>
    linOpen p0 (p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))) U.1 (lform D (wLet w ∘ std i.1 i.2 (Nat.le_of_lt_succ i.2.2)))
  refine ⟨p0 ⁻¹ᵁ U.1 ⊓ ⟨⋂ i, (F i : Set P), isOpen_iInter_of_finite fun i => (F i).2⟩, fun k _ z => ⟨fun h => ?_, ?_⟩⟩
  · have h1 : Set.range (z ≫ p0) ⊆ Set.range U.2.fromSpec := by
      rw [U.2.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact (h ⟨x, rfl⟩).1
    have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    let l := IsOpenImmersion.lift U.2.fromSpec (z ≫ p0) h1
    have hφ : z ≫ p0 = spMap (Spec.preimage l).hom ≫ U.2.fromSpec :=
      (IsOpenImmersion.lift_fac _ _ h1).symm.trans (congrArg (· ≫ _) (Spec.map_preimage l).symm)
    refine ⟨(Spec.preimage l).hom, hφ, fun τ j hj b v hv hz => ?_⟩
    refine (mem_linOpen_iff p0 _ U.2 _ z _ hφ b v hv hz (IsLocalRing.closedPoint k)).1 ?_
    exact Set.mem_iInter.1 (h ⟨_, rfl⟩).2 ⟨τ, j, Nat.lt_succ_of_le hj⟩
  · rintro ⟨φ, hφ, H⟩ _ ⟨x, rfl⟩
    refine ⟨?_, Set.mem_iInter.2 fun i => ?_⟩
    · change x ∈ (z ≫ p0) ⁻¹ᵁ U.1
      rw [hφ, Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_self]
      trivial
    · let y := z ≫ p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))
      obtain ⟨v, hv, e⟩ := exists_eq_pt (Spec.preimage (y ≫ PSpace.str _ _)).hom y (Spec.map_preimage _).symm
      exact (mem_linOpen_iff p0 _ U.2 _ z φ hφ _ v hv e x).2 (H _ _ _ _ v hv e)

end GlobalTheory.FlagEmb.CellOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatLIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem atDat_lIntegral : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => z.R.toRealDat.LIntegral := fun _ _ _ =>
  StepW.of_all fun _ _ _ _ _ _ _ _ _ _ _ z _ _ _ hG i =>
    ⟨z.geo.fw.ks i, GlobalTheory.GoodLat.mkFull_of_tie z.geo.fw hG.latFull i,
      GlobalTheory.RealGeoIn.mkStable_of_rhoGeo z.geo.fw z.geo.pins z.geo.rhoGeo i⟩

end GlobalTheory.Mem.Top.Bl
end

