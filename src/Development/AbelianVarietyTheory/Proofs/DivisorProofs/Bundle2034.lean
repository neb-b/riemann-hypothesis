module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitMulClauseOfGeneratesIffNonzero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsUniqueSecIsFnAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0614
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroFibresUnitMultipleThetaSeries
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven.ThetaNorm

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (σ : U.LG.L.Sec) (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), NzFib σ → (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) → (∀ e, U.ExpandsAt e 1 σ₁ f) → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (ϑ : Fam D.toPre C 1) (c : C), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1) → ν.FamV ϑ (c • N.vth) → ‖c‖ = 1 := by
  intro V _ _ _ _ hc D A G _ _ hG U σ σ₁ f hNz hch hE C _ _ _ _ _ _ hC N ν hI ϑ c hϑ hV
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hL4 : Laws4 := GlobalTheory.allSixLaws.2.2.2.1
  have hS : SecBaseChangeSt := hL.secBaseChange
  have h1 : ReciprocityTheory.ChartRestriction.G.DVR.NonzeroOnSpecial U σ₁ := by
    obtain ⟨z, hz, hzn⟩ := hNz (IsLocalRing.closedPoint V)
    refine GlobalTheory.ThetaUnit.nonzeroOnSpecial_of_mem U σ₁ z hz ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hzn
    have hle : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i :=
      fun y hy => Set.mem_iInter.1 hy 0
    have hzi : z ∈ U.LG.L.U i := G.left.basicOpen_le _ hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
    rw [hch i hle]
    change z ∈ G.left.basicOpen ((G.left.presheaf.map (homOfLE hle).op) (σ.f i))
    rw [Scheme.basicOpen_res]
    exact ⟨fun _ ⟨k, hk⟩ => hk ▸ hzi, hi⟩
  have hCL : CLND V := (GlobalTheory.ThetaCompare.clnd_iff_of_dvr V).2 hc
  obtain ⟨f', hf', hgen'⟩ := ReciprocityTheory.ChartRestriction.G.DVR.isTheta_of_nonzeroOnSpecial' hL hL4 hCL rfl U σ₁ h1 0
  have hgen := GlobalTheory.ThetaCompare.secBGenerates_of_expandsAt hS le_rfl U.toUnifPre hf' (hE 0) hgen'
  obtain ⟨g, hg⟩ := GlobalTheory.ThetaCompare.exists_corr_right D.toPre ν.th
  have hgg := (GlobalTheory.ThetaCompare.generates_iff_secBGenerates hS hg).1 (fun s => ν.th_gen s)
  have hgs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul (g : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgg
  have hfs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul ((f 0 : D.toPre.SecB 1 0) : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgen
  obtain ⟨u, hu⟩ := (GlobalTheory.ThetaCompare.generates_iff_unit_smul (fun s => (hgs s).exists) _).1 (fun s => (hfs s).exists)
  have hum : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul D.toPre.P.A.hom (u : V) (f 0) g :=
    (GlobalTheory.ThetaUnit.secIsMul_iff _ _ _ _).2 hu

  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := GlobalTheory.Ex.FamVal.good ν z
  have hcst : ∀ a : C, cst (𝟙 (Sp C)) z a = toStk z a := fun a => by
    rw [cst, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq _ _ ⊤ trivial, toStk]
    rfl
  have hc0 : N.c 0 = 1 := by
    have h := N.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hx : ∀ x, c * N.th x * ν.rg = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) * (N.th x * ν.rg) := by
    intro x
    have H := (GlobalTheory.Ex.FamVal.famV_iff ν z ϑ _).1 hV 0 x
    have e1 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal (hϑ 0) (GlobalTheory.Ex.FamVal.pt ν x).left z hJ
    have e2 := GlobalTheory.IndivisibleSection.sval_of_secIsMul hum
      ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e3 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal hg ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e4 : toStk z (N.th x * ν.rg) = sval ν.th (ν.eA x).left z ν.J :=
      (congrArg (toStk z) (ν.th_eq x)).trans (GlobalTheory.Ex.FamVal.toStk_sF hJ _ _)
    have ep : (GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left = (ν.eA x).left := by
      rw [← Over.comp_left, lift_snd]
    rw [map_zero] at H
    rw [Category.comp_id, ep, ← e4] at e3
    rw [ep] at e2
    rw [e1, ep, e2, ← e3] at H
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, pow_one] at H
    have ec : cst ((ν.eA x).left ≫ D.toPre.P.A.hom) z (u : V) =
        toStk z (algebraMap (FractionRing V) C (algebraMap V _ (u : V))) := by
      have ew : (ν.eA x).left ≫ D.toPre.P.A.hom =
          (𝟙 (Sp C) ≫ spMap (algebraMap (FractionRing V) C)) ≫ spMap (algebraMap V (FractionRing V)) := by
        rw [Category.id_comp]; exact Over.w (ν.eA x)
      rw [ew, cst_comp, cst_comp, hcst]
    have ev : N.vth 0 x = N.th x := by
      simp [NumD.vth, N.ψ_zero, hc0]
    rw [ev, ← GlobalTheory.Ex.FamVal.rg_eq, ec, ← map_mul, ← map_mul] at H
    exact (toStk z).injective H
  have hL2 : Laws2 := GlobalTheory.abelianSchemeLaws_all.2
  have hB := GlobalTheory.Ex.brFam hL hL2 V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨x, hx0⟩ : ∃ x, N.th x ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨s, f0, hf0, hne⟩ := hB.2.2.2.1
    obtain ⟨c', hc'⟩ := hB.2.2.2.2.1 s f0 hf0
    refine hne ?_
    rw [hc']
    funext α y
    simp [NumD.vth, hno]
  have hcu : c = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) := by
    have h := hx x
    rw [_root_.mul_assoc] at h
    exact mul_right_cancel₀ (mul_ne_zero hx0 (GlobalTheory.Ex.FamVal.rg_ne ν)) h
  have n1 := hC.1 (u : V)
  have n2 := hC.1 ((u⁻¹ : Vˣ) : V)
  have hprod : ‖algebraMap (FractionRing V) C (algebraMap V _ (u : V))‖ *
      ‖algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  rw [hcu]
  nlinarith [norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))),
    norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ (u : V)))]

end GlobalTheory.KeyEven.ThetaNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAtFirstOrderOfTangents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TangentFirstOrder

theorem fst_eq_of_tangent : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := by
  intro K C _ _ _ P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
  have key : ∀ {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens) (s : Γ(X, U)),
      (valR y U s).fst = valR (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ y) U s := by
    intro X y U s
    by_cases h : ⊤ ≤ y ⁻¹ᵁ U
    · exact (GlobalTheory.MBLow.BaseChRig.valR_spMap (TrivSqZeroExt.fstHom C C C).toRingHom y h s).symm
    · have h' : ¬ ⊤ ≤ (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ y) ⁻¹ᵁ U :=
        fun h' => h ((GlobalTheory.ArcLie.le_iff_fst y U).2 h')
      unfold valR
      rw [dite_eq_right h, dite_eq_right h']
      rfl
  have sq : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap (dualMap (algebraMap K C)) =
      spMap (algebraMap K C) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    simp [dualMap]
  have e0 : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yv = spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yw := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, hv1, Category.assoc, hw1]
    · rw [Category.assoc, hv2, Category.assoc, hw2, ← Category.assoc, ← Category.assoc, sq, Category.assoc,
        Category.assoc, hv, hw]
  have hU : ⊤ ≤ (spMap (algebraMap K C)) ⁻¹ᵁ (P.L.pull (eSec P.A)).U (fun _ => i₀) :=
    fun q hq => Set.mem_iInter.2 fun _ => hi hq
  have hr : valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ≠ 0 := by
    unfold valR
    rw [dite_eq_left hU]
    exact (((ρ.s fun _ => i₀).isUnit.map _).map _).ne_zero
  have h1 := congrArg TrivSqZeroExt.fst ev
  have h2 := congrArg TrivSqZeroExt.fst ew
  rw [key] at h1 h2
  rw [e0, h2] at h1
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero] at h1
  exact (mul_left_cancel₀ (pow_ne_zero k hr) h1).symm

end GlobalTheory.TangentFirstOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinCombChangeOfCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem valHom_res_pullU_zpow {X Y : Scheme.{0}} {A : Type} [CommRing A] (y : Sp A ⟶ Y) (f : Y ⟶ X)
    (U : X.Opens) {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V) (u : Γ(X, U)ˣ) (n : ℤ) :
    GlobalTheory.ZH.CrdCalc.valHom y V hV ((res e (pullU f U u)) ^ n : Γ(Y, V)ˣ).val = valR (y ≫ f) U (u ^ n).val := by
  rw [← map_zpow, ← map_zpow, ← GlobalTheory.ZH.CrdCalc.valR_eq y V hV]
  have hU : ⊤ ≤ y ⁻¹ᵁ f ⁻¹ᵁ U := hV.trans (y.preimage_mono e)
  refine (GlobalTheory.ZH.CrdCalc.valR_res y e hV _).trans ?_
  exact GlobalTheory.ZH.EvCrd.valR_comp y f U hU _

theorem valR_linComb_sec : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (s.f j) =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (s.f j') := by
  intro X Y L K _ φ ε s A _ y j j' h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y
    (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) hh (s.f j)
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y
    (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') hh (s.f j')
  rw [← e1, ← e2]
  have c := s.compat j j'
  change valR y _ ((Y.presheaf.map _).hom _) = _ * valR y _ ((Y.presheaf.map _).hom _)
  refine (congrArg (valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')) c).trans ?_
  refine (GlobalTheory.ZH.CrdCalc.valR_mul y (LB.wchart L φ j ⊓ LB.wchart L φ j') hh _ _).trans ?_
  congr 1
  refine (GlobalTheory.ZH.CrdCalc.valR_eq y (LB.wchart L φ j ⊓ LB.wchart L φ j') hh _).trans ?_
  dsimp only [LB.LinComb]
  rw [Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := fun q _ =>
    ⟨wchart_top_le L φ j y h k (x := q) trivial, wchart_top_le L φ j' y h' k (x := q) trivial⟩
  unfold trV
  exact valHom_res_pullU_zpow y (φ k) (L.U (j k) ⊓ L.U (j' k)) (V := LB.wchart L φ j ⊓ LB.wchart L φ j') _ hh
    (L.g (j k) (j' k)) (ε k)

end GlobalTheory.MBLow.TanGauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinearRelationLinComb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

theorem valR_secLin : ∀ {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (s₂ : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)),
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c → ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y'),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ₁ j₁ → ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ₂ j₂ →
    valR y (LB.wchart L φ₁ j₁) (s₁.f j₁) = ∑ i, valR y ⊤ (c i) * valR (y ≫ h) (LB.wchart L φ₂ j₂) ((s₂ i).f j₂) := by
  intro X Y Y' L K₁ K₂ _ _ φ₁ ε₁ s₁ φ₂ ε₂ n s₂ h c H j₁ j₂ hc A _ y hy₁ hy₂
  have hy₂' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ₂ k) j₂ :=
    top_le_wchart L _ _ y fun k => by rw [← Category.assoc]; exact wchart_top_le L φ₂ j₂ (y ≫ h) hy₂ k
  have hW : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂) := fun q hq => ⟨hy₁ hq, hy₂' hq⟩
  have a₂ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ₂ j₂ :=
    inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  have e := congrArg (valR y (LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂)) (H j₁ j₂ hc)
  rw [← GlobalTheory.ZH.CrdCalc.valR_res y inf_le_left hW (s₁.f j₁)]
  refine e.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ hW, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← GlobalTheory.ZH.CrdCalc.valR_eq y _ hW, ← GlobalTheory.ZH.CrdCalc.valR_eq y _ hW]
  congr 1
  · exact GlobalTheory.ZH.CrdCalc.valR_res y le_top hW (c i)
  · exact (GlobalTheory.ZH.CrdCalc.valR_res y a₂ hW _).trans
      (GlobalTheory.ZH.EvCrd.valR_comp y h (LB.wchart L φ₂ j₂) (fun q hq => hy₂ hq) _)

end GlobalTheory.MBLow.TanGauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLineBundlePowSeparateFirstJetsOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.MBLow.JetSep

theorem sep : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (N : ℕ), 4 ≤ N → ∀ (i₀ : x.P.L.ι),
    ⊤ ≤ (𝟙 (Sp K) ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U i₀ → ∀ (j₀ : Fin g) (a : K) (c : Fin g → K),
    (∀ s : LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))),
      a * (valR (epsLift (x.v (j₀.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).fst +
        ∑ j, c j * (valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).snd = 0) →
    a = 0 ∧ c = 0 := by
  intro K _ x g hg N hN i₀ hi₀ j₀ a c H
  subst hg
  have := x.P.isAb.comm
  have k₀ : ⊤ ≤ eSec x.P.A ⁻¹ᵁ x.P.L.U i₀ := by simpa using hi₀
  let U' : x.P.A.left.Opens := (lbPow x.P.L N).U fun _ => i₀
  have hU' : ⊤ ≤ eSec x.P.A ⁻¹ᵁ U' :=
    (GlobalTheory.ThetaFn.le_wchart_unique x.P.L (K := PUnit) (eSec x.P.A) (𝟙 _) (fun _ => i₀)).2 (by simpa using k₀)
  let pb : (lbPow x.P.L N).Sec → LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))) := fun s =>
    GlobalTheory.ThetaFn.pullPow x.P.L (K := PUnit) (K' := Fin 1) (snd (baseOver (Sp K)) x.P.A).left
      (Category.comp_id _) (N : ℤ) s
  have hval : ∀ (s : (lbPow x.P.L N).Sec) (w : epsR K ⟶ x.P.A), IsTangent w →
      valR (epsLift w) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀) ((pb s).f fun _ => i₀) =
        valR w.left U' (s.f fun _ => i₀) := by
    intro s w hw
    have h1 : ⊤ ≤ epsLift w ⁻¹ᵁ ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀) := by
      refine (GlobalTheory.ThetaFn.le_wchart_unique x.P.L (K := Fin 1) (epsLift w) _ (fun _ => i₀)).2 ?_
      rw [JetUniq.epsLift_snd]
      exact JetUniq.tan_le hw k₀
    refine (GlobalTheory.HolHom.valR_appLE _ _ _ _ _ _ h1).trans ?_
    rw [JetUniq.epsLift_snd]
    rfl
  have Hs : ∀ s : (lbPow x.P.L N).Sec, a * valR (eSec x.P.A) U' (s.f fun _ => i₀) +
      (valR (tanComb c x.v).left U' (s.f fun _ => i₀)).snd = 0 := by
    intro s
    have e := H (pb s)
    simp only [Fin.cast_eq_self] at e
    rw [hval s _ (x.basis.1 j₀), JetUniq.fst_valR (x.basis.1 j₀) hU'] at e
    rw [JetUniq.snd_valR x.basis.1 (isLieComb_tanComb c x.v) hU']
    refine Eq.trans ?_ e
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hval s _ (x.basis.1 j)]
  obtain ⟨M, sec, hsec⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow GlobalTheory.allSixLaws.1.ample K x.P N hN
  have key : ∀ d : Fin x.P.g → K, d ≠ 0 → ∃ s₀ s₁ : (lbPow x.P.L N).Sec,
      valR (eSec x.P.A) U' (s₀.f fun _ => i₀) ≠ 0 ∧ valR (eSec x.P.A) U' (s₁.f fun _ => i₀) = 0 ∧
      (valR (tanComb d x.v).left U' (s₁.f fun _ => i₀)).snd ≠ 0 := by
    intro d hd
    have hy := isTangent_tanComb K x.P.A _ x.v d x.basis.1
    obtain ⟨s₀, s₁, h0, h1, h2⟩ := Orders.exists_sep sec hsec hy (Orders.tanComb_ne_one x.basis hd) (fun _ => i₀) hU'
    refine ⟨s₀, s₁, ?_, ?_, ?_⟩
    · rwa [Orders.valR_eq _ _ hU']
    · rwa [Orders.valR_eq _ _ hU']
    · rwa [Orders.valR_eq _ _ (Orders.top_le_tangent hy hU')]
  have hc : c = 0 := by
    by_contra hc
    obtain ⟨-, s₁, -, h1, h2⟩ := key c hc
    have e := Hs s₁
    rw [h1, mul_zero, zero_add] at e
    exact h2 e
  refine ⟨?_, hc⟩
  have hd : (Pi.single j₀ 1 : Fin x.P.g → K) ≠ 0 := fun h => by simpa using congrFun h j₀
  obtain ⟨s₀, -, h0, -, -⟩ := key _ hd
  have e := Hs s₀
  subst hc
  rw [JetUniq.snd_valR x.basis.1 (isLieComb_tanComb 0 x.v) hU'] at e
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at e
  exact (mul_eq_zero.1 e).resolve_right h0

end GlobalTheory.MBLow.JetSep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianLocusNonempty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ZHAbLocusNonempty

theorem abLocus_nonempty : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (abLocus Zh.G).Nonempty := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hO
  obtain ⟨z, hz⟩ := hO.ne
  refine ⟨z, ?_⟩
  rw [Zh.ab]
  show S.TT M z = ⊥
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  have h1 : S.perp ⊥ = ⊤ := by
    refine top_unique fun a _ h hh => ?_
    rw [AddSubgroup.mem_bot.mp hh]
    simp [ZH.eStd]
  rw [ZH.ThetaSys.TT, ZH.ThetaSys.HH, hO.supI_eq hz, S.supp, ← h1, hpp]

end GlobalTheory.ZHAbLocusNonempty
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelQuotientFamilyLocalPointsEqOfObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem GlobalTheory.SiegLev.SQuot.eq_of_siegPB : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (ζ' : o') (F : SFam h N ζ') (j : o →+* o') (Q : SQuot F n ζ j) (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ Q.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'), x ≫ Q.s = y ≫ Q.s → SiegPB c Q.univ x → SiegPB c Q.univ y → x = y := by
  intro h n N o o' _ _ ζ ζ' F j Q R _ _ x y s' c hxy hx hy
  haveI := Q.fin; haveI := Q.etale; haveI := Q.onto
  obtain ⟨R1, _, _, φ1, hl1, hφ1, x1, hx1⟩ := _root_.GlobalTheory.LiftLocal.lift R Q.X F.X Q.π x
  obtain ⟨R2, _, _, φ2, hl2, hφ2, y2, hy2⟩ := _root_.GlobalTheory.LiftLocal.lift R1 Q.X F.X Q.π (spMap φ1 ≫ y)
  set g : Sp R2 ⟶ Sp R := spMap φ2 ≫ spMap φ1 with hg
  set x2 : Sp R2 ⟶ F.X := spMap φ2 ≫ x1 with hx2d
  have hx2 : x2 ≫ Q.π = g ≫ x := by simp only [x2, g, Category.assoc, hx1]
  have hy2' : y2 ≫ Q.π = g ≫ y := by simp only [g, Category.assoc, hy2]
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c2, hc2⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n o o ζ ζ (RingHom.id o) (Sp R) (Sp R2) s' (g ≫ s') g rfl (by rw [hid, Category.comp_id])).1 c
  have key : ∀ z : Sp R ⟶ Q.X, ∀ z2 : Sp R2 ⟶ F.X, z2 ≫ Q.π = g ≫ z → SiegPB c Q.univ z → SRel c2 F.univ 1 (N / n) z2 := by
    intro z z2 hz hcz
    have A := (_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n n o o o ζ ζ ζ Q.X (Sp R) (Sp R2) Q.s s' (g ≫ s') Q.univ c c2 z g 1 1 1 ((sRel_one_one_iff _ _ _).2 hcz)).1
    have B : SRel c2 Q.univ 1 1 (g ≫ z) := A.1 ((sRel_one_one_iff _ _ _).2 hc2)
    have C := (_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n N n o o' o ζ ζ' ζ Q.X F.X (Sp R2) Q.s F.s (g ≫ s') Q.univ F.univ c2 Q.π z2 1 (N / n) 1 Q.low).1
    rw [hz] at C
    exact C.2 B
  have e := Q.fibre R2 x2 y2 (g ≫ s') c2 (by
      rw [← Q.base, ← Category.assoc, ← Category.assoc y2, hx2, hy2', Category.assoc, Category.assoc, hxy]; simp only [g, Category.assoc])
    (key x x2 hx2 hx) (key y y2 hy2' hy)
  rw [hx2, hy2'] at e
  have hcomp : spMap (φ2.comp φ1) = g := by
    simp only [g, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  exact GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom R R2 (φ2.comp φ1) inferInstance (hφ2.comp hφ1) Q.X x y (by rw [hcomp]; exact e)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveInfOfGeometricallyIntegral
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory

theorem surjective_inf_of_geometricallyIntegral :
    ∀ (Z T : Scheme.{0}) (f : Z ⟶ T) [GeometricallyIntegral f] (O O' : Z.Opens),
      Surjective (O.ι ≫ f) → Surjective (O'.ι ≫ f) → Surjective ((O ⊓ O').ι ≫ f) := by
  intro Z T f _ O O' hO hO'
  refine ⟨fun t => ?_⟩
  have hint : IsIntegral (f.fiber t) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback f (T.fromSpecResidueField t))
  have hi : IsPreirreducible (f ⁻¹' {t}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ (f.fiberι t).continuous.continuousOn
  obtain ⟨x, hx⟩ := (O.ι ≫ f).surjective t
  obtain ⟨x', hx'⟩ := (O'.ι ≫ f).surjective t
  obtain ⟨y, hy, k₁, k₂⟩ := hi _ _ O.2 O'.2
    ⟨x.1, by rw [← hx]; rfl, x.2⟩ ⟨x'.1, by rw [← hx']; rfl, x'.2⟩
  exact ⟨⟨y, k₁, k₂⟩, hy⟩

end GlobalTheory
end
end

