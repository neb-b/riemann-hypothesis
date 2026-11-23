module

public import Mathlib
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBessel
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem vec_bigPt_eq_bessel : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬ ((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → p.V H (TBB.bigPt P.r c) = 0) ∧ (((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → 0 < TBB.Gp p (TBB.bigPt P.r c) ∧ ∀ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ γ → γ ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H γ) := by
  intro Wp Wq _ _ _ _ _ _ P p H c
  refine ⟨fun hn => ?_, fun ⟨hd, hlt⟩ => ?_⟩
  · show D.vecV p.T.base p.ν' p.m₀ H (TBB.bigPt P.r c) = 0
    unfold D.vecV
    rw [dite_eq_right]
    rintro ⟨hl, hG⟩
    refine hn ⟨fun a => ?_, Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG⟩
    exact (hl.1 (1, c a) (List.mem_ofFn.2 ⟨a, rfl⟩)).2
  · have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hd _
    have hG : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r
        (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := by
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      have hlt' : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) := hlt
      nlinarith [mul_lt_mul_of_pos_left hlt' hp]
    have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    refine ⟨hG, fun γ hγ hZ hD => ?_⟩
    have hZ' : Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := hZ
    have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' γ := by
      rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt c) _ hl hZ']; exact hG
    refine ⟨⟨hγ, hpos⟩, ?_⟩
    show D.vecV p.T.base p.ν' p.m₀ H (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep P.k P.r Wp Wq p.T.base p.ν' p.m₀ H _ hl γ p.hF hG hγ hZ' hD]
    have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt c) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt c hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) hl.2 hl.1
    rw [hw] at hmono
    rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ hpos hnz (hZ'.trans hmono) H]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsFunctional
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_normalised_bessel_map : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hside
  have hconv := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside
  by_cases hz : ∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0
  · obtain ⟨l₀, La, hB, hnz, hshape⟩ :=
      _root_.GlobalTheory.BesselShape.bessel_shape H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside hz
    have hTK : ∀ v ∈ R.TK, v ∈ R.sm :=
      (GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hDS).2.2.2.2.1
    obtain ⟨v₀, hv₀, hl₀⟩ := GlobalTheory.bessel_nonzero_on_translates H k r ε mu R Wp z π l₀ hDS hB hnz
    obtain ⟨c₀, -, hc₀⟩ := GlobalTheory.BesselDegree.schur_fdeg H k r ε μG hside.2.2.2.2.2.2.1
    have hP := GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside _ (hc₀ mu R hDS).1
    have hadj := _root_.GlobalTheory.BesselAdjoint.adjoint_be H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside
    obtain ⟨c, hc, hLa⟩ := _root_.GlobalTheory.hermitian_rankOne_kernel_shape R.TK Wp (fun v => l₀ v) (fun v => La v)
      (fun v w => by
        have := hadj v v.2 w w.2
        rwa [hshape w (hTK _ w.2) v v.2, hshape v (hTK _ v.2) w w.2] at this)
      (fun v ξ => by
        have := hP v v.2 ξ
        rw [hshape v (hTK _ v.2) v v.2] at this
        exact ⟨this.1, this.2.1⟩)
      ⟨⟨v₀, hv₀⟩, hl₀⟩
    refine ⟨fun w => ((Real.sqrt c : ℝ) : ℂ) • l₀ w, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hB _, ?_⟩
    intro w hw v hv
    refine ⟨(hconv v hv).1 w hw, ?_⟩
    have hv' : La v = (c : ℂ) • l₀ v := hLa ⟨v, hv⟩
    rw [hshape w hw v hv, hv']
    ext ξ
    have hs : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, Complex.conj_ofReal,
      smul_smul]
    congr 1
    rw [← hs]; ring
  · push Not at hz
    refine ⟨fun _ => 0, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero, ?_⟩
    intro w hw v hv
    refine ⟨(hconv v hv).1 w hw, ?_⟩
    rw [hz w hw v hv]
    ext ξ
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffOfJet
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.IntegralGerm

section Val

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem gs_comp (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem sval_comp {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y') (h : Y' ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) fun ψ => J (r ≫ ψ)) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem sval_secLin (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    {c : Fin n → Γ(Y', ⊤)} (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₁ r z J = ∑ i, gs r z ⊤ (c i) * sval (s i) (r ≫ h) z J := by
  have e := (FieldBaseChange.secLin_iff_val hL s₁ s h c).1 H (r z) (fun ψ => J (r ≫ ψ)) fun ψ => hJ (r ≫ ψ)
  have e₁ := sval_comp s₁ r (𝟙 _) z hJ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Category.comp_id, e, map_sum] at e₁
  refine e₁.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, ← gs_stalkMap r z ⊤ trivial, Category.id_comp, ← sval_comp (s i) r h z hJ]

theorem exists_value (hL : L.IsLB) {q : ℕ} (s : H0 L q) (h : Y ⟶ X)
    (t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (1 : ℤ)))) (ht : t.IsGen) :
    ∃ u : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s (r ≫ h) z J = gs r z ⊤ u * (val t r z J ^ q).val := by
  obtain ⟨w, hw⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ hh => by simp [Fintype.prod_sum_type])
    (pullMulSec s h (LB.invGen L _ _ (GeneratorPullback.powGen L _ _ t q))
      (invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht q)))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (K := PEmpty) (Y := Y) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (w.f PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e := hw Z r z J hJ
  have ep : val (GeneratorPullback.powGen L _ _ t q) r z J = val t r z J ^ q := map_pow _ _ _
  rw [sval_pullMulSec _ _ _ _ _ z hJ, val_inv, ep, sval_of w _ z J PEmpty.elim (fun k => k.elim)] at e
  refine Eq.trans ?_ (congrArg (· * _) ((gs_res r z le trivial _).trans e).symm)
  rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end Val

theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Sp B) (a : A) :
    gs (spMap f) y ⊤ (toΓ A a) = gs (𝟙 _) y ⊤ (toΓ B (f a)) := by
  have e := FieldBaseChange.constVal_specMap (𝟙 (Sp B)) f y a
  rw [Category.id_comp] at e
  exact e

theorem toΓ_surjective (A : Type) [CommRing A] : Function.Surjective (toΓ A) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective

theorem coeff_of_jet {V F κ : Type} [CommRing V] [CommRing F] (g : V →+* F) [Fintype κ] [DecidableEq κ]
    (f : MvPowerSeries κ F) (e : κ →₀ ℕ) {n : ℕ} (c : Fin n → F) (a : Fin n → Jet V κ e.degree)
    (h : psJet e.degree f = ∑ i, algebraMap F (Jet F κ e.degree) (c i) * jetCoef g κ e.degree (a i)) :
    ∃ b : Fin n → V, MvPowerSeries.coeff e f = ∑ i, c i * g (b i) := by
  choose p hp using fun i => Ideal.Quotient.mk_surjective (a i)
  refine ⟨fun i => AddMonoidAlgebra.coeff (p i) e, ?_⟩
  have h1 : psJet e.degree f = Ideal.Quotient.mk _ (∑ i, MvPolynomial.C (c i) * MvPolynomial.map g (p i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hp]
    rfl
  rw [psJet, Ideal.Quotient.eq] at h1
  have h2 := GermFun.coeff_eq_zero_of_mem h1 (Nat.lt_succ_self _)
  rw [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc _ _ _ le_rfl, sub_eq_zero] at h2
  rw [h2, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → AIntSt := by
  intro hLaw _ _ hT V _ _ _ _ ϖ hϖ D A G _ _ U κ _ _ z _ τ hτ F _ _ _ _ v hv q hq σ' s f hE hG hs e
  obtain ⟨n, c, σ, hc, hlin⟩ := IntegralCombination.main hLaw.globalFns hT V ϖ hϖ D A G U F v hv q hq σ' s hE hs
  obtain ⟨zF, h1, h2, h3⟩ := hG e.degree
  have hL := U.LG.isLB
  choose u hu using fun i => exists_value hL (σ i) (z e.degree).left (τ e.degree) (hτ e.degree)
  choose a ha using fun i => toΓ_surjective (Jet V κ e.degree) (u i)
  obtain ⟨b, hb⟩ := coeff_of_jet (algebraMap V F) f e c a (GermFun.toΓ_injective _ (fn_ext fun y _ => by
    choose J hJ using fun χ : Sp (Jet F κ e.degree) ⟶ G.left => exists_chart hL (χ y)
    have e₁ := (h3 y J hJ).symm.trans (sval_secLin hL hlin zF y hJ)
    refine (Units.mul_left_inj _).1 (e₁.trans ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, gs_eq _ y ⊤ trivial, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← gs_eq _ y ⊤ trivial, map_mul, gs_mul _ y ⊤ trivial, h2, hu i _ _ y J hJ, ← ha, gs_spMap, _root_.mul_assoc,
      FieldBaseChange.gs_scal, h1]
    exact congrArg (· * _) (gs_spMap _ y _)))
  rw [hb]
  refine v.map_le_sum fun i _ => ?_
  rw [AddValuation.map_mul, IsScalarTower.algebraMap_apply V (FractionRing V) F]
  exact add_nonneg (hc i) (GC.v_alg_nonneg hϖ hv _)

end GlobalTheory.IntegralGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentiableU1
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.JetAlg

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_sub_one_lt {y : ℂ_[p]} {k : ℕ} (h : y ^ p ^ k = 1) : ‖y - 1‖ < 1 := by
  have hne : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hy : ‖y‖ ≤ 1 := by
    have h1 : ‖y‖ ^ p ^ k = 1 := by rw [← norm_pow, h, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hne).1 h1).le
  let Y : ball p := ⟨y, hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out (Y - 1) 1 k
  have hr' := congrArg (fun t : ball p => (t : ℂ_[p])) hr
  simp only [sub_add_cancel, one_pow, mul_one] at hr'
  push_cast at hr'
  have hz : ‖y - 1‖ ≤ 1 := (Y - 1).2
  have hrr : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have e : (y - 1) ^ p ^ k = -((p : ℂ_[p]) * (y - 1) * r) := by
    have : (Y : ℂ_[p]) = y := rfl
    rw [this, h] at hr'
    linear_combination -hr'
  have h2 : ‖(y - 1) ^ p ^ k‖ < 1 := by
    rw [e, norm_neg, norm_mul, norm_mul, mul_assoc]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_p_lt_one
      (mul_le_one₀ hz (norm_nonneg _) hrr)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hne).1 h2

theorem bd_derivative {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (PowerSeries.derivative f) := by
  intro n
  rw [coeff_derivative, norm_mul]
  refine mul_le_one₀ (hf _) (norm_nonneg _) ?_
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  simpa using this

theorem bd_DT {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (DT f) := by
  have h := bd_derivative hf
  intro n
  rw [DT, add_mul, one_mul, map_add (f := _)]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h n) ?_)
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul]; exact h n

theorem bd_iterate {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) (k : ℕ) : Bd 1 (DT^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact bd_DT ih

theorem differentiable_U1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

theorem differentiable_W1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (W1 d x F) := by
  have := differentiable_U1 d x hF
  unfold W1
  fun_prop

end GlobalTheory.MomOne.JetAlg

namespace GlobalTheory.MomOne
open JetAlg

theorem jets_algebraic : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsTh d θ → δ ≠ 0 → (∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ) → ∀ (ι : ℂ ≃+* ℂ_[q]) (t y : ℂ) (n s k : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good ι d n s y → δ⁻¹ ^ k * iteratedDeriv k (W1 d y (U1 d t θ)) 0 ∈ algebraicClosure ℚ ℂ := by
  intro d q hq δ θ hd hd16 hsp hθ hδ hL ι t y n s k hs ht hy
  refine mem_algebraicClosure_of_norm_le q ι _ 1 ?_
  intro ι' hι'
  obtain ⟨Ω, hΩ, h1', h2', -⟩ := hL ι'
  obtain ⟨hA, hB, -⟩ := okArith d q ι hd hd16 hsp
  have hy' : Good ι' d n s y := by
    obtain ⟨v, hv, hn, rfl⟩ := hy
    refine ⟨v, hv, ?_, rfl⟩
    have hc : InOK d (conj v) := (hA.2.2 v v hv hv).2.2.2
    have := hι' ⟨conj v, (hB _ hc).2.2⟩
    simp only at this
    rw [this]; exact hn
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · exact absurd (by simpa using hs) hq.out.ne_one
    · exact h
  obtain ⟨hζ, hE⟩ := h2' t y n s hs ht hy'
  have hb := (Shift.shift_laws q _ (norm_sub_one_lt hζ)).1 _ _ (h1' t ⟨s, hs0, hs, ht⟩)
  rw [← hE] at hb
  have han : AnalyticAt ℂ (W1 d y (U1 d t θ)) 0 :=
    (differentiable_W1 d y (differentiable_U1 d t hθ.1)).analyticAt 0
  have hk := (hat_multiplicative_chart q ι' (Ω / ι' δ) _ han).2.1 k
  have hc := bd_iterate hb k 0
  rw [coeff_zero_eq_constantCoeff_apply, hk, div_eq_mul_inv, mul_pow, mul_assoc, norm_mul, norm_pow, hΩ,
    one_pow, one_mul] at hc
  rw [map_mul, map_pow, map_inv₀]
  exact hc

end GlobalTheory.MomOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterOnPoints
section
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FamGerm GlobalTheory.KernelNoTorsion

theorem ringAct_natCast {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Λ : Type} [Ring Λ]
    (ρ : RingAct A Λ) (n : ℕ) : ρ.act n = (𝟙 A) ^ n := by
  induction n with
  | zero =>
    have h : ρ.act 0 = ρ.act 0 * ρ.act 0 := by
      have := ρ.map_add 0 0
      rwa [add_zero] at this
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.mp h
  | succ n ih =>
    rw [Nat.cast_succ, ρ.map_add, ih, ρ.map_one, pow_succ]
    rfl

abbrev Admissible {V O : Type} [CommRing V] [IsLocalRing V] [CommRing O] (f : V →+* O) (A : Type) [CommRing A]
    [Algebra O A] : Prop :=
  (Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0

theorem dualBC_inr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (s : O) :
    dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr s) = TrivSqZeroExt.inr (algebraMap O R s) :=
  TrivSqZeroExt.lift_apply_inr _ _ _ _ _ s

theorem fst_comp_dualBC {O R : Type} [CommRing O] [CommRing R] [Algebra O R] :
    (TrivSqZeroExt.fstHom O R R).comp (dualBC (Algebra.ofId O R)) =
      (Algebra.ofId O R).comp (TrivSqZeroExt.fstHom O O O) := by
  apply DualNumber.algHom_ext
  show (dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr 1)).fst =
    algebraMap O R (TrivSqZeroExt.inr 1 : DualNumber O).fst
  rw [dualBC_inr, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_inr, map_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

theorem dAct_eq_map {R O F Λ : Type} [CommRing R] [CommRing O] [CommRing F] [CommRing Λ] [StarRing Λ] [Algebra R F]
    [Algebra O F] (f : R →+* O) (hf : ∀ r, algebraMap O F (f r) = algebraMap R F r) {d : ℕ}
    (B : Geo.Tor.Germ.FB R d Λ) (a : Λ) :
    TB.dAct F B a = ((TB.dLin (B.A.act a)).map f).map (algebraMap O F) := by
  ext i k
  simp [TB.dAct, TB.dLin, Geo.Tor.Germ.FB.actK, hf]

end GlobalTheory.TorsionCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralExpansions_of_valuation_ge : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (q : ℕ), 1 ≤ q → ∀ (s : Fam D.toPre F q) (r : ℚ), (∀ χ, VGe D F v q χ (s.s χ) r) → ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α), (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i)) ∧ (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε q) (s.s α) (D.toPre.famφB α) (DegPre.famε q) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) := by
  first | exact @GlobalTheory.exists_integral_expansions_of_vge | exact GlobalTheory.exists_integral_expansions_of_vge | (intros; apply GlobalTheory.exists_integral_expansions_of_vge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.QuadSubfield

namespace GlobalTheory.PlaceComponents

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem emb_mem (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}

end GlobalTheory.PlaceComponents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyBoundStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_setup_cayley_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.RatioMoment.ratio_moment | exact GlobalTheory.RatioMoment.ratio_moment | (intros; apply GlobalTheory.RatioMoment.ratio_moment <;> assumption)
end

