module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1701
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectors
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaShiftSmooth

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (κ : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  have hs : (flagL (R.datWp i R.triv)).s = 0 := rfl
  have hQ : (flagL (R.datWp i R.triv)).Q = ∅ := rfl
  rw [hs, hQ]
  simp

theorem exists_translate (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) :
    ∃ U ∈ R.Wall i σ, ∀ v x, U v x = X v (x * κ') := by
  refine ⟨postOn (R.MW i σ) (actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0) X,
    GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) g0 X hX _ fun _ => rfl, fun v x => ?_⟩
  have hT : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (X v) := fun k hk h =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i σ) _ _ X hX v).2.2 k hk h
  have h1 := level_action_spec (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) hT ⟨κ', hκ'⟩ κ' hκ' x
  rw [levChi_flag_eq_one, inv_one, one_mul] at h1
  exact h1

theorem translate_of_lowT (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X X' : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) (hX' : X' ∈ R.Wall i σ)
    (h : ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (x : GA D (Wc D i)), X' (fun ρ => v ρ) x = X (fun ρ => v ρ) (x * κ'))
    (v : (R.MW i σ).Vec) (x : GA D (Wc D i)) : X' v x = X v (x * κ') := by
  obtain ⟨U, hU, hUv⟩ := exists_translate R hθ i σ g0 κ' hκ' X hX
  have h0 : X' - U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i σ) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ (X' - U) (Submodule.sub_mem _ hX' hU) fun w => by
      funext z
      exact sub_eq_zero.2 ((h w z).trans (hUv _ z).symm)
  rw [sub_eq_zero.1 h0]
  exact hUv v x

theorem thF_shift_all : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : (R.MW i (sg0 D A)).Vec) (x : GA D (Wc D i)), R.thF i t y' v x = R.thF i t y v (x * κ') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hP i t g0 κ κ' hκ hκ' y y' hy
  exact translate_of_lowT R hM.inf i (sg0 D A) g0 κ' hκ' (R.thF i t y) (R.thF i t y') (hP.thF_mem i t y)
    (hP.thF_mem i t y') (_root_.GlobalTheory.ThetaShift.thF_shift_of_models R hL hM hP i t g0 κ κ' hκ hκ' y y' hy)

end GlobalTheory.ThetaShiftSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOfUnitVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.VacRead
open GlobalTheory.ThetaLawMoved GlobalTheory.ThetaLawOF

theorem theta_of_unit_vacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, δ ≠ 0 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  intro D ψ θ S T frS frT hS hT δ hδ Ls Lt hLs hLt f hf Φ hΦd hΦ
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S frS hS Ls hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T frT hT Lt hLt
  rw [← hΛS, ← hΛT] at hf
  have hψ := hf.1
  have hθ := hf.2.inf
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, -, h3⟩ := _root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hSd hTd
  refine ⟨hΦd.comp ((differentiable_id).const_smul δ⁻¹), ?_⟩
  intro x hx Y
  obtain ⟨v, hv, rfl⟩ := mem_La_frame_sd S T frS frT hS hT Ls Lt hLs δ x hx
  rw [← hΛS, ← hΛT] at hv
  have hv' : GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) := by
    rw [AddMonoidHom.map_neg]; exact neg_mem hv
  obtain ⟨ε, -, hε⟩ := h3 f hf.2.lat _ hv'
  have hsign := sign_eq_alpha_sd ψ S T frS frT hS hT hψ ΛS ΛT hSd hTd δ hδ v hv ε (fun g hg => hε g hg)
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hch hψ hf.2.theta v (hε f hf.2.lat)
  set X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b with hX
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := δ⁻¹ • Y with hZ
  have hZY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  set z : GlobalTheory.FockCompare.RW T S := fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ with hz
  have hzτ : ∀ τ, (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) :=
    fun τ => coord_back frS frT Z τ
  have hz1 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) = Z := by
    rw [zCo_iota hch]; funext τ; exact coord_back frS frT Z τ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v)) = Z + X := by
    rw [zCo_iota hch]; funext τ
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) + Matrix.of (GlobalTheory.VacUnique.infRat S T v τ)) * GlobalTheory.FockPos.frAt frS τ = Z τ + X τ
    rw [Matrix.mul_add, Matrix.add_mul, hzτ τ]
    rfl
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) z = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re := by
    rw [omO_frame frS frT hS hT]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hzτ τ]
    rfl
  have hl := hlaw z
  rw [hΦ _ (hch.real_iota T S _), hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO, hz1, hz2, hom, hsign] at hl

  simp only [Formalism.MainNotions.TaylorLogMetric.U]
  have e1 : δ⁻¹ • (Y + δ • X) = Z + X := by rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [e1, hZY, torusHermitianForm_scaled_coordinate_eq hδ, torusHermitianForm_scaled_coordinate_eq hδ]
  have hZZ : δ⁻¹ • δ • Z = Z := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [hZZ]
  set a := Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) with ha
  have kE : Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    push_cast at h ⊢
    linear_combination h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)))
  rw [← kE]
  calc _ = a * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) *
        (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) * Φ (Z + X)) := by
        rw [kE]; ring
    _ = _ := by
        rw [hl]
        have := al_mul_self (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X)
        rw [← ha] at this
        linear_combination (Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) * Φ Z) * this

end GlobalTheory.VacRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledCoordsBoxProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox

variable {F : Type} [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem thetaSum_schr_negY (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ]
    (x y : κ → AdeleRing (𝓞 F) F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      star (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) (fun u => star (φ u)))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  unfold GlobalTheory.WeilM.thetaSum
  rw [Complex.star_def, Complex.conj_tsum]
  refine tsum_congr fun ξ => ?_
  generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
  simp only [GlobalTheory.WeilM.schr, map_mul, Complex.star_def, Complex.conj_conj, hc, dotProduct_neg, neg_add, mul_neg]

end GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox


open GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox in
theorem GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) =>
            GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) *
              star (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => star (φ₂ x)) (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)) := by
  intro D ψ hψ S T JA JB ξ hA κ _ co φ₁ h₁ φ₂ h₂
  funext w
  have he : (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co).e w =
      (Sum.elim (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inl) id)).1 (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)).1,
        Sum.elim (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inl) id)).2
          (-(co.e (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)).2)) := rfl
  have hs : ∀ (v : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ v φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun v φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ v φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho]
  rw [he, DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.schr_boxFun_elim,
    DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂), thetaSum_schr_negY ψ hψ.1.2.1]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleSquareSplitPlaceCharacterEqLocalGrid
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

namespace GlobalTheory.PureMatch

open GlobalTheory.LFun

theorem chrW_triple_split_nu : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil)
    (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ (w : Pl D.host.E) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    splitPrime τ = w →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ = ((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α τ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β τ := by
  intro D T L sc G μ₀ hL W M t i j e Bs Γ X hX w v hv τ hw
  subst hw
  have e1 : X.ν = G.nu t i (j + 1) := by
    show X.α / X.β = _
    rw [hX.α, hX.β]
    exact mul_div_mul_right_eq_div _ _ _
  refine ⟨?_, ?_⟩
  · ext x
    show (locChar X.ν (splitPrime τ) (Units.map (complMap hv).toMonoidHom x) : ℂ) = _
    rw [e1, locChar_eq_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)]
    have hj : (j : ℕ) < D.R.m := j.2
    simp only [GlobalTheory.FunObj.SqNum.nuH, Grid.nu, locGrid, muBase, dite_eq_left hj]
    rfl
  · ext x
    show (locChar X.α (splitPrime τ) _ : ℂ) =
      (locChar (X.α / X.β) (splitPrime τ) _ * locChar X.β (splitPrime τ) _ : ℂˣ)
    simp [locChar]

end GlobalTheory.PureMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMixedCoordinateSumRapidDecayStatement
section
namespace I195MixedCoordinates_5ebd72a9a6f704b036de0605

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_5ebd72a9a6f704b036de0605

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_mixedCoordinate_sum_rapid_decay : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ (c : ℝ), 0 < c →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 → ∀ (τ₀ : D.what₂.Tau) (e : ℕ),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      (∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → (_root_.I195MixedCoordinates_5ebd72a9a6f704b036de0605.source d) X ψ μ' 𝓕' Ψ x 0 = 0) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ α : Mx D r r, α.map (finPart D) = 1 →
        (∀ τ, compAt θ τ α = diagonal (fun i => (t i : ℂ))) →
        ENNReal.ofReal (∏ i, t i ^ e) *
          ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E, ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 k Ψ).toReal) := by
  first | exact @GlobalTheory.TorusMixedDecay.prod_mul_sum_mixS_le | exact GlobalTheory.TorusMixedDecay.prod_mul_sum_mixS_le | (intros; apply GlobalTheory.TorusMixedDecay.prod_mul_sum_mixS_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPlacesBoundChainTwoRunChain
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OnAtPlacesBase

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

theorem on_of_has_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : HasIndexBound O) (hD : LeafData O) (hJ : GlobalTheory.TraceClassRank.RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : HasTwistBound O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hE : HasExpBound N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ∃ err, ONwith S N err := by
  obtain ⟨Th1, a, r1, r2, de2, hT0⟩ := hT0
  obtain ⟨ε, h1⟩ := h1
  obtain ⟨-, Jp, hJS, hJE⟩ := hE
  exact ⟨_, GlobalTheory.TraceClassRank.on_core_atPlaces N
    ({ O with Th1 := Th1, a := a, r1 := r1, r2 := r2, de2 := de2, ε0 := ε, Jp := Jp } : OnObj S P c) CE hRk
    hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1⟩

end Free

theorem on_base_atPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ (s : ℕ) (N : IndefNum A.fam.base) (C : ℝ), A.fam.Ok s → R.grp_levels F → R.grp_chiW → R.IsModels → R.tup_mu_conj → R.thP_thG → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → RankRows ((R.toCx F).data F.cr false) → LeafLevelSq O (Res R) D.R.f → LeafYBound O → LeafSup O → LeafSpan O → LeafLemmaS O → HasIndexBound O → LeafData O → GlobalTheory.TraceClassRank.RankAtPlaces O → LeafIdentity O → LeafTW2 O → HasTwistBound O → LeafShareI O → LeafBadShare O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O → LeafSizes O → LeafX O → LeafBad O → HasExpBound N O → c.CE ≤ C → ErrorConstantMatchesDefinition N O C → ∃ err, ONwith ((R.toCx F).data F.cr false) N err := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r c O hO s N C hOk h1 h2 hM hμ hth hU hB hrat hRk hSq hY hSup hSp hS hT0
    hD hJ hI hT2 hT1 hSh hBS hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1
  classical
  obtain ⟨hc, hinj, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  have hN : TieLevelNum O (rankPred D.R) D.R.f := by
    letI := st
    letI := hostAlg D
    refine ⟨hd.f_eq, ?_⟩
    rw [hO.rr_eq, OntoChain.rank_eq]
    push_cast
    rfl
  obtain ⟨w, hw⟩ := GlobalTheory.BigOnBase.exists_tieCoord_base ht (fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩) hOk h1 h2 hM.HV hM.jV hM.HW hμ (phasedLift_one hth) hU hB hrat hI hT2
  obtain ⟨tU, hMk, hP⟩ := level_of_tied ht hOk.irr h1
  exact on_of_has_atPlaces N (withCoord O w) C hRk hMk hSup hP hw hSp hS hT0 hD hJ hI hT2 hT1 hSh
    (leafIndexU_of O D.R.f (mirab_levelGroups _ _) hSq hY tU hN) hBS (leafUnip_of O D.R.f (mirab_levelGroups _ _) hSq tU hN)
    hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1

end GlobalTheory.OnAtPlacesBase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove
section
noncomputable section

namespace GlobalTheory.UnrEuler.ConjFac

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors TensorProduct
open Formalism.L2.Host (aboveF)
open GlobalTheory.CuspRep (conjSrc conjPl_conjSrc)

theorem absNorm_conjSrc {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (conjSrc c w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc c w)]
  rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
  exact Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv c)) w.asIdeal
    (RingOfIntegers.mapRingEquiv c)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective (RingOfIntegers.mapRingEquiv c)) _).symm).toEquiv

end GlobalTheory.UnrEuler.ConjFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverseStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_continuous_inverse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ [Invertible (2 : mixedEmbedding.mixedSpace F)], ∃ ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ,
        (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) ∧
        ∃ A : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
            (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
          ∀ w (f g : SInf F (Fin n × Fin d)), (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
            (ei g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (ei f) := by
  first | exact @GlobalTheory.ArchIntertw.ei_schr | exact GlobalTheory.ArchIntertw.ei_schr | (intros; apply GlobalTheory.ArchIntertw.ei_schr <;> assumption)
end

