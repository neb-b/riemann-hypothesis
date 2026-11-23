module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarUnitModulus
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0017
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0023
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0550
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0040
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0030

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistNormKappaMovedPlace
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedKappaNorm
section Mean
open MeasureTheory
open scoped Pointwise
end Mean
theorem norm_kappa_of_moved_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ → ‖κ‖ = 1 := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hκ
  have hC := ch.S.Z.crv
  have he0 := ch.S.Z.e0_is p hp
  have hsd := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp x y
  have hvac := _root_.GlobalTheory.T.twisted_moved_vacuum_integral hP hI ch hch p hp x y
  have hvac0 := ch.S.Z.vac_is p hp
  have hc0 := ch.S.Z.kernelNorm_constant_spec p hp
  have hd := _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hP hI ch hch p hp x y
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have h2 := fun f k => _root_.GlobalTheory.FockConj.pureTensorO_negSp_monomial ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.frC (.grid (i + 1) D.R.m))
      (ch.S.N.frC (.grid i D.R.m)) f ch.W.ψ_std ch.W.θ_is k 0
    have key := fun Ls Lt => @normSq_scalar D ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.fr (.grid (i + 1) D.R.m)) (ch.S.N.fr (.grid i D.R.m))
      (ch.S.N.fr_on _ ⟨hi, rfl⟩) (ch.S.N.fr_on _ ⟨by omega, rfl⟩)
      (ch.W.cart_is _ ⟨hi, le_rfl⟩) (ch.W.cart_is _ ⟨by omega, le_rfl⟩) _ _ hC ch.S.Z.pt0 _ he0 Ls Lt
    have hconj := _root_.GlobalTheory.VacConj.isVacO_conj_negSp ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac
    have hconj0 := _root_.GlobalTheory.VacConj.isVacO_conj_negSp ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac0
    refine norm_eq_one_of_sq (c := starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ))
      (key _ _ (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) _ (by rw [inV_stdL, inV_stdL]; exact hconj0) _
        fun k => ?_) (key _ _ hsd.1 hsd.2 _ hconj _ fun k => ?_)
    · rw [iop_self hC he0]
      have h := congrArg (starRingEnd ℂ) ((h2 _ k).symm.trans (hc0 k))
      rw [Complex.conj_conj, map_mul] at h
      refine h.trans ?_
      show _ * starRingEnd ℂ (starRingEnd ℂ _) = _
      rw [Complex.conj_conj]
    · have h := congrArg (starRingEnd ℂ) ((h2 _ k).symm.trans (hκ k))
      rw [Complex.conj_conj, map_mul, GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd] at h
      refine h.trans ?_
      show _ * starRingEnd ℂ (starRingEnd ℂ _) = _
      rw [Complex.conj_conj, mul_left_comm _ κ, mul_assoc]
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have hj1 : j + 1 ≤ D.R.m := hp
    have key := fun Ls Lt => @normSq_scalar D ch.W.ψ ch.W.θ (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))
      (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) (ch.S.N.fr (.top j)) (ch.S.N.fr (.top (j + 1)))
      (ch.S.N.fr_on (.top j) (by show j ≤ D.R.m; omega)) (ch.S.N.fr_on (.top (j + 1)) hj1)
      (ch.W.cart_is (.top j) (by show j ≤ D.R.m; omega)) (ch.W.cart_is (.top (j + 1)) hj1) _ _ hC ch.S.Z.pt0 _ he0 Ls Lt
    refine norm_eq_one_of_sq (c := (ch.S.Z.c0 (.top t j) : ℂ))
      (key _ _ (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) _ (by rw [inV_stdL, inV_stdL]; exact hvac0) _
        fun k => ?_) (key _ _ hsd.1 hsd.2 _ hvac _ fun k => ?_)
    · rw [iop_self hC he0]
      exact hc0 k
    · have h := hκ k
      rw [GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd] at h
      refine h.trans ?_
      show _ * RingHom.id ℂ _ = _
      rw [RingHom.id_apply, mul_left_comm _ κ, mul_assoc]
end GlobalTheory.MovedKappaNorm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_norm_kappa_moved_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ → ‖κ‖ = 1 := by
  first | exact @_root_.GlobalTheory.MovedKappaNorm.norm_kappa_of_moved_place | exact _root_.GlobalTheory.MovedKappaNorm.norm_kappa_of_moved_place | (intros; apply _root_.GlobalTheory.MovedKappaNorm.norm_kappa_of_moved_place <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperCuspLiftApproxCusp
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate
namespace GlobalTheory.UpCuspApprox
end GlobalTheory.UpCuspApprox
namespace GlobalTheory.UpCuspApprox
theorem upperCusp_lift_approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P i).Maps) (v : Fin n → SmT (G.P i).M), (∀ l, F l ∈ (G.P i).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) (G.mP i).fd (G.mP i).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g ∂(G.mP i).ν‖ < ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hI0 C hC ε hε
  have hω := (hG.arrows.dn i hi).weil
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have e : ∀ h g, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) =
      starRingEnd ℂ (thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g Φ) :=
    fun h g => by rw [GlobalTheory.UpArrowConv.thetaKO_toSgn]
  obtain ⟨C0, A0, hC0⟩ := GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D R.ψ _ _ _ _ _ hω Φ hΦ
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact _ (hC.image (GlobalTheory.Grid.continuous_ofSgn_symm true _))
  have hK : ∀ h ∈ C, ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)‖ ≤
      C0 * (max H 1) ^ A0 * 2 ^ A0 * GlobalTheory.Grow.quotHeight (G.P i).V g ^ A0 := by
    intro h hh g
    have hb : ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)‖ ≤ C0 * (max H 1) ^ A0 * GlobalTheory.Grow.height (G.P i).V g ^ A0 := by
      intro g
      rw [e, RCLike.norm_conj]
      refine (hC0 _ g).trans ?_
      have h1 := hH _ ⟨h, hh, rfl⟩
      have h0 := GlobalTheory.Grow.height_pos (GlobalTheory.Grid.neg (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true _).symm h)
      have hC00 : 0 ≤ C0 := le_trans (norm_nonneg _) ((hC0 1 1).trans (by simp))
      rw [mul_pow, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC00) (pow_nonneg (GlobalTheory.Grow.height_pos _ _).le _)
      exact pow_le_pow_left₀ h0.le (h1.trans (le_max_left _ _)) _
    exact GlobalTheory.Grow.norm_le_quotHeight_pow
      (fun γ hγ g => by rw [e, e, GlobalTheory.UpArrowConv.thetaKO_left_snd hω hΦ _ γ hγ g]) hb g
  set B := C0 * (max H 1) ^ A0 * 2 ^ A0 with hBdef
  have hfin : (G.mP i).ν (G.mP i).fd < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hm.1.1 hm.2
  set Vol := (G.mP i).ν.real (G.mP i).fd with hVol
  have hV0 : 0 ≤ Vol := measureReal_nonneg
  have hB1 : 0 < |B| + 1 := by positivity
  set δ := ε / (2 * ((|B| + 1) * (Vol + 1))) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨n, F, v, hF, happ⟩ := _root_.GlobalTheory.T.twist_cusp_form_approx_weighted D R.θ hR.inf hP (G.P i) φ hφ A0 δ hδ
  have hI : ∀ l h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) (G.mP i).fd (G.mP i).ν := by
    intro l h
    have hv := val_aut_cusp (hF l) (v l)
    have e' : (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) =
        fun g => starRingEnd ℂ (thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g Φ) * F l (v l) g :=
      funext fun g => by rw [e]
    rw [e']
    exact GlobalTheory.UpArrowConv.conj_thetaKO_mul_integrableOn hP.cuspRapidDecay hR.inf hω hΦ hm.1.1 hm.2 hv.1 hv.2 _
  refine ⟨n, F, v, hF, hI, fun h hh => ?_⟩
  rw [← integral_finsetSum _ (fun l _ => hI l h), ← integral_sub (hI0 h) (integrable_finsetSum _ fun l _ => hI l h)]
  have hpt : ∀ g ∈ (G.mP i).fd, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g‖ ≤ |B| * δ := by
    intro g _
    rw [← Finset.mul_sum, ← mul_sub, norm_mul]
    have h1 := hK h hh g
    have h2 := happ g
    have hq := pow_nonneg (GlobalTheory.Grow.quotHeight_pos (G.P i).V g).le A0
    calc ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)‖ * ‖φ g - ∑ l, F l (v l) g‖
        ≤ (|B| * GlobalTheory.Grow.quotHeight (G.P i).V g ^ A0) * ‖φ g - ∑ l, F l (v l) g‖ :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self B) hq)) (norm_nonneg _)
      _ = |B| * (‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ A0) := by ring
      _ ≤ |B| * δ := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
  refine (norm_setIntegral_le_of_norm_le_const hfin hpt).trans_lt ?_
  have hε2 : |B| * δ * Vol ≤ ε / 2 := by
    rw [hδdef]
    have : |B| * Vol ≤ (|B| + 1) * (Vol + 1) := by nlinarith [abs_nonneg B]
    calc |B| * (ε / (2 * ((|B| + 1) * (Vol + 1)))) * Vol = (|B| * Vol) * (ε / (2 * ((|B| + 1) * (Vol + 1)))) := by ring
      _ ≤ ((|B| + 1) * (Vol + 1)) * (ε / (2 * ((|B| + 1) * (Vol + 1)))) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = ε / 2 := by field_simp
  linarith
end GlobalTheory.UpCuspApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_upperCusp_lift_approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P i).Maps) (v : Fin n → SmT (G.P i).M), (∀ l, F l ∈ (G.P i).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) (G.mP i).fd (G.mP i).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g ∂(G.mP i).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.UpCuspApprox.upperCusp_lift_approx_cusp | exact _root_.GlobalTheory.UpCuspApprox.upperCusp_lift_approx_cusp | (intros; apply _root_.GlobalTheory.UpCuspApprox.upperCusp_lift_approx_cusp <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedBaseExistence
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.RowEx
theorem twisted_base_existence (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hC : ConstEx) : BaseEx := by
  obtain ⟨CF0, hC⟩ := hC
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hC ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  have hQ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS
  intro G W hW S₀
  obtain ⟨rm, c, hrm, hc⟩ := hQ G W hW S₀.B
  have hL := hS.core.lev
  obtain ⟨M, hM⟩ := exists_vol G hL A.μ0
  obtain ⟨n, e, -, -, -, -⟩ := TestLatModel.exists_testLat (G := G)
    (node_isV G hL (X := .grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩).sd.1.fg default
  obtain ⟨Pm, -, -⟩ := hS.size.1
  have hCh : ∀ k, GlobalTheory.Chain.ChainPar D k := GlobalTheory.Corev.ChainParOfGap.chainPar_of_nodeGap D
    (GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap D (by simpa using Pm.nodeGap_ge_cubic_rank))
  obtain ⟨cv, hcv⟩ := GlobalTheory.RowTest.WVec.exists_w_ne hP.discreteSeriesCover hP.harishChandraModules hCh R hL
    hS.core.chain hS.core.models.inf
  obtain ⟨S'⟩ := sumChoice_nonempty W S₀ hS.core.fam.tie (GlobalTheory.ForcedWeights.lamRForced D)
  exact ⟨M, fun _ => 0, 0, cv, rm, { S' with toGridChoice := S₀ }, default, n, e, c, rfl,
    ⟨guard_of_qGuard hS.guard, hW, hM.isRow, hrm, hcv, hc⟩⟩
end GlobalTheory.RowEx
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilLieAlgebraActionByLineDerivatives
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.MaxLie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.RealLift Formalism.BasicNotions.TH
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_derivation_action_weil (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ := by
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => _root_.GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => _root_.GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := _root_.GlobalTheory.HeisDer.derEx
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := _root_.GlobalTheory.FockMapEx.fockEx_of_derEx hD
  have hsec := _root_.GlobalTheory.T.real_lift_lie_second_order hPr hD hfe hvl (_root_.GlobalTheory.T.weil_lie_algebra_scalar_action hPr hD hvl)
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1
    hc.expβ
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  intro γ hγ f hf
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨Yg, -, hY⟩ := _root_.GlobalTheory.RealLiftGen.genEx F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
  have h2 := (hL F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Yg hY T)
  exact ⟨_, mem _, h2⟩
theorem thetaSum_weil_hasDerivAt (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om')
    (γ : Multiplicative ℝ →* UA σ G.W.J) (hγ : γ ∈ Lines σ G.W) (f : SInf F (Fin a × Fin (a + a')))
    (hf : f ∈ G.M.Pol B.ψ B.emb) (f₁ : SInf F (Fin a × Fin (a + a')))
    (hA : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hev : ∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) (u : Matrix (Fin a) (Fin (a + a')) (AE F E)) :
    HasDerivAt (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (pure f φ))))
      (thetaSum F (G.M.co.rho B.ψ u (pure f₁ φ))) 0 :=
  _root_.GlobalTheory.T.thetaSum_pure_line_differentiable hPr F E σ B a a' G X om om' h γ hγ f hf f₁ hA φ hSB hev u
theorem exists_line_derivative_maxLie (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om')
    (γ : Multiplicative ℝ →* UA σ G.W.J) (hγ : γ ∈ Lines σ G.W) :
    ∀ Φ ∈ algD G.M B.ψ B.emb, ∃ Ψ ∈ algD G.M B.ψ B.emb,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Ψ x) 0) ∧
      ∀ u, HasDerivAt (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) Φ)))
        (thetaSum F (G.M.co.rho B.ψ u Ψ)) 0 := by
  have hψ : IsStd B.ψ := h.base.std
  have hM := h.geo.hM
  have hsch : ∀ p, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun p Φ hΦ => (IsUWeilPair.isUSplitting h.weil).pres p Φ hΦ
  have hAD := GlobalTheory.SquareAgree.HeisDeriv.algD_le_schA G.M B.ψ B.emb hM
  have hrs : ∀ u, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), G.M.co.rho B.ψ u Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun u Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hψ u Φ hΦ
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_, fun u => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · simp only [map_zero, GlobalTheory.SquareAgree.CoinvPass.rho_zero']
      simpa [thetaSum] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add a₁ b₁ ha₁ hb₁ ha hb =>
    obtain ⟨a₂, ha₂, hpa, hta⟩ := ha
    obtain ⟨b₂, hb₂, hpb, htb⟩ := hb
    refine ⟨a₂ + b₂, add_mem ha₂ hb₂, fun x => ?_, fun u => ?_⟩
    · simp only [map_add (f := _), Pi.add_apply]
      exact (hpa x).add (hpb x)
    · have e : (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (a₁ + b₁)))) =
          fun t => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) a₁)) +
            thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) b₁)) := by
        funext t
        rw [map_add (f := _), GlobalTheory.SquareAgree.CoinvPass.rho_add', thetaSum_add F (hrs u _ (hsch _ _ (hAD ha₁)))
          (hrs u _ (hsch _ _ (hAD hb₁)))]
      rw [e, GlobalTheory.SquareAgree.CoinvPass.rho_add', thetaSum_add F (hrs u _ (hAD ha₂)) (hrs u _ (hAD hb₂))]
      exact (hta u).add (htb u)
  | smul c a₁ ha₁ ha =>
    obtain ⟨a₂, ha₂, hpa, hta⟩ := ha
    refine ⟨c • a₂, Submodule.smul_mem _ c ha₂, fun x => ?_, fun u => ?_⟩
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hpa x).const_mul c
    · simp only [map_smul, GlobalTheory.SquareAgree.CoinvPass.rho_smul', GlobalTheory.SquareAgree.HeisDeriv.thetaSum_smul]
      exact (hta u).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    obtain ⟨f₁, hf₁, hA⟩ := _root_.GlobalTheory.SquareAgree.MaxLie.exists_derivation_action_weil hPr h γ hγ f hf
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨pure f₁ φ, Submodule.subset_span ⟨f₁, φ, hf₁, hSB, hev, rfl⟩, fun x => ?_, fun u => ?_⟩
    · exact hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x
    · exact _root_.GlobalTheory.SquareAgree.MaxLie.thetaSum_weil_hasDerivAt hPr h γ hγ f hf f₁ hA φ hSB hev u
end Gen
theorem maximal_lie_subalgebra_acts : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N, ∀ Φ,
    IsDatum Γ.M ψ cA ΦD Φ → ∃ Φ₁D ∈ N, ∃ Φ₁ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA Φ₁D Φ₁ ∧
      IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ₁ := by
  intro hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _hTr hO hT Pi rf rl p p' _hm N hN τ Y hY
    ΦD hΦD Φ hD
  have hψB := hO.psi
  subst hψB
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨Ψ, hΨ, hpt, hth⟩ := _root_.GlobalTheory.SquareAgree.MaxLie.exists_line_derivative_maxLie hPr hT γ hγ ΦD (hN.1 hΦD)
  have hΨN : Ψ ∈ N := hN.2.2.2 γ hγ ΦD hΦD Ψ hΨ hpt
  obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algA' Ψ hΨ
  refine ⟨Ψ, hΨN, Φ₁, hΦ₁, hD₁, fun z => ?_⟩
  obtain ⟨u, rfl⟩ := cA.surjective z
  have key : (fun t : ℝ => ωA (1, oneP θ X τ Y t) Φ (cA u)) =
      fun t => thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (om (1, γ (Multiplicative.ofAdd t)) ΦD)) := by
    funext t
    have k := (hO.weilA ΦD Φ hD 1 (oneP θ X τ Y t)).2 u
    rw [GlobalTheory.LocWeilAct.conjU_one', ← hγt t] at k
    exact k.symm
  show HasDerivAt (fun t : ℝ => ωA (1, oneP θ X τ Y t) Φ (cA u)) (Φ₁ (cA u)) 0
  rw [key, ← hD₁.2 u]
  exact hth u
end GlobalTheory.SquareAgree.MaxLie
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_lie_algebra_action_by_line_derivatives : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N, ∀ Φ,
    IsDatum Γ.M ψ cA ΦD Φ → ∃ Φ₁D ∈ N, ∃ Φ₁ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA Φ₁D Φ₁ ∧
      IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ₁ := by
  first | exact @_root_.GlobalTheory.SquareAgree.MaxLie.maximal_lie_subalgebra_acts | exact _root_.GlobalTheory.SquareAgree.MaxLie.maximal_lie_subalgebra_acts | (intros; apply _root_.GlobalTheory.SquareAgree.MaxLie.maximal_lie_subalgebra_acts <;> assumption)
end
end

