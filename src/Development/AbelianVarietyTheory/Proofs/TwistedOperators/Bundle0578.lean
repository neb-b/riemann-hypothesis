module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameOfRealizationModels
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0243
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryStabiliserEmbeddingNormLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryNearIdentityEqExpLogBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
public import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionInjectiveParameters
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroCayleyA
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientIntegralBoundsOfUnitaryLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientDerivativeIntegralBoundsOfLa

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateVacuumReadRationalPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7}

theorem ratW_sub_realPt_inf (S T : HSp D) (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ).map (infPart D) = 0 := by
  ext i j
  change infPart D (incA D (ℓ i j) - pairA D.host.F 1 0 ⊗ₜ[D.host.F] ℓ i j) = 0
  rw [map_sub]
  change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ ℓ i j) -
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 1 0 ⊗ₜ ℓ i j) = 0
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one]
  exact sub_eq_zero.2 rfl

theorem realPt_sub (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T (X - Y) = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T Y := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt, Matrix.of_apply, Matrix.sub_apply, TensorProduct.tmul_sub]

theorem actO_inf (S T : HSp D) (h : GA D T) {w : WO S T} (hw : w.map (infPart D) = 0) :
    (actO S T 1 h w).map (infPart D) = 0 := by
  have hw' : ∀ k l, infPart D (w k l) = 0 := fun k l => congrFun (congrFun hw k) l
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold actO
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, hw', mul_zero, zero_mul, Finset.sum_const_zero]

theorem actO_add (S T : HSp D) (h : GA D T) (u v : WO S T) :
    actO S T 1 h (u + v) = actO S T 1 h u + actO S T 1 h v := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

end GlobalTheory.HeisRatRead

namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem heis_translate_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∀ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
    w.map (infPart D) = 0 → heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i →
    x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w →
    ∀ X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      R.ωP i A.μ0 (1, g) (heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i)) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
        R.ψ (-(symplOH (Vc D i) (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) +
            symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (actO (Vc D i) (Wc D i) 1 g w))) *
          R.ωP i A.μ0 (1, g) (R.vacP i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) := by
  intro D G _ _ Pl0 T0 A T _ R hL hF hT i g x hx ℓ w hw hρw hxe X
  have hW := hT.ωP i A.μ0
  have hv := hT.vP i A.μ0
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hv.1.2.theta
  set F := R.ωP i A.μ0 (1, g) (R.vacP i) with hFdef
  have hFθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) F := hW.om_pres _ _ hf
  set lf := ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ with hlf
  have hlf0 : lf.map (infPart D) = 0 := ratW_sub_realPt_inf (Vc D i) (Wc D i) ℓ
  set gw := actO (Vc D i) (Wc D i) 1 g w with hgw
  have hgw0 : gw.map (infPart D) = 0 := actO_inf (Vc D i) (Wc D i) g hw
  have hgx : actO (Vc D i) (Wc D i) 1 g x = lf + gw := by
    rw [hxe, actO_add, ← GlobalTheory.HeckeVacuum.act_mul, mul_inv_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hFw : heisO R.ψ (Vc D i) (Wc D i) gw F = F := by
    have := hW.om_heis 1 g w (R.vacP i) hf
    rw [hρw] at this
    exact this.symm
  set P := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X
  set z := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)
  have hP0 : P.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) X
  have hz0 : z.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) (X - ℓ)
  have hl0 : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ).map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) ℓ
  have hzF : F (z + gw) = F z := by
    have := congrFun hFw z
    simp only [heisO, symplOH_real_fin hgw0 hz0, AddChar.map_zero_eq_one, one_mul] at this
    exact this
  have hpt : P + (lf + gw) = ratW (Wc D i) (Vc D i) ℓ + (z + gw) := by
    simp only [z, P, hlf, realPt_sub]
    abel
  have hratW : ratW (Wc D i) (Vc D i) ℓ = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ + lf := by
    rw [hlf]; abel
  rw [hW.om_heis 1 g x (R.vacP i) hf, ← hFdef]
  show R.ψ (symplOH (Vc D i) (Wc D i) P (actO (Vc D i) (Wc D i) 1 g x)) * F (P + actO (Vc D i) (Wc D i) 1 g x) = _
  rw [hgx, hpt, hFθ.quasi, hzF, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  rw [hratW, symplOH_add_right, symplOH_add_left, symplOH_add_right, symplOH_add_right,
    symplOH_real_fin hlf0 hP0, symplOH_real_fin hgw0 hP0, symplOH_real_fin hgw0 hl0, symplOH_fin_real hlf0 hz0]
  ring

end GlobalTheory.HeisRatRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapIncAMulRealPt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FrameChangeRead

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.FD Formalism.IndefR.Datum

variable {D : D7}

theorem map_incA_mul_realPt (S T : HSp D) (M : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    HMul.hMul (M.map (incA D)) (realPt S T X : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = realPt S T (M * X) := by
  ext a c
  simp only [realPt, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sum]

theorem exists_frAt {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (hM : R.IsModels) (ht : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (h : GA D (Wc D i)) :
    ∃ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h := by
  have e : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]
    exact res_embLL T ht.alg ht.laws.pins.2.2.1
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := e ▸ T.toCore.good_σ₀
  obtain rfl : σ = res T (sg0 D A) := hσ.trans e.symm
  have hb : BaseFrT T.toCore R := by
    intro j τ hτ hW
    have hj : InR D ((j : ℕ) + 1) := inR j
    obtain ⟨th, hr, hth, hd⟩ := ht.laws.dictU _ hj _ hτ
    obtain ⟨hr', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := ht.laws.adPin _ hj _ hτ
    obtain ⟨hr'', hw⟩ := ht.laws.modelW _ hj _ hτ
    have e' : th' = th := funext fun k => funext fun τ => GlobalTheory.SmoothForms.RealPts.infEmb_unique _ _ _ (hth' k τ) (hth k τ)
    subst e'
    exact GlobalTheory.HolDict.BaseFrame.baseFr_of hW _ hM.inf hr _ hth hd (ht.x0 j τ hτ)
      (fun k ρ => (((ht.laws.unf _ hj _ hτ).2.1 k).2 _).2 (ht.laws.pins.1.2.2.2 ρ)) hw (ht.laws.familyUniformisationBasePointOrthogonal _ hj _ hτ)
      fun h => (hL h).imp fun γ hγ => ⟨hγ.1, hγ.2.2.2⟩
  obtain ⟨γ, h1, h2, -⟩ := (hb i (sg0 D A) hg hV).2.2 h
  exact ⟨γ, h1, h2⟩

set_option maxHeartbeats 12000000 in
theorem frame_change : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
    ∀ (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
      (∀ (h : GA D (Wc D i)), ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h →
      ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom)
        (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
        (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ a, z a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
        Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
            GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
          ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ a, Y.θ (z a)) →
    ∀ γ' ∈ GQ (Wc D i),
    ∃ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h ∧
      ∃ M : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E, Formalism.L2.Theta.mt (Wc D i) (γ * γ'⁻¹) = M.map (Formalism.L2.Theta.incA D) ∧
      ∃ (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt),
        ∀ (Z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : Fin (Vc D i).rank → Fin Wt.g → ℂ),
          (∀ c, w c = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, (M * Z) (Fin.cast (rank_Wc i).symm m) n * b n c) →
          GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ' * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Z) =
            ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ c, (Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w c) (w c))) * Y.θ (w c)) := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hS h hx
    ph b hph hbON hpin γ' hγ'
  obtain ⟨γ, hγ, hfr⟩ := exists_frAt hMod hTie i σ hσ hV h
  obtain ⟨M, hM⟩ := Formalism.IndefR.Eqv.mt_GQ _ (mul_mem hγ (inv_mem hγ'))
  obtain ⟨_, Wt, ⟨Y⟩⟩ := exists_witness T i σ hV hTie.laws.toLawsM (hσ ▸ T.toCore.good_σ₀) h
  refine ⟨γ, hγ, hfr, M, hM, Wt, Y, fun Z w hw => ?_⟩
  have hω := hThP.ωP i A.μ0
  have hv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := (hThP.vP i A.μ0).1.2.theta
  have key : thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ' * h) (realPt (Vc D i) (Wc D i) Z) =
      thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (realPt (Vc D i) (Wc D i) (M * Z)) := by
    rw [thetaAt_eq, thetaAt_eq]
    have e : ((1 : GA D (Vc D i)), γ' * h) = (1, (γ * γ'⁻¹)⁻¹) * (1, γ * h) := by
      simp [mul_assoc]
    rw [e, map_mul, Module.End.mul_apply,
      GlobalTheory.RawLift.Move.om_rat_inv_apply hω (mul_mem hγ (inv_mem hγ')) (hω.om_pres _ _ hv),
      GlobalTheory.RawLift.Move.actO_one_left, hM, map_incA_mul_realPt]
  have h1 := hpin h γ hγ hfr hx Wt Y (M * Z) w hw
  rw [key]
  have h3 : Complex.exp (Real.pi / 2 * ∑ c, hermForm Y.Hm (w c) (w c)) *
      ∏ c, Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w c) (w c))) = 1 := by
    rw [← Complex.exp_sum, ← Complex.exp_add, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel, Complex.exp_zero]
  rw [Finset.prod_mul_distrib]
  linear_combination (∏ c, Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w c) (w c)))) * h1 -
    thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (realPt (Vc D i) (Wc D i) (M * Z)) * h3

end GlobalTheory.FrameChangeRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealInputOfBranching
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.RealAsm

variable {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isUnit_Jm' (ε : Fin m → Bool) : IsUnit (Jm ε) := by
  refine IsUnit.of_mul_eq_one (Jm ε) ?_
  simp only [Jm, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem umat_mem (ε : Fin m → Bool) (g : UJ ε) : umat g ∈ UJset ε := g.2

theorem one_mem (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := (1 : UJ ε).2

theorem continuous_umat (ε : Fin m → Bool) : Continuous (fun g : UJ ε => umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem smV_translate {ε : Fin m → Bool} {lam : Fin m → ℝ} {π : Mat m → (H →L[ℂ] H)} (hπ : IsDS ε lam π) {g : Mat m}
    (hg : g ∈ UJset ε) {v : H} (hv : SmV (lieOf (Jm ε)) π v) : SmV (lieOf (Jm ε)) π (π g v) :=
  GlobalTheory.SmLinSub.rep_mem (isUnit_Jm' ε) hπ.2.2.1 hv hg

theorem smV_const_smul {L : Set (Mat m)} {π : Mat m → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : SmV L π v) : SmV L π (a • v) :=
  fun k Xs hX => by simpa only [map_smul] using (hv k Xs hX).const_smul a

theorem integrable_low_coef (hD : DecPow) (hI : PowInt) {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (B : ℝ) (hn : 3 ≤ n)
    (hl : IsHCParam lam) (hg : GapAtLeast ε lam (1000 * (n : ℝ) ^ 3)) (hB : ∀ a, |lam a| ≤ B)
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w) :
    Integrable (fun h : UJ ε => ⟪w, σ (umat h) w⟫_ℂ) (muG ε) := by
  have hdec := hD n ε lam B hn hl hg hB H σ hσ w hw
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hA : 4 * (n : ℝ) ^ 2 + 1 ≤ 40 * (n : ℝ) ^ 2 := by nlinarith
  have hpow := (hI n ε (40 * (n : ℝ) ^ 2) (by omega) hA).1
  refine (hpow.const_mul (Real.exp (100 * (n : ℝ) ^ 3))).mono' ?_ (Filter.Eventually.of_forall fun h => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.inner ((hσ.2.2.1.2.2 w).comp_continuous (continuous_umat ε) (umat_mem ε))
  · exact hdec _ (umat_mem ε h)

theorem big_mul (a b : ℝ) (n : ℕ) (B : ℝ) : big a n B * big b n B = big (a + b) n B := by
  unfold big
  rw [← Real.exp_add]
  ring_nf

theorem big_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) {B : ℝ} (hB : 1 ≤ B) : big a n B ≤ big b n B := by
  unfold big
  apply Real.exp_le_exp.2
  have h1 : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith)
  have h2 : 0 ≤ ((n : ℝ) + 1) ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_right hab h2
  exact mul_le_mul_of_nonneg_right this h1

theorem big_pos (a : ℝ) (n : ℕ) (B : ℝ) : 0 < big a n B := Real.exp_pos _

theorem one_le_B {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
    {mu : Fin n → ℝ} {B : ℝ} (hP : Par e ε lam ε' mu B) : 1 ≤ B := by
  have hn := hP.three_le
  have h := hP.wide ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h0 := abs_le.1 (hP.bound.1 ⟨0, by omega⟩)
  have h1 := abs_le.1 (hP.bound.1 ⟨1, by omega⟩)
  linarith [h0.1, h0.2, h1.1, h1.2]

theorem gap_mono {k : ℕ} {ε : Fin k → Bool} {lam : Fin k → ℝ} {a b : ℝ} (hab : a ≤ b) (h : GapAtLeast ε lam b) :
    GapAtLeast ε lam a := fun x y hxy => hab.trans (h x y hxy)

end GlobalTheory.SepReal.RealAsm

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.RealAsm

end GlobalTheory.SepReal

end
end

