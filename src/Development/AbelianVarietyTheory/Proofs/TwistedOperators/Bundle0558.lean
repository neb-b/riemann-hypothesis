module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralUnitRootNormOneAdele
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0449

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSecRdUNeZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DictLevel

section NonZero

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal GlobalTheory.AdTh.GenConst
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem exists_sec_rdU_ne_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (hr1 : 1 ≤ r) (k : U.Comp) (n : ℕ) (hn : Even n) (x : (U.X k).dom) (hux : IsUnitFr (U.X k) x.1) :
    ∃ f ∈ sec Xo c 0 n, Formalism.L2.PjFree.rdU U f k x.1 ≠ 0 := by
  have hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨-, hL, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ThRead.cmHost_idempotent_trace_eq_one H
  have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun _ => antitone_const, hn⟩
  obtain ⟨Dc, he, -⟩ := exists_dic E H Dw l c σ r W.g n (U.X k) 0 W.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hL hD
  have hs := Dc.sympl
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n hs hn _ hw hw' _ hL 1 _
    (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  obtain ⟨A, hA, ϑ, hϑ, hmean⟩ := uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx hs
    (he ▸ Dc.per_eq) (he ▸ Dc.ty_eq) x hux
  have hT := isTheta1_of_reads_generator E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 _ _ A hs x.2 hL ϑ hϑ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r (U.X k) W.g Dc.bas Dc.idx n hs hn _ hw hw' _ hL v hv x.1 x.2 ϑ hT
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hL hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  obtain ⟨q, hq⟩ := exists_root_ne_zero hs hL x.2 hmk hY hT (ne_zero_of_meanOne hmean)
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond E H Dw l Xo c
  have hLaw : Laws := GlobalTheory.allSixLaws.1
  have hP := one_mem_harmA (Dw := Dw) c n
  obtain ⟨f, hf⟩ := (existsUnique_thRule Xo c nab (GlobalTheory.thValTot_of_chartIndep hLaw hC E H Dw l Xo c nab hnab)
    (fun b => levRep (q b)) hP).exists
  refine ⟨f, GlobalTheory.thetaRule_mem_sec hLaw hC E H Dw l Xo c nab hnab 0 n f ⟨_, _, hP, hf⟩, ?_⟩
  have hval := thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 _ _ A hs x.2 hL Dw.p n Dc.hr
    Dc.eL hU.1 hn (he ▸ Dc.dir_eq) nab hnab ϑ v _ hϑ hv hκ (W.mark k) hmk hA (fun b => levRep (q b)) (Y q)
    (fun b => by
      obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY q b
      exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1
        (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))).symm), hy⟩, hj⟩) 0 1 hP _
    (ThRead.thValAt_evR hC Xo c nab hnab _ hP hf ℂ (unC U k x))
  have h2 := (fock_laws E r _ _ Dc.bas Dc.idx n hs hn x.1 x.2 1 ϑ).2.2.2.2 (fun _ => ϑ) _ v hv.1 hκ (Y q) 0
  have h3 : κ * thA (U.X k) Dc.bas Dc.idx (heisG (U.X k) Dc.bas (Y q) v) x.1 0 ≠ 0 := by
    refine h2 ▸ Finset.prod_ne_zero_iff.2 fun b _ => ?_
    rw [fock, Pi.zero_apply, zero_add, zero_add]
    exact mul_ne_zero (Complex.exp_ne_zero _) (hq b)
  rw [map_one, map_one, thP, polyDeriv_one] at hval
  exact fun h0 => h3 (hval.symm.trans ((dif_pos x.2).symm.trans h0))

end NonZero

section Scalar

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.GeoLevel GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix
open GlobalTheory.Dict (castFr IsUnitFr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Scalar

section Record

open NumberField IsDedekindDomain CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
  {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}

end Record

end GlobalTheory.DictLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatBFSource
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.Unf.FB GlobalTheory.FinPl.HandInvPf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem qS_xZero {S S₀ T T₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ ρ) (c : skewA D ρ) (w : Mx D ρ ρ) :
    d.qS T c (xZero d' ⬝ w) = 0 := by
  have h : adj (xZero d' ⬝ w) ⬝ (gA T ⬝ (xZero d' ⬝ w)) = 0 := by
    rw [xZero, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc (adj d'.jX), d'.gram_XX,
      Matrix.zero_mul, Matrix.mul_zero]
  rw [← cenS_nC, ← neg_inj, LinkPoint.neg_cenS_eq, h, Matrix.zero_mul, trace_zero, map_zero, neg_zero]


set_option maxHeartbeats 1000000 in
theorem flatBF_source {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {n : GA D B.V} (hn : n ∈ flagN B.d) :
    flatBF s (s.om (n, 1) Ψ) = psiBes ψ B.d 1 (vecB B.o B.ζ) n • flatBF s Ψ := by
  have hψ := s.weil.std
  obtain ⟨u, hu, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp B.d hn
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have FS := fun f hf => _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have MV := fun x => (_root_.GlobalTheory.MixValues.mixed_values D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  have hfl : psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.levi u * (B.d.nB b * B.d.nC c)) =
      psiUni ψ u * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) := by
    rw [psiBes_mul B.d ψ 1 _ (B.d.levi_mem_NFlag hu) (mul_mem (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c)),
      psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c), psiBes_nC, mul_one, psiBes_levi]
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular bt, Units.val_one]
    exact Finset.prod_eq_one fun i _ => (hu i i).2
  have hmod : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod J.W.rank u = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet, map_one, NNReal.coe_one, Real.one_rpow]
  have h1 := s.weil.om_pres (B.d.nC c, 1) Ψ hΨ
  have h2 := s.weil.om_pres (B.d.nB b, 1) _ h1
  have e : s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ =
      s.om (B.d.levi u, 1) (s.om (B.d.nB b, 1) (s.om (B.d.nC c, 1) Ψ)) := by
    rw [← om_mul, ← om_mul, mul_assoc, mul_one, mul_one]
  let u' : UX D ρ := ⟨u, hu⟩
  have key : ∀ v : UX D ρ,
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1)
          (yZero B.V₀ ρ (vecB B.o B.ζ)) =
        psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) •
          evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
    intro v
    have ex : xZero J.d ⬝ v.1.1 ⬝ u.1 = xZero J.d ⬝ (v * u').1.1 := by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    have t1 := (FS _ h2).levi u (xZero J.d ⬝ v.1.1)
    rw [hdet, hmod, map_one, inv_one, Circle.coe_one, Complex.ofReal_one, mul_one, one_smul, ex] at t1
    have t2 := (FS _ h1).unip b (xZero J.d ⬝ (v * u').1.1)
    rw [Matrix.mul_assoc (xZero J.d)] at t2
    have t3 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) =
        ψ (B.d.qS J.W c (xZero J.d ⬝ (v * u').1.1)) • B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) :=
      (FS _ hΨ).centre c _
    rw [qS_xZero, AddChar.map_zero_eq_one, one_smul] at t3
    have t4 := (_root_.GlobalTheory.HeisTarget.main D ψ hψ B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _ (MV (xZero J.d ⬝ (v * u').1.1))).1
      ((v * u').1.1 ⬝ b) (yZero B.V₀ ρ (vecB B.o B.ζ))
    have t5 : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ ((v * u').1.1 ⬝ b))) =
        psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) := by
      refine (psi_yZero ψ B.d J.d _ _).trans ?_
      rw [psiBes_nB, psiBes_nB, ← Matrix.mulVec_mulVec, dotProduct_mulVec (ell D ρ) (v * u').1.1, ell_vecMul (v * u').2]
    rw [t5] at t4
    unfold evalAt
    rw [e]
    change I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d B.V₀ ψ s.vT.μ s.vT.𝓕
      (I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d J.W ψ s.vS.μ s.vS.𝓕 _ _) _ = _
    rw [t1, t2]
    change I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d J.W ψ s.vS.μ s.vS.𝓕
      (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) =
      I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) at t3
    rw [t3]
    exact t4
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have hmul : ∀ v : UX D ρ, psiUni ψ (v * u').1 = psiUni ψ v.1 * psiUni ψ u := fun v => by
    rw [← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, Subgroup.coe_mul, map_mul,
      psiFlag_mul J.d ψ (J.d.levi_mem_NFlag v.2) (J.d.levi_mem_NFlag hu)]
  have hu1 : psiUni ψ u * star (psiUni ψ u) = 1 := mul_star_psi hψ _
  funext w
  rw [hfl]
  simp only [Pi.smul_apply, smul_eq_mul]
  change ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν = _ *
    ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ v.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν
  conv_rhs => rw [← integral_mul_right_eq_self _ u', ← integral_const_mul]
  congr 1
  funext v
  rw [key, hmul, star_mul']
  simp only [Pi.smul_apply, smul_eq_mul]
  generalize evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) _ _ = z
  linear_combination (-(star (psiUni ψ v.1) * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) * z)) * hu1

theorem flatBF_bes {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Φ : WO B.V J.W → ℂ}
    (hΦ : IsThetaFunO ψ B.V J.W Φ) {n : GA D B.V} (hn : n ∈ flagN B.d) (a : GA D B.A) (g : GA D B.V) (h : GA D J.W) :
    flatBF s (s.om (n * embA B.d B.o a * g, h) Φ) =
      psiBes ψ B.d 1 (vecB B.o B.ζ) n • s.om₀ (B.o.emb (a, 1), 1) (flatBF s (s.om (g, h) Φ)) := by
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have hΨ := s.weil.om_pres (g, h) Φ hΦ
  have c := _root_.GlobalTheory.FlatEqui.flatBF_equivariant D ψ _ B J s om' hom' _ hΨ a 1 (one_mem _) 1
  have p1 : psiFlag ψ J.d 1 = 1 := by
    have := psiFlag_levi_mul ψ J.d 1 (one_mem (stabX J.d))
    rw [map_one, mul_one] at this
    rw [this, psiUni, Units.val_one, upSum_one, psiE_zero]
  rw [map_one, mul_one, p1, star_one, one_smul, opA, jacT_one, id, show s.om₀ (1, 1) = 1 from map_one _,
    Module.End.one_apply] at c
  rw [← c, ← flatBF_source s (s.weil.om_pres _ _ hΨ) hn, ← om_mul, ← om_mul, one_mul, one_mul]

theorem om_rat_line {V₀ A L S : HSp D} (o : OrthDec V₀ A L) {χ χ' : (AE D)ˣ →* Circle} {om : Om V₀ S}
    (hom : IsWeilDatumO ψ V₀ S χ χ' om) {γ : GA D A} (hγ : γ ∈ GQ A) {f : WO V₀ S → ℂ} (hf : IsThetaFunO ψ V₀ S f) (y : WO L S) :
    om (o.emb (γ, 1), 1) f ((o.resS S).symm (0, y)) = f ((o.resS S).symm (0, y)) := by
  have hact : actO V₀ S (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) = (o.resS S).symm (0, y) := by
    apply (o.resS S).injective
    rw [o.resS_actO, AddEquiv.apply_symm_apply]
    simp only [actO_eq, inv_one, mt_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul]
  have h0 : ∀ F : WO V₀ S → ℂ, ∀ p, heisO ψ V₀ S p F 0 = F p := fun F p => by
    rw [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  have h1 := congrFun (hom.om_heis (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) f hf) 0
  rw [hact, h0] at h1
  rw [← h1, hom.om_aut _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf _), h0]

theorem handBF_move {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') {φ : GA D B.A → ℂ} (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g) {Ξ : WO B.V₀ J.W₀ → ℂ}
    (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (c : ℂ) (hc : c * star c = 1) (a : GA D B.A) :
    handBF s l (star c • rTrans a φ) (c • s.om₀ (B.o.emb (a, 1), 1) Ξ) = handBF s l φ Ξ := by
  funext h w
  unfold handBF
  congr 1
  rw [← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D B.A B.vA.μ B.vA.𝓕 B.vA.haar B.vA.fund
    (fun h₀ => φ h₀ * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) ?_ a]
  · congr 1
    funext x
    rw [map_smul, ← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, rTrans]
    linear_combination (φ (x * a) * s.om₀ (B.o.emb (x * a, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) * hc
  · intro γ hγ x
    have e : s.om₀ (B.o.emb (γ * x, 1), h) Ξ = s.om₀ (B.o.emb (γ, 1), 1) (s.om₀ (B.o.emb (x, 1), h) Ξ) := by
      rw [← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    simp only [hφ γ hγ]
    rw [e, om_rat_line B.o s.weil₀ hγ (s.weil₀.om_pres _ _ hΞ)]

theorem hand_right {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Φ₁ : WO B.V J.W → ℂ) {Φ₂ : WO J.W B'.V → ℂ}
    (hΦ₂ : IsThetaFunO ψ J.W B'.V Φ₂) (φ : GA D B.A → ℂ) (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V)
    {n : GA D B'.V} (hn : n ∈ flagN B'.d) (a : GA D B'.A) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (n * embA B'.d B'.o a * h₂) =
      star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) • rTrans a (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) := by
  have hD : Descent D := GlobalTheory.Desc.weil_data_descend D
  have hΨ₂ := s₂.weil.om_pres (h₁, h₂) Φ₂ hΦ₂
  have e : flatFB s₂ (s₂.om (h₁, n * embA B'.d B'.o a * h₂) Φ₂) = star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) •
      s₂.om₀ (1, B'.o.emb (a, 1)) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := by
    have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B' s₂ _ hΨ₂ 1 a
    rw [map_one] at c
    rw [← c, ← _root_.GlobalTheory.Unf.FB.UnipAct.flatFB_flagN D hD ψ σ J B' s₂ _ (s₂.weil.om_pres _ _ hΨ₂) n hn, ← om_mul, ← om_mul, one_mul, one_mul]
  unfold Chain.hand
  rw [e, handFB_smul_om]

theorem hand_left {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {Φ₁ : WO B.V J.W → ℂ} (Φ₂ : WO J.W B'.V → ℂ)
    (hΦ₁ : IsThetaFunO ψ B.V J.W Φ₁) {φ : GA D B.A → ℂ} (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V) {n : GA D B.V} (hn : n ∈ flagN B.d) (a : GA D B.A) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ (star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • rTrans a φ) (n * embA B.d B.o a * g) h₁ h₂ =
      Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ := by
  have hΞ := (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (_root_.GlobalTheory.Unf.Flat.flatLaw D) ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h₁) Φ₁ hΦ₁)
  unfold Chain.hand
  rw [flatBF_bes s₁ hΦ₁ hn, handBF_move s₁ l hφ hΞ (psiBes ψ B.d 1 (vecB B.o B.ζ) n) (mul_star_psi s₁.weil.std _)]

theorem biLift_last {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {χA χz χS : (AE D)ˣ →* Circle} {om₁ : Om V₀ S} {oma : Om A S} {omz : Om L S}
    (h₁ : IsWeilDatumO ψ V₀ S (χA * χz) χS om₁) (ha : IsWeilDatumO ψ A S χA χS oma) (hz : IsWeilDatumO ψ L S χz χS omz)
    (omb : Om S X) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : ∀ γ ∈ GQ A, ∀ g, φ (γ * g) = φ g) {Ξ : WO V₀ S → ℂ}
    (hΞ : IsThetaFunO ψ V₀ S Ξ) (Φ₂ : WO S T → ℂ) (c : ℂ) (hc : c * star c = 1) (a : GA D A) :
    GlobalTheory.SeeSaw.biLift oma omb vA vS (star c • rTrans a φ) (GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂) =
      GlobalTheory.SeeSaw.biLift oma omb vA vS φ (GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂) := by
  have hsrc := _root_.GlobalTheory.TensorSrc.tensorSource D ψ h₁.std V₀ A L o S
  have e0 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) =
      Φ₂ (o''.resT S v).1 • fun u => Ξ ((o.resS S).symm (u, GlobalTheory.FinPl.kap τ S (o''.resT S v).2)) := fun v => rfl
  have e1 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) =
      c • oma (a, 1) fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v := fun v => by
    funext u
    have k := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz a 1 1 Ξ hΞ (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)).2 u
    rw [show omz (1, 1) = 1 from map_one _] at k
    simp only [Module.End.one_apply] at k
    rw [e0, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FinPl.lastBi, OrthDec.boxT, k]
    ring
  funext h₂
  unfold GlobalTheory.SeeSaw.biLift
  congr 1
  funext h
  rw [← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A vA.μ vA.𝓕 vA.haar vA.fund
    (fun h₀ => φ h₀ * omb (h, h₂) (fun v => oma (h₀, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) ?_ a]
  · congr 1
    funext x
    have e2 : (fun v => oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) 0) =
        c • fun v => oma (x * a, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 := by
      funext v
      rw [e1, map_smul, ← om_mul, mul_one]
      rfl
    rw [e2, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, rTrans]
    linear_combination (φ (x * a) * omb (h, h₂) (fun v => oma (x * a, h)
      (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) * hc
  · intro γ hγ x
    have e : ∀ v, oma (γ * x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 =
        oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 := fun v => by
      have k := ha.om_aut γ hγ 1 (one_mem _) _
        (ha.om_pres (x, h) _ ((hsrc.slice_theta Ξ hΞ).1 (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)))
      rw [← om_mul, one_mul] at k
      rw [e0, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, k]
    simp only [hφ γ hγ, e]

end GlobalTheory.BesMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlaceShiftConditionTorusDiagIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.ShiftInt

variable {D : D7}

theorem mul_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem upSum_single {ρ : ℕ} {i j : Fin ρ} (hj : j.1 = i.1 + 1) (c : AE D) :
    upSum (Matrix.single i j c : Mx D ρ ρ) = c := by
  unfold upSum
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [if_pos hj, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h
    · rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, -⟩
      exact hb rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mxAt_single {P : GlobalTheory.FinPl.Pl D → Prop} {ρ : ℕ} (i j : Fin ρ) {c : AE D} (hc : c ∈ idAt D P) :
    MxAt P (Matrix.single i j c : Mx D ρ ρ) := by
  intro a b
  rw [Matrix.single_apply]
  split_ifs
  · exact hc
  · exact zero_mem _

theorem mul_single_mulVec {m ρ : ℕ} (x : Mx D m ρ) (i j : Fin ρ) (c : AE D) (z : Fin ρ → AE D) :
    (x ⬝ (Matrix.single i j c : Mx D ρ ρ)) *ᵥ z = GlobalTheory.FinPl.colMul x i (c * z j) := by
  funext k
  rw [← Matrix.mulVec_mulVec, Matrix.single_mulVec, Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [GlobalTheory.FinPl.colMul, mul_comm]
  · intro b _ hb
    simp [Function.update_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ _) h


set_option maxHeartbeats 1000000 in
theorem shift_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ N : Mx D ρ ρ, MxAt (· = v) N → (∀ i j, j ≤ i → N i j = 0) → mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ N) ∈ p.A₁ → psiE ψ (upSum N) = 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ _ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t htd ht hsh i j hj
  have hlt : i < j := by rw [Fin.lt_def]; omega
  obtain ⟨h1, -, -⟩ := GlobalTheory.FinPl.InvStep.diag_inv t htd
  have hti : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := GlobalTheory.FinPl.InvStep.levi_sub_one_mem dW ht i i
    rwa [one_apply_eq] at this
  refine GlobalTheory.ColonInt.colon_int D V V₀ ρ dV LV LV₀ v (GlobalTheory.FinPl.TamePlaces.tame D v) hG.sdV hG.monoV i j _ hti ?_
  intro r hr hR
  have hP := hG.prim i j hj
  refine (hP (r * t.1 i i) (Ideal.mul_mem_right _ _ hr)).2 ?_
  intro o ho
  have hψr := (hP r hr).1 hR
  have hro : r * o ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hr
  have hRo : ∀ a : AE D, GlobalTheory.FinPl.colMul dV.jX j a ∈ latV V LV (· = v) →
      GlobalTheory.FinPl.colMul dV.jX i (r * o * a) ∈ latV V LV (· = v) :=
    (hP (r * o) hro).2 fun o' ho' => by rw [mul_assoc]; exact hψr _ (mul_mem_intAt ho ho')
  have hN : (Matrix.single i j (r * t.1 i i * o) : Mx D ρ ρ) = t.1 ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ) := by
    conv_rhs => rw [h1]
    ext a b
    rw [diagonal_mul, Matrix.single_apply, Matrix.single_apply]
    split_ifs with h
    · rw [← h.1]; ring
    · rw [mul_zero]
  have hmove : mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ (Matrix.single i j (r * t.1 i i * o) : Mx D ρ ρ)) =
      xZero dW ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ) := by
    rw [hN, xZero, ← map_inv, ← Matrix.mul_assoc, HypDec.levi_jX, Matrix.mul_assoc, ← Matrix.mul_assoc (t⁻¹).1,
      show (t⁻¹).1 ⬝ t.1 = 1 from t.inv_mul, Matrix.one_mul]
  have hx : MxAt (· = v) (xZero dW ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ)) := by
    intro a b
    have := GlobalTheory.FinPl.InvStep.mat_mem_idAt (xZero dW) _ 1 (mxAt_single i j hro) a b
    rwa [Matrix.mul_one] at this
  have hA : xZero dW ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ) ∈ p.A₁ := by
    refine (hS.a _ hx).2 ((GlobalTheory.FinPl.LatMem.mem_latO_iff D V W LV LW hG.sdV hG.sdW _ _).2 ⟨?_, fun y hy => ?_⟩)
    · rw [HypDec.extX_apply]
      exact fun a b => GlobalTheory.FinPl.InvStep.mat_mem_idAt (xZero dW) _ dV.pX (mxAt_single i j hro) a b
    · have h2 := (hG.cols i _ (Ideal.mul_mem_right _ _ hro)).1 (hRo _ (((hG.monoV y).1 hy).1 j))
      rw [← mul_single_mulVec, Matrix.mulVec_mulVec] at h2
      rw [HypDec.extX_apply]
      exact h2
  have h3 := hsh (Matrix.single i j (r * t.1 i i * o))
    (mxAt_single i j (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hr)))
    (fun a b hab => by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact absurd hlt (not_lt.2 hab))
    (by rw [hmove]; exact hA)
  rwa [upSum_single hj] at h3

end GlobalTheory.AscFin.ShiftInt

end
end

