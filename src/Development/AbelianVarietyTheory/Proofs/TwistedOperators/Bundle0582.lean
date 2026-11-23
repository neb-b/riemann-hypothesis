module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdmissibleSplitHeckePrimeOfConjNe
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorSquareNormEqProdLocalVolumes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntireEqOfMonomialDerivationsAtZeroEq
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

noncomputable section

namespace GlobalTheory.EntireJetUniq


open Formalism.L2.KerInert.PullbackComparison in
theorem eq_of_applyAt0_monomial_eq : ∀ {D : D7} {N N' : ℕ} (Φ Ψ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ), Differentiable ℂ Φ → Differentiable ℂ Ψ → (∀ k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ, Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ = Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Ψ) → Φ = Ψ := by
  intro D N N' Φ Ψ hΦ hΨ h
  classical
  have aΦ := GlobalTheory.analyticOnNhd_of_differentiable_vc Φ hΦ
  have aΨ := GlobalTheory.analyticOnNhd_of_differentiable_vc Ψ hΨ
  have hmono : ∀ (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ),
      Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G =
        (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
    intro k G
    unfold Formalism.MainNotions.GL3Theta.applyAt0
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_pos rfl, one_mul]
  have ht : ∀ α : Formalism.MainNotions.TaylorLogMetric.Mono D N N', Formalism.MainNotions.TaylorLogMetric.taylor D Φ α = Formalism.MainNotions.TaylorLogMetric.taylor D Ψ α := by
    intro α
    have h1 := h α
    rw [hmono, hmono] at h1
    have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    exact mul_left_cancel₀ hne h1
  have hd : ∀ (n : ℕ) (z : Formalism.MainNotions.TaylorLogMetric.VC D N N'),
      iteratedFDeriv ℂ n Φ 0 (fun _ => z) = iteratedFDeriv ℂ n Ψ 0 (fun _ => z) := by
    intro n z
    rw [iter_expand, iter_expand]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [iter_eq_taylor D Φ aΦ κ (ak D κ) (toMultiset_ak D κ).symm,
      iter_eq_taylor D Ψ aΨ κ (ak D κ) (toMultiset_ak D κ).symm, ht]
  obtain ⟨p, r, hp⟩ := aΦ 0 (Set.mem_univ _)
  obtain ⟨q, s, hq⟩ := aΨ 0 (Set.mem_univ _)
  refine aΦ.eq_of_eventuallyEq aΨ (z₀ := 0) ?_
  have hball : Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') (min r s) ∈ nhds 0 :=
    Metric.eball_mem_nhds 0 (lt_min hp.r_pos hq.r_pos)
  filter_upwards [hball] with y hy
  have hy1 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') r :=
    Metric.eball_subset_eball (min_le_left _ _) hy
  have hy2 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') s :=
    Metric.eball_subset_eball (min_le_right _ _) hy
  have s1 := hp.hasSum_iteratedFDeriv hy1
  have s2 := hq.hasSum_iteratedFDeriv hy2
  simp only [zero_add] at s1 s2
  simp only [hd] at s1
  exact s1.unique s2

end GlobalTheory.EntireJetUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointThetaTraceEqPhasedTranslateSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem GlobalTheory.HeckeGeoRead.theta_trace_eq_phased_sum : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ a ∈ Rc, ∀ (C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          (∀ j, j ≠ none → t j = 1) → FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z →
    ∀ (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
      (∀ (h : GA D (Wc D i)), ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h →
      ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom)
        (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
        (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ a, z a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
        Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
            GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
          ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ a, Y.θ (z a)) →
    ∀ γ' ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ' (h * a) →
    ∀ (Wt' : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) (Y' : UnitAt Wt')
      (e : AE D), IsIdemAt e P → ∀ Δ : Finset (WO (Vc D i) (Wc D i)),
        GlobalTheory.HeckeVacuum.IsHalfReps (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (cA D e) a Δ →
    ∀ (ℓ : WO (Vc D i) (Wc D i) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : WO (Vc D i) (Wc D i) → WO (Vc D i) (Wc D i)),
      (∀ x ∈ Δ, (u x).map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) (u x) (R.vacP i) = R.vacP i ∧
          x = actO (Vc D i) (Wc D i) 1 (γ' * h)⁻¹ (ratW (Wc D i) (Vc D i) (ℓ x) - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (ℓ x)) + u x) →
    ∀ (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z' : Fin (Vc D i).rank → Fin Wt'.g → ℂ),
        (∀ a, z' a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt' fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
      Formalism.L2.PjFree.toC (t none : CAt σ) ^ (Vc D i).rank *
                (ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h)) *
                ∏ a, (Complex.exp (-(Real.pi / 2 * hermForm Y'.Hm (z' a) (z' a))) * Y'.θ (z' a)) =
        ∑ x ∈ Δ, R.ψ (-(symplOH (Vc D i) (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (ℓ x)) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ x)) +
            symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) (ℓ x) - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (ℓ x)) (actO (Vc D i) (Wc D i) 1 (γ' * h) (u x)))) *
          R.ωP i A.μ0 (1, γ' * h) (R.vacP i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ x)) := by
  intro D hHk hSplit hVac G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hSet h hx a ha C z hz hx' t ht hFB ph b hph hb hpin γ' hγ' hFr' Wt' Y' e he Δ hΔ ℓ u hu X z' hz'
  obtain ⟨γ, hγ, hFr, M, hM, Wt, Y, h1⟩ := GlobalTheory.FrameChangeRead.frame_change D hHk hSplit hVac G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hSet h hx ph b hph hb hpin γ' hγ'
  obtain ⟨wf, hwf⟩ : ∃ wf : WO (Vc D i) (Wc D i) → Fin (Vc D i).rank → Fin Wt.g → ℂ, ∀ x c, wf x c =
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, (M * (X - ℓ x)) (Fin.cast (rank_Wc i).symm m) n * b n c := ⟨_, fun _ _ => rfl⟩
  have h2 := GlobalTheory.HeckeGeomSum.theta_prod_eq_phased_sum D hHk hSplit hVac G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hSet h hx a ha C z hz hx' t ht hFB ph b hph hb hpin γ' hγ' hFr' Wt' Y' e he Δ hΔ ℓ u hu γ hγ hFr M hM Wt Y X z' hz' wf hwf
  have key : ∀ x, R.ωP i A.μ0 (1, γ' * h) (R.vacP i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ x)) =
      ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ c, (Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (wf x c) (wf x c))) * Y.θ (wf x c)) := fun x => by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt_eq]; exact h1 _ _ (hwf x)
  simp_rw [key]
  rw [mul_right_comm, h2, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjXCols

theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem exists_nat_smul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) (A : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ s ∈ Λ, (N : E) • (A *ᵥ s) ∈ Λ := by
  classical
  obtain ⟨gens, hg⟩ := hΛ.fg
  have key : ∀ g : Fin n → E, ∃ z : ℤ, z ≠ 0 ∧ (z : E) • (A *ᵥ g) ∈ Λ := fun g =>
    GlobalTheory.OrthDual.exists_int_smul_mem Λ (by rw [hΛ.span_eq_top]; trivial)
  choose z hz0 hz using key
  have hnat : ∀ g, ((z g).natAbs : E) • (A *ᵥ g) ∈ Λ := by
    intro g
    rcases Int.natAbs_eq (z g) with h | h
    · have h1 := hz g
      rw [h, Int.cast_natCast] at h1
      exact h1
    · have h1 := hz g
      rw [h, Int.cast_neg, Int.cast_natCast, neg_smul, Submodule.neg_mem_iff] at h1
      exact h1
  refine ⟨∏ g ∈ gens, (z g).natAbs, Finset.prod_pos fun g _ => Int.natAbs_pos.2 (hz0 g), ?_⟩
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    (((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • Matrix.mulVecLin A).restrictScalars (𝓞 E)
  have hle : Submodule.span (𝓞 E) (gens : Set (Fin n → E)) ≤ Λ.comap f := by
    rw [Submodule.span_le]
    intro g hgm
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun g => (z g).natAbs) hgm
    have hk' : (∏ g ∈ gens, (z g).natAbs) = (z g).natAbs * k := hk
    show ((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • (A *ᵥ g) ∈ Λ
    rw [hk', Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (hnat g) k
  rw [hg] at hle
  intro s hs
  exact hle hs

variable {D : D7}

theorem sum_mul_eq (S : HSp D) (N : ℕ) (Q M : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (hQM : S.gram * Q = M * S.gram)
    (s : Fin S.rank → D.host.E) (j : Fin S.rank) :
    ∑ l, (∑ k, star (s k) * S.gram k l) * ((N : D.host.E) • Q) l j =
      ∑ k, star (((N : D.host.E) • (Mᴴ *ᵥ s)) k) * S.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) S.gram) ((N : D.host.E) • Q) =
      Matrix.vecMul (star ((N : D.host.E) • (Mᴴ *ᵥ s))) S.gram := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_smul, hQM, star_smul, star_natCast, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.vecMul_vecMul]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

theorem rat_natCast_smul {m n : ℕ} (N : ℕ) (X : Matrix (Fin m) (Fin n) D.host.E) :
    (rat ((N : D.host.E) • X) : Mx D m n) = N • (rat X : Mx D m n) := by
  ext i j
  simp [rat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]

end GlobalTheory.ProjXCols

namespace GlobalTheory.ProjXCols


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem nsmul_projX_mem_latBig : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G (2 * ρ + 1), N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) ∈ latBig G (2 * ρ + 1) := by
  intro D hQ T L μ0 hL sc G W M hM F hF ρ h
  have hi : 2 * ρ + 1 < D.R.m := by omega
  have h0 : ∀ j, (Node.grid (2 * ρ + 1 + 1) 0 : Node) ≠ .grid 0 j := fun j hh => by
    injection hh with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.isV (show (Node.grid (2 * ρ + 1 + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  obtain ⟨N, hN, hNs⟩ := exists_nat_smul_mulVec_mem _ (selfDual_isFullLattice _ _ hsd)
    ((G.V (.grid (2 * ρ + 1 + 1) 0)).gram * (F.dB ρ h).e * (F.dB ρ h).e'ᴴ)ᴴ
  refine ⟨N, hN, fun u hu => ?_⟩
  have e1 : N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) =
      u ⬝ (rat ((N : D.host.E) • ((F.dB ρ h).e * (F.dB ρ h).qX)) :
        Mx D (G.V (.grid (2 * ρ + 1 + 1) 0)).rank (G.V (.grid (2 * ρ + 1 + 1) 0)).rank) := by
    rw [rat_natCast_smul, rat_mul, Matrix.mul_smul, Matrix.mul_assoc]
    rfl
  rw [e1]
  refine GlobalTheory.CoreRowLat.latO_mul_right _ (fun s hs => ⟨_, hNs s hs, fun j => ?_⟩) hu
  refine sum_mul_eq _ N _ _ ?_ s j
  simp only [HypDec.qX, Matrix.mul_assoc]

end GlobalTheory.ProjXCols
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

namespace GlobalTheory.LevelIndex

theorem levelIndexNormC : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → LevelIndexNormC R F := by
  intro hLoc D G _ _ Pl0 T A Ks _ _ _ R F hPM
  intro i t σ s P cμ cη m ω BW f₀ f c io hd
  classical
  have hC : Hk3.Core R F := hd.1
  obtain ⟨Hl, cl, hP⟩ := hd.2.2.2.1
  refine ⟨?_, fun μ 𝓧 hμ => ?_⟩
  · obtain ⟨c0, hc0⟩ := hC.lev.βV i
    rw [one_pow] at hc0
    exact _root_.GlobalTheory.LevelInLatStab.lev_le_latLev D (Vc D i) _ _ _ hc0
  · have hn := _root_.GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt hLoc R F hPM i t σ s P cμ cη m ω BW f₀ f c io hd Hl cl hP μ 𝓧 hμ
    rw [_root_.GlobalTheory.ParIndex.relIndex_levV_latLev R F i t P m Hl cl hC hP, hn]
    obtain ⟨hdis, hinj, hsp⟩ := _root_.GlobalTheory.TwistTypePlaces.places_split R F hC t
    have hrank : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have hrt : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have key : ∀ PP ∈ R.Pg ∪ R.Q t, (dLoc D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))⁻¹ =
        (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) *
          (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
      intro PP hPP
      obtain ⟨h2, hq⟩ := hsp PP hPP
      haveI : Fact PP.asIdeal.IsMaximal := ⟨PP.isMaximal⟩
      letI : Field (kP PP) := Ideal.Quotient.field _
      rw [_root_.GlobalTheory.Twist.GLIndexLoc.index_loc (kP PP) _ D.R.r D.R.t hrt, hrank]
      unfold dLoc quadTerm quadSign
      rw [if_pos h2, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [inv_inv, hq]
      simp
    have hcard : ∀ PP : Pl D.host.E, ∀ n : ℕ, (Nat.card (GL (Fin n) (kP PP)) : ℝ) ≠ 0 := fun PP n => by
      have : Finite (GL (Fin n) (kP PP)) := inferInstance
      exact_mod_cast (Nat.card_pos (α := GL (Fin n) (kP PP))).ne'
    have hHl : ∀ PP, (Nat.card (Hl PP) : ℝ) ≠ 0 := fun PP => by
      exact_mod_cast (Nat.card_pos (α := Hl PP)).ne'
    have hq0 : ∀ PP : Pl D.host.E, (Nat.card (kP PP) : ℝ) ≠ 0 := fun PP => by
      exact_mod_cast (Nat.card_pos (α := kP PP)).ne'
    unfold finS
    rw [Finset.prod_image hinj, Finset.prod_union hdis, ← Finset.prod_attach R.Pg, mul_mul_mul_comm,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP.1 (Finset.mem_union_left _ PP.2)]
      field_simp [hHl PP, hcard PP.1, hq0 PP.1]
    · refine Finset.prod_congr rfl fun PP hPP => ?_
      rw [key PP (Finset.mem_union_right _ hPP)]
      field_simp [hcard PP, hq0 PP]

end GlobalTheory.LevelIndex

end
end

