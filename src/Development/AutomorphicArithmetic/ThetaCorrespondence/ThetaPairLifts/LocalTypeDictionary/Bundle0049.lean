module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridKernelPairingIndependentOfExpansion
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1686
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0598
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0042
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0026

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull
namespace GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem rowSum_of_hypotheses_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ t a => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.RowClaim.Test.pde_ne_q hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := GlobalTheory.RowClaim.Test.guard hS t
  obtain ⟨h1, h2, h3, h4, h5⟩ := GridChoice.sumOK_classes ch.W ch.S.toGridChoice t (ch.Phi a) hL
  obtain ⟨f1, f2, -⟩ := GridChoice.sumOK_flat_fin_ex hL ch.S.toGridChoice t (ch.Phi a) hde hc
  obtain ⟨v1, v2⟩ := _root_.GlobalTheory.FunObj.sumOK_vec_indep D T R.toLevCh ch.sc ch.G ch.W Set.univ ch.S.toGridChoice A.μ0 hL t trivial (ch.Phi a)
  exact
    { flat := f1
      flatA := fun w _ => flatIntegrable_aaVac_of_conductor ch.W w (hasConductor_psiAt_AA ch.W w)
      fin := f2
      ex := GridChoice.sumOK_ex hL ch.S.toGridChoice t (ch.Phi a) hde hc
      vec := v1
      indep := v2
      cls := h1
      gam := h2
      wts := h3
      br := h4
      read := h5 }
end GlobalTheory.RowClaim
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumOKK_of_theta_local_inputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.SumOKK := by
  first | exact @_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt | exact _root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmoothOfThetaLiftFiniteSum
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ColFockRed
open GlobalTheory.Grid
theorem theta_lift_finite_sum_smooth : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    ∀ (n : ℕ) (F : Fin n → (G.Xp j).Cusp R.θ) (w : Fin n → SmT (G.Xp j).M),
    (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g) (G.measX j).fd (G.measX j).ν) →
    ∃ (k : ℕ) (F' : Fin k → (G.Xp (j + 1)).Cusp R.θ) (z : Fin k → SmT (G.Xp (j + 1)).M),
      (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g ∂(G.measX j).ν) = ∑ i, (F' i).1 (z i) := by
  intro hL _hPr D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t j hj Φ hΦ n F w hint
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hRB hG
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨νS, PS, hS⟩ := xp_is hG j hj.le
  obtain ⟨νT, PT, hT⟩ := xp_is hG (j + 1) hj
  obtain ⟨hsig, hdef⟩ := GlobalTheory.ColTypeLift.xp_definite hG j hj.le
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.DefCenChar.cusp_hasCen D R.θ hθ (G.Xp j) νS PS hS
  have hψc : GlobalTheory.SeeSaw.HasCen (G.Xp j).V χ (∑ i, (F i).1 (w i)) := fun z hz hc h => by
    simp only [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hχ (F i) (w i) z hz hc h
  have hψa : GlobalTheory.Unf.IsContAut (G.Xp j).V (∑ i, (F i).1 (w i)) := by
    refine ⟨fun γ hγ g => ?_, by rw [Finset.sum_fn]; exact continuous_finsetSum _ fun i _ => (isContAut_cusp (F i) (w i)).2⟩
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (isContAut_cusp (F i) (w i)).1 γ hγ g
  obtain ⟨hν, hfd⟩ := measX_haar_fd hG j hj.le
  have hA := hG.arrows.col t j hj
  obtain ⟨Φ', hΦ', heig, heq⟩ := _root_.GlobalTheory.CenAvgOne.exists_central_average_one D R.ψ _ _ _ _ (G.col t j).ω hA.weil hsig hdef _ _ hν hfd χ _ hψc hψa Φ hΦ hint
  obtain ⟨k, f, p, hf, hsum⟩ := _root_.GlobalTheory.CenFockGen.cenFock_fin D R.ψ R.θ hθ (G.Xp j) (G.Xp (j + 1)) νS νT PS PT hS hT (G.col t j) _ _ hA
    (fun z => (χ z)⁻¹) Φ' hΦ' heig
  have hcol := hCA.col t j hj
  choose F' hF' hI using fun (l : Fin k) (i : Fin n) => hcol (f l) (hf l) (F i).1 (F i).2
  refine ⟨k * n, fun q => ⟨F' (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2, hF' _ _⟩,
    fun q => (G.col t j).It (p (finProdFinEquiv.symm q).1) (w (finProdFinEquiv.symm q).2), ?_⟩
  funext h
  rw [heq h, hsum]
  have key : ∀ g, thetaKO (G.col t j).ω g h (∑ l, fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (∑ i, (F i).1 (w i)) g = ∑ l, ∑ i, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
        (F i).1 (w i) g := fun g => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [thetaKO, map_sum, Finset.sum_apply, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ => (hI l i (p l) (w i) h).1]
  simp_rw [integral_finsetSum _ fun i _ => (hI _ i _ (w i) h).1]
  have e2 : ∀ l i, ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (F i).1 (w i) g ∂(G.measX j).ν = F' l i ((G.col t j).It (p l) (w i)) h := fun l i => (hI l i (p l) (w i) h).2
  simp_rw [e2]
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_apply]
  exact (finProdFinEquiv.symm.sum_comp (fun x : Fin k × Fin n => F' x.1 x.2 ((G.col t j).It (p x.1) (w x.2)) h)).symm
end GlobalTheory.ColFockRed
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_of_theta_lift_finite_sum : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    ∀ (n : ℕ) (F : Fin n → (G.Xp j).Cusp R.θ) (w : Fin n → SmT (G.Xp j).M),
    (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g) (G.measX j).fd (G.measX j).ν) →
    ∃ (k : ℕ) (F' : Fin k → (G.Xp (j + 1)).Cusp R.θ) (z : Fin k → SmT (G.Xp (j + 1)).M),
      (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g ∂(G.measX j).ν) = ∑ i, (F' i).1 (z i) := by
  first | exact @_root_.GlobalTheory.ColFockRed.theta_lift_finite_sum_smooth | exact _root_.GlobalTheory.ColFockRed.theta_lift_finite_sum_smooth | (intros; apply _root_.GlobalTheory.ColFockRed.theta_lift_finite_sum_smooth <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SphericalVectorFixedAtAlmostAllPlaces
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
namespace GlobalTheory.LocVacFix
theorem vacuum_fixed_at_cofinitely_many_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v, v ∉ S₀ → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT
  classical
  refine ⟨(bad_finite F).toFinset ∪ X.T, fun v hv k hk => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hv
  obtain ⟨⟨hd, h6⟩, hvT⟩ := hv
  have hψ := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hT.base.std v hd
  obtain ⟨h2, h3⟩ := two_three_of_six v h6
  by_cases hin : ∃ w, Formalism.UG.IsInertAt F E v w
  · obtain ⟨w, hw⟩ := hin
    exact GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum F E σ B a a' G X om om' hT v w hw hvT k hk
  · push_neg at hin
    exact vac_fixed_split F E σ B a a' G X om om' hT v hin hvT hψ h2 h3 k hk
end GlobalTheory.LocVacFix
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
theorem _root_.GlobalTheory.T.spherical_vector_fixed_at_almost_all_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v, v ∉ S₀ → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  first | exact @_root_.GlobalTheory.LocVacFix.vacuum_fixed_at_cofinitely_many_places | exact _root_.GlobalTheory.LocVacFix.vacuum_fixed_at_cofinitely_many_places | (intros; apply _root_.GlobalTheory.LocVacFix.vacuum_fixed_at_cofinitely_many_places <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplittingOfMovedKappaTwist
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
namespace GlobalTheory.SplitMoveKappa
theorem movedKappa_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y) (c * κ) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hJ e he s s' hs hs'
  obtain ⟨x₀, y₀, hx₀, hy₀, ζ, ⟨n, hn, hζ⟩, r, hr, hJ'⟩ := _root_.GlobalTheory.T.twist_jetKappa_split_move hP hI ch hch p hp x y κ hJ e he s s' hs hs'
  have h1 := _root_.GlobalTheory.T.twist_norm_kappa_moved_place hP hI ch hch p hp x y κ hJ
  have h2 := _root_.GlobalTheory.T.twist_norm_kappa_moved_place hP hI ch hch p hp _ _ _ hJ'
  have hζn : ‖ζ‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, hζ, norm_one])
  have hχn : ‖((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ)‖ = 1 := Circle.norm_coe _
  have hr1 : (r : ℂ) = 1 := by
    rw [norm_mul, norm_mul, norm_mul, hζn, hχn, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h2
    simp only [mul_one] at h2
    rw [h2]; simp
  rw [hr1, one_mul] at hJ'
  have hA := _root_.GlobalTheory.T.twist_split_character_values hP hI ch hch p hp e he x₀ hx₀
  have hB := _root_.GlobalTheory.T.twist_split_character_values hP hI ch hch p hp e he y₀ hy₀
  have hco : ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) =
      ((ch.G.chrT p x₀ : Circle) : ℂ)⁻¹ * ((ch.G.chrS p y₀ : Circle) : ℂ) := by
    rw [Circle.coe_mul, Circle.coe_inv]
  have hm : Mod1All ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) := by
    rw [hco]
    exact GlobalTheory.FamilyTieProof.mod1All_mul' (GlobalTheory.FamilyTieProof.mod1All_inv hA.1.2) hB.1.1
  refine ⟨ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ), GlobalTheory.FamilyTieProof.mod1All_mul' (mod1All_root hn hζ) hm,
    fun q _ hq => ?_, hJ'⟩
  refine unitAt_mul (qbar_of_root hn hζ) hm.1 (unitAt_root q hn hζ) ?_
  rw [hco]
  exact unitAt_mul (inv_mem hA.1.2.1) hB.1.1.1 (unitAt_inv hA.1.2.1 ((hA.2 q hq).2)) ((hB.2 q hq).1)
end GlobalTheory.SplitMoveKappa
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
theorem _root_.GlobalTheory.T.splitting_of_moved_kappa_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y) (c * κ) := by
  first | exact @_root_.GlobalTheory.SplitMoveKappa.movedKappa_split | exact _root_.GlobalTheory.SplitMoveKappa.movedKappa_split | (intros; apply _root_.GlobalTheory.SplitMoveKappa.movedKappa_split <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareAgreeLineDerivationIsDerivation
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SquareAgree.LineDerFunB
end GlobalTheory.SquareAgree.LineDerFunB
open GlobalTheory.SquareAgree.LineDerFunB in
theorem GlobalTheory.SquareAgree.LineDerFunB.lineDerivation_isDerivation_of_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hO.JX (oneP θ X τ Y t)) ΦD x) (Ψ x) 0) → ∀ Φ Φ',
    IsDatum Γ.M' ψ cB ΦD Φ → IsDatum Γ.M' ψ cB Ψ Φ' → IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hT τ Y hY ΦD hΦD Ψ hΨ hD Φ Φ'
    hDat hDat'
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.T.twist_lie_derivative_model hP Bs Γ Xc om om' hT γ hγ
  obtain ⟨m, f, φ, hf, rfl⟩ := exists_sum_pure Γ.M' Bs.ψ Bs.emb hΦD
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 :=
    fun i => ((hf i).2.2.and hT.geo.hM'.std).mono fun v h => h.1.trans h.2
  have hder : ∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x)
      ((∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i)) x) 0 := by
    intro x
    have e1 : (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x) =
        fun t => ∑ i, om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
    rw [e1, Finset.sum_apply]
    exact HasDerivAt.fun_sum fun i _ =>
      (hδ _ (hf i).1).2 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hΨe : Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i) := by
    funext x
    have h1 := hD x
    simp only [← hγt] at h1
    exact h1.unique (hder x)
  intro z
  obtain ⟨u, rfl⟩ := cB.surjective z
  have hs : IsStd ψ := hO.psi ▸ hT.base.std
  have hg : Γ.M'.IsGood ψ := hO.psi ▸ hT.geo.hM'
  have hw : Γ.M'.IsWeil ψ Xc.α (Xc.α / Xc.β) om' := hO.psi ▸ hT.weil'
  have key := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M' ψ Xc.α (Xc.α / Xc.β) om' hT.base.cm hs hg hw γ hγ m f (fun i => δ (f i)) φ
    (fun i => (hf i).2) (fun i => (hδ _ (hf i).1).2) u
  have e2 : (fun t : ℝ => ωB (1, oneP θ X τ Y t) Φ (cB u)) = fun t : ℝ =>
      GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))) := by
    funext t
    have h1 := (hO.weilB _ Φ hDat 1 (oneP θ X τ Y t)).2 u
    rw [conjU_one, ← hγt t] at h1
    exact h1.symm
  rw [e2, ← hDat'.2 u, hΨe]
  exact key
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
theorem _root_.GlobalTheory.T.squareAgree_lineDerivation_isDerivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hO.JX (oneP θ X τ Y t)) ΦD x) (Ψ x) 0) → ∀ Φ Φ',
    IsDatum Γ.M' ψ cB ΦD Φ → IsDatum Γ.M' ψ cB Ψ Φ' → IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' := by
  first | exact @_root_.GlobalTheory.SquareAgree.LineDerFunB.lineDerivation_isDerivation_of_datum | exact _root_.GlobalTheory.SquareAgree.LineDerFunB.lineDerivation_isDerivation_of_datum | (intros; apply _root_.GlobalTheory.SquareAgree.LineDerFunB.lineDerivation_isDerivation_of_datum <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralLineHasDerivAt
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace GlobalTheory.ThetaIntegralLine
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}
theorem thetaIntegral_line_hasDerivAt (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (χY χW : Chr F E) (om : Rep σ Y W)
    (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (hw : M.IsWeil ψ χY χW om) (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ)
    (hcont : ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f φ) h)
    {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ Φ₁ ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) ∧
      ∀ h, HasDerivAt (fun t : ℝ => M.I om Φ (h * γ (Multiplicative.ofAdd t))) (M.I om Φ₁ h) 0 := by
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw).pres
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun x => ?_, fun h => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · have e : ∀ h', M.I om 0 h' = 0 := fun h' => by simpa using I_smul M om 0 0 h'
      simpa [e] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add Φ Ψ hΦ hΨ ihΦ ihΨ =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ihΦ
    obtain ⟨Ψ₁, m₂, p₂, q₂⟩ := ihΨ
    refine ⟨Φ₁ + Ψ₁, Submodule.add_mem _ m₁ m₂, fun x => ?_, fun h => ?_⟩
    · simpa only [map_add (f := _), Pi.add_apply] using (p₁ x).fun_add (p₂ x)
    · simpa only [I_add M om hpres hconv hΦ hΨ, I_add M om hpres hconv m₁ m₂] using (q₁ h).fun_add (q₂ h)
  | smul c Φ hΦ ih =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ih
    refine ⟨c • Φ₁, Submodule.smul_mem _ c m₁, fun x => ?_, fun h => ?_⟩
    · simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using (p₁ x).const_mul c
    · simpa only [I_smul] using (q₁ h).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hφ, rfl⟩ := hΦ
    obtain ⟨c, c', h0, hlim, hacts⟩ := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP M ψ χY χW om hcm hψ hw γ hγ f
    have hmem : ∀ u : SInf F (Fin n × Fin d), pureA F u φ ∈ schA F (Fin n × Fin d) :=
      fun u => Submodule.subset_span ⟨u, φ, hφ, rfl⟩
    have hR : Rest (evI F) (⇑f) (fun x : Fin n × Fin d → AF F => φ fun i => (x i).2) := by
      refine ⟨fun x z hz => congrArg φ (funext fun i => ?_), hmem f⟩
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at z hz i, add_zero]
    have hc : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (pureA F f φ) = pureA F (c t) φ := fun t => hacts t _ hR
    refine ⟨pureA F c' φ, hmem c', fun x => ?_, fun h => ?_⟩
    · have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
        (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
          (fun j => evI F (x j))).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
      have h2 : HasDerivAt (fun t : ℝ => c t (fun j => evI F (x j)) * φ fun i => (x i).2)
          (c' (fun j => evI F (x j)) * φ fun i => (x i).2) 0 := by
        rw [hasDerivAt_iff_tendsto_slope]
        refine (((ev.tendsto c').comp hlim).mul_const _).congr' (Filter.Eventually.of_forall fun t => ?_)
        rw [slope_def_module, h0]
        simp only [Function.comp_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
        ring
      simp only [hc]
      exact h2
    · let L : SInf F (Fin n × Fin d) →ₗ[ℝ] ℂ :=
        { toFun := fun u => M.I om (pureA F u φ) h
          map_add' := fun u u' => by
            have e : pureA F ⇑(u + u') φ = pureA F u φ + pureA F u' φ := by
              funext x; simp [pureA, add_mul]
            rw [e, I_add M om hpres hconv (hmem u) (hmem u')]
          map_smul' := fun s u => by
            have e : pureA F ⇑(s • u) φ = (s : ℂ) • pureA F u φ := by
              funext x; simp [pureA, mul_assoc, Complex.real_smul]
            rw [e, I_smul, RingHom.id_apply, Complex.real_smul] }
      have hL : Continuous L := hcont φ hφ h
      have hcurve : (fun t : ℝ => M.I om (pureA F f φ) (h * γ (Multiplicative.ofAdd t))) = fun t => L (c t) := by
        funext t
        rw [← I_om_one, hc]
        rfl
      rw [hcurve, hasDerivAt_iff_tendsto_slope]
      refine ((hL.tendsto c').comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, slope_def_module, h0, sub_zero, map_smul, map_sub]
end GlobalTheory.ThetaIntegralLine
end
end
end

