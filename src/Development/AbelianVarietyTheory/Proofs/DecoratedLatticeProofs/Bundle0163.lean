module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomain
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.DefFund

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem exists_measurable_fundamentalDomain_subset [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]
    {K : Set G} (hK : IsClosed K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) :
    ∃ S ⊆ K, MeasurableSet S ∧ IsFundamentalDomain Γ S μ := by
  classical
  have := GlobalTheory.countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Γ
  obtain ⟨c, hc⟩ := exists_injective_nat Γ
  let S : Set G := K ∩ ⋃ g : Γ, ((fun y => g • y) ⁻¹' D ∩ ⋂ h : Γ, ⋂ _ : c h < c g, ((fun y => (h⁻¹ * g) • y) ⁻¹' K)ᶜ)
  have hS : ∀ y, y ∈ S ↔ y ∈ K ∧ ∃ g : Γ, g • y ∈ D ∧ ∀ h : Γ, c h < c g → (h⁻¹ * g) • y ∉ K := fun y => by
    simp only [S, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
  have hSm : MeasurableSet S :=
    hK.measurableSet.inter <| MeasurableSet.iUnion fun g => (measurable_const_smul g hD).inter <|
      MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ => (measurable_const_smul _ hK.measurableSet).compl
  refine ⟨S, Set.inter_subset_left, hSm, IsFundamentalDomain.mk' hSm.nullMeasurableSet fun x => ?_⟩
  obtain ⟨d, hd, hdu⟩ := hu x
  have hex : ∃ n, ∃ g : Γ, c g = n ∧ (g⁻¹ * d) • x ∈ K := by
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine ⟨_, d * (⟨γ, hγ⟩ : Γ)⁻¹, rfl, ?_⟩
    rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
    exact h
  obtain ⟨g, hg, hgK⟩ := Nat.find_spec hex
  refine ⟨g⁻¹ * d, (hS _).2 ⟨hgK, g, ?_, fun h hh hK' => ?_⟩, fun k hk => ?_⟩
  · rw [smul_smul, mul_inv_cancel_left]; exact hd
  · refine Nat.find_min hex (hg ▸ hh) ⟨h, rfl, ?_⟩
    rwa [smul_smul, mul_assoc, mul_inv_cancel_left] at hK'
  · obtain ⟨hkK, g', h1, h2⟩ := (hS _).1 hk
    rw [smul_smul] at h1
    have e : g' * k = d := hdu _ h1
    have ek : k = g'⁻¹ * d := by rw [← e, inv_mul_cancel_left]
    have hle : Nat.find hex ≤ c g' := Nat.find_min' hex ⟨g', rfl, ek ▸ hkK⟩
    rcases hle.eq_or_lt with h | h
    · rw [ek, hc (hg.trans h)]
    · refine (h2 g (hg ▸ h) ?_).elim
      rw [smul_smul, mul_assoc, e]
      exact hgK

end GlobalTheory.DefFund

theorem GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact :
    ∀ (D : D7) (A : HSp D), HSpace.SigOK A → HSpace.IsPosDef A → ∀ m : Measure (GA D A), m.IsHaarMeasure → GlobalTheory.Unf.CoCpt A ∧ ∃ (X K : Set (GA D A)), MeasurableSet X ∧ IsFundamentalDomain (GQ A) X m ∧ IsCompact K ∧ X ⊆ K := by
  intro D A hs hp m hm
  have hc : GlobalTheory.Unf.CoCpt A := (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D A).2 fun τ => by
    have h1 := hs (tauE D τ)
    rw [hp (tauE D τ)] at h1
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature h1
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨K, hK, hcov⟩ := hc
  obtain ⟨X, hXK, hXm, hX⟩ := GlobalTheory.DefFund.exists_measurable_fundamentalDomain_subset (GQ A) hK.isClosed hcov m
  exact ⟨⟨K, hK, hcov⟩, X, K, hXm, hX, hK, hXK⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DerivativeClosedFunctionClassSmoothAndSchwartz
section
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

namespace GlobalTheory.Unf.PartialClass

theorem smooth_schwartz : ∀ (k : ℕ) (V : Set ((Fin k → ℝ) → ℂ)), (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ x : Fin k → ℝ, HasDerivAt (fun t : ℝ => φ (x + t • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' x) 0) → (∀ φ ∈ V, ContDiff ℝ ∞ φ) ∧ ((∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖φ x‖ ≤ C) → ∀ φ ∈ V, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ x, g x = φ x) := by
  intro k V hc hd
  have hsm : ∀ φ ∈ V, ContDiff ℝ ∞ φ := by
    refine GlobalTheory.Unf.MatCoef.contDiff_of_partials (fun F => F ∈ V) hc ?_
    intro F hF i
    obtain ⟨φ', hφ', hD⟩ := hd F hF i
    refine ⟨1, fun _ => fun _ => 1, fun _ => φ', fun _ => contDiff_const, fun _ => hφ', ?_⟩
    intro t
    simpa using hD t
  refine ⟨hsm, fun hdec => ?_⟩
  choose φ' hφ' hD using hd

  have hfd : ∀ φ (hφ : φ ∈ V), fderiv ℝ φ = fun x => ∑ i, φ' φ hφ i x •
      (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (1 : ℂ) := by
    intro φ hφ
    funext x
    have h := _root_.GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs k φ (fun i => φ' φ hφ i) (fun i => hc _ (hφ' φ hφ i)) (fun i t => hD φ hφ i t) x
    rw [h.fderiv]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext v
    simp [mul_comm]
  have key : ∀ j : ℕ, ∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖iteratedFDeriv ℝ j φ x‖ ≤ C := by
    intro j
    induction j with
    | zero =>
      intro φ hφ N
      obtain ⟨C, hC⟩ := hdec φ hφ N
      exact ⟨C, fun x => by simpa [norm_iteratedFDeriv_zero] using hC x⟩
    | succ j ih =>
      intro φ hφ N
      choose C hC using fun i => ih (φ' φ hφ i) (hφ' φ hφ i) N
      set L : Fin k → ((Fin k → ℝ) →L[ℝ] ℂ) := fun i =>
        (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (1 : ℂ)
      refine ⟨∑ i, ‖(ContinuousLinearMap.id ℝ ℂ).smulRight (L i)‖ * C i, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv, hfd φ hφ]
      have hsum : iteratedFDeriv ℝ j (fun x => ∑ i, φ' φ hφ i x • L i) x =
          ∑ i, ((ContinuousLinearMap.id ℝ ℂ).smulRight (L i)).compContinuousMultilinearMap
            (iteratedFDeriv ℝ j (φ' φ hφ i) x) := by
        rw [iteratedFDeriv_fun_sum_apply]
        · refine Finset.sum_congr rfl fun i _ => ?_
          exact iteratedFDeriv_smul_const_apply
            (((hsm _ (hφ' φ hφ i)).of_le (mod_cast le_top)).contDiffAt)
        · intro i _
          exact (((hsm _ (hφ' φ hφ i)).of_le (mod_cast le_top)).smul contDiff_const).contDiffAt
      rw [hsum]
      refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      refine le_trans (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
        (by positivity)) ?_
      have := hC i x
      nlinarith [norm_nonneg ((ContinuousLinearMap.id ℝ ℂ).smulRight (L i)),
        norm_nonneg (iteratedFDeriv ℝ j (φ' φ hφ i) x), pow_nonneg (norm_nonneg x) N]
  intro φ hφ
  refine ⟨{ toFun := φ, smooth' := hsm φ hφ, decay' := fun N j => ?_ }, fun x => rfl⟩
  obtain ⟨C, hC⟩ := key j φ hφ N
  exact ⟨C, hC⟩

end GlobalTheory.Unf.PartialClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLagrangianTransverseInOpenOrbit
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

namespace GlobalTheory.Core.Rk.Dich

theorem exists_mem_siegel_of_diagSnd : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → x = 0) → ∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V := by
  intro D V γ hγ γi hγi hinj
  have hinc : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  obtain ⟨g, hg, hg1, hg2⟩ := exists_rat (dblSp V) hγ
  have hγi' : γi = (g⁻¹).1 := Matrix.map_injective hinc (hγi.symm.trans hg2)
  have hgγ : g.1 * γi = 1 := by rw [hγi']; exact Units.mul_inv g
  have hgi : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * dblGram finSumFinEquiv V.gram * γi =
      dblGram finSumFinEquiv V.gram := by
    have h := inv_mem hg
    change Formalism.UG.cT _ (g⁻¹).1 * (dblSp V).gram * (g⁻¹).1 = (dblSp V).gram at h
    rw [gram_hdbl] at h
    rw [hγi']; exact h
  have hiso := isotropic_diag hgi
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set P := leviMat finSumFinEquiv γi with hP
  set Q := diagSnd γi with hQ
  have hQu : IsUnit Q := Matrix.mulVec_injective_iff_isUnit.1 fun x y h =>
    sub_eq_zero.1 (hinj _ (by rw [Matrix.mulVec_sub, h, sub_self]))
  have hQ1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)
  have hcT : ∀ M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E,
      Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
    intro M N; simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcT1 : Formalism.UG.cT σ Q⁻¹ * Formalism.UG.cT σ Q = 1 := by
    rw [← hcT, hQ1]; simp [Formalism.UG.cT]
  have hδ : Formalism.UG.cT σ (P * Q⁻¹) * V.gram * (P * Q⁻¹) = V.gram := by
    calc Formalism.UG.cT σ (P * Q⁻¹) * V.gram * (P * Q⁻¹)
        = Formalism.UG.cT σ Q⁻¹ * (Formalism.UG.cT σ P * V.gram * P) * Q⁻¹ := by simp only [hcT, Matrix.mul_assoc]
      _ = V.gram := by
        rw [hiso]; simp only [Matrix.mul_assoc]
        rw [hQ1, Matrix.mul_one, ← Matrix.mul_assoc, hcT1, Matrix.one_mul]
  have hdet : IsUnit (P * Q⁻¹).det := by
    have h := congrArg Matrix.det hδ
    rw [Matrix.det_mul, Matrix.det_mul] at h
    have hJ : IsUnit V.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V
    rw [← h] at hJ
    exact isUnit_of_mul_isUnit_right hJ
  set d : GL (Fin V.rank) D.host.E := ((Matrix.isUnit_iff_isUnit_det (P * Q⁻¹)).2 hdet).unit with hd
  have hdv : d.1 = P * Q⁻¹ := rfl
  have hdU : d ∈ Formalism.UG.UJ σ V.gram := by
    change Formalism.UG.cT σ d.1 * V.gram * d.1 = V.gram
    rw [hdv]; exact hδ
  obtain ⟨δ', hδ'Q, hδ'⟩ := exists_of_rat V hdU
  refine ⟨δ'⁻¹, inv_mem hδ'Q, ?_⟩
  rw [show (io V (δ'⁻¹, 1))⁻¹ = io V (δ', 1) by rw [← map_inv, Prod.inv_mk, inv_inv, inv_one]]
  have hm : (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (δ', 1))).1 =
      (g.1 * blkMat finSumFinEquiv (P * Q⁻¹) 1).map (incA D) := by
    rw [map_mul, Units.val_mul, hg1, matHom_io, val_blkGL, hδ', map_one, Units.val_one, hdv]
    conv_rhs => rw [Matrix.map_mul, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  refine mem_siegelOf.2 ?_
  change KeepsDiag finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (δ', 1))).1
  rw [hm]
  refine KeepsDiag.map _ (keepsDiag_of_mulVec fun w hw => ?_) _
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
  rw [← Matrix.mulVec_mulVec, blkMat_mulVec, Matrix.one_mulVec]
  have h2 : pairVec finSumFinEquiv ((P * Q⁻¹) *ᵥ x) x = γi *ᵥ pairVec finSumFinEquiv (Q⁻¹ *ᵥ x) (Q⁻¹ *ᵥ x) := by
    rw [mulVec_pairVec_diag, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_mulVec, hgγ, Matrix.one_mulVec]
  exact (pairVec_mem_diagSub _).2 rfl

end GlobalTheory.Core.Rk.Dich
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont

open Matrix Formalism.IndefR.Datum

variable {D : D7}

theorem jX_dblDec_mulVec (V : HSp D) (y : Fin V.rank → AE D) :
    (dblDec V).jX *ᵥ y = pairVec finSumFinEquiv (GlobalTheory.MixModel.giA V *ᵥ y) (GlobalTheory.MixModel.giA V *ᵥ y) := by
  funext k
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
  · rw [pairVec_inl]
    simp only [mulVec, HypDec.jX, dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows,
      GlobalTheory.MixModel.giA, GlobalTheory.MixModel.rat, Matrix.map_apply,
      Matrix.submatrix_apply, id, Equiv.symm_apply_apply, fromRows_apply_inl, fromRows_apply_inr]
  · rw [pairVec_inr]
    simp only [mulVec, HypDec.jX, dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows,
      GlobalTheory.MixModel.giA, GlobalTheory.MixModel.rat, Matrix.map_apply,
      Matrix.submatrix_apply, id, Equiv.symm_apply_apply, fromRows_apply_inl, fromRows_apply_inr]

theorem mem_siegel_of_mem_stab (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ stab (dblDec V)) : p ∈ siegel V := by
  obtain ⟨α, hα⟩ := h
  refine mem_siegelOf.2 (keepsDiag_of_mulVec fun w hw => ?_)
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
  have hx : pairVec finSumFinEquiv x x = (dblDec V).jX *ᵥ (GlobalTheory.MixModel.gA V *ᵥ x) := by
    rw [jX_dblDec_mulVec, mulVec_mulVec, GlobalTheory.MixModel.giA_mul_gA, one_mulVec]
  change mt (dblSp V) p *ᵥ _ ∈ _
  rw [hx, mulVec_mulVec, hα, ← mulVec_mulVec, jX_dblDec_mulVec]
  exact (pairVec_mem_diagSub _).2 rfl

theorem mul_jX_dblDec (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) :
    mt (dblSp V) p ⬝ (dblDec V).jX = (dblDec V).jX ⬝
      (GlobalTheory.MixModel.gA V * leviMat finSumFinEquiv (mt (dblSp V) p) * GlobalTheory.MixModel.giA V) := by
  have hk : KeepsDiag finSumFinEquiv (mt (dblSp V) p) := mem_siegelOf.1 h
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, jX_dblDec_mulVec, jX_dblDec_mulVec, hk.mulVec_diag, mulVec_mulVec,
    mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.MixModel.giA_mul_gA, Matrix.one_mul]

def gramGL (V : HSp D) : GL (Fin V.rank) (AE D) :=
  ⟨GlobalTheory.MixModel.gA V, GlobalTheory.MixModel.giA V, GlobalTheory.MixModel.gA_mul_giA V, GlobalTheory.MixModel.giA_mul_gA V⟩

theorem mem_stab_of_mem_siegel (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) : p ∈ stab (dblDec V) :=
  ⟨gramGL V * leviOf finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V)) ⟨p, h⟩ * (gramGL V)⁻¹,
    mul_jX_dblDec V h⟩

theorem onX_dblDec (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)) :
    onX (dblDec V) ⟨p, h'⟩ =
      gramGL V * leviOf finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V)) ⟨p, h⟩ * (gramGL V)⁻¹ :=
  Units.ext ((eq_of_mul_jX _ (mul_jX (dblDec V) ⟨p, h'⟩)).trans (eq_of_mul_jX _ (mul_jX_dblDec V h)).symm)

theorem isAniso_zeroSp (D : D7) : IsAniso (zeroSp D) := by
  rintro r C ⟨hr, hC, -⟩
  exact hC.ne_zero ⟨0, hr⟩ (funext fun i => Fin.elim0 i)

theorem siegel_eq_stab_dblDec : ∀ (D : D7) (V : HSp D), siegel V = stab (dblDec V) ∧ (∀ (p : GA D (dblSp V)) (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)), aP V ⟨p, h⟩ = Matrix.GeneralLinearGroup.det (onX (dblDec V) ⟨p, h'⟩)) ∧ IsAniso (zeroSp D) ∧ ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → ∃ (L : Submodule (𝓞 D.host.E) (Fin (dblSp V).rank → D.host.E)) (b : GL (Fin (dblSp V).rank) (AE D)), IsLevel (dblSp V) L b ∧ Khat V a = lev (dblSp V) L b := by
  intro D V
  refine ⟨Subgroup.ext fun p => ⟨mem_stab_of_mem_siegel V, mem_siegel_of_mem_stab V⟩, fun p h h' => ?_,
    isAniso_zeroSp D, fun a ha => ⟨frameLat (dblSp V), blkGL finSumFinEquiv (a, a),
      ⟨(isLattice_frameLat_host (dblSp V)).toIsLattice, SelfDual.isSelfDualAt_frameLat D (dblSp V), ha.dbl⟩, Khat_eq V a⟩⟩
  rw [onX_dblDec V h h', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rfl

end GlobalTheory.EisCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotent
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

open Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

def stkRows {R : Type} {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) R) : Matrix (Fin (a + a)) (Fin k) R :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem stkRows_mul {R : Type} [CommRing R] {a k l : ℕ} (X Y : Matrix (Fin a) (Fin k) R) (B : Matrix (Fin k) (Fin l) R) :
    stkRows X Y * B = stkRows (X * B) (Y * B) := by
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [stkRows, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> simp [Matrix.mul_apply]

theorem keepsDiag_mul_stkRows {R : Type} [CommRing R] {n k : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) R}
    (h : KeepsDiag finSumFinEquiv M) (X : Matrix (Fin n) (Fin k) R) :
    M * stkRows X X = stkRows (leviMat finSumFinEquiv M * X) (leviMat finSumFinEquiv M * X) := by
  have hk := (keepsDiag_iff finSumFinEquiv).1 h
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Matrix.mul_apply, stkRows, Matrix.submatrix_apply, id]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
  rw [← Finset.sum_add_distrib]
  rcases s with a | a
  · simp only [Matrix.fromRows_apply_inl, Matrix.mul_apply, leviMat, Matrix.add_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, add_mul]
  · simp only [Matrix.fromRows_apply_inr, Matrix.mul_apply, leviMat, Matrix.add_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, ← add_mul, ← hk]

theorem rat_stackRows {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) D.host.E) :
    rat (stackRows X Y) = stkRows (rat X) (rat Y) := by
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [rat, stackRows, stkRows, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> simp

theorem dblDec_jX (A : HSp D) : (dblDec A).jX = stkRows (giA A) (giA A) := rat_stackRows _ _

theorem siegel_mt_jX (A : HSp D) {g : GA D (dblSp A)} (hg : g ∈ siegel A) :
    mt (dblSp A) g ⬝ (dblDec A).jX =
      (dblDec A).jX ⬝ (gA A ⬝ leviMat finSumFinEquiv (mt (dblSp A) g) ⬝ giA A) := by
  have hk : KeepsDiag finSumFinEquiv (mt (dblSp A) g) := mem_siegelOf.1 hg
  rw [dblDec_jX, keepsDiag_mul_stkRows hk, stkRows_mul]
  simp only [← Matrix.mul_assoc, giA_mul_gA, Matrix.one_mul]


set_option maxHeartbeats 1000000 in
theorem siegel_eq_levi_nC : ∀ (D : D7) (A : HSp D) (p : siegel A), ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank),
    (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c := by
  intro D A p
  obtain ⟨p, hp⟩ := p
  obtain ⟨α, hα⟩ : ∃ α : Mx D A.rank A.rank, mt (dblSp A) p ⬝ (dblDec A).jX = (dblDec A).jX ⬝ α := ⟨_, siegel_mt_jX A hp⟩
  obtain ⟨α', hα'⟩ : ∃ α' : Mx D A.rank A.rank, mt (dblSp A) p⁻¹ ⬝ (dblDec A).jX = (dblDec A).jX ⬝ α' :=
    ⟨_, siegel_mt_jX A (inv_mem hp)⟩
  have e1 : α ⬝ α' = 1 := by
    have h : (dblDec A).jX = (dblDec A).jX ⬝ (α ⬝ α') := by
      calc (dblDec A).jX = mt (dblSp A) (p * p⁻¹) ⬝ (dblDec A).jX := by
            rw [mul_inv_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mul]
        _ = mt (dblSp A) p ⬝ (mt (dblSp A) p⁻¹ ⬝ (dblDec A).jX) := by
            rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc]
        _ = (dblDec A).jX ⬝ (α ⬝ α') := by rw [hα', ← Matrix.mul_assoc, hα, Matrix.mul_assoc]
    have h2 := congrArg (HMul.hMul (dblDec A).pX) h
    rwa [← Matrix.mul_assoc, (dblDec A).pX_jX, Matrix.one_mul, eq_comm] at h2
  have e2 : α' ⬝ α = 1 := by
    have h : (dblDec A).jX = (dblDec A).jX ⬝ (α' ⬝ α) := by
      calc (dblDec A).jX = mt (dblSp A) (p⁻¹ * p) ⬝ (dblDec A).jX := by
            rw [inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mul]
        _ = mt (dblSp A) p⁻¹ ⬝ (mt (dblSp A) p ⬝ (dblDec A).jX) := by
            rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc]
        _ = (dblDec A).jX ⬝ (α' ⬝ α) := by rw [hα, ← Matrix.mul_assoc, hα', Matrix.mul_assoc]
    have h2 := congrArg (HMul.hMul (dblDec A).pX) h
    rwa [← Matrix.mul_assoc, (dblDec A).pX_jX, Matrix.one_mul, eq_comm] at h2
  have u := GlobalTheory.MixModel.mt_unitary (dblSp A) p

  have h1 : adj α ⬝ ((dblDec A).pY ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) = 1 := by
    calc adj α ⬝ ((dblDec A).pY ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY))
        = adj (mt (dblSp A) p ⬝ (dblDec A).jX) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) := by
          rw [hα, (dblDec A).pY_eq, adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (dblDec A).jX ⬝ ((adj (mt (dblSp A) p) ⬝ (gA (dblSp A) ⬝ mt (dblSp A) p)) ⬝ (dblDec A).jY) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [u, (dblDec A).gram_XY]
  have hG : adj (mt (dblSp A) p ⬝ (dblDec A).jY) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) = 0 := by
    calc adj (mt (dblSp A) p ⬝ (dblDec A).jY) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY))
        = adj (dblDec A).jY ⬝ ((adj (mt (dblSp A) p) ⬝ (gA (dblSp A) ⬝ mt (dblSp A) p)) ⬝ (dblDec A).jY) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [u, (dblDec A).gram_YY]
  generalize hYdef : mt (dblSp A) p ⬝ (dblDec A).jY = Y at h1 hG
  have hpY : (dblDec A).pY ⬝ Y = adj α' := by
    calc (dblDec A).pY ⬝ Y = (adj α' ⬝ adj α) ⬝ ((dblDec A).pY ⬝ Y) := by
          rw [← adj_mul, e1, adj_one, Matrix.one_mul]
      _ = adj α' := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h0 : (dblDec A).j0 ⬝ (dblDec A).p0 = 0 :=
    Matrix.ext fun i j => by rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  generalize hu : (dblDec A).pX ⬝ Y = w
  have hY : Y = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ w := by
    calc Y = ((dblDec A).jX ⬝ (dblDec A).pX + (dblDec A).j0 ⬝ (dblDec A).p0 + (dblDec A).jY ⬝ (dblDec A).pY) ⬝ Y := by
          rw [(dblDec A).sum_eq_one, Matrix.one_mul]
      _ = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ w := by
          rw [h0, add_zero, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hpY, hu, add_comm]
  have hskew : adj (α' ⬝ w) = -(α' ⬝ w) := by
    rw [hY] at hG
    simp only [adj_add, adj_mul, adj_adj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      cancel₃ (dblDec A).gram_YY, cancel₃ (dblDec A).gram_YX, cancel₃ (dblDec A).gram_XY, cancel₃ (dblDec A).gram_XX,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero] at hG
    rw [adj_mul, eq_neg_iff_add_eq_zero]
    exact hG
  let a : GL (Fin A.rank) (AE D) := ⟨α, α', e1, e2⟩
  refine ⟨a, ⟨α' ⬝ w, mem_skewA.2 hskew⟩, (dblDec A).ga_ext ?_ ?_ ?_⟩
  · rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, (dblDec A).nC_jX, (dblDec A).levi_jX, hα]
  · exact Matrix.ext fun _ j => Fin.elim0 j
  · rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, (dblDec A).nC_jY, Matrix.mul_add, (dblDec A).levi_jY,
      ← Matrix.mul_assoc, (dblDec A).levi_jX, hYdef, hY]
    show _ = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ α ⬝ (α' ⬝ w)
    rw [Matrix.mul_assoc (dblDec A).jX, ← Matrix.mul_assoc α, e1, Matrix.one_mul]

end GlobalTheory.Core.Rk.SWLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjVec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Mi

theorem exists_conjVec : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → ∃ v₀ : M.Vec, ConjVec X h θ M v₀ := by
  intro hcl D X h θ S M hS hθ _hgap hιE
  subst hS
  obtain ⟨-, -, hreal, -⟩ := _root_.GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hιE
  obtain ⟨-, -, -, -, hmult, -, hstrict⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hcl
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_of_classification hcl
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.SeeInt.exists_conj_intertwiner hU hmult hstrict X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ
    X.B.w X.B.lam X.lam_eq X.ds X.low M
  refine ⟨fun τ => ⟨(c τ).symm (X.B.w (X.pl.symm τ)), hc2 τ⟩, c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x,
    fun τ => ?_⟩
  exact LinearIsometryEquiv.apply_symm_apply _ _

end GlobalTheory.Core.Mi

end
end

