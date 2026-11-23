module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SphericalBigCell.IsLocallyConstantFinprod
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0713
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
public import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfTsumEnormLtTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0704
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import GroundTheory.LocalFields.CompleteTrivialLocal

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.HandIAdd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.IwaAd

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
  {X : Type*} [Countable X]

theorem integrable_descend_tsum (a : G → X → ℂ) (ha : ∀ x, Measurable fun g => a g x)
    (hA : LeftInv Γ fun g => ∑' x, ‖a g x‖ₑ) (hL : LeftInv Γ fun g => ∑' x, a g x)
    (hfin : ∫⁻ q, descend Γ (fun g => ∑' x, ‖a g x‖ₑ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ < ⊤) :
    Integrable (descend Γ fun g => ∑' x, a g x) (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ∧
      ∀ᵐ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, Summable (a q.out) := by
  set A : G → ℝ≥0∞ := fun g => ∑' x, ‖a g x‖ₑ with hAdef
  have hAm : Measurable A := Measurable.tsum fun x => (ha x).enorm
  have hAq : Measurable (descend Γ A) := measurable_from_quotient.2 (by
    rw [show descend Γ A ∘ Quotient.mk'' = A from hA.lift_descend]
    exact hAm)
  have hae : ∀ᵐ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, descend Γ A q < ⊤ := ae_lt_top hAq hfin.ne
  have haeG : ∀ᵐ g ∂μ, A g < ⊤ := by
    filter_upwards [ae_quotMeasure_iff.1 hae] with g hg
    rwa [hA.descend_mk] at hg
  have hBm : AEStronglyMeasurable (fun g => ∑' x, a g x) μ := by
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset X))
      (f := fun s g => ∑ x ∈ s, a g x) (fun s => ?_) ?_
    · exact (Finset.measurable_sum s fun x _ => ha x).aestronglyMeasurable
    · filter_upwards [haeG] with g hg
      exact (GlobalTheory.CompanionTheory.ThetaOrbit.summable_of_tsum_enorm_lt_top hg).hasSum
  have hGm : AEStronglyMeasurable (descend Γ fun g => ∑' x, a g x) (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
    rw [aestronglyMeasurable_quotMeasure_iff_lift, hL.lift_descend]
    exact hBm
  refine ⟨⟨hGm, ?_⟩, ?_⟩
  · refine (lintegral_mono fun q => ?_).trans_lt hfin
    show ‖∑' x, a q.out x‖ₑ ≤ ∑' x, ‖a q.out x‖ₑ
    exact enorm_tsum_le_tsum_enorm
  · filter_upwards [hae] with q hq
    exact GlobalTheory.CompanionTheory.ThetaOrbit.summable_of_tsum_enorm_lt_top hq

theorem average_descend_finset_sum {N : ℕ} (a : Fin N → G → X → ℂ) (ha : ∀ j x, Measurable fun g => a j g x)
    (hA : ∀ j, LeftInv Γ fun g => ∑' x, ‖a j g x‖ₑ) (hL : ∀ j, LeftInv Γ fun g => ∑' x, a j g x)
    (hfin : ∀ j, ∫⁻ q, descend Γ (fun g => ∑' x, ‖a j g x‖ₑ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ < ⊤) :
    ⨍ q, descend Γ (fun g => ∑' x, ∑ j, a j g x) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ =
      ∑ j, ⨍ q, descend Γ (fun g => ∑' x, a j g x) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  have key := fun j => integrable_descend_tsum (μ := μ) (a j) (ha j) (hA j) (hL j) (hfin j)
  have hae : ∀ᵐ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, ∀ j, Summable (a j q.out) :=
    ae_all_iff.2 fun j => (key j).2
  have hcongr : (descend Γ fun g => ∑' x, ∑ j, a j g x) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => ∑ j, descend Γ (fun g => ∑' x, a j g x) q := by
    filter_upwards [hae] with q hq
    show ∑' x, ∑ j, a j q.out x = ∑ j, ∑' x, a j q.out x
    exact Summable.tsum_finsetSum fun j _ => hq j
  simp_rw [average_eq]
  rw [integral_congr_ae hcongr, integral_finsetSum _ fun j _ => (key j).1, Finset.smul_sum]

end Abstract

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem ifrB_finset_sum {V : HSp D} {ν : Measure (GA D V)} (hν : ν.IsHaarMeasure) {r : ℕ} (β : HermE D r)
    {N : ℕ} (φs : Fin N → Mx D V.rank r → ℂ) (hc : ∀ j, Continuous (φs j))
    (habs : ∀ j, GlobalTheory.SiegelFormula.absThetaInt V ν (φs j) < ⊤) :
    IfrB V ν (∑ j, φs j) β = ∑ j, IfrB V ν (φs j) β := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin V.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin r → D.host.E))
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hfin : ∀ j, ∫⁻ q, descend (GQ V) (fun g => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      ‖φs j (GlobalTheory.SiegelFormula.invPt V g x.1)‖ₑ) q ∂autMeasure V ν < ⊤ := fun j => by
    refine (lintegral_mono fun q => ?_).trans_lt (habs j)
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun ξ => ‖φs j (GlobalTheory.SiegelFormula.invPt V q.out ξ)‖ₑ)
  have key := average_descend_finset_sum (Γ := GQ V) (μ := ν)
    (X := {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1})
    (fun j h x => φs j (GlobalTheory.SiegelFormula.invPt V h x.1))
    (fun j x => ((hc j).comp (GlobalTheory.AbsThetaSemi.continuous_invPt V x.1)).measurable)
    (fun j => GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V (fun y => ‖φs j y‖ₑ)
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩))
    (fun j => GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V (φs j)
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩))
    hfin
  have e : IfrB V ν (∑ j, φs j) β = ⨍ q, descend (GQ V) (fun g =>
      ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        ∑ j, φs j (GlobalTheory.SiegelFormula.invPt V g x.1)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν := by
    unfold IfrB
    simp only [Finset.sum_apply]
    rfl
  rw [e]
  exact key

theorem hasTemperateGrowth_evalPoly {m n : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (z τ))).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    convert Function.HasTemperateGrowth.const (E := D.what₂.Tau → Fin m → Fin n → ℂ) c using 1
    funext z
    simp [evalPoly]
  | add p q hp hq =>
    convert hp.add hq using 1
    funext z
    simp [evalPoly]
  | mul_X p k hp =>
    have hcoord : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => z k.1 k.2.1 k.2.2.1).HasTemperateGrowth :=
      ((ContinuousLinearMap.proj (R := ℝ) k.2.2.1).comp ((ContinuousLinearMap.proj (R := ℝ) k.2.1).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) k.1))).hasTemperateGrowth
    have hk : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1).HasTemperateGrowth := by
      split_ifs
      · exact (Complex.conjCLE.toContinuousLinearMap.comp ((ContinuousLinearMap.proj (R := ℝ) k.2.2.1).comp
          ((ContinuousLinearMap.proj (R := ℝ) k.2.1).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) k.1)))).hasTemperateGrowth
      · exact hcoord
    have e : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X k) (fun τ => Matrix.of (z τ))) =
        fun z => evalPoly p (fun τ => Matrix.of (z τ)) *
          (if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1) := by
      funext z
      simp only [evalPoly, map_mul, MvPolynomial.eval_X]
      rfl
    rw [e]
    exact hp.mul hk

theorem mem_schwartzA_of_isMonoFock {n : ℕ} {θ : InfFam D} {V : HSp D} {l : D.what₂.Tau → ℝ}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hl : ∀ τ, l τ ≠ 0)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) {φ : Mx D V.rank n → ℂ} (h : IsMonoFock θ V l s φ) :
    φ ∈ schwartzA θ V.rank n := by
  obtain ⟨e, c, g, d, bs, gv, hpure, rfl⟩ := h
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  have hg := mem_SB_of_isPureFin bs g gv hpure
  have h1 : (fun x : Mx D V.rank n => gauss V l s (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))) ∈
      schwartzA θ V.rank n := by
    refine Submodule.subset_span ⟨f, g, hg, ?_⟩
    funext x
    rw [hf]
    rfl
  have h2 := GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ V.rank n _ (hasTemperateGrowth_evalPoly (MvPolynomial.monomial e c)) _ h1
  convert h2 using 1
  funext x
  rw [← mul_assoc]
  rfl

theorem mem_schwartzA_mul_right {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (a : GL (Fin n) (AE D)) {φ : Mx D V.rank n → ℂ} (hφ : φ ∈ schwartzA θ V.rank n) :
    (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) ∈ schwartzA θ V.rank n := by
  obtain ⟨g, hg⟩ := GlobalTheory.StdUnn.Model.exists_levi (D := D) a
  set c : ℂ := (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
    npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) with hcdef
  have hc : c ≠ 0 := mul_ne_zero (Circle.coe_ne_zero _) (GlobalTheory.Doubling.npow_ne_zero (GlobalTheory.CompanionTheory.IwaAd.absA_pos _) _)
  have heq : (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) = c⁻¹ • (ω g ⟨φ, hφ⟩).1 := by
    funext x
    rw [Pi.smul_apply, hω.levi g a hg ⟨φ, hφ⟩ x, smul_eq_mul, ← hcdef, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [heq]
  exact (schwartzA θ V.rank n).smul_mem _ (ω g ⟨φ, hφ⟩).2

theorem ifrBAdd_of_weilThetaConvergence (hW : GlobalTheory.Published.WeilThetaConvergence) : IfrBAdd := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR β _hβ a N φs hφs
  have hl : ∀ τ, l τ ≠ 0 := GlobalTheory.ResAniso.VacSchwartz.realPar_ne_zero D θ hS.hθ ψ hS.hψ l hS.hl
  have hmem : ∀ j, (fun x : Mx D V.rank n => φs j (HMul.hMul x a.1)) ∈ schwartzA θ V.rank n := fun j =>
    mem_schwartzA_mul_right hS.hω a (mem_schwartzA_of_isMonoFock hl hS.hs (hφs j))
  have hn : 1 ≤ n := by obtain ⟨h1, h2, -⟩ := hR; omega
  refine Eq.trans (congrArg (fun f => IfrB V ν f β) ?_) (ifrB_finset_sum hS.hν β _
    (fun j => (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hS.hθ _ _ _ (hmem j)).1)
    (fun j => hW D n V hn (Or.inr hR.2.2) θ hS.hθ ν hS.hν ⟨_, hmem j⟩))
  funext x
  simp only [Finset.sum_apply]
  exact map_sum (Pi.evalAddMonoidHom (fun _ : Mx D V.rank n => ℂ) _) φs Finset.univ



end PositivityTheory.PfSWUS.HandIAdd

end
