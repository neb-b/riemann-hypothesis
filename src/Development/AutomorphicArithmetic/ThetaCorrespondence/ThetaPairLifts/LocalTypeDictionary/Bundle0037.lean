module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0033
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0032
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0583
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0028

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineDerivativeSplitEqSum
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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.LineDerivSplit
theorem line_derivative_split_eq_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ ΦD ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb, ∀ Φ₁D : (Fin n × Fin d → AF F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : ι → ((Fin n × Fin d → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb) ∧
      (∀ i, ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (om (γs i (Multiplicative.ofAdd t), 1) ΦD)))
        (GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (Ψ i))) 0) ∧ Φ₁D = (l.map Ψ).sum := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP ι l γs hγs γ hγ hprod ΦD hΦD Φ₁D hΦ₁
  have hact := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  choose Ds hDsP hDs using fun i => hact.1 (γs i) (hγs i)
  obtain ⟨Dγ, -, hDγ⟩ := hact.1 γ hγ
  obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').1 hΦD
  choose f φ hf hSB hcof hgf using fun j => (g j).2
  have hstd : ∀ j, ∀ᶠ v in Filter.cofinite,
      φ j v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1 := by
    intro j
    filter_upwards [hcof j, hP.good.std] with v h1 h2
    rw [h1, h2]
  have hmem : ∀ j, c j • f j ∈ M.Pol B.ψ B.emb := fun j => Submodule.smul_mem _ _ (hf j)
  have hΦ : ΦD = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgf j, pure_smul₀]
  refine ⟨fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j), fun i => ?_, fun i u => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_
    exact ⟨_, φ j, hDsP i _ (hmem j), hSB j, hcof j, rfl⟩
  · rw [hΦ]
    exact _root_.GlobalTheory.ThetaLineDerFirst.hasDerivAt_thetaSum_along_line hPr M B.ψ χX χW om hP.base.std hP.good hP.weil (γs i) (hγs i) m
      (fun j => c j • f j) (fun j => Ds i (c j • f j)) φ (fun j => ⟨hSB j, hcof j⟩)
      (fun j => (hDs i _ (hmem j) _).2 rfl) u
  · have hpt : ∀ x, Φ₁D x = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x := by
      intro x
      have h2 : HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x)
          (∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x) 0 := by
        have e : (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) =
            fun t => ∑ j, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j)) x := by
          funext t
          set_option synthInstance.maxHeartbeats 100000 in
            rw [hΦ, map_sum, Finset.sum_apply]
        rw [e]
        have hs := HasDerivAt.sum (u := Finset.univ) fun j _ => GlobalTheory.ThetaFacInf.Fib.hasDerivAt_pure (φ j) (hSB j) (hstd j)
          ((hDγ _ (hmem j) _).2 rfl) x
        simpa [Finset.sum_fn] using hs
      exact (hΦ₁ x).unique h2
    have hadd : ∀ j, Dγ (c j • f j) = (l.map fun i => Ds i (c j • f j)).sum := fun j =>
      _root_.GlobalTheory.T.line_derivative_additive_in_lines hPr F E σ B n d X W M χX χW om r s r' s' hP l γs hγs γ hγ hprod _ (hmem j) _ _
        ((hDγ _ (hmem j) _).2 rfl) (fun i => (hDs i _ (hmem j) _).2 rfl)
    calc Φ₁D = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) :=
          funext fun x => (hpt x).trans (Finset.sum_apply x _ _).symm
      _ = ∑ j, (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum := by
          simp only [hadd, pure_listSum]
      _ = (l.map fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum :=
          sum_listSum l (fun j i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j))
end GlobalTheory.LineDerivSplit
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
theorem _root_.GlobalTheory.T.line_derivative_splits : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ ΦD ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb, ∀ Φ₁D : (Fin n × Fin d → AF F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : ι → ((Fin n × Fin d → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb) ∧
      (∀ i, ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (om (γs i (Multiplicative.ofAdd t), 1) ΦD)))
        (GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (Ψ i))) 0) ∧ Φ₁D = (l.map Ψ).sum := by
  first | exact @_root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum | exact _root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum | (intros; apply _root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineSumExistsDerivativeFactor
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
namespace GlobalTheory.LineSum
theorem lineSum_exists_derivative_factor (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (hθ : IsInfFam θ) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om') (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (hY : Y ∈ lieAt X τ) :
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∃ Ψ ∈ algD Γ.M Bs.ψ Bs.emb,
      ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) ΦD x) (Ψ x) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hJ
  obtain ⟨Dop, hDP, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ D.sp.cm.sig Bs _ _ Γ.V Γ.W Γ.M Xc.β (Xc.β / Xc.α) om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hT)).2.2.1 γ hγ
  have hfun : ∀ Φ : (Fin a × Fin (a + a') → AF D.host.F) → ℂ, ∀ x,
      (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) Φ x) = fun t => om (1, γ (Multiplicative.ofAdd t)) Φ x := by
    intro Φ x; funext t; rw [hγt t]
  intro ΦD hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q _ _ hp hq =>
    obtain ⟨p', hp', hdp⟩ := hp
    obtain ⟨q', hq', hdq⟩ := hq
    refine ⟨p' + q', add_mem hp' hq', fun x => ?_⟩
    have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) (p + q) x) =
        fun t => om (1, kapX X e hJ (oneP θ X τ Y t)) p x + om (1, kapX X e hJ (oneP θ X τ Y t)) q x := by
      funext t; simp
    rw [e1]
    exact (hdp x).add (hdq x)
  | smul c p _ hp =>
    obtain ⟨p', hp', hdp⟩ := hp
    refine ⟨c • p', Submodule.smul_mem _ c hp', fun x => ?_⟩
    have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) (c • p) x) =
        fun t => c * om (1, kapX X e hJ (oneP θ X τ Y t)) p x := by
      funext t; simp
    rw [e1]
    simpa using (hdp x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
      (hev.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dop f) φ, Submodule.subset_span ⟨Dop f, φ, hDP f hf, hSB, hev, rfl⟩, fun x => ?_⟩
    rw [hfun]
    exact ((hD f hf (Dop f)).2 rfl) _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x
theorem lineSum_product_rule (hpure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin a × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
    ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (∑ i, Ψ i x) 0) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (∑ i, Ψ i x) 0 := by
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD
  have hex : ∀ (Φ : (Fin a × Fin (a + a') → AF D.host.F) → ℂ), Φ ∈ algD Γ.M Bs.ψ Bs.emb → ∀ i : Fin l.length,
      ∃ Ψ ∈ algD Γ.M Bs.ψ Bs.emb, ∀ x,
      HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) Φ x) (Ψ x) 0 :=
    fun Φ hΦ i => _root_.GlobalTheory.LineSum.lineSum_exists_derivative_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) Φ hΦ
  induction hΦD using Submodule.span_induction with
  | zero =>
    intro Ψ hΨ x
    have h0 : ∀ i, Ψ i x = 0 := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    simp only [h0, Finset.sum_const_zero]
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q hp hq ihp ihq =>
    intro Ψ hΨ x
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    choose Ψq hΨq hdq using hex q (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hq)
    have hsplit : ∀ i, Ψ i x = Ψp i x + Ψq i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (p + q) x) =
          fun t => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x +
            om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) q x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).add (hdq i x)
    have e2 : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (p + q) x) =
        fun t => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x +
          om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) q x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).add (ihq Ψq (fun i => ⟨hΨq i, hdq i⟩) x)
  | smul c p hp ihp =>
    intro Ψ hΨ x
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    have hsplit : ∀ i, Ψ i x = c * Ψp i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (c • p) x) =
          fun t => c * om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).const_mul c
    have e2 : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (c • p) x) =
        fun t => c * om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.mul_sum]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    exact hpure hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl f hf φ hSB hev
theorem lineSum_derivative_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Φ₁D hΦ₁
  have hex : ∀ i : Fin l.length, ∃ Ψ ∈ algD Γ.M Bs.ψ Bs.emb, ∀ x,
      HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ x) 0 :=
    fun i => _root_.GlobalTheory.LineSum.lineSum_exists_derivative_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) ΦD hΦD
  choose Ψ hΨ hder using hex
  refine ⟨Ψ, fun i => ⟨hΨ i, hder i⟩, ?_⟩
  funext x
  rw [Finset.sum_apply]
  exact (hΦ₁ x).unique (_root_.GlobalTheory.LineSum.lineSum_product_rule _root_.GlobalTheory.T.derivative_pure_tensor_product hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Ψ (fun i => ⟨hΨ i, hder i⟩) x)
end GlobalTheory.LineSum
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
theorem _root_.GlobalTheory.T.derivative_of_line_sum_theta : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  first | exact @_root_.GlobalTheory.LineSum.lineSum_derivative_sum | exact _root_.GlobalTheory.LineSum.lineSum_derivative_sum | (intros; apply _root_.GlobalTheory.LineSum.lineSum_derivative_sum <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MaximalCompactFixedRelPolynomialKernelConstTerm
section
section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.PolKerCpt
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
theorem maximalCompact_fixed_rel_polynomialKernel_constTerm : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V Bs.emb, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (k, 1) Φ - Φ) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM k hk Φ hΦ
  obtain ⟨D, hDP, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs a (a + a') G.V G.W G.M Xc.β (Xc.β / Xc.α) om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)).2.1 k hk
  obtain ⟨n, c, g, rfl⟩ := (Submodule.mem_span_set').1 hΦ
  choose f φ hf hSB hcof hg using fun i => (g i).2
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hcof i, hM.triple.geo.hM.std] with v h1 h2
    rw [h1, h2]
  have hmem : ∀ i, c i • f i ∈ G.M.Pol Bs.ψ Bs.emb := fun i => Submodule.smul_mem _ _ (hf i)
  have key : ∀ i, om (k, 1) (pure (c i • f i) (φ i)) = pure (D (c i • f i)) (φ i) := fun i =>
    (hD _ (hmem i) _).2 rfl _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ (hSB i) (hstd i))
  have hp : ∀ i, R.p (D (c i • f i) - c i • f i) = 0 := fun i => by
    rw [map_sub, hM.real.quot.cpt k hk _ (hmem i) _ ((hD _ (hmem i) _).2 rfl), sub_self]
  classical
  let S : Fin n → Finset (Pl F) := fun i => (Filter.eventually_cofinite.1 (hcof i)).toFinset
  refine ⟨Xc.T ∪ Finset.univ.biUnion S, Finset.subset_union_left, n, fun i => D (c i • f i) - c i • f i, φ,
    fun i => ⟨Submodule.sub_mem _ (hDP _ (hmem i)) (hmem i), hSB i, fun v hv => ?_⟩, ?_, ?_⟩
  · by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simpa [S] using h⟩))
  · have e : ∀ i, c i • (g i : (Fin a × Fin (a + a') → AF F) → ℂ) = pure (c i • f i) (φ i) := fun i => by
      rw [hg i, GlobalTheory.PolMatchLin.pure_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_sum, key, pure_sub, Finset.sum_sub_distrib]
  · simp only [hp, TensorProduct.zero_tmul, Finset.sum_const_zero]
end GlobalTheory.PolKerCpt
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_invariants_polynomialKernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V Bs.emb, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (k, 1) Φ - Φ) := by
  first | exact @_root_.GlobalTheory.PolKerCpt.maximalCompact_fixed_rel_polynomialKernel_constTerm | exact _root_.GlobalTheory.PolKerCpt.maximalCompact_fixed_rel_polynomialKernel_constTerm | (intros; apply _root_.GlobalTheory.PolKerCpt.maximalCompact_fixed_rel_polynomialKernel_constTerm <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitVprimeStabilizerFixesVacuum
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SplitSphVPrimeStab
theorem vacuum_fixed_by_split_spherical_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hTr
  classical
  have hfin1 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) |
      ¬ G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite :=
    hTr.geo.hM'.std
  have hfin2 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | differentIdeal ℤ (𝓞 F) ≤ v.asIdeal}.Finite := by
    have h0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 hv
  have hfin3 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(2 : 𝓞 F)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact two_ne_zero
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ⟨X.T ∪ hfin1.toFinset ∪ hfin2.toFinset ∪ hfin3.toFinset, ?_⟩
  intro v hv _ k hk
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hv
  obtain ⟨⟨⟨hvT, hstd⟩, hdiff⟩, h2⟩ := hv
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (GlobalTheory.SphOffFinite.isUnram_of_unramified hTr.base.unram v) with hs | ⟨w, hw⟩
  · have hψ := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hTr.base.std v hdiff
    obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
    obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v k hk.1
    obtain ⟨hφ₁, hact⟩ := hS _ hSB
    have h1 := GlobalTheory.InertSphLeft.acts_vacCond_of_mem_KAt_left F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB _ hφ₁ hact hvac
    obtain ⟨c, hc'⟩ := _root_.GlobalTheory.SphOffFinite.spherical_vacuum_unique_off_finite_set hPr F E σ B a a' G X om om' hTr v hs hψ h2 θ hθ hvac _ hφ₁ h1
    rw [hc'] at hact
    have hc := _root_.GlobalTheory.T.split_left_scalar_factor_eq_one hPr F E σ B a a' G X om om' hTr v hs hvT hψ h2 hstd k hk c hact
    rwa [hc, one_smul] at hact
  · exact GlobalTheory.InertSphLeft.vac_fixed_left F E σ B a a' G X om om' hTr v w hw hvT k hk
end GlobalTheory.SplitSphVPrimeStab
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_vprime_stabilizer_fixes_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @_root_.GlobalTheory.SplitSphVPrimeStab.vacuum_fixed_by_split_spherical_left | exact _root_.GlobalTheory.SplitSphVPrimeStab.vacuum_fixed_by_split_spherical_left | (intros; apply _root_.GlobalTheory.SplitSphVPrimeStab.vacuum_fixed_by_split_spherical_left <;> assumption)
end
end

