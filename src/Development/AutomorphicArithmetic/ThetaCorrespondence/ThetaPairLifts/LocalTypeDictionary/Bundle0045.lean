module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0555
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0033
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0040
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0549
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KInftyExponentialLineInDerivativeSpan
section
section
open NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.KExpLine
section Abstract
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
end Abstract
end GlobalTheory.KExpLine
namespace GlobalTheory.KExpLine
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
theorem sub_mem_span_kInfty_exp_derivatives : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ →
      f₁ - f ∈ Submodule.span ℂ {g₁ | g₁ ∈ M.Pol B.ψ B.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∃ g ∈ M.Pol B.ψ B.emb,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) g g₁} := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f hf f₁ hact
  obtain ⟨hDer, hOp, -, -⟩ := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨γ, hγL, hγ1, hγK⟩ := _root_.GlobalTheory.CompactLine.exists_line_in_kInf F E σ B n X r s hP.base hP.herm k hk
  obtain ⟨S, hSfin, hS⟩ := _root_.GlobalTheory.T.fock_vectors_kFinite hPr F E σ B n d X W M χX χW om r s r' s' hP f hf
  haveI := hSfin
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let c : ℝ → SInf F (Fin n × Fin d) := fun t => D t f
  have hcP : ∀ t, c t ∈ M.Pol B.ψ B.emb := fun t => hDP t f hf
  have hcA : ∀ t, Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (c t) := fun t => (hD t f hf (c t)).2 rfl
  have hc1 : c 1 = f₁ := ((hD 1 f hf f₁).1 (by rw [hγ1]; exact hact)).symm
  have hc0 : c 0 = f := by
    have h1 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by
      rw [ofAdd_zero, map_one]
    have hA : Acts (evI F) (om (γ (Multiplicative.ofAdd (0 : ℝ)), 1)) f f := by
      intro ρ _
      rw [h1]
      show om 1 _ = _
      rw [map_one]
      rfl
    exact ((hD 0 f hf f).1 hA).symm
  have hder : ∀ y t, HasDerivAt (fun u => c u y) (Dg (c t) y) t := by
    intro y t
    let ρ := GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)
    let x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (y, 0)
    have hx : (fun i => evI F (x i)) = y := funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv _ _ i
    have hρ : ρ x = 1 := by
      show GlobalTheory.ArchIsom.g0 F (Fin n × Fin d) (fun i => (x i).2) = 1
      have : (fun i => (x i).2) = (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := rfl
      rw [this]
      exact Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts _) _
    have htens : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) ρ x = g y := by
      intro g
      show g (fun i => evI F (x i)) * ρ x = g y
      rw [hx, hρ, mul_one]
    have hom : ∀ u, om (γ (Multiplicative.ofAdd u), 1) (tens (evI F) (⇑f) ρ) = tens (evI F) (⇑(c u)) ρ :=
      fun u => hcA u ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)
    have hsplit : ∀ s', om (γ (Multiplicative.ofAdd (s' + t)), 1) (tens (evI F) (⇑f) ρ) =
        om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) := by
      intro s'
      have e : ((γ (Multiplicative.ofAdd (s' + t)), (1 : UA σ W.J)) : UA σ X.J × UA σ W.J) =
          (γ (Multiplicative.ofAdd s'), 1) * (γ (Multiplicative.ofAdd t), 1) := by
        rw [ofAdd_add, map_mul, Prod.mk_mul_mk, mul_one]
      rw [e, map_mul, Module.End.mul_apply, hom t]
    have h0 := (hDg (c t) (hcP t) (Dg (c t))).2 rfl ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ (c t)) x
    have h0' : HasDerivAt (fun s' => c (s' + t) y) (Dg (c t) y) 0 := by
      have e1 : (fun s' : ℝ => om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) x) =
          fun s' => c (s' + t) y := by
        funext s'
        rw [← hsplit s', hom, htens]
      rw [e1, htens] at h0
      exact h0
    have h2' : HasDerivAt (fun u => c (u - t + t) y) (Dg (c t) y) t := by
      have := h0'
      rw [show (0 : ℝ) = t - t from (sub_self t).symm] at this
      exact this.comp_sub_const t t
    simpa only [sub_add_cancel] using h2'
  rw [← hc1, ← hc0]
  refine sub_mem_of_hasDerivAt S _ c (fun t => Dg (c t)) (fun u => hS _ (hγK _) (c u) (hcA u)) (fun t => ?_) hder
  exact Submodule.subset_span ⟨hDgP _ (hcP t), γ, hγL, c t, hcP t, (hDg (c t) (hcP t) _).2 rfl⟩
end GlobalTheory.KExpLine
end
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kInfty_exponential_line_in_derivative_span : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ →
      f₁ - f ∈ Submodule.span ℂ {g₁ | g₁ ∈ M.Pol B.ψ B.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∃ g ∈ M.Pol B.ψ B.emb,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) g g₁} := by
  first | exact @_root_.GlobalTheory.KExpLine.sub_mem_span_kInfty_exp_derivatives | exact _root_.GlobalTheory.KExpLine.sub_mem_span_kInfty_exp_derivatives | (intros; apply _root_.GlobalTheory.KExpLine.sub_mem_span_kInfty_exp_derivatives <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineKernelProjectionWeyl
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
namespace GlobalTheory.LineKerW
theorem ker_projection_eq_line_weyl : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) ΦD x) (Φ₁D x) 0) → ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ = 0 → p Φ₁ = 0 := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' Pi rf rl p p' hm γ hγ ΦD hΦD
    Φ₁D hΦ₁D hder Φ Φ₁ hD hD₁ hp
  obtain ⟨l, hl, hγl⟩ := _root_.GlobalTheory.KapXLineDec.line_dec D θ X e Γ.W hO.JX hθ γ hγ
  have hder' : ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hO.JX ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x)
      (Φ₁D x) 0 := by
    intro x; have := hder x; simp only [hγl] at this; exact this
  obtain ⟨Ψ, hΨ, hsum⟩ := _root_.GlobalTheory.T.derivative_of_line_sum_theta hP D θ X e Bs Γ Xc om om' hO.JX hθ hT' l hl ΦD hΦD Φ₁D hder'
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT'.base.std
  have hΦF : Φ ∈ algF ψ θ true A B := by
    obtain ⟨Φ', hΦ', hD'⟩ := hO.algA' ΦD hΦD
    rwa [IsDatum.fun_eq Γ.M ψ cA cA.surjective hD hD']
  choose Φ' hΦ'F hΦ'D using fun i => hO.algA' (Ψ i) (hΨ i).1
  have hsumD : ∀ s : Finset (Fin l.length), IsDatum Γ.M ψ cA (∑ i ∈ s, Ψ i) (∑ i ∈ s, Φ' i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (CoinvPass.isDatum_zero (M := Γ.M) (ψ := ψ) (crd := cA))
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact CoinvPass.isDatum_add hψ (hΦ'D a) ih
  have hΦ₁ : Φ₁ = ∑ i, Φ' i := IsDatum.fun_eq Γ.M ψ cA cA.surjective hD₁ (hsum ▸ hsumD Finset.univ)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΦ₁, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := hl _ (List.get_mem l i)
  rw [hm.mapA.eql _ _ hi Φ hΦF (Φ' i) (hΦ'F i)
    (_root_.GlobalTheory.T.squares_agree_line_derivative_isDerivation hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' _ _ hi ΦD hΦD (Ψ i) (hΨ i).1
      (hΨ i).2 Φ (Φ' i) hD (hΦ'D i)), hp, map_zero]
end GlobalTheory.LineKerW
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
theorem _root_.GlobalTheory.T.line_kernel_projection_weyl : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) ΦD x) (Φ₁D x) 0) → ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ = 0 → p Φ₁ = 0 := by
  first | exact @_root_.GlobalTheory.LineKerW.ker_projection_eq_line_weyl | exact _root_.GlobalTheory.LineKerW.ker_projection_eq_line_weyl | (intros; apply _root_.GlobalTheory.LineKerW.ker_projection_eq_line_weyl <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftApproxOfApproxData
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.ThetaArrowApprox
theorem theta_lift_approx_of_approx_data (hL1 : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε) (hL2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (ε : Bool) (S T : GlobalTheory.Grid.Node D) (U : AddSubgroup (WO S.V T.V)), IsOpen (U : Set (WO S.V T.V)) → ∀ Φ, Φ ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U → ∀ (μ : Measure (WO S.V T.V)) (𝓕 : Set (WO S.V T.V)), IsCovolOne (ratL T.V (GlobalTheory.Grid.sgn ε S.V)) μ 𝓕 → ∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U ∧ @GlobalTheory.Size.sobO D ψ θ (GlobalTheory.Grid.sgn ε S.V) T.V μ 𝓕 d (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) < ENNReal.ofReal δ) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ := by
  intro hLC hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC δ hδ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨hν, hfd⟩ := GlobalTheory.PairLift.haar_vert hRB hG t hi (Nat.succ_le_of_lt hj)
  have hvol := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hν hfd
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (G.V i j).V.rank (G.V i (j + 1)).V.rank
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (G.V i j).V (G.V i (j + 1)).V
  obtain ⟨C0, hC0, hK⟩ := (H _ _ rfl rfl).real R.ψ hRB.inf hU
  obtain ⟨Hc, hHc⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact _ hC
  have hrd := GlobalTheory.Grow.rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf hφ.1 hφ.2.1
  obtain ⟨B, hB⟩ := hrd.2.2 Ae
  set M : ℝ := max Hc 1 with hM
  set Kc : ℝ := C0 * M ^ Ae * 2 ^ Ae with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have kb : ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ h ∈ C, ∀ g,
      ‖thetaKO (G.th t i j).ω h g f‖ ≤
        Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d f).toReal * GlobalTheory.Grow.quotHeight _ g ^ Ae := by
    intro f hf h hh g
    have hM1 : 0 ≤ GlobalTheory.Grow.height _ h := (GlobalTheory.Grow.height_pos _ h).le
    have hMh : GlobalTheory.Grow.height _ h ^ Ae ≤ M ^ Ae := pow_le_pow_left₀ hM1 ((hHc h hh).trans (le_max_left _ _)) Ae
    have h1 : ∀ g', ‖thetaKO (G.th t i j).ω h g' f‖ ≤
        (C0 * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d f).toReal * M ^ Ae) * GlobalTheory.Grow.height _ g' ^ Ae := by
      intro g'
      refine ((hK _ _ _ hω μ 𝓕 hμ f hf).2 h g').trans ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMh (mul_nonneg hC0 ENNReal.toReal_nonneg))
        (pow_nonneg (GlobalTheory.Grow.height_pos _ g').le _)
    have := GlobalTheory.Grow.norm_le_quotHeight_pow (GlobalTheory.Chain.LiftConv.thetaKO_left hω hf.1 h) h1 g
    refine this.trans (le_of_eq ?_)
    rw [hKc]; ring
  set s0 : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d Φ).toReal with hs0
  set Vl : ℝ := (G.meas t i (j + 1)).ν.real (G.meas t i (j + 1)).fd with hVl
  have hVl0 : 0 ≤ Vl := measureReal_nonneg
  have hs00 : 0 ≤ s0 := ENNReal.toReal_nonneg
  set K0 : ℝ := Kc * s0 with hK0
  have hK00 : 0 ≤ K0 := mul_nonneg hKc0 hs00
  set ε1 : ℝ := δ / (3 * (K0 * Vl + 1)) with hε1
  have hε10 : 0 < ε1 := by positivity
  obtain ⟨n1, F, v, hF, happ⟩ := hL1 D R.θ hRB.inf hP (G.V i (j + 1)) φ hφ Ae ε1 hε10
  set B' : ℝ := max B 0 with hB'
  set η : ℝ := δ / (3 * (Kc * (B' + ε1) * Vl + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨n2, f, p, hf, hlev, hsob⟩ :=
    hL2 D R.ψ R.θ hRB.inf hω.std false (G.V i j) (G.V i (j + 1)) U hU Φ hΦU μ 𝓕 hμ d η hη0
  have hsob' : (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d
      (Φ - ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l))).toReal < η :=
    ENNReal.toReal_lt_of_lt_ofReal hsob
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hB0 : ∀ g, ‖φ g‖ * GlobalTheory.Grow.quotHeight _ g ^ Ae ≤ B' := fun g => (hB g).trans (le_max_left _ _)
  let e := (finProdFinEquiv : Fin n1 × Fin n2 ≃ Fin (n1 * n2))
  refine ⟨n1 * n2, fun l => f (e.symm l).2, fun l => p (e.symm l).2, fun l => F (e.symm l).1,
    fun l => v (e.symm l).1, fun l => hf _, fun l => hF _, fun h hh => ?_⟩
  have hLCa := (hLC D hS G₀ Pl0 T A Ks R G hRB hG).th t i j hi hj
  have hintl : ∀ l : Fin (n1 * n2), IntegrableOn (fun g => thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν := by
    intro l
    obtain ⟨_, _, hall⟩ := hLCa _ (hf (e.symm l).2) _ (hF (e.symm l).1)
    exact (hall _ _ h).1
  rw [← integral_finsetSum _ (fun l _ => hintl l),
    ← integral_sub (hint h) (integrable_finsetSum _ fun l _ => hintl l)]
  set Φ' := ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l) with hΦ'
  have hsum : ∀ g, ∑ l : Fin (n1 * n2), thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g = thetaKO (G.th t i j).ω h g Φ' * ∑ a, F a (v a) g := by
    intro g
    refine (Equiv.sum_comp e.symm (fun ab : Fin n1 × Fin n2 => thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f ab.2) (p ab.2)) * F ab.1 (v ab.1) g)).trans ?_
    rw [Fintype.sum_prod_type, hΦ']
    unfold thetaKO
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_mul_sum, Finset.sum_comm]
  have hq : ∀ g, 0 < GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := fun g => pow_pos (GlobalTheory.Grow.quotHeight_pos _ g) _
  have bound : ∀ g, ‖thetaKO (G.th t i j).ω h g Φ * φ g - ∑ l : Fin (n1 * n2), thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g‖ ≤ K0 * ε1 + Kc * η * (B' + ε1) := by
    intro g
    rw [hsum g]
    have hab : thetaKO (G.th t i j).ω h g Φ - thetaKO (G.th t i j).ω h g Φ' =
        thetaKO (G.th t i j).ω h g (Φ - Φ') := by
      unfold thetaKO; rw [map_sub, Pi.sub_apply]
    have e1 : ∀ a b x y : ℂ, a * x - b * y = a * (x - y) + (a - b) * y := fun a b x y => by ring
    rw [e1, hab]
    have ha : ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ K0 * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := kb Φ hΦU h hh g
    have hxy : ‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae ≤ ε1 := happ g
    have hd : ‖thetaKO (G.th t i j).ω h g (Φ - Φ')‖ ≤ Kc * η * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae :=
      (kb _ hlev h hh g).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsob'.le hKc0) (hq g).le)
    have hy : ‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae ≤ B' + ε1 := by
      have h3 : ‖∑ a, F a (v a) g‖ ≤ ‖φ g‖ + ‖φ g - ∑ a, F a (v a) g‖ := by
        simpa using norm_sub_le (φ g) (φ g - ∑ a, F a (v a) g)
      calc ‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae
          ≤ (‖φ g‖ + ‖φ g - ∑ a, F a (v a) g‖) * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae :=
            mul_le_mul_of_nonneg_right h3 (hq g).le
        _ = ‖φ g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae +
            ‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := add_mul _ _ _
        _ ≤ B' + ε1 := add_le_add (hB0 g) hxy
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc _ ≤ K0 * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae * ‖φ g - ∑ a, F a (v a) g‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ = K0 * (‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae) := by ring
        _ ≤ K0 * ε1 := mul_le_mul_of_nonneg_left hxy hK00
    · rw [norm_mul]
      calc _ ≤ Kc * η * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae * ‖∑ a, F a (v a) g‖ :=
            mul_le_mul_of_nonneg_right hd (norm_nonneg _)
        _ = Kc * η * (‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae) := by ring
        _ ≤ Kc * η * (B' + ε1) := mul_le_mul_of_nonneg_left hy (by positivity)
  refine (norm_setIntegral_le_of_norm_le_const hvol fun g _ => bound g).trans_lt ?_
  have t1 : K0 * ε1 * Vl ≤ δ / 3 := by
    have h0 : K0 * Vl + 1 ≠ 0 := by positivity
    calc K0 * ε1 * Vl = (K0 * Vl) * ε1 := by ring
      _ ≤ (K0 * Vl + 1) * ε1 := mul_le_mul_of_nonneg_right (by linarith) hε10.le
      _ = δ / 3 := by rw [hε1]; field_simp
  have t2 : Kc * η * (B' + ε1) * Vl ≤ δ / 3 := by
    have h0 : Kc * (B' + ε1) * Vl + 1 ≠ 0 := by positivity
    calc Kc * η * (B' + ε1) * Vl = (Kc * (B' + ε1) * Vl) * η := by ring
      _ ≤ (Kc * (B' + ε1) * Vl + 1) * η := mul_le_mul_of_nonneg_right (by linarith) hη0.le
      _ = δ / 3 := by rw [hη]; field_simp
  have : (K0 * ε1 + Kc * η * (B' + ε1)) * Vl = K0 * ε1 * Vl + Kc * η * (B' + ε1) * Vl := by ring
  rw [this]
  linarith
theorem theta_lift_approximates : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ :=
  _root_.GlobalTheory.ThetaArrowApprox.theta_lift_approx_of_approx_data _root_.GlobalTheory.T.twist_cusp_form_approx_weighted GlobalTheory.FockApprox.theta_approx_fock
end GlobalTheory.ThetaArrowApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximation_by_theta_lifts : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ := by
  first | exact @_root_.GlobalTheory.ThetaArrowApprox.theta_lift_approximates | exact _root_.GlobalTheory.ThetaArrowApprox.theta_lift_approximates | (intros; apply _root_.GlobalTheory.ThetaArrowApprox.theta_lift_approximates <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistDownwardApproxCusp
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownApprox
open GlobalTheory.Size
variable {D : D7}
theorem downward_approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P (i + 1)).Maps) (v : Fin n → SmT (G.P (i + 1)).M), (∀ l, F l ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F l (v l) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * F l (v l) g ∂(G.mP (i + 1)).ν‖ < ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi Φ hΦ φ hφ hint C hC ε hε
  obtain ⟨hν, h𝓕⟩ := GlobalTheory.DownConv.MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  obtain ⟨C1, A1, hC1, hK⟩ := thetaKO_le_quotHeight hB.inf true ((hG.arrows.dn i hi).weil) hΦ hC
  have hfin : (G.mP (i + 1)).ν (G.mP (i + 1)).fd < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hν h𝓕
  set X := C1 * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal with hX
  have hX0 : 0 ≤ X := mul_nonneg hC1 ENNReal.toReal_nonneg
  set δ := ε / (2 * (X + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  obtain ⟨n, F, v, hF, happ⟩ := _root_.GlobalTheory.T.twist_cusp_form_approx_weighted D R.θ hB.inf hP (G.P (i + 1)) φ hφ A1 δ hδ0
  have hI : ∀ l h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F l (v l) g) (G.mP (i + 1)).fd
      (G.mP (i + 1)).ν := fun l h => by
    obtain ⟨ha, hc, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ _ _ R.θ hB.inf _ _
      (F l) (hF l) (v l)
    exact GlobalTheory.DownConv.integrableOn_thetaKO_mul_cusp hP.cuspRapidDecay hB.inf true ((hG.arrows.dn i hi).weil) hΦ
      hν h𝓕 ha hc h
  refine ⟨n, F, v, hF, hI, fun h hh => ?_⟩
  rw [← integral_finsetSum Finset.univ fun l _ => hI l h,
    ← integral_sub (hint h) (integrable_finsetSum _ fun l _ => hI l h)]
  have : IsFiniteMeasure ((G.mP (i + 1)).ν.restrict (G.mP (i + 1)).fd) := isFiniteMeasure_restrict.2 hfin.ne
  have hpt : ∀ g, ‖thetaKO (G.dn i).ω g h Φ * φ g - ∑ l, thetaKO (G.dn i).ω g h Φ * F l (v l) g‖ ≤ C1 * δ :=
    fun g => by
      rw [← Finset.mul_sum, ← mul_sub, norm_mul]
      have h1 := hK h hh g
      have h2 := happ g
      calc _ ≤ C1 * GlobalTheory.Grow.quotHeight _ g ^ A1 * ‖φ g - ∑ l, F l (v l) g‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = C1 * (‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight _ g ^ A1) := by ring
        _ ≤ C1 * δ := mul_le_mul_of_nonneg_left h2 hC1
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)).trans_lt ?_
  have hv : C1 * δ * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal = X * δ := by rw [hX]; ring
  have hlt : X * δ < ε := by
    rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  simpa [Measure.real, Measure.restrict_apply_univ, hv] using hlt
end GlobalTheory.DownApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_downward_approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P (i + 1)).Maps) (v : Fin n → SmT (G.P (i + 1)).M), (∀ l, F l ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F l (v l) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * F l (v l) g ∂(G.mP (i + 1)).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.DownApprox.downward_approx_cusp | exact _root_.GlobalTheory.DownApprox.downward_approx_cusp | (intros; apply _root_.GlobalTheory.DownApprox.downward_approx_cusp <;> assumption)
end
end

