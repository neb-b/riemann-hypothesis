module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0013
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0507
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1734
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0023
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationPairDerivation
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
namespace GlobalTheory.DerPol
theorem polarization_pair_derivation (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (F := F) E w) (χX χW : Chr F E) (om : Rep σ X W) (hcm : IsCMExt F E σ) (hψ : IsStd ψ)
    (hW : M.IsWeil ψ χX χW om) :
    ∀ γ ∈ Lines σ W, ∃ δ : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f ∈ M.Pol ψ τ,
      δ f ∈ M.Pol ψ τ ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro γ hγ
  obtain ⟨m, u, v, c, c₀, hat, hQ⟩ := _root_.GlobalTheory.T.oscillator_lie_action_quadratic hP M ψ χX χW om hcm hψ hW γ hγ
  choose Du hDu using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (u i) (hat i).1
  choose Dv hDv using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (v i) (hat i).2
  have closed : ∀ w, At (evI F) w → ∀ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ w) f (D f)) → ∀ f ∈ M.Pol ψ τ, D f ∈ M.Pol ψ τ := by
    intro w hw D hD f hf
    rw [Model.Pol, Submodule.mem_sInf] at hf ⊢
    intro N hN
    exact hN.2 w hw f (hf N hN) (D f) (hD f)
  refine ⟨∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id, fun f hf => ⟨?_, ?_⟩⟩
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ hf)
    exact closed _ (hat i).1 _ (hDu i) _ (closed _ (hat i).2 _ (hDv i) _ hf)
  · intro r hr x
    choose F₁ hF₁ using fun t : ℝ => _root_.GlobalTheory.T.theta_action_archimedean_locality hP M ψ χX χW om hcm hψ hW (γ (Multiplicative.ofAdd t)) (hγ.2 _) f
    have hd := hQ f (fun i => Dv i f) (fun i => Du i (Dv i f)) (fun i => hDv i f) (fun i => hDu i _) F₁ hF₁
      (fun i => evI F (x i))
    have e : (fun t => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) x) =
        fun t => F₁ t (fun i => evI F (x i)) * r x := by
      funext t; rw [hF₁ t r hr]; rfl
    rw [e]
    refine (hd.mul_const (r x)).congr_deriv ?_
    show _ = ((∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) f) (fun i => evI F (x i)) * r x
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
    congr 2
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, SchwartzMap.add_apply, ih]; simp
theorem exists_lie_derivative_model : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ f ∈ G.M'.Pol B.ψ B.emb,
      δ f ∈ G.M'.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ
  exact _root_.GlobalTheory.DerPol.polarization_pair_derivation hP G.M' B.ψ B.emb X.α (X.α / X.β) om' hT.base.cm hT.base.std hT.weil' γ hγ
end GlobalTheory.DerPol
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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_lie_derivative_model : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ f ∈ G.M'.Pol B.ψ B.emb,
      δ f ∈ G.M'.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  first | exact @_root_.GlobalTheory.DerPol.exists_lie_derivative_model | exact _root_.GlobalTheory.DerPol.exists_lie_derivative_model | (intros; apply _root_.GlobalTheory.DerPol.exists_lie_derivative_model <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PureTensorThetaSmoothAlongLine
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
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical
namespace GlobalTheory.Twist.SmoothLine
theorem smooth_line_of_pure_tensor_theta : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    (∃ y : Fin n × Fin d → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0) →
    ∀ c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) →
      ∃ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hCM hψ hM hW γ hγ f φ hSB hvac hne c hc
  obtain ⟨c₁, c', h0, hlim, hacts⟩ := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP M ψ χX χW om hCM hψ hW γ hγ f
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evI F) (⇑f) r :=
    ⟨fun x z hz => finprod_add_of_at φ x z hz, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  obtain ⟨y, hy⟩ := hne
  have heq : ∀ t, c t = c₁ t := by
    intro t
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evI F) (⇑(c₁ t)) r :=
      (hc t).symm.trans (hacts t r hRest)
    ext x
    let z : Fin n × Fin d → AF F := fun i => (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i),
        (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from y i).2))
    have hzI : (fun i => evI F (z i)) = x := by
      funext i
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i)) = x i
      exact RingEquiv.apply_symm_apply _ _
    have hzF : (∏ᶠ v, φ v fun i => evFin F v (z i)) = ∏ᶠ v, φ v fun i => evFin F v (y i) := rfl
    have e := congrFun h1 z
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, r, hzI, hzF] at e
    exact mul_right_cancel₀ hy e
  have hc' : c = c₁ := funext heq
  subst hc'
  refine ⟨c', ?_⟩
  rw [h0]
  exact hlim
end GlobalTheory.Twist.SmoothLine
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_tensor_theta_smooth_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    (∃ y : Fin n × Fin d → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0) →
    ∀ c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) →
      ∃ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  first | exact @_root_.GlobalTheory.Twist.SmoothLine.smooth_line_of_pure_tensor_theta | exact _root_.GlobalTheory.Twist.SmoothLine.smooth_line_of_pure_tensor_theta | (intros; apply _root_.GlobalTheory.Twist.SmoothLine.smooth_line_of_pure_tensor_theta <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitPlaceWeilScalarTrivial
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitScalar
theorem weil_scalar_eq_one_of_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac k hk c hc
  obtain ⟨-, dd, omd, hdc, hws, hres⟩ := hTr.weil'.1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hV := hTr.geo.hM'.vac v
  have hSB : G.M'.vac v ∈ SB _ := hV.1
  have hne : G.M'.vac v ≠ 0 := hV.2.1
  have hRv := hR _ hSB
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΨ' : (fun x => star (Ψ x)) ∈ schA F _ := GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ
  let H : Subgroup (GlobalTheory.InertDbl.UD σ G.W) :=
    { carrier := {g | omd g (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hgen := (GlobalTheory.T.scalarSq_smul_matrix_supported_at_place) F E σ B a a' G X om om' hTr v hsp hψ h2 k hk
  have hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact (_root_.GlobalTheory.T.split_double_parabolic_derivative_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv g hg
    · exact (_root_.GlobalTheory.T.nabla_preserves_split_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv g hg
  have hfix : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ := hle hgen
  have hact : om' (1, k) Ψ = c • Ψ := by
    rw [hΨdef, hc R hRv]
    funext x
    simp [tens, mul_assoc]
  have hr := hres k (GlobalTheory.InertDbl.inlD σ G.W k) rfl Ψ hΨ (fun x => star (Ψ x)) hΨ'
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hr
  rw [hact] at hr
  have key : c • GlobalTheory.InertDbl.dblFun Ψ = GlobalTheory.InertDbl.dblFun Ψ := by
    have e1 : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ := by
      unfold GlobalTheory.InertDbl.dblFun
      rw [hr]
      funext x
      simp only [boxFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← e1, hfix]
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hRx : R x = R 0 := by
    have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  have hΨx : Ψ x ≠ 0 := by
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx]
    exact mul_ne_zero hy hR0
  have h2' := congrFun key (Sum.elim x x)
  simp only [GlobalTheory.InertDbl.dblFun, boxFun, Pi.smul_apply, smul_eq_mul] at h2'
  have hz : Ψ x * star (Ψ x) ≠ 0 := mul_ne_zero hΨx (star_ne_zero.mpr hΨx)
  have h3 : (Sum.elim x x ∘ Sum.inl : Fin a' × Fin (a + a') → AF F) = x := rfl
  have h4 : (Sum.elim x x ∘ Sum.inr : Fin a' × Fin (a + a') → AF F) = x := rfl
  rw [h3, h4] at h2'
  exact (mul_eq_right₀ hz).mp h2'
end GlobalTheory.SplitScalar
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_weil_scalar_trivial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @_root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split | exact _root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split | (intros; apply _root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLineDerivative
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
namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical
end GlobalTheory.ThetaLineDeriv
namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ m f f₁ r hR hD u
  have hS := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP G.M B.ψ X.β (X.β / X.α) om hT.base.cm hT.base.std hT.weil γ hγ
  have key : ∀ i, ∃ (v : ℝ → ℂ) (w : ℂ), (∀ t : ℝ, HasSum (fun ξ : Fin a × Fin (a + a') → F =>
      G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)))
        (fun j => algebraMap F (AF F) (ξ j))) (v t)) ∧
      HasSum (fun ξ : Fin a × Fin (a + a') → F => G.M.co.rho B.ψ u (tens (evI F) (⇑(f₁ i)) (r i))
        (fun j => algebraMap F (AF F) (ξ j))) w ∧ HasDerivAt v w 0 := by
    intro i
    by_cases h0 : f i = 0
    · have ht0 : tens (evI F) (⇑(f i)) (r i) = 0 := by funext x; simp [tens, h0]
      have ht1 : tens (evI F) (⇑(f₁ i)) (r i) = 0 := by
        funext x
        have h := hD i (r i) (hR i) x
        simp only [ht0, map_zero, Pi.zero_apply] at h
        exact h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
      refine ⟨fun _ => 0, 0, fun t => ?_, ?_, hasDerivAt_const _ _⟩
      · rw [ht0, map_zero, rho_zero]; exact hasSum_zero
      · rw [ht1, rho_zero]; exact hasSum_zero
    · obtain ⟨c, c', hc0, hl, hact⟩ := hS (f i)
      obtain ⟨T, hT'⟩ := GlobalTheory.ThetaSchrCont.exists_clm_hasSum G.M B.ψ hT.base.std u (f i) (r i) (hR i) h0
      have htens : tens (evI F) (⇑(f₁ i)) (r i) = tens (evI F) (⇑c') (r i) := by
        funext x
        have h1 := hD i (r i) (hR i) x
        have h2 : HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)) x)
            (tens (evI F) (⇑c') (r i) x) 0 := by
          have e : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)) x) =
              fun t => c t (fun j => evI F (x j)) * r i x := by
            funext t; rw [hact t (r i) (hR i)]; rfl
          rw [e]
          exact (hasDerivAt_eval c (f i) c' hc0 hl _).mul_const _
        exact h1.unique h2
      refine ⟨fun t => T (c t), T c', fun t => ?_, ?_, hasDerivAt_clm c (f i) c' hc0 hl T⟩
      · rw [hact t (r i) (hR i)]; exact hT' (c t)
      · rw [htens]; exact hT' c'
  choose v w hv hw hd using key
  have e1 : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t))
      (∑ i, tens (evI F) (⇑(f i)) (r i)))) = ∑ i, v i t := by
    intro t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, rho_sum]
    refine HasSum.tsum_eq ?_
    convert hasSum_sum (s := Finset.univ) (fun i _ => hv i t) using 1
    funext ξ
    simp [Finset.sum_apply]
  have e2 : GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i))) = ∑ i, w i := by
    rw [rho_sum]
    refine HasSum.tsum_eq ?_
    convert hasSum_sum (s := Finset.univ) (fun i _ => hw i) using 1
    funext ξ
    simp [Finset.sum_apply]
  rw [show (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t))
      (∑ i, tens (evI F) (⇑(f i)) (r i))))) = fun t => ∑ i, v i t from funext e1, e2]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
  have e3 : (fun t : ℝ => ∑ i, v i t) = ∑ i, v i := by funext t; simp [Finset.sum_apply]
  rw [e3]
  exact hs
end GlobalTheory.ThetaLineDeriv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_line_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally | exact _root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally | (intros; apply _root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilLieAlgebraScalarAction
section
section
noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
namespace GlobalTheory.LieScal
open scoped Classical in
theorem lie_algebra_acts_by_scalar : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → VacLine → LieScalar := by
  intro hP hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hom
  obtain ⟨ω₀, c₀, hH, hc, hact⟩ := _root_.GlobalTheory.T.isGeneric_localComponent hP hD hV F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ν, hν, hmul, hνc, hν0⟩ := _root_.GlobalTheory.T.metaplectic_splitting_unique_up_to_character hP F E σ α β κ ψ JA JB d om ω₀ hψ hom hH hc
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.T.realLift_characterTrace_hasDerivAt hP F E σ β R S τ JB b C hCM hFr.2.2 ν hmul hνc hν0
  unfold cA at *
  refine ⟨fun w => c₀ w + k w, ?_⟩
  intro γ hγ Y hY T g hg l hl
  have hH1 : ∀ t : ℝ, At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) := fun t => hγ.2 _
  have hpm : ∀ f : SInf F κ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) =
      fun t => ν (γ (Multiplicative.ofAdd t)) * l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g)) := by
    funext t; rw [hν _ (hH1 t) (pureA F (Φ T) g) (hpm (Φ T)), map_smul, smul_eq_mul]
  show HasDerivAt (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) _ 0
  rw [e1]
  have h3 := (hk γ hγ Y hY).mul (hact γ hγ Y hY T g hg l hl)
  have hγ0 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by rw [ofAdd_zero, map_one]
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hν1 : ν 1 = 1 := by
    have := hmul 1 1 h1m h1m
    rw [mul_one] at this
    exact (mul_eq_left₀ (hν0 1 h1m)).mp this.symm
  beta_reduce at h3
  simp only [hγ0, hν1, map_one, Module.End.one_apply, one_mul] at h3
  refine h3.congr_deriv ?_
  have e2 : sumPl (fun w => fockAct2 P Q R S (Y w) + (((fun w => c₀ w + k w) w) * (Y w).trace) • (1 : Module.End ℂ _)) =
      sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) +
        (∑ w, k w * (Y w).trace) • (1 : Module.End ℂ (Tens F P Q R S)) := by
    simp only [add_mul, add_smul, ← add_assoc]
    exact sumPl_add_smul (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) _
  rw [e2, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul]
  have key : ∀ (z : ℂ) (f f' : SInf F κ), pureA F ⇑(f' + z • f) g = z • pureA F ⇑f g + pureA F ⇑f' g := by
    intro z f f'; funext x; simp [pureA]; ring
  rw [key, map_add (f := _), map_smul, smul_eq_mul]
end GlobalTheory.LieScal
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_lie_algebra_scalar_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := by
  first | exact @_root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar | exact _root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar | (intros; apply _root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar <;> assumption)
end
end

