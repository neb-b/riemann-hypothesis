module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumIsFockVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterWeilOperatorDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberLieAlgebraPreservesPolynomialFock
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLieFockX

theorem lineGroupX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        (∀ (s t : ℝ) (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ _ γ _ T hA
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.ArchUniq.exists_admissible_finite_factor (F := F) (Fin n × Fin d)
  refine ⟨fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · rw [← hA (s + t) f r₀ (hR f), ← hA s (T t f) r₀ (hR _), ← hA t f r₀ (hR f), ofAdd_add, map_mul,
      show (γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) =
        (γ (Multiplicative.ofAdd s), (1 : UA σ W.J)) * (γ (Multiplicative.ofAdd t), 1) by
          simp [Prod.mk_mul_mk], map_mul, Module.End.mul_apply]
  · rw [← hA 0 f r₀ (hR f), ofAdd_zero, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]

theorem vacX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ f₀, M.IsGauss ψ τ f₀ →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := lineGroupX F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hU := _root_.GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair_left F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa MeasureTheory.Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := _root_.GlobalTheory.ArchLineAct.intertwine_pair_left F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hC := _root_.GlobalTheory.ArchLineContPairLeft.continuous_apply F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := _root_.GlobalTheory.FockPair.exists_fock_cx F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW f₀ hf₀
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, k, qs, qs', cs, c, hd⟩ := _root_.GlobalTheory.WeilVacuum.smooth_flow (V := Fin n × Fin d → mixedEmbedding.mixedSpace F)
    MeasureTheory.Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d))
    (GlobalTheory.GaussLine.pairInf_nondeg F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ M.Pol ψ τ := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := _root_.GlobalTheory.PolMul.pol_mul_pairInf_pair F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem heisX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) →
          (∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) →
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ →
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  intro F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hW τ _ _ γ hγ T hTa u hu f hf hsm hder f₁ hf₁
  obtain ⟨f', hf'P, hf'd⟩ := hder
  have hstab : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) v → ∀ g ∈ M.Pol ψ τ,
      ∃ g₁ ∈ M.Pol ψ τ, ∀ y, g₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co v).1 (GlobalTheory.HeisOrbit.archCo M.co v).2 g y := by
    intro v hv g hg
    obtain ⟨D, hD⟩ := _root_.GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J)
      M.co hψ
    have h0 : ∀ t, M.heisLine ψ v t 0 = 0 := fun t => by
      funext x
      simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hA : ActsD (evI F) (M.heisLine ψ v) g (D v g) :=
      (GlobalTheory.RealLift.actsLaws F _ g (D v g) (D v g)).1 _ h0 (hD v hv g).1
    refine ⟨D v g, Submodule.mem_sInf.2 fun N hN => hN.2 v hv g (Submodule.mem_sInf.1 hg N hN) _ hA, fun y => ?_⟩
    rw [(hD v hv g).2 y]
    rfl
  have hrel : ∀ t y, T t f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1
      (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2 (T t f) y := fun t =>
    GlobalTheory.T.weil_operator_left_intertwines_heisenberg_derivative M ψ χX χW om hψ hW (γ (Multiplicative.ofAdd t)) (T t) (hTa t) u hu f f₁ hf₁
  obtain ⟨hφ, u', hu', hφd⟩ := GlobalTheory.T.archimedean_darboux_coords_one_param_orbit_smooth (W := W) M γ hγ u hu
  have hfun : (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) =
      fun p => GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd p.1)) * u)).1
        (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd p.1)) * u)).2 (T p.1 f) p.2 :=
    funext fun p => hrel p.1 p.2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GlobalTheory.HeisOrbit.dOp_contDiff_family (fun t => T t f) (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1)
      (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2) hsm hφ.fst hφ.snd
  have hT0 : T 0 f = f := by
    have h1 : om (γ (Multiplicative.ofAdd 0), 1) = 1 := by
      rw [ofAdd_zero, map_one]
      exact map_one om
    have hA : Acts (evI F) (om (γ (Multiplicative.ofAdd 0), 1)) f f := by
      rw [h1]
      intro r _
      rfl
    exact (GlobalTheory.RealLift.actsLaws F _ f (T 0 f) f).2.2.2.1 _ (hTa 0 f) hA
  have hφ0 : GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd (0 : ℝ))) * u) = GlobalTheory.HeisOrbit.archCo M.co u := by
    rw [ofAdd_zero, map_one]
    simp [mat]
  obtain ⟨g₁, hg₁P, hg₁⟩ := hstab u hu f' hf'P
  obtain ⟨g₂, hg₂P, hg₂⟩ := hstab u' hu' f hf
  refine ⟨g₁ + g₂, add_mem hg₁P hg₂P, fun x => ?_⟩
  have hP := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have hQ := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have h4 := GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt (fun t => T t f) (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1)
    (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2) f' _ _ hsm hf'd hP hQ x
  simp only [hφ0, hT0] at h4
  rw [SchwartzMap.add_apply, hg₁, hg₂]
  exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hrel t x)

theorem lie_deriv_polX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    have e : mat (1 : UA σ W.J) = 1 := rfl
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [e, sub_self, smul_zero]
  choose T hT' using fun t : ℝ => GlobalTheory.FockCompactW.exists_op_of_UAt hψ hwe (γ (Multiplicative.ofAdd t), 1) (hγ.2 _) h1W
  have hvac : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | f ∈ M.Pol ψ τ ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add (f := _), SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : M.Pol ψ τ ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, vacX F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h,
        heisX F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  intro f hf f₁ h₁
  obtain ⟨-, -, f', hf', hd⟩ := hPN hf
  have hA : ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f' := by
    intro r hr x
    have h1 : ∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) = tens (evI F) (T t f) r :=
      fun t => hT' t f r hr
    simp only [h1]
    exact (hd _).mul_const (r x)
  have e : f₁ = f' := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ f').2.2.1 _ h₁ hA
  rw [e]; exact hf'

end GlobalTheory.RealLieFockX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberMaximalCompactPreservesPolynomialFock
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.FockCompactX

open GlobalTheory.RealLift GlobalTheory.FockCompactW

section Der

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem at_mul_left {m p q : Type} [Fintype p] {z : Matrix p q (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hz : At (evI F) z)
    (A : Matrix m p (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : At (evI F) (A * z) := by
  intro u hu; rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem sd_intertwine_left {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (h : UA σ Y.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (h, 1)) f g) (hf₁ : Acts (evI F) (om (h, 1)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (mat h * u)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (h, 1) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (h, 1) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((h, 1) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat h * u) := by
    change mat h * (realAd F t • u) * (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

end Der

theorem pol_stable_compact_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ k ∈ KInf σ X τ, ∀ f ∈ M.Pol ψ τ,
          ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hw τ _ _ k hk f hf f₁ hf₁
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := exists_op_of_UAt hψ hw (k, 1) hk.1 h1
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.HeisDer.derEx F E σ _ _ _ ψ _ _ M.co hψ
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (FockCompactW.heisLine_zero M ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ (mat k * u)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (FockCompactW.heisLine_zero M ψ _)
      (sd_intertwine_left hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : mat k * mat k⁻¹ = 1 := by
    change mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), mat k * (mat k⁻¹ * u) = u := fun u => by
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hle : M.Pol ψ τ ≤ (M.Pol ψ τ).comap A := by
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩
    · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_
      obtain ⟨ε, hε⟩ := hf₀
      refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
      have hv := at_mul_left hu (mat k⁻¹)
      have hv' := at_mul_left hu' (mat k⁻¹)
      have h1 := hint _ hv f₀
      have h2 := hint _ hv' f₀
      rw [hcan] at h1 h2
      have e1 := (hL _ _ _).2.2.1 _ hg h1
      have e2 := (hL _ _ _).2.2.1 _ hg' h2
      have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
      · rw [e1, e2, key, map_smul]
      · have hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
          rw [← Matrix.map_mul]
          change (mat (k⁻¹ * k)).map _ = 1
          rw [inv_mul_cancel]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 hm
        have hc : (mat k⁻¹).map (piInf (τ w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (τ w)) := by
          calc _ = (mat k⁻¹).map (piInf (τ w)) * X.θ w *
                ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by rw [hm', Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (τ w)) * (X.θ w * (mat k).map (piInf (τ w))) *
                (mat k⁻¹).map (piInf (τ w)) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.mul_smul]
        congr 1
        simp only [← Matrix.mul_assoc]
        rw [hc]
    · have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_sInf.2 fun N hN =>
        hN.2 _ (at_mul_left hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.FockCompactX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberParameterInvOfChainParameterInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainInv

variable {D : D7}

theorem conjP_eq_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

theorem under_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  rw [← conjP_eq_conjPl]
  exact GlobalTheory.GridPlaces.under_conjP w

theorem absNorm_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr
    (Ideal.quotientEquiv w.asIdeal (Formalism.DivisionValues.conjPl w).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

theorem not_isSplit_of_conjPl_eq {w : HeightOneSpectrum (𝓞 D.host.E)} (hc : Formalism.DivisionValues.conjPl w = w) :
    ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) := by
  intro hs
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
  have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E), R.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → R = w :=
    fun R hR => (GlobalTheory.GridPlaces.eq_or_eq_conjP hR).elim id fun h => h.trans ((conjP_eq_conjPl w).trans hc)
  exact hPQ ((key P hP).trans (key Q hQ).symm)

theorem val_conjPl_of_resEta (χ : (AE D)ˣ →* Circle) (n : ℕ) (hr : Formalism.L2.Theta.ResEta D χ n)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hu : GlobalTheory.LFun.UnrAt χ w) (hu' : GlobalTheory.LFun.UnrAt χ (Formalism.DivisionValues.conjPl w)) :
    GlobalTheory.LFun.val (F := D.host.F) χ (Formalism.DivisionValues.conjPl w) = (GlobalTheory.LFun.val (F := D.host.F) χ w)⁻¹ := by
  have h2 := (GlobalTheory.AdelicU.isCMExt_host D).2.2.1
  by_cases hc : Formalism.DivisionValues.conjPl w = w
  · have hns := not_isSplit_of_conjPl_eq hc
    rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (GlobalTheory.VacCoef.isUnram_host D (w.under (𝓞 D.host.F))) with hs | ⟨w0, hw0⟩
    · exact absurd hs hns
    · obtain rfl : w0 = w := GlobalTheory.LFun.eq_of_not_isSplit hns (GlobalTheory.LFun.under_eq_of_isInertAt hw0) rfl
      have hv := GlobalTheory.LFun.ResEta.val_of_isInertAt h2 hr hw0 hu
      rw [hc, hv, ← inv_pow, inv_neg_one]
  · exact eq_inv_of_mul_eq_one_right (GlobalTheory.LFun.ResEta.val_mul_val h2 hr (Ne.symm hc) rfl (under_conjPl w) hu hu')

theorem val_step_conjPl (c : Com D) (hc : c.Is) (k : ℕ) (hk : k < D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) :
    GlobalTheory.LFun.val (F := D.host.F) (c.chS (k + 1)) (Formalism.DivisionValues.conjPl w) =
                 (GlobalTheory.LFun.val (F := D.host.F) (c.chS (k + 1)) w)⁻¹ ∧
      GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) (Formalism.DivisionValues.conjPl w) =
        (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w)⁻¹ := by
  have hw' : Formalism.DivisionValues.conjPl w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    intro h
    apply hw
    rw [GlobalTheory.LFun.above, Set.mem_setOf_eq] at h ⊢
    rwa [under_conjPl] at h
  have hμ : GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) (Formalism.DivisionValues.conjPl w) =
      (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) w)⁻¹ :=
    val_conjPl_of_resEta _ 0 (hc.chars.2.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2 w
      (hc.unr ⟨k, hk⟩ w hw) (hc.unr ⟨k, hk⟩ _ hw')
  have hη : GlobalTheory.LFun.val (F := D.host.F) c.η (Formalism.DivisionValues.conjPl w) = (GlobalTheory.LFun.val (F := D.host.F) c.η w)⁻¹ :=
    val_conjPl_of_resEta _ 1 hc.chars.2.2.1 w (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w)
      (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 _)
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs <;> simp only [GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv, hμ, hη, mul_inv, inv_inv, and_self]

theorem range_reflect (t : ℕ) : (Multiset.range t).map (fun i => t - 1 - i) = Multiset.range t := by
  refine (Multiset.Nodup.ext ?_ (Multiset.nodup_range t)).2 fun a => ?_
  · refine (Multiset.nodup_range t).map_on fun x hx y hy h => ?_
    rw [Multiset.mem_range] at hx hy
    omega
  · simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩; omega
    · intro ha; exact ⟨t - 1 - a, by omega, by omega⟩

theorem seg_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) (z : ℂˣ) (t : ℕ) :
    GlobalTheory.LFun.seg (Formalism.DivisionValues.conjPl w) z⁻¹ t = (GlobalTheory.LFun.seg w z t).map (·⁻¹) := by
  have hN : ∀ y, GlobalTheory.LFun.npowU (Formalism.DivisionValues.conjPl w) y = GlobalTheory.LFun.npowU w y := fun y =>
    Units.ext (by simp only [GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, absNorm_conjPl])
  simp only [GlobalTheory.LFun.seg, hN, Multiset.map_map, Finset.range_val]
  conv_rhs => rw [← range_reflect t, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  simp only [Function.comp_apply, mul_inv]
  congr 1
  refine Units.ext ?_
  simp only [GlobalTheory.LFun.coe_npowU, Units.val_inv_eq_inv_val, GlobalTheory.LFun.npow]
  rw [← Complex.cpow_neg]
  congr 1
  push_cast [Nat.cast_sub (show i ≤ t - 1 by omega), Nat.cast_sub (show 1 ≤ t by omega)]
  ring

theorem chainPar_conjPl (c : Com D) (hc : c.Is) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
    (hB : B' (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹)) :
    ∀ k ≤ D.R.m, chainPar c B' k (Formalism.DivisionValues.conjPl w) = (chainPar c B k w).map (·⁻¹) := by
  intro k hk
  induction k with
  | zero => exact hB
  | succ k ih =>
    obtain ⟨hS, hT⟩ := val_step_conjPl c hc k (by omega) w hw
    rw [chainPar_succ, chainPar_succ]
    simp only [stepPar]
    rw [ih (by omega), hS, hT, seg_conjPl, Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, mul_inv, inv_inv]

theorem conjPl_inv_of_chainPar : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ (B : GlobalTheory.LFun.Fam D.host.E),
    ∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))),
    chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) →
      B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by
  intro D c hc j hj B w hw h
  classical
  let B' : GlobalTheory.LFun.Fam D.host.E := Function.update B (Formalism.DivisionValues.conjPl w) ((B w).map (·⁻¹))
  have hB : B' (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by simp [B']
  have h1 := chainPar_conjPl c hc B B' w hw hB j hj
  have h2 := chainPar_inj_at D c j B B' (Formalism.DivisionValues.conjPl w) (h.trans h1.symm)
  rw [h2, hB]

end GlobalTheory.ChainInv

end
end

