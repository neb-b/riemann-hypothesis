module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactLineAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0573
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationKernelCompactVanishing
section
section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.PolKerCpt
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealActs Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
private theorem hecke_character_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩
private theorem restriction_eta_pow_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring
private def polarizationInductionMap {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) : V →ₗ[ℂ] V :=
  (π.quotKerEquivOfSurjective hπ).toLinearMap ∘ₗ (LinearMap.ker π).mapQ (LinearMap.ker π) D (fun u hu => hD u hu) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
private theorem induced_map_apply {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) (u : U) :
    polarizationInductionMap π hπ D hD (π u) = π (D u) := by
  have e : (π.quotKerEquivOfSurjective hπ).symm (π u) = Submodule.Quotient.mk u := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [polarizationInductionMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.mapQ_apply]
  rfl
private theorem acts_zero_at_infinity {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]
theorem polarization_zero_of_compact : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W Bs.emb, ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, k) Φ) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM k hk Φ hZ
  obtain ⟨T, hT, m, f, φ, hf, rfl, hz⟩ := hZ
  have hTr := hM.triple
  have hPV : IsPair Bs G.M Xc.β (Xc.β / Xc.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨hTr.base, hTr.geo.hV, hTr.geo.hW, hTr.geo.hM, hTr.chars.heckeβ,
      hecke_character_div hTr.chars.heckeβ hTr.chars.heckeα, hTr.chars.resβ,
      restriction_eta_pow_div hTr.chars.resβ hTr.chars.resα rfl, hTr.weil⟩
  have actV := _root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs a (a + a') G.V G.W G.M _ _ om _ _ _ _ hPV
  obtain ⟨D, hDm, hDi⟩ := actV.2.2.2 k hk
  have hA : ∀ g ∈ G.M.Pol Bs.ψ Bs.emb, Acts (evI F) (⇑(om (1, k))) (⇑g) (⇑(D g)) := fun g hg =>
    (hDi g hg (D g)).2 rfl
  have hpure : ∀ i, om (1, k) (pure (f i) (φ i)) = pure (D (f i)) (φ i) := by
    intro i
    have hstd : ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [T.finite_toSet.compl_mem_cofinite, hTr.geo.hM.std] with v hv hv'
      rw [(hf i).2.2 v hv, hv']
    exact hA (f i) (hf i).1 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 hstd)
  let N := G.M.Pol Bs.ψ Bs.emb
  let π : N →ₗ[ℂ] R.Pi := R.p ∘ₗ N.subtype
  have hπ : Function.Surjective π := fun y => by
    have : y ∈ N.map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 this
    exact ⟨⟨g, hg⟩, e⟩
  have ker0 : ∀ u : N, π u = 0 → π ((D.restrict hDm) u) = 0 := by
    intro u hu
    have := hM.real.cpt k hk u.1 u.2 0 (zero_mem _) (D u.1) 0 (hA u.1 u.2) (acts_zero_at_infinity _)
      (by rw [map_zero]; exact hu)
    rw [map_zero] at this
    exact this
  let ρ := polarizationInductionMap π hπ (D.restrict hDm) ker0
  have hρ : ∀ i, R.p (D (f i)) = ρ (R.p (f i)) := fun i =>
    (induced_map_apply π hπ (D.restrict hDm) ker0 ⟨f i, (hf i).1⟩).symm
  refine ⟨T, hT, m, fun i => D (f i), φ, fun i => ⟨hDm _ (hf i).1, (hf i).2⟩, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hpure i
  · have := congrArg (LinearMap.rTensor _ ρ) hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at this
    simpa only [LinearMap.rTensor_tmul, hρ] using this
end GlobalTheory.PolKerCpt
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_kernel_compact_vanishing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W Bs.emb, ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, k) Φ) := by
  first | exact @_root_.GlobalTheory.PolKerCpt.polarization_zero_of_compact | exact _root_.GlobalTheory.PolKerCpt.polarization_zero_of_compact | (intros; apply _root_.GlobalTheory.PolKerCpt.polarization_zero_of_compact <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StabilizerOfKExponentialLine
section
section
open NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.KExpLineW
section Abstract
variable {α : Type}
end Abstract
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
section Orbit
variable {α : Type}
end Orbit
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem KExpLine_stabilizes_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, (∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb) →
    ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F n d),
      (∀ Ψ ∈ N, ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B M,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N) →
      ∀ Φ ∈ N, Φ ∈ GlobalTheory.ThK.PolData B M → om (1, γ (Multiplicative.ofAdd (1 : ℝ))) Φ ∈ N := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγL hγK N hN Φ hΦN hΦ
  obtain ⟨-, -, hDer, hOp⟩ := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let U : Multiplicative ℝ →* Module.End ℂ (Fn F n d) := om.comp ((MonoidHom.inr (UA σ X.J) (UA σ W.J)).comp γ)
  have hdiff : ∀ Ψ ∈ PolData B M, ∀ x (t : ℝ),
      DifferentiableAt ℝ (fun s : ℝ => U (Multiplicative.ofAdd s) Ψ x) t := by
    intro Ψ hΨ x
    induction hΨ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hy
      intro t
      have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
        (hvac.and hP.good.std).mono fun _ h => h.1.trans h.2
      have hpt : ∀ u : ℝ, U (Multiplicative.ofAdd u) (pure f φ) = pure (D u f) φ := fun u =>
        map_pure M B.ψ hP.good _ f (D u f) ((hD u f hf (D u f)).2 rfl) φ hφ hvac
      have hshift : ∀ s', U (Multiplicative.ofAdd (s' + t)) (pure f φ) =
          U (Multiplicative.ofAdd s') (pure (D t f) φ) := by
        intro s'
        rw [ofAdd_add, map_mul, Module.End.mul_apply, hpt t]
      have h0 := (hDg (D t f) (hDP t f hf) (Dg (D t f))).2 rfl _
        (GlobalTheory.ThK.EvUniqInf.rest_pure (D t f) φ hφ hstd) x
      have h0' : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) 0 :=
        h0.differentiableAt
      have e : (fun s : ℝ => U (Multiplicative.ofAdd s) (pure f φ) x) =
          (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) ∘ fun s => s - t := by
        funext s
        show _ = U (Multiplicative.ofAdd (s - t)) (pure (D t f) φ) x
        rw [← hshift, sub_add_cancel]
      have h4 : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x)
          ((fun s : ℝ => s - t) t) := by
        simp only [sub_self]
        exact h0'
      rw [e]
      exact DifferentiableAt.comp (f := fun s : ℝ => s - t) t h4 (differentiableAt_id.sub_const t)
    | zero =>
      intro t
      simp only [map_zero, Pi.zero_apply]
      exact differentiableAt_const _
    | add y z _ _ hy hz =>
      intro t
      simp only [map_add (f := _), Pi.add_apply]
      exact (hy t).add (hz t)
    | smul a y _ hy =>
      intro t
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hy t).const_mul a
  obtain ⟨C, hCfin, hCP, hCk⟩ := polData_kfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  haveI := hCfin
  exact orbit_mem U (PolData B M) N C hCP (fun Ψ h Ψ₁ h₁ hd => hN Ψ h Ψ₁ h₁ hd) Φ hΦN
    (fun t => hCk _ (hγK _)) (hdiff Φ hΦ) 1
end GlobalTheory.KExpLineW
end
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_of_K_exponential_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, (∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb) →
    ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F n d),
      (∀ Ψ ∈ N, ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B M,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N) →
      ∀ Φ ∈ N, Φ ∈ GlobalTheory.ThK.PolData B M → om (1, γ (Multiplicative.ofAdd (1 : ℝ))) Φ ∈ N := by
  first | exact @_root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | exact _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | (intros; apply _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSubgroupOfKerDerivation
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
namespace GlobalTheory.KerDSub
open Filter GlobalTheory.WeilM GlobalTheory.AdelicU
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
theorem ker_derivation_isThetaSubgroup : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∃ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ),
      (∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ) ∧
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N ∧ N ≠ algD Γ.M' Bs.ψ Bs.emb := by
  intro hP F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM
  obtain ⟨h0, hlin⟩ := GlobalTheory.PolMatchLin.polMatch_linear Bs Γ Xc om om' R Rf hM.fin
  let N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) :=
    { carrier := {Φ | Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by simpa using hlin 0 0 x y 1 hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, h0⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, by simpa using hlin 0 0 0 x c h0 hx.2⟩ }
  have hN : ∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ := fun _ => Iff.rfl
  have hmem : ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ → Φ ∈ N := fun Φ h =>
    ⟨polMatch_mem_algD Bs Γ Xc R Rf h, h⟩
  have hpa : ∀ f φ, f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ SB _) → (∀ᶠ w in cofinite, φ w = Γ.M'.vac w) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD Γ.M' Bs.ψ Bs.emb := fun f φ hf hφ hv =>
    Submodule.subset_span ⟨f, φ, hf, hφ, hv, rfl⟩
  obtain ⟨Φp, hΦp, hnot⟩ := _root_.GlobalTheory.SquareAgree.exists_algD_not_polMatch_zero Bs Γ Xc om om' R Rf hM
  refine ⟨N, hN, ⟨fun Φ h => h.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun e => hnot ((hN Φp).mp (e ▸ hΦp)).2⟩
  ·
    intro v f φ hf hφ hv hφv
    have hz : Rf.p' v (φ v) = 0 := hM.fin.inv' v hφv
    refine hmem _ (polMatch_zero_pure Bs Γ Xc R Rf f hf φ hφ hv {v} fun T hT => ?_)
    rw [MultilinearMap.map_coord_zero _ (⟨v, hT (Finset.mem_singleton_self v)⟩ : T) hz, TensorProduct.tmul_zero]
  ·
    intro γ hγ f hf f₁ hf₁ hact φ hφ hv
    have hz : R.p' f₁ = 0 := hM.real.quot'.lie γ hγ f hf f₁ hact
    exact hmem _ (polMatch_zero_pure Bs Γ Xc R Rf f₁ hf₁ φ hφ hv ∅ fun T _ => by rw [hz, TensorProduct.zero_tmul])
  ·
    intro k hk f hf f₁ hf₁ hact φ hφ hv
    have hz : R.p' (f₁ - f) = 0 := by rw [map_sub, hM.real.quot'.cpt k hk f hf f₁ hact, sub_self]
    rw [← pure_sub]
    exact hmem _ (polMatch_zero_pure Bs Γ Xc R Rf (f₁ - f) (sub_mem hf₁ hf) φ hφ hv ∅ fun T _ => by
      rw [hz, TensorProduct.zero_tmul])
  ·
    classical
    intro v h hh Φ hΦ
    obtain ⟨T, hXT, hOn⟩ := (GlobalTheory.ThK.PolynomialMatching.polMatch_iff Bs Γ Xc R Rf 0 Φ).mp hΦ.2
    have hOn' : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf (insert v T) 0 Φ := by
      by_cases hvT : v ∈ T
      · rwa [Finset.insert_eq_of_mem hvT]
      · exact GlobalTheory.ThK.PolynomialMatching.polMatchOn_insert F E σ Bs a a' Γ Xc R Rf v
          (hM.fin.sph v fun h' => hvT (hXT h')).1 T 0 Φ hOn
    have := _root_.GlobalTheory.T.polynomial_matching_induction hP F E σ Bs a a' Γ Xc om om' R Rf hM (insert v T) v (Finset.mem_insert_self v T) h hh 0 Φ hOn'
    rw [map_zero] at this
    exact hmem _ ((GlobalTheory.ThK.PolynomialMatching.polMatch_iff Bs Γ Xc R Rf 0 _).mpr
      ⟨insert v T, hXT.trans (Finset.subset_insert v T), this⟩)
  ·
    intro γ hγ Φ hΦ Φ₁ _ hd
    refine hmem _ (_root_.GlobalTheory.T.line_polarization_match_derivative hP Bs Γ Xc om om' R Rf hM γ hγ 0 Φ hΦ.2 0 Φ₁ (fun x => ?_) hd)
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const 0 (0 : ℂ)
  ·
    intro k hk Φ hΦ
    have := polMatch_kInf Bs Γ Xc om om' R Rf hM k hk 0 Φ hΦ.2
    rw [map_zero] at this
    exact hmem _ this
end GlobalTheory.KerDSub
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
theorem _root_.GlobalTheory.T.thetaSubgroup_of_ker_derivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∃ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ),
      (∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ) ∧
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N ∧ N ≠ algD Γ.M' Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.KerDSub.ker_derivation_isThetaSubgroup | exact _root_.GlobalTheory.KerDSub.ker_derivation_isThetaSubgroup | (intros; apply _root_.GlobalTheory.KerDSub.ker_derivation_isThetaSubgroup <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine
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
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDer
theorem hasDerivAt_theta_sum_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hcm hψ hG hW γ hγ m f f₁ φ hφ hD u
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    fun i => ((hφ i).2.and hG.std).mono fun v h => h.1.trans h.2
  have hmem : ∀ i (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i g => GlobalTheory.TensUniq.pure_mem_schA g (φ i) (hφ i).1 (hstd i)
  choose c g hcg using fun i => _root_.GlobalTheory.T.twisted_smoothLine_pure_weight hP M ψ χX χW om hcm hψ hG hW γ hγ (f i) (φ i) (hφ i).1 (hφ i).2
  have hc := fun i => (hcg i).1
  have hlim := fun i => (hcg i).2
  choose Λ hΛ using fun i => GlobalTheory.ThetaHeisCLM.exists_clm_thetaSum_rho_pure M ψ hψ hG u (φ i) (hφ i).1 (hφ i).2
  have hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      = fun t => ∑ i, Λ i (c i t) := by
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hc]
    rw [rho_sum M ψ hψ u _ (fun i => hmem i _)]
    simp only [hΛ]
  have hg : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i) := by
    intro i
    funext x
    have hR := GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hφ i).1 (hstd i)
    have h1 := hD i _ hR x
    have ev : Continuous fun s : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
      by
        have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
        have h2 := (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
          (fun j => evI F (x j))).comp h1
        exact h2
    have h2 : HasDerivAt (fun t : ℝ => c i t (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j))
        (g i (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j)) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      exact (((ev.tendsto (g i)).comp (hlim i)).mul_const _).congr' (Filter.Eventually.of_forall fun t => schwartz_diffQuotient_eval_mul_eq_slope _ _ _ t)
    have h3 : (fun t : ℝ => c i t (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j)) =
        fun t => om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evI F) (⇑(f i)) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))) x := by
      funext t
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i t) (φ i) x = om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x
      rw [hc i t]
    rw [h3] at h2
    exact h2.unique h1
  have hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) = ∑ i, Λ i (g i) := by
    rw [rho_sum M ψ hψ u _ (fun i => hmem i _)]
    simp only [← hg, hΛ]
  have hc0 : ∀ i, HasDerivAt (fun t => Λ i (c i t)) (Λ i (g i)) 0 := by
    intro i
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((Λ i).continuous.tendsto (g i) |>.comp (hlim i)).congr' (Filter.Eventually.of_forall fun t => ?_)
    simp [slope_def_module, map_sub, map_smul]
  rw [hcurve, hend]
  have := HasDerivAt.sum (u := Finset.univ) fun i _ => hc0 i
  simpa [Finset.sum_fn] using this
end GlobalTheory.ThetaLineDer
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
theorem _root_.GlobalTheory.T.theta_sum_differentiable_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line | exact _root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line | (intros; apply _root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line <;> assumption)
end
end

