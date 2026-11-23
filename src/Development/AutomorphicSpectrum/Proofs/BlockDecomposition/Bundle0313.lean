module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0288
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqSmulIntegralAvg
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotVan

def AbsVanish : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (Q K : Subgroup G) (_ : IsClosed (Q : Set G)) (_ : IsCompact (K : Set G))
  (_ : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
  (N M : Subgroup Q) [N.Normal] (_ : IsClosed (N : Set Q)) (_ : IsClosed (M : Set Q))
  (_ : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m) (_ : N ⊓ M = ⊥)
  (νN : Measure N) [νN.IsHaarMeasure]
  (T : Subgroup G) (_ : ∀ t ∈ T, ∃ h : t ∈ Q, (⟨t, h⟩ : Q) ∈ M)
  (μT : Measure T) [SFinite μT] [μT.IsInvInvariant]
  (F : G → ℂ), Measurable F → (∀ t ∈ T, ∀ x, F (t * x) = F x) → (∀ k ∈ K, ∀ x, F (x * k) = F x) →
    (∀ x, ∫ u : N, F (((u : Q) : G) * x) ∂νN = 0) → quotIntegral μ T μT F = 0

theorem integral_mul_weight_eq_zero {Q : Type} [Group Q] [MeasurableSpace Q]
    (N M : Subgroup Q) (νN : Measure N) [SFinite νN] (νM : Measure M) [SFinite νM]
    (δ : M → ℝ≥0∞) (hδ : Measurable δ) (hδt : ∀ m, δ m ≠ ∞)
    (hφ : MeasurableEmbedding (fun p : N × M => (p.1 : Q) * (p.2 : Q)))
    (f w : Q → ℂ) (w' : M → ℂ) (hw : ∀ (u : N) (m : M), w ((u : Q) * (m : Q)) = w' m)
    (hf0 : ∀ m : M, ∫ u : N, f ((u : Q) * (m : Q)) ∂νN = 0) :
    ∫ q, f q * w q ∂(((νN.prod νM).withDensity fun p => δ p.2).map
      (fun p : N × M => (p.1 : Q) * (p.2 : Q))) = 0 := by
  rw [hφ.integral_map,
    integral_withDensity_eq_integral_toReal_smul (f := fun p : N × M => δ p.2) (hδ.comp measurable_snd)
      (Filter.Eventually.of_forall fun p => lt_top_iff_ne_top.2 (hδt p.2))]
  by_cases hI : Integrable (fun p : N × M => (δ p.2).toReal • (f ((p.1 : Q) * (p.2 : Q)) *
      w ((p.1 : Q) * (p.2 : Q)))) (νN.prod νM)
  · rw [integral_prod_symm _ hI]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun m => ?_)
    simp only [hw, Pi.zero_apply]
    rw [integral_smul, integral_mul_const, hf0 m]
    simp
  · exact integral_undef hI

theorem integral_eq_smul_integral_avg {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) (Q K : Subgroup G) (νQ : Measure Q) [SFinite νQ] (κ : Measure K) [SFinite κ]
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hμ : μ = c • (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G)))
    (F : G → ℂ) (hF : Measurable F) (hFK : ∀ k ∈ K, ∀ x, F (x * k) = F x)
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hfin : ∀ᵐ g ∂μ, ρ g < ∞)
    (hint : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ) :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ =
      c.toReal • ∫ q : Q, F q * (((∫⁻ k : K, ρ ((q : G) * (k : G)) ∂κ).toReal : ℝ) : ℂ) ∂νQ := by
  have hm : Measurable (fun p : Q × K => (p.1 : G) * (p.2 : G)) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hg : Measurable (fun g => F g * ((ρ g).toReal : ℂ)) :=
    hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)
  subst hμ
  have hint' := (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).1
    ((integrable_smul_measure hc0 hct).1 hint)
  have hfin' : ∀ᵐ p ∂(νQ.prod κ), ρ ((p.1 : G) * (p.2 : G)) < ∞ :=
    ae_of_ae_map hm.aemeasurable ((Measure.absolutelyContinuous_smul hc0).ae_le hfin)
  have hint'' : Integrable (fun p : Q × K => F ((p.1 : G) * (p.2 : G)) *
      ((ρ ((p.1 : G) * (p.2 : G))).toReal : ℂ)) (νQ.prod κ) := hint'
  rw [integral_smul_measure, integral_map hm.aemeasurable hg.aestronglyMeasurable,
    integral_prod _ hint'']
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hfin'] with q hq
  have hmk : Measurable fun k : K => ρ ((q : G) * (k : G)) :=
    hρ.comp (measurable_subtype_coe.const_mul _)
  have e1 : ∀ k : K, F ((q : G) * (k : G)) = F q := fun k => hFK k k.2 _
  simp only [e1]
  rw [integral_const_mul, integral_complex_ofReal, integral_toReal hmk.aemeasurable hq]

section Normalisers

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def onQ (Q T : Subgroup G) (h : T ≤ Q) (t : T) : T.subgroupOf Q :=
  ⟨⟨t, h t.2⟩, Subgroup.mem_subgroupOf.2 t.2⟩

theorem measurable_onQ (Q T : Subgroup G) (h : T ≤ Q) : Measurable (onQ Q T h) :=
  (measurable_subtype_coe.subtype_mk).subtype_mk

theorem isInvInvariant_map_onQ (Q T : Subgroup G) (h : T ≤ Q) (μT : Measure T) [μT.IsInvInvariant] :
    (μT.map (onQ Q T h)).IsInvInvariant := by
  have hi : MeasurableInv T := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hi' : MeasurableInv (T.subgroupOf Q) := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  show Measure.map Inv.inv (μT.map (onQ Q T h)) = μT.map (onQ Q T h)
  rw [Measure.map_map measurable_inv (measurable_onQ Q T h)]
  have e : (Inv.inv ∘ onQ Q T h) = onQ Q T h ∘ Inv.inv := rfl
  rw [e, ← Measure.map_map (measurable_onQ Q T h) measurable_inv]
  exact congrArg (Measure.map (onQ Q T h)) (Measure.inv_eq_self μT)

theorem normaliser_onQ {Q T : Subgroup G} (hTQ : T ≤ Q) {μT : Measure T} {σ : Q → ℝ≥0∞}
    (hσ : Measurable σ) (h : ∀ q : Q, ∫⁻ t : T, σ (⟨t, hTQ t.2⟩ * q) ∂μT = 1) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ)) σ := by
  refine ⟨hσ, fun q => ?_⟩
  have hm : Measurable fun x : T.subgroupOf Q => σ ((x : Q) * q) :=
    hσ.comp (measurable_subtype_coe.mul_const q)
  rw [lintegral_map hm (measurable_onQ Q T hTQ)]
  exact h q

theorem normaliser_avg {Q K T : Subgroup G} (hTQ : T ≤ Q) (κ : Measure K) [SFinite κ]
    (hκ : κ Set.univ = 1) {μT : Measure T} [SFinite μT] {ρ : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser T μT ρ) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ))
      (fun q => ∫⁻ k : K, ρ ((q : G) * (k : G)) ∂κ) := by
  have hm : Measurable fun p : Q × K => ρ ((p.1 : G) * (p.2 : G)) :=
    hρ.1.comp ((measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd))
  refine normaliser_onQ hTQ hm.lintegral_prod_right' fun q => ?_
  rw [lintegral_lintegral_swap]
  · have key : ∀ k : K, ∫⁻ t : T, ρ (((⟨t, hTQ t.2⟩ * q : Q) : G) * (k : G)) ∂μT = 1 := fun k => by
      have := hρ.2 ((q : G) * (k : G))
      simpa [mul_assoc] using this
    simp only [key, lintegral_one, hκ]
  · have : Measurable fun p : T × K => ρ (((p.1 : G) * (q : G)) * (p.2 : G)) :=
      hρ.1.comp (((measurable_subtype_coe.comp measurable_fst).mul_const _).mul
        (measurable_subtype_coe.comp measurable_snd))
    exact this.aemeasurable

theorem normaliser_proj {Q T : Subgroup G} (hTQ : T ≤ Q) (N M : Subgroup Q) [hN : N.Normal]
    (hTM : ∀ t : T, (⟨t, hTQ t.2⟩ : Q) ∈ M) (hdec : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m)
    (pr : Q → M) (hprm : Measurable pr) (hpr : ∀ (u : N) (m : M), pr ((u : Q) * (m : Q)) = m)
    {μT : Measure T} {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser T μT ρ) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ)) (fun q => ρ ((pr q : Q) : G)) := by
  refine normaliser_onQ hTQ
    (hρ.1.comp (measurable_subtype_coe.comp (measurable_subtype_coe.comp hprm))) fun q => ?_
  obtain ⟨u, hu, m, hm, rfl⟩ := hdec q
  have key : ∀ t : T, ((pr ((⟨t, hTQ t.2⟩ : Q) * (u * m)) : Q) : G) = (t : G) * ((m : Q) : G) := by
    intro t
    have e : (⟨t, hTQ t.2⟩ : Q) * (u * m) =
        ((⟨(⟨t, hTQ t.2⟩ : Q) * u * (⟨t, hTQ t.2⟩ : Q)⁻¹, hN.conj_mem u hu _⟩ : N) : Q) *
          ((⟨(⟨t, hTQ t.2⟩ : Q) * m, M.mul_mem (hTM t) hm⟩ : M) : Q) := by
      simp only
      group
    rw [e, hpr]
    rfl
  simp only [key]
  exact hρ.2 _

end Normalisers

theorem absVanish_of (hQK : HaarQK) (hNM : HaarNM) : AbsVanish := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hdec N M _ hN hM hnm hinf νN _ T hT μT _ _ F hF hFT hFK hF0
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T μT ρ
  swap
  · simp [quotIntegral, hex]
  rw [quotIntegral, dite_eq_left hex]
  have hρ := hex.choose_spec
  generalize hex.choose = ρ at hρ
  have hTQ : T ≤ Q := fun t ht => by
    obtain ⟨h, _⟩ := hT t ht
    exact h
  have hTM : ∀ t : T, (⟨t, hTQ t.2⟩ : Q) ∈ M := fun t => by
    obtain ⟨h, h'⟩ := hT t t.2
    exact h'
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology Q := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology M := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : PolishSpace N := PI.VolStabS.TopoPolish.polish_of_lcsc N
  haveI : PolishSpace M := PI.VolStabS.TopoPolish.polish_of_lcsc M
  obtain ⟨νQ, _⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨νM, _⟩ : ∃ ν : Measure M, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨κ, _, hκ⟩ : ∃ κ : Measure K, κ.IsHaarMeasure ∧ κ Set.univ = 1 :=
    ⟨Measure.haarMeasure ⊤, inferInstance, Measure.haarMeasure_self⟩
  obtain ⟨c, hc0, hct, hμ⟩ := hQK μ Q K hQ hK hdec νQ κ
  obtain ⟨δ, hδ, hδt, hνQ⟩ := hNM νQ N M hN hM hnm hinf νN νM
  have φc : Continuous fun p : N × M => (p.1 : Q) * (p.2 : Q) := by fun_prop
  have φemb : MeasurableEmbedding fun p : N × M => (p.1 : Q) * (p.2 : Q) :=
    φc.measurableEmbedding (mulMap_injective N M hinf)
  let pr : Q → M := Function.extend (fun p : N × M => (p.1 : Q) * (p.2 : Q)) Prod.snd (fun _ => 1)
  have hprm : Measurable pr := φemb.measurable_extend measurable_snd measurable_const
  have hpr : ∀ (u : N) (m : M), pr ((u : Q) * (m : Q)) = m := fun u m =>
    (mulMap_injective N M hinf).extend_apply Prod.snd _ (u, m)
  have hfin := GlobalTheory.CompanionTheory.QuotNorm.ae_lt_top_of_normaliser (μG := μ) hρ
  by_cases hint : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ
  swap
  · exact integral_undef hint
  rw [integral_eq_smul_integral_avg μ Q K νQ κ c hc0 hct hμ F hF hFK ρ hρ.1 hfin hint]
  haveI := isInvInvariant_map_onQ Q T hTQ μT
  have hρ₁ := normaliser_avg (Q := Q) hTQ κ hκ hρ
  have hρ₂ := normaliser_proj hTQ N M hTM hnm pr hprm hpr hρ
  have e := GlobalTheory.CompanionTheory.QuotNorm.integral_normaliser_eq_of (μG := νQ) (F := fun q : Q => F q)
    (hF.comp measurable_subtype_coe)
    (fun h hh g => hFT h (Subgroup.mem_subgroupOf.1 hh) g) hρ₁ hρ₂
  have z : ∫ q : Q, F q * ((ρ ((pr q : Q) : G)).toReal : ℂ) ∂νQ = 0 := by
    rw [hνQ]
    exact integral_mul_weight_eq_zero N M νN νM δ hδ hδt φemb _ _
      (fun m => ((ρ ((m : Q) : G)).toReal : ℂ)) (fun u m => by simp only [hpr])
      (fun m => hF0 _)
  rw [e, z, smul_zero]

theorem absVanish : AbsVanish := absVanish_of haarQK haarNM

end GlobalTheory.CompanionTheory.QuotVan

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.KerSeq

variable {X : Scheme.{0}}

def secMap {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := fun r x => Scheme.Modules.Hom.app_smul _ _ _

theorem secMap_apply {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) (x : Γ(F, U)) :
    secMap φ U x = φ.app U x := rfl

theorem secMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (U : X.Opens) (x : Γ(F, U)) :
    secMap ψ U (secMap φ U x) = secMap (φ ≫ ψ) U x := by
  rw [secMap_apply, secMap_apply, secMap_apply, Scheme.Modules.Hom.comp_app]
  rfl

theorem isCoherent_copies {k : ℕ} {F : X.Modules} (hF : IsCoherent F) :
    IsCoherent (⨁ fun _ : Fin k => F) := by
  haveI : SheafOfModules.IsQuasicoherent F := hF.1
  refine And.intro (isQuasicoherent_biproduct _) fun U hU => ?_
  haveI : Module.Finite Γ(X, U) Γ(F, U) := hF.2 U hU
  let L : (Fin k → Γ(F, U)) →ₗ[Γ(X, U)] Γ(⨁ fun _ : Fin k => F, U) :=
    ∑ j, (secMap (biproduct.ι (fun _ : Fin k => F) j) U).comp (LinearMap.proj (R := Γ(X, U)) j)
  refine Module.Finite.of_surjective L fun m =>
    ⟨fun j => secMap (biproduct.π (fun _ : Fin k => F) j) U m, ?_⟩
  refine Eq.trans ?_ (biproduct_app_eq_sum (fun _ : Fin k => F) U m).symm
  simp only [L, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    secMap_apply]

variable {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}

theorem iSup_range_diagOp (h : OpSeq k M T d) (U : X.affineOpens) (e : ℕ) :
    ⨆ j, LinearMap.range (secMap (diagOp T d j e) (U : X.Opens)) = ⊤ := by
  have key : ∀ c : Fin k, ⊤ ≤ (⨆ j, LinearMap.range (secMap (diagOp T d j e) (U : X.Opens))).comap
      (secMap (biproduct.ι (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens)) := by
    intro c
    rw [← h.gen (d + e) (Nat.le_add_right d e) U]
    refine Submodule.span_le.mpr fun y hy => ?_
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hy
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem i (LinearMap.mem_range.mpr
      ⟨secMap (biproduct.ι (fun _ : Fin k => M (d + e)) c) (U : X.Opens) x, ?_⟩)
    rw [secMap_comp, ← secMap_apply (T i (d + e)), secMap_comp]
    rw [show biproduct.ι (fun _ : Fin k => M (d + e)) c ≫ diagOp T d i e =
        T i (d + e) ≫ biproduct.ι (fun _ : Fin k => M (d + e + 1)) c by
          unfold diagOp
          exact biproduct.ι_map _ _]
  rw [eq_top_iff]
  intro m _
  rw [biproduct_app_eq_sum (fun _ : Fin k => M (d + e + 1)) (U : X.Opens) m]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hc := Submodule.mem_comap.mp (key c (Submodule.mem_top
    (x := secMap (biproduct.π (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens) m)))
  rwa [secMap_apply, secMap_apply] at hc

theorem kerSeq_gen_bounded : GradedNoeth → ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (U : X.affineOpens), ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) = ⊤ := by
  intro hGN X _ k M T d h U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have hfin : ∀ e, Module.Finite Γ(X, U) Γ(sumN M k d e, U) := fun e =>
    (isCoherent_copies (k := k) (h.coherent (d + e))).2 U U.2
  obtain ⟨d', hd'⟩ := hGN Γ(X, U) k (fun e => Γ(sumN M k d e, U))
    (fun j e => secMap (diagOp T d j e) (U : X.Opens))
    (fun i j e x => by
      rw [secMap_comp, secMap_comp, diagOp_comm T h.comm d i j e])
    0 (fun e _ => iSup_range_diagOp h U e)
    (fun e => LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens)))
    (fun i e => by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
      refine LinearMap.mem_range.mpr ⟨secMap (kerOp T h.comm d i e) (U : X.Opens) x, ?_⟩
      rw [secMap_comp, secMap_comp, kerOp_ι])
  refine ⟨d', fun e he => ?_⟩
  have hd'' : ⨆ i, Submodule.map (secMap (diagOp T d i e) (U : X.Opens))
      (LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens))) =
      LinearMap.range (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens)) := hd' e he
  have hinj : Function.Injective (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens)) :=
    GlobalTheory.QCoh.app_injective_of_mono _ _
  apply Submodule.map_injective_of_injective hinj
  have hS : Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) =
      ⨆ i, LinearMap.range (secMap (kerOp T h.comm d i e) (U : X.Opens)) := by
    rw [Submodule.iSup_eq_span]
    simp only [LinearMap.coe_range]
    rfl
  rw [hS, Submodule.map_iSup, Submodule.map_top, ← hd'']
  refine iSup_congr fun i => ?_
  rw [← LinearMap.range_comp, ← LinearMap.range_comp]
  congr 1
  ext x
  simp only [LinearMap.comp_apply]
  rw [secMap_comp, secMap_comp, kerOp_ι]

end GlobalTheory.CompanionTheory.GE.KerSeq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalCoordsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_product_local_coords : SiteLaws → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q' V' ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff | exact GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethSwapStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_swap : ∀ {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)), KunE pr → KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kunE_swap | exact GlobalTheory.CompanionTheory.KunGlue.kunE_swap | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kunE_swap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEquivContinuousStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_equiv_continuous : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → Continuous φ ∧ Continuous φ.symm := by
  first | exact @GlobalTheory.CompanionTheory.LeviCont.levi_iso_homeo | exact GlobalTheory.CompanionTheory.LeviCont.levi_iso_homeo | (intros; apply GlobalTheory.CompanionTheory.LeviCont.levi_iso_homeo <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingBaseOfVanishingCohomology
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Step

theorem shortExact_lvl_zero {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ClosedSys I P S) :
    (ShortComplex.mk (incl (anti hS) 0) (grπ (anti hS) 0) (incl_grπ (anti hS) 0)).ShortExact := by
  have : Mono (incl (anti hS) 0) := by
    unfold incl
    infer_instance
  have : Epi (grπ (anti hS) 0) := by
    exact coequalizer.π_epi
  exact { exact := ShortComplex.exact_cokernel (incl (anti hS) 0) }

theorem lifts_zero : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules}
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ),
    Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (S 0 : X.Modules) H n) 1) → Lifts I H hS n 0 := by
  intro A _ _ I X _ H hH P S hS n hv y
  have hsurj : Function.Surjective
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) 0)).app ⊤) :=
    GlobalTheory.cohOn.app_surjective
      (GlobalTheory.Twist.shortExact_map (GlobalTheory.Twist.isLB_lbZPow hH n) (shortExact_lvl_zero hS)) ⊤ hv
  obtain ⟨c, hc⟩ := hsurj y
  refine ⟨c, hc, ?_⟩
  have htop : Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ 0) = ⊤ := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
  simp only [twPow, htop, Submodule.top_smul]
  trivial

end GlobalTheory.CompanionTheory.GE.Step
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingInductiveSuccessiveApproximation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem step_of_lifts {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB) {P : X.Modules}
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ) (e : ℕ) (hL : Lifts I H hS n (e + 1)) :
    ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  rintro x ⟨c0, rfl⟩
  have hLB : (GlobalTheory.lbZPow H n).IsLB := GlobalTheory.Twist.isLB_lbZPow hH n
  let S0 : ShortComplex X.Modules :=
    ShortComplex.mk (incl (anti hS) (e + 1)) (grπ (anti hS) (e + 1)) (incl_grπ (anti hS) (e + 1))
  have hex0 : S0.Exact := S0.exact_of_g_is_cokernel (cokernelIsCokernel _)
  have hex1 : (S0.map (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n))).Exact :=
    (GlobalTheory.Twist.exact_map_iff hLB S0).mpr hex0
  have hmono0 : Mono (incl (anti hS) (e + 1)) := mono_of_mono_fac (incl_arrow (anti hS) (e + 1))
  have hmono1 : Mono (S0.map (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n))).f :=
    (GlobalTheory.Twist.mono_map_iff hLB (incl (anti hS) (e + 1))).mpr hmono0
  have hexΓ := GlobalTheory.QCoh.exact_app_of_exact_of_mono hex1 ⊤
  let c1 : Γ(GlobalTheory.twistZ (lvl S (e + 1) : X.Modules) H n, ⊤) := c0
  obtain ⟨c, hc1, hc2⟩ := hL ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) (e + 1))).app ⊤ c1)
  have hker : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) (e + 1))).app ⊤ (c1 - c) = 0 := by
    rw [map_sub, hc1, sub_self]
  obtain ⟨d, hd⟩ := (hexΓ (c1 - c)).mp hker
  let d1 : Γ(GlobalTheory.twistZ (S (e + 1) : X.Modules) H n, ⊤) := d
  have hd' : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (incl (anti hS) (e + 1))).app ⊤ d1 = c1 - c := hd
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1, ⟨d1, rfl⟩, ?_⟩
  have harr0 : incl (anti hS) (e + 1) ≫ (S e).arrow = (S (e + 1)).arrow :=
    incl_arrow (anti hS) (e + 1)
  have harr : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1 =
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ (c1 - c) :=
    (congrArg (fun φ => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) φ).app ⊤ d1) harr0.symm).trans
      ((congrArg (fun f => f.app ⊤ d1)
          (GlobalTheory.Twist.map_comp (GlobalTheory.lbZPow H n) (incl (anti hS) (e + 1)) (S e).arrow)).trans
        ((GlobalTheory.QCoh.app_app _ _ ⊤ d1).symm.trans
          (congrArg (fun s => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ s) hd')))
  have hfin : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1 =
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c := by
    calc _ = (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
          (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ (c1 - c) := by rw [harr]
      _ = (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
          ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c1 -
            (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c) :=
          congrArg (fun t => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 - t)
            (map_sub (ConcreteCategory.hom ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤)) c1 c)
      _ = _ := sub_sub_cancel _ _
  rw [hfin]
  exact hc2

end GlobalTheory.CompanionTheory.GE.Step
end
end

