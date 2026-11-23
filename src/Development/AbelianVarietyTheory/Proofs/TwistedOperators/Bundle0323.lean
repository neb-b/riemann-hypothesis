module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine
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

namespace GlobalTheory.RealLieOp

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.RealLift

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem actsD_zero' (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _


open scoped Classical in
theorem actsD_comb (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f + g) ⇑(c • f₁ + g₁) := by
  have e : ∀ (r : (κ → AF F) → ℂ) (φ ψ : SInf F κ),
      tens (evI F) ⇑(c • φ + ψ) r = c • tens (evI F) ⇑φ r + tens (evI F) ⇑ψ r := by
    intro r φ ψ; funext y; simp [tens]; ring
  have key : ∀ r, Rest (evI F) ⇑f r → Rest (evI F) ⇑g r → ∀ x,
      HasDerivAt (fun t => L t (tens (evI F) ⇑(c • f + g) r) x) (tens (evI F) ⇑(c • f₁ + g₁) r x) 0 := by
    intro r h1 h2 x
    rw [e, e]
    have h := ((hf r h1 x).const_mul c).add (hg r h2 x)
    have hfun : (fun t => L t (c • tens (evI F) ⇑f r + tens (evI F) ⇑g r) x) =
        (fun t => c * L t (tens (evI F) ⇑f r) x) + (fun t => L t (tens (evI F) ⇑g r) x) := by
      funext t; simp [map_add (f := _), map_smul]
    rw [hfun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h

  set g₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl
  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r₀ := fun φ =>
    ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨φ, g₀, hg₀, rfl⟩⟩
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  intro r hr x
  by_cases h0 : c • f + g = 0
  · have hz : c • f₁ + g₁ = 0 := by
      ext a
      have h := key r₀ (hrest₀ f) (hrest₀ g) (ptAt a 0)
      rw [h0, hzeroT] at h
      simp only [map_zero, Pi.zero_apply] at h
      have h' := h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
      rw [htens₀, pureA_ptAt, hg₀0, mul_one] at h'
      simpa using h'
    rw [h0, hz, hzeroT]
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const _ _
  · have hR : (fun y => r (fun i => ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F), y i))) ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :=
      mem_SB_of_pureA_mem h0 (tens_eq_pureA _ hr.1 ▸ hr.2)
    have hrest : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r := fun φ =>
      ⟨hr.1, by rw [tens_eq_pureA _ hr.1]; exact Submodule.subset_span ⟨φ, _, hR, rfl⟩⟩
    exact key r (hrest f) (hrest g) x

theorem actsD_add (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(f + g) ⇑(f₁ + g₁) := by
  simpa only [one_smul] using actsD_comb L 1 hf hg

theorem actsD_smul (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f) ⇑(c • f₁) := by
  simpa only [add_zero] using actsD_comb L c hf (actsD_zero' L)

end GlobalTheory.RealLieOp

theorem GlobalTheory.RealLieOp.exists_realOp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∃ T : Module.End ℂ R.Pi,
      (∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f₁ = T (R.p f)) ∧
      ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f' f₁' → R.p' f₁' = T (R.p' f') := by
  intro F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM γ hγ
  let L : ℝ → Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ) := fun t => om (1, γ (Multiplicative.ofAdd t))
  let L' : ℝ → Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) := fun t => om' (1, γ (Multiplicative.ofAdd t))
  let S : Set (R.Pi × R.Pi) :=
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ z = (R.p f, R.p f₁)} ∪
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')), f ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f ⇑f₁ ∧ z = (R.p' f, R.p' f₁)}
  have hspan : ∀ z ∈ Submodule.span ℂ S, ∃ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (f' f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f' ⇑f₁' ∧
      z = (R.p f + R.p' f', R.p f₁ + R.p' f₁') := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨f, f₁, hf, h1, rfl⟩ | ⟨f, f₁, hf, h1, rfl⟩
      · exact ⟨f, f₁, 0, 0, hf, h1, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', by simp⟩
      · exact ⟨0, 0, f, f₁, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, hf, h1, by simp⟩
    | zero => exact ⟨0, 0, 0, 0, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', Prod.ext (by simp) (by simp)⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      obtain ⟨g, g₁, g', g₁', hg, h2, hg', h2', rfl⟩ := hy
      refine ⟨f + g, f₁ + g₁, f' + g', f₁' + g₁', add_mem hf hg, GlobalTheory.RealLieOp.actsD_add L h1 h2,
        add_mem hf' hg', GlobalTheory.RealLieOp.actsD_add L' h1' h2', ?_⟩
      simp only [map_add (f := _), Prod.mk_add_mk]
      abel_nf
    | smul c x _ hx =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      refine ⟨c • f, c • f₁, c • f', c • f₁', Submodule.smul_mem _ c hf, GlobalTheory.RealLieOp.actsD_smul L c h1,
        Submodule.smul_mem _ c hf', GlobalTheory.RealLieOp.actsD_smul L' c h1', ?_⟩
      simp only [map_smul, Prod.smul_mk, smul_add]
  have hgraph : ∀ z ∈ Submodule.span ℂ S, z.1 = 0 → z.2 = 0 := by
    intro z hz hz0
    obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hspan z hz
    have e : R.p f + R.p' f' = 0 := hz0
    have e2 : R.p f = R.p' (-f') := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left e
    have hn : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑(-f') ⇑(-f₁') := by
      simpa only [neg_one_smul] using GlobalTheory.RealLieOp.actsD_smul L' (-1) h1'
    have := hM.real.lie γ hγ f hf (-f') (neg_mem hf') f₁ (-f₁') h1 hn e2
    show R.p f₁ + R.p' f₁' = 0
    rw [this, map_neg, neg_add_cancel]
  obtain ⟨T, hT⟩ := LinearMap.exists_extend (Submodule.span ℂ S).toLinearPMap.toFun
  have hT' : ∀ z ∈ Submodule.span ℂ S, T z.1 = z.2 := by
    intro z hz
    have hz' : z ∈ (Submodule.span ℂ S).toLinearPMap.graph := by
      rw [Submodule.toLinearPMap_graph_eq _ hgraph]; exact hz
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hz'
    rw [← hy1, ← hy2]
    exact LinearMap.congr_fun hT y
  refine ⟨T, fun f hf f₁ h1 => ?_, fun f hf f₁ h1 => ?_⟩
  · exact (hT' (R.p f, R.p f₁) (Submodule.subset_span (Or.inl ⟨f, f₁, hf, h1, rfl⟩))).symm
  · exact (hT' (R.p' f, R.p' f₁) (Submodule.subset_span (Or.inr ⟨f, f₁, hf, h1, rfl⟩))).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTypeIwahoriMaximalCompactIdempotentFamily
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem isIntegralOp_smoothOp {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G W} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ} (hf : IsLocallyConstant f ∧ HasCompactSupport f) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ ρ f (smoothOp ρ μ f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf.1 hf.2 v
  refine ⟨?_, ?_⟩
  · simpa [smul_eq_mul] using integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
  · rw [hρ.map_smoothOp (μ := μ) hf.1 hf.2 l v]
    simp [smul_eq_mul]

theorem isSmooth_comp_locFin {D : D7} {V : HSp D} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hσ : GlobalTheory.PRep.IsSmooth σ) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.PRep.IsSmooth (σ.comp (locFin V v)) := fun x =>
  (hσ x).preimage ((continuous_emb D.sp.cm.sig V.gram v).subtype_mk _)


set_option maxHeartbeats 2000000 in
theorem exists_idemFam : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∃ e, IsFinFamily D.sp.cm.sig V.gram (frameLat V) e ∧ (∀ v : T.S, e v = T.idem μf v) ∧ (∀ v, conv (μf v) (e v) (e v) = e v) ∧ (∀ k ∈ U.frame.iwahori, ∀ g, e U.u (k * g) = e U.u g) ∧ SphRest T U e ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → HasTypeVec T σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → P ≠ 0 := by
  intro D V T U hu μf hH h1 ν hν
  refine ⟨fam T U μf T.S, _root_.GlobalTheory.TrIdem.isFinFamily_fam D V T U μf hH h1 hu T.S, fun v => fam_of_mem T U μf T.S v.2 v.2, ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ T.S
    · rw [fam_of_mem T U μf T.S hv hv]
      let s := T.frame ⟨v, hv⟩
      have hk : IsOpen (s.red.ker : Set (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) := by
        rw [show (s.red.ker : Set (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) = (↑) ⁻¹' (stabLocOne D.sp.cm.sig V.gram s.emb (frameLat V) : Set (GLoc D.sp.cm.sig V.gram v)) from
          Set.ext s.red_eq_one_iff]
        exact (isOpen_stabLocOne V.gram s.emb (frameLat V) s.cm).preimage continuous_subtype_val
      exact conv_typeIdem (μf v) (isOpen_stabLoc _ _ _ v) (isCompact_stabLoc _ _ _ v) s.red_surjective hk _ (T.irred _)
    · rw [fam_of_not T U μf T.S (fun h => hv h.1)]
      obtain ⟨ho, hle⟩ := _root_.GlobalTheory.TrIdem.levelFam_open_le D V T U hu v
      exact GlobalTheory.T.groupConvolution_normalizedIndicator_self _ (μf v) _ ho ((isCompact_stabLoc _ _ _ v).of_isClosed_subset
        (Subgroup.isClosed_of_isOpen _ ho) hle)
  · intro k hk g
    rw [fam_of_not T U μf T.S (fun h => hu h.1), levelFam_u]
    simp only [normInd, Pi.smul_apply]
    congr 1
    by_cases hg : g ∈ U.frame.iwahori
    · rw [indicator_of_mem (show k * g ∈ (U.frame.iwahori : Set _) from mul_mem hk hg), indicator_of_mem (show g ∈ (U.frame.iwahori : Set _) from hg)]; rfl
    · rw [indicator_of_notMem (show k * g ∉ (U.frame.iwahori : Set _) from fun h => hg ((Subgroup.mul_mem_cancel_left _ hk).1 h)),
        indicator_of_notMem (show g ∉ (U.frame.iwahori : Set _) from hg)]
  · intro v hv hvu k hk k' hk' g
    rw [fam_of_not T U μf T.S (fun h => hv h.1), levelFam_of_notMem T U hv hvu]
    simp only [normInd, Pi.smul_apply]
    congr 1
    have : k * g * k' ∈ Kv V v ↔ g ∈ Kv V v := by
      rw [Subgroup.mul_mem_cancel_right _ hk', Subgroup.mul_mem_cancel_left _ hk]
    by_cases hg : g ∈ Kv V v
    · rw [indicator_of_mem (show k * g * k' ∈ (Kv V v : Set _) from this.2 hg), indicator_of_mem (show g ∈ (Kv V v : Set _) from hg)]; rfl
    · rw [indicator_of_notMem (show k * g * k' ∉ (Kv V v : Set _) from fun h => hg (this.1 h)),
        indicator_of_notMem (show g ∉ (Kv V v : Set _) from hg)]
  · intro W _ _ σ hσ hT P hP
    rw [HasTypeVec] at hT
    obtain ⟨x, hx0, hxK, hxS⟩ := hT

    have hxker : ∀ v : T.S, ∀ k ∈ kerSub T v, σ (locFin V v k) x = x := by
      intro v
      have hle : Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} ≤
          GlobalTheory.PRep.fixed (σ.comp (locFin V v)) (kerSub T v) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨φ, hφ, z, rfl⟩ ⟨_, ⟨k, hk1, rfl⟩⟩
        have := hφ k z
        rw [MonoidHom.mem_ker.1 hk1, map_one] at this
        simpa using this.symm
      intro k hk
      simpa using hle (hxS v) ⟨k, hk⟩
    have hxlev : ∀ v, ∀ k ∈ levelFam T U v, σ (locFin V v k) x = x := by
      intro v k hk
      by_cases hvu : v = U.u
      · subst hvu
        rw [levelFam_u] at hk
        exact hxK _ hu k (U.frame.iwahori_le hk)
      · by_cases hv : v ∈ T.S
        · rw [levelFam_of_mem T U hu ⟨v, hv⟩] at hk
          exact hxker ⟨v, hv⟩ k hk
        · rw [levelFam_of_notMem T U hv hvu] at hk
          exact hxK v hv k hk
    have hlev := _root_.GlobalTheory.TrIdem.levelFam_open_le D V T U hu
    have key : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)), A ⊆ T.S → ∀ P,
        GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf A)) P → P x = x := by
      intro A
      induction A using Finset.induction_on with
      | empty =>
        intro _ P hP
        have e : fam T U μf ∅ = fun v => normInd (μf v) (levelFam T U v : Set _) :=
          funext fun v => fam_of_not T U μf ∅ (fun h => Finset.notMem_empty v h.2)
        rw [e] at hP
        refine _root_.GlobalTheory.TrIdem.integralOp_normInd_fix D V μf hH h1 ν hν (levelFam T U) (fun v => (hlev v).1) (fun v => (hlev v).2) ?_ W σ x
          (_root_.GlobalTheory.TrIdem.fixed_of_forall_finLoc_mem D V W σ hσ (levelFam T U) (fun v => (hlev v).2) x hxlev) P hP
        filter_upwards [T.S.eventually_cofinite_notMem, eventually_cofinite_ne U.u] with v hv hvu
        exact levelFam_of_notMem T U hv hvu
      | insert a A ha ih =>
        intro hsub P hP
        have haS : a ∈ T.S := hsub (Finset.mem_insert_self a A)
        obtain ⟨H, K, -, -, -, hHB⟩ := _root_.GlobalTheory.OffOp.exists_offOp D V a μf hH h1 ν hν W σ hσ (fam T U μf A)
          (_root_.GlobalTheory.TrIdem.isFinFamily_fam D V T U μf hH h1 hu A)
        have hloc := isSmooth_comp_locFin hσ a
        have hfin := (_root_.GlobalTheory.TrIdem.isFinFamily_fam D V T U μf hH h1 hu A).1
        have hfin' := (_root_.GlobalTheory.TrIdem.isFinFamily_fam D V T U μf hH h1 hu (insert a A)).1
        have hg : fam T U μf (insert a A) a = T.idem μf ⟨a, haS⟩ := fam_of_mem T U μf _ haS (Finset.mem_insert_self _ _)
        have e1 : Function.update (fam T U μf A) a (fam T U μf (insert a A) a) = fam T U μf (insert a A) := by
          funext v
          by_cases hva : v = a
          · subst hva
            rw [Function.update_self]
          · rw [Function.update_of_ne hva]
            by_cases hv : v ∈ T.S ∧ v ∈ A
            · rw [fam_of_mem T U μf _ hv.1 hv.2, fam_of_mem T U μf _ hv.1 (Finset.mem_insert_of_mem hv.2)]
            · rw [fam_of_not T U μf _ hv, fam_of_not T U μf _ (fun h => hv ⟨h.1, (Finset.mem_insert.1 h.2).resolve_left hva⟩)]
        have h2 : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf (insert a A)))
            (H ∘ₗ smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf (insert a A) a)) := by
          have := hHB _ (hfin' a) _ (isIntegralOp_smoothOp (μf a) hloc ⟨(hfin' a).1, (hfin' a).2⟩)
          rwa [e1] at this
        have hPB := hP.unique h2
        have h3 : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf A))
            (H ∘ₗ smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf A a)) := by
          have := hHB _ (hfin a) _ (isIntegralOp_smoothOp (μf a) hloc ⟨(hfin a).1, (hfin a).2⟩)
          rwa [Function.update_eq_self] at this
        have hB' := ih (fun v hv => hsub (Finset.mem_insert_of_mem hv)) _ h3
        have hBx : smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf (insert a A) a) x = x :=
          hg ▸ _root_.GlobalTheory.idemOp_fix_span D V T μf hH W σ hσ ⟨a, haS⟩ x (hxS ⟨a, haS⟩)
        have hB'x : smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf A a) x = x := by
          rw [fam_of_not T U μf A (fun h => ha h.2)]
          obtain ⟨ho, hle⟩ := hlev a
          exact _root_.GlobalTheory.TrIdem.smoothOp_normInd_of_fixed _ (μf a) _ ho ((isCompact_stabLoc _ _ _ a).of_isClosed_subset
            (Subgroup.isClosed_of_isOpen _ ho) hle) W _ hloc x (hxlev a)
        rw [hPB, LinearMap.comp_apply, hBx]
        rw [LinearMap.comp_apply, hB'x] at hB'
        exact hB'
    intro h0
    have hx := key T.S (Finset.Subset.refl _) P hP
    subst h0
    exact hx0 hx.symm

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlathFactorisationOfTensorProduct
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

namespace GlobalTheory

theorem flathFactorisation_of_tensorProduct (h1 : GlobalTheory.Published.FlathTensorProduct)
    (h2 : GlobalTheory.Published.UnitaryIrreducibleAdmissible) : GlobalTheory.Published.FlathFactorisation := by
  intro F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ
  obtain ⟨R, ξ, B, hf⟩ := h1 F E σ hc n J hJ H π hπ
  have hirr : ∀ v, (smRep (Flath.finFactor R v)).IsIrreducible ∧ IsAdmissible (smRep (Flath.finFactor R v)) := by
    intro v
    have := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v
    exact _root_.GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep (GLoc σ J v) (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr
      (fun K hK hK' => h2 F E σ hc n J hJ v (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr K hK hK')
  refine ⟨R, ξ, B, hf, hirr, ?_⟩
  intro L hL
  have := hL
  have hu : ∀ᶠ v in cofinite, ‖ξ (.inr v)‖ = 1 := Sum.inr_injective.tendsto_cofinite.eventually hf.unit
  filter_upwards [hu, hf.eventually_fixed L,
    _root_.GlobalTheory.AntiInvLoc.eventually_exists_antiInv F E σ hc n J hJ L
      (by infer_instance)] with v hv hfix hθ
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := hθ
  have hKo : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := isOpen_stabLoc σ J L v
  have hKc : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := isCompact_stabLoc σ J L v
  have sm : ∀ y, y ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v) →
      y ∈ GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v)) := by
    intro y hy
    let S : Subgroup (GLoc σ J v) :=
      { carrier := {g | toRep (Flath.finFactor R v) g y = y}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq, map_mul, mul_apply_eq_comp] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at *
          conv_lhs => rw [← ha]
          rw [← mul_apply_eq_comp, ← map_mul]
          simp }
    have hle : stabLoc σ J L v ≤ S := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hy k hk
    exact Subgroup.isOpen_mono hle hKo
  have hξ : ξ (.inr v) ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix k hk
  let x : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v)) := ⟨ξ (.inr v), sm _ hξ⟩
  have hx : x ∈ fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hξ k hk)
  have hx0 : x ≠ 0 := fun e => by
    have : ξ (.inr v) = 0 := congrArg Subtype.val e
    rw [this, norm_zero] at hv
    exact zero_ne_one hv
  have hline := _root_.GlobalTheory.fixed_eq_span_of_gelfandPair (GLoc σ J v) (stabLoc σ J L v) hKo hKc θ hθ1 hθ2 hθ3 _
    (smRep (Flath.finFactor R v)) (hirr v).1 (hirr v).2 x hx hx0
  refine le_antisymm (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hξ)
  have hy' : (⟨y, sm y hy⟩ : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v))) ∈
      fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hy k hk)
  rw [hline] at hy'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy'
  exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtLevelIndicatorCoefficientTestOneParam
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.TermDeriv

theorem hasDerivAt_coef_oneP : ∀ (D : D7), GlobalTheory.Published.HarishChandraModules → ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ) (τ : D.what₂.Tau), b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → ∀ X ∈ lieAt V τ, ∀ x : GA D V, HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 := by
  intro D hHC θ hθ V S M K v b τ hb X hX x
  have hfin : ∀ s : ℝ, Lev.finE V (x * oneP θ V τ X s) = Lev.finE V x := by
    intro s
    have h : finHom V (oneP θ V τ X s) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
    show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X s) = _
    rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X s), h, map_one, mul_one]
    rfl
  by_cases hK : Lev.finE V x ∈ K
  swap
  · have e : (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun _ => 0 := by
      funext s
      simp only [coef, hfin s, hK, if_false]
    rw [e]
    have e2 : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x = 0 := by
      simp only [coef, hK, if_false]
    rw [e2]
    exact hasDerivAt_const _ _
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hsv : SmoothVec (lieAt V τ) (M.rep τ) (b τ) :=
    hHC.smoothVec hstd.1 hstd.2.1 hb (M.fr_unit τ) (M.fr_gram τ)
  have hd0 := Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_hasDerivAt hsv hX 0
  rw [zero_smul, NormedSpace.exp_zero, Formalism.IndefR.SchurOrthogonalityAlt.gp_rep_one, ContinuousLinearMap.one_apply] at hd0
  set c : ℂ := ∏ τ' ∈ Finset.univ.erase τ, ⟪v τ', M.rep τ' (cmp θ τ' x) (b τ')⟫_ℂ with hc
  have hfun : ∀ s : ℝ, coef θ M K v b (x * oneP θ V τ X s) =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ := by
    intro s
    simp only [coef, hfin s, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
    congr 1
    · refine Finset.prod_congr rfl fun τ' hτ' => ?_
      have hne := Finset.ne_of_mem_erase hτ'
      have h := (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.2 τ' hne
      show ⟪v τ', M.rep τ' (infMat D.sp.cm.sig V.gram (θ τ') (x * oneP θ V τ X s)) (b τ')⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, h, Matrix.mul_one]
    · show ⟪v τ, M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (x * oneP θ V τ X s)) (b τ)⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.1,
        Formalism.IndefR.SchurOrthogonalityAlt.rep_mul M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ) (GlobalTheory.Mem.Lift.exp_mem hX s)]
      rfl
  have hval : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (dRep (M.rep τ) X (b τ))⟫_ℂ := by
    simp only [coef, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun τ' hτ' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ')]
  rw [hval, show (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun s : ℝ =>
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ from funext hfun]
  refine HasDerivAt.const_mul c ?_
  exact (((innerSL ℂ (v τ)).comp (M.rep τ (cmp θ τ x))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd0

end GlobalTheory.TermDeriv

end
end

