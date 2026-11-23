module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerSpanKFiniteTensors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePath
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AvgOtherPlace

open Formalism.MainNotions.S Formalism.REAL MeasureTheory Matrix GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open scoped TensorProduct

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem atTau_comm (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) {g h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ')) :
    atTau θ V τ g * atTau θ V τ' h = atTau θ V τ' h * atTau θ V τ g := by
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have a := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  have b := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ' hh
  refine R.2.2.1 _ (mul_mem a.1 b.1) _ (mul_mem b.1 a.1) fun ρ => ?_
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul]
  by_cases c : ρ = τ
  · subst c
    rw [a.2.1, b.2.2 ρ (Ne.symm hne), Matrix.mul_one, Matrix.one_mul]
  · rw [a.2.2 ρ c, Matrix.mul_one, Matrix.one_mul]

theorem adAt_atTau_of_ne (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    adAt θ (atTau θ V τ g) τ' X = X := by
  have a := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  have b := GlobalTheory.PointAtPlaceHom.isAtTau_inv V τ hg a
  rw [adAt, a.2.2 τ' hne, b.2.2 τ' hne, Matrix.one_mul, Matrix.mul_one]

section Avg

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}


variable (θ V) in
def avgF (τ : D.what₂.Tau) (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ) (e : K → ℂ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ

theorem avgF_zero : avgF θ V μ τ κ e 0 = 0 := by
  funext x
  simp [avgF]

theorem avgF_add (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (he : Continuous e) {f g : GA D V → ℂ} (hf : Continuous f) (hg : Continuous g) :
    avgF θ V μ τ κ e (f + g) = avgF θ V μ τ κ e f + avgF θ V μ τ κ e g := by
  funext x
  simp only [avgF, Pi.add_apply, mul_add]
  exact integral_add (GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hf x)
    (GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hg x)

theorem avgF_smul (c : ℂ) (f : GA D V → ℂ) : avgF θ V μ τ κ e (c • f) = c • avgF θ V μ τ κ e f := by
  funext x
  simp only [avgF, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul c _

theorem avgF_Rder (hθ : IsInfFam θ) (hne : τ' ≠ τ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (he : Continuous e) {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ') :
    Rder θ V τ' X (avgF θ V μ τ κ e ψ) = avgF θ V μ τ κ e (Rder θ V τ' X ψ) := by
  set 𝒟 : Set (GA D V → ℂ) := {ψ | IsAutFunSm θ V ψ}
  have h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ := fun _ h => h
  have hR : ∀ ψ ∈ 𝒟, ∀ τ'' X, X ∈ lieAt V τ'' → Rder θ V τ'' X ψ ∈ 𝒟 :=
    fun _ h _ _ hX => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX h
  have F := GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives D θ hθ V K μ (GlobalTheory.RealAverage.famSpan θ V τ κ 𝒟)
    (GlobalTheory.RealAverage.famSpan_cont hθ hκ hU h𝒟) (GlobalTheory.RealAverage.famSpan_sm hθ hU h𝒟)
    (GlobalTheory.RealAverage.famSpan_Rder hθ hκ hU h𝒟 hR)
    (fun k x => e k * ψ (x * atTau θ V τ (κ k))) (Submodule.subset_span ⟨e, he, ψ, hψ, rfl⟩)
  have h1 := F.2.2.1 [(τ', X)] (by simpa using hX)
  simp only [List.foldr_cons, List.foldr_nil] at h1
  show Rder θ V τ' X (fun x => ∫ k, e k * ψ (x * atTau θ V τ (κ k)) ∂μ) = _
  rw [h1]
  funext x
  simp only [avgF]
  congr 1
  funext k
  have e1 : (fun x => e k * ψ (x * atTau θ V τ (κ k))) = e k • rTr V (atTau θ V τ (κ k)) ψ := rfl
  rw [e1, Rder_smul, Rder_rTr hθ (isRealPt_atTau hθ τ (hU k)) hX, adAt_atTau_of_ne hθ hne (hU k)]
  rfl

theorem isGKMap_avgF (hθ : IsInfFam θ) (hne : τ' ≠ τ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (he : Continuous e) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ε : Fin V.rank → Bool} {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} {T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ)} (hT : IsGKMap θ V τ' ε σ P T) :
    ∃ T' : kFin ε σ →ₗ[ℂ] (GA D V → ℂ), IsGKMap θ V τ' ε σ P T' ∧ ∀ v, T' v = avgF θ V μ τ κ e (T v) := by
  let T' : kFin ε σ →ₗ[ℂ] (GA D V → ℂ) :=
    { toFun := fun v => avgF θ V μ τ κ e (T v)
      map_add' := fun a b => by
        rw [map_add (f := _)]
        exact avgF_add μ hθ hκ hU he (hT.aut a).cont (hT.aut b).cont
      map_smul' := fun c a => by
        rw [map_smul]
        exact avgF_smul μ c (T a) }
  refine ⟨T', ⟨fun v => ?_, fun g hg hgK v w hw => ?_, fun X hX v w hd => ?_⟩, fun v => rfl⟩
  · exact GlobalTheory.RealAverage.isAutFunSm_average D θ hθ V τ K μ κ hκ hU e he _ (hT.aut v)
  · show avgF θ V μ τ κ e (T w) = rTr V (atTau θ V τ' g) (avgF θ V μ τ κ e (T v))
    rw [hT.mapK g hg hgK v w hw]
    funext x
    simp only [avgF, rTr]
    congr 1
    funext k
    rw [mul_assoc, mul_assoc, atTau_comm hθ hne (hU k) hg]
  · show avgF θ V μ τ κ e (T w) = Rder θ V τ' X (avgF θ V μ τ κ e (T v))
    rw [hT.mapLie X hX v w hd, avgF_Rder μ hθ hne hκ hU he (hT.aut v) hX]

end Avg

section Closure

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}

theorem hasTypeAt_avgF (hθ : IsInfFam θ) (hne : τ' ≠ τ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (he : Continuous e) {S : SPar} {φ : GA D V → ℂ}
    (hφc : Continuous φ) (h : HasTypeAt θ V τ' S φ) : HasTypeAt θ V τ' S (avgF θ V μ τ κ e φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : Continuous fun k => atTau θ V τ (κ k) := GlobalTheory.RealAverage.continuous_atTau hθ hκ hU
  let W' : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | Continuous f ∧ avgF θ V μ τ κ e f ∈ finPartOfType θ V τ' S}
      zero_mem' := ⟨continuous_const, by rw [avgF_zero]; exact zero_mem _⟩
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, by
        rw [avgF_add μ hθ hκ hU he ha.1 hb.1]; exact add_mem ha.2 hb.2⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, by
        rw [avgF_smul]; exact Submodule.smul_mem _ c ha.2⟩ }
  have hle : finPartOfType θ V τ' S ≤ W' := by
    refine sSup_le ?_
    rintro W ⟨H, _, _, σ, lam, ε, P, T, hE, hlam, hD, hP, hJ, hT, rfl⟩ f ⟨v, rfl⟩
    obtain ⟨T', hT', hv⟩ := isGKMap_avgF μ hθ hne hκ hU he hT
    refine ⟨(hT.aut v).cont, ?_⟩
    rw [← hv]
    exact (le_sSup (a := LinearMap.range T') ⟨H, _, _, σ, lam, ε, P, T', hE, hlam, hD, hP, hJ, hT', rfl⟩ :
      _ ≤ finPartOfType θ V τ' S) ⟨v, rfl⟩
  intro C hC δ hδ
  have hI0 : 0 ≤ ∫ k, ‖e k‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  set M : ℝ := (∫ k, ‖e k‖ ∂μ) + 1 with hMdef
  have hM : 0 < M := by linarith
  have hC' : IsCompact ((fun p : GA D V × K => p.1 * atTau θ V τ (κ p.2)) '' (C ×ˢ Set.univ)) :=
    (hC.prod isCompact_univ).image (continuous_fst.mul (hk.comp continuous_snd))
  obtain ⟨ψ, hψ, hap⟩ := h _ hC' (δ / M) (div_pos hδ hM)
  have hψ' := hle hψ
  refine ⟨_, hψ'.2, fun x hx => ?_⟩
  have i1 := GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hφc x
  have i2 := GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hψ'.1 x
  simp only [avgF]
  rw [← integral_sub i1 i2]
  have hb : ∀ k, ‖e k * φ (x * atTau θ V τ (κ k)) - e k * ψ (x * atTau θ V τ (κ k))‖ ≤ ‖e k‖ * (δ / M) :=
    fun k => by
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (hap _ ⟨(x, k), ⟨hx, Set.mem_univ _⟩, rfl⟩).le (norm_nonneg _)
  have hie : Integrable (fun k => ‖e k‖) μ :=
    he.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le (hie.mul_const _) (Filter.Eventually.of_forall hb)) ?_
  rw [integral_mul_const]
  have hlt : (∫ k, ‖e k‖ ∂μ) < M := by linarith
  calc (∫ k, ‖e k‖ ∂μ) * (δ / M) < M * (δ / M) := mul_lt_mul_of_pos_right hlt (div_pos hδ hM)
    _ = δ := mul_div_cancel₀ _ hM.ne'

end Closure

end GlobalTheory.AvgOtherPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumThetaTransformEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.VacDatum

theorem vacDatum_exists : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ f : WO S X → ℂ, IsFinF ψ θ ε A B f → ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD f := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f hf
  obtain ⟨ξ, JB, co, hJB, hrat, hiff⟩ :=
    _root_.GlobalTheory.SquareAgree.exists_darboux_transport D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D ψ (hψ ▸ hBs.std)
  obtain ⟨-, -, hon⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := sgn ε S) (T := X) co hstd rfl hJB hrat
  obtain ⟨Φ, hΦ, hΦf⟩ := (hon f).1 hf.1
  have hD : IsDatum M ψ cS Φ f := (hiff Φ f).2 ⟨hΦ, hΦf⟩
  have hG := _root_.GlobalTheory.VacTransfer.vacDatum_transfer D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f Φ hf hD
  have hsp := _root_.GlobalTheory.VacFactor.mem_span_of_isGaussEq M Bs.ψ Bs.emb hBs.std Φ hΦ hG
  refine ⟨Φ, Submodule.span_le.2 ?_ hsp, hD⟩
  rintro _ ⟨g, h, hg, hh, rfl⟩
  exact _root_.GlobalTheory.SquareAgree.pureA_mem_algD M Bs.ψ Bs.emb hM g hg h hh

end GlobalTheory.VacDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfLatticeAdjointFrameReductionsEq
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AdjRedOnto

open Formalism.IndefR.Datum GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec

theorem exists_half_redM_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ z : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
  ∃ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = z PP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io _ e he z
  have he2 := idemSum_mul_self he
  obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
  obtain ⟨⟨es, h1, h2⟩, -⟩ := he
  have hk : ∀ PP ∈ R.Pg ∪ R.Q t, toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun PP hPP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).1
  have hdel : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ PP' (hPP' : PP' ∈ R.Pg ∪ R.Q t),
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP'), hk PP' hPP'⟩ = if PP' = PP then 1 else 0 := by
    intro PP hPP PP' hPP'
    by_cases hq : PP' = PP
    · subst hq
      rw [if_pos rfl]
      exact (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP' hPP')).2
    · rw [if_neg hq]
      have hne : PP ≠ PP' := fun h => hq h.symm
      have horth : es PP * es PP' = 0 :=
        (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP).1 (h1 PP' hPP').1).resolve_left fun h => by
          have h' := h1 PP' hPP'
          rw [← h] at h'
          exact hne (isIdemAt_inj (h1 PP hPP) h')
      have h4 : (⟨toEAf D (es PP), hk PP hPP⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP'), hk PP' hPP'⟩ = 0 :=
        Subtype.ext (by change toEAf D (es PP) * toEAf D (es PP') = 0; rw [← RingHom.map_mul, horth, RingHom.map_zero])
      have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
      rwa [RingHom.map_mul, RingHom.map_zero, (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).2, one_mul] at h5
  choose a ha using fun (PP : Formalism.L2.DIV.Pl D.host.E) (j : Fin (Vc D i).rank) (k : Fin (Wc D i).rank) =>
    Ideal.Quotient.mk_surjective (I := PP.asIdeal) (z PP j k)
  set L : Formalism.L2.DIV.Pl D.host.E → Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (Formalism.IndefR.Datum.EAf D) :=
    fun PP j k => ((Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) with hL
  obtain ⟨x, hx, hx'⟩ := GlobalTheory.AdjDatumNe.exists_half_frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) he2
    (∑ PP ∈ R.Pg ∪ R.Q t, toEAf D (es PP) • L PP)
  have hent : ∀ j k, frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x j k =
      ((⟨toEAf D e, hi⟩ * ∑ PP ∈ (R.Pg ∪ R.Q t).attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP.1 j k) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := by
    intro j k
    rw [hx', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Subring.coe_mul, AddSubmonoidClass.coe_finsetSum]
    congr 1
    rw [← Finset.sum_attach]
    rfl
  refine ⟨x, hx, fun j k => ?_, fun PP hPP => ?_⟩
  · rw [hent]; exact Subtype.prop _
  · funext j k
    unfold redM
    rw [dite_eq_left (by rw [hent]; exact Subtype.prop _)]
    have hsub : (⟨frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x j k, by rw [hent]; exact Subtype.prop _⟩ :
        Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D e, hi⟩ * ∑ PP ∈ (R.Pg ∪ R.Q t).attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP.1 j k) := Subtype.ext (hent j k)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsub, RingHom.map_mul, hres PP hPP, one_mul, map_sum]
    simp_rw [RingHom.map_mul, Formalism.L2.DIV.resS_oToS]
    rw [Finset.sum_eq_single ⟨PP, hPP⟩]
    · rw [hdel PP hPP PP hPP, if_pos rfl, one_mul, ha]
    · intro b _ hb
      rw [hdel PP hPP b.1 b.2, if_neg (fun h => hb (Subtype.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_attach _ _) h

end GlobalTheory.AdjRedOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.ExItY

theorem ex_ItY_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G]
    [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW →
    R.ex_ItY := by
  intro hDS hHC D G _ _ Pl0 T A Ks _ _ _ R hL _ hM hH hW
  have hθ : IsInfFam R.θ := hM.inf
  exact GlobalTheory.Chain.innerIntertwiners_of_pair D G Pl0 T A Ks R (GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep hDS hHC D)
    (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hθ
    (GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX)

end GlobalTheory.Chain.ExItY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeOfMemSpan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Formalism.L2.DIV Formalism.L2.Indef NumberField GlobalTheory.Chain GlobalTheory.Chain.IoLift
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowTest.WVec

variable {D : D7}

theorem tprod_ne_zero {κ : Type} [Fintype κ] {E : κ → Type} [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {v : ∀ j, E j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem exists_inclK_ne {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h : KSm M) :
    ∃ y : KT M, inclK h y ≠ 0 := by
  have hu : ∀ τ, ∃ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, u ≠ 0 := fun τ => by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
    exact ⟨⟨x, hx⟩, fun e => hx0 (congrArg Subtype.val e)⟩
  choose u hu using hu
  refine ⟨PiTensorProduct.tprod ℂ u, fun e => tprod_ne_zero hu ?_⟩
  exact GlobalTheory.Chain.IoLift.FinTensor.inclK_injective h (e.trans (map_zero _).symm)

theorem exists_ne_of_mem_span {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) {s : Set E} {x : E} (hx : x ∈ Submodule.span ℂ s) (h : L x ≠ 0) : ∃ z ∈ s, L z ≠ 0 := by
  by_contra hn
  push_neg at hn
  exact h ((Submodule.span_le (p := LinearMap.ker L)).2 (fun z hz => hn z hz) hx)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem dnVec_congr (d d' : ChainVec R) : ∀ n, (∀ k < n, d.polY k = d'.polY k) → d.dnVec n = d'.dnVec n
  | 0, _ => rfl
  | n + 1, h => by
    show d.dnVec n ∘ₗ R.ItY n (d.polY n) = d'.dnVec n ∘ₗ R.ItY n (d'.polY n)
    rw [dnVec_congr d d' n fun k hk => h k (by omega), h n (by omega)]

def ofPol (p : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) : ChainVec R := ⟨p, 0, 0⟩

theorem exists_w_ne (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules)
    (hC : ∀ k, ChainPar D k) (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hch : R.IsChain) (hθ : R.models_inf) :
    ∃ cv : ChainVec R, cv.w ≠ 0 := by
  have hm := D.R.two_le_m
  have hS := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hch.ωY hch.ωX hch.vY hch.vX
  have stepY : ∀ k, k + 1 < D.R.m → ∃ (h : KSm (R.MY k)) (h' : KSm (R.MY (k + 1))),
      LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, R.ItY k φ (inclK h' y) = x} := fun k hk => by
    obtain ⟨hW, hV⟩ := hS.1 A.μ0 ⟨k, by omega⟩ hk
    exact _root_.GlobalTheory.Chain.KFinOnto.itW_onto_kFin hD hH D ⟨k, by omega⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left (by omega))
      (min_eq_left (by omega)) _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY A.μ0 k) (R.vY A.μ0 k) hW hV (R.ItY k)
      (hch.ItY A.μ0 k hk)
  have stepX : ∃ (h : KSm (R.MY (D.R.m - 1))) (h' : KSm R.MX),
      LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, R.ItX φ (inclK h' y) = x} := by
    obtain ⟨hW, hV⟩ := hS.2 A.μ0 ⟨D.R.m - 1, by omega⟩ rfl
    exact _root_.GlobalTheory.Chain.KFinOnto.itW_onto_kFin hD hH D ⟨D.R.m - 1, by omega⟩ (min (D.R.m - 1) D.R.m) D.R.m (min_eq_left (Nat.sub_le _ _))
      (by show D.R.m = D.R.m - 1 + 1; omega) _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ hθ (hC _) (R.ωX A.μ0) (R.vX A.μ0) hW hV
      R.ItX (hch.ItX A.μ0)
  have key : ∀ n, n + 1 ≤ D.R.m → ∃ (p : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (h : KSm (R.MY n))
      (y : KT (R.MY n)), (ofPol (R := R) p).dnVec n (inclK h y) ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨h, -, -⟩ := stepY 0 (by omega)
      obtain ⟨y, hy⟩ := exists_inclK_ne h
      exact ⟨fun _ => 0, h, y, hy⟩
    | succ n ih =>
      intro hn
      obtain ⟨p, h, y, hy⟩ := ih (by omega)
      obtain ⟨h1, h2, hsp⟩ := stepY n (by omega)
      obtain ⟨z, ⟨φ, y', rfl⟩, hz⟩ := exists_ne_of_mem_span _ (hsp ⟨y, rfl⟩) hy
      refine ⟨Function.update p n φ, h2, y', ?_⟩
      show (ofPol (R := R) (Function.update p n φ)).dnVec n
        (R.ItY n ((Function.update p n φ) n) (inclK h2 y')) ≠ 0
      rw [Function.update_self, dnVec_congr (ofPol (Function.update p n φ)) (ofPol p) n
        fun k hk => Function.update_of_ne (by omega) _ _]
      exact hz
  obtain ⟨p, h, y, hy⟩ := key (D.R.m - 1) (by omega)
  obtain ⟨h1, h2, hsp⟩ := stepX
  obtain ⟨z, ⟨φ, y', rfl⟩, hz⟩ := exists_ne_of_mem_span _ (hsp ⟨y, rfl⟩) hy
  refine ⟨⟨p, φ, inclK h2 y'⟩, ?_⟩
  show ChainVec.dnVec ⟨p, φ, inclK h2 y'⟩ (D.R.m - 1) (R.ItX φ (inclK h2 y')) ≠ 0
  rwa [dnVec_congr ⟨p, φ, inclK h2 y'⟩ (ofPol p) (D.R.m - 1) fun k _ => rfl]

end GlobalTheory.RowTest.WVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePathStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedFiniteTensor_of_representing_oppositePath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (Φ : G.Datum) (Q : GlobalTheory.FlipRun.PolE G →₀ ℂ) (τ : TotT G (oppPath t D.R.m)), GlobalTheory.FlipRun.RepFin B ρ t (oppPath t D.R.m) τ (Tflip W B t Φ) → ∃ τ', GlobalTheory.RowClaim.IsFlipFin t B ρ Φ τ' ∧ GlobalTheory.FlipRun.tensE W (oppPath t D.R.m) Q τ = GlobalTheory.RowClaim.oppTens W t (Q.mapDomain GlobalTheory.FlipRun.toOpp) τ' := by
  first | exact @GlobalTheory.OppConv.flipFin_of_repFin | exact GlobalTheory.OppConv.flipFin_of_repFin | (intros; apply GlobalTheory.OppConv.flipFin_of_repFin <;> assumption)
end

