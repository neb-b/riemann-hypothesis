module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SkewSpaceLineOneParamFockDerivativeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewSpaceLine_oneParam_fockDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X)
    (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ), IsInfFam θ →
    IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
    ∀ (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
      (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
      ∃ (h : ℝ → GA D X) (Y : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ τ, Y τ ∈ lieAt X τ) ∧
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (h t)) ∧
        ∀ f₀ : WO (sgn ε M) X → ℂ, IsVacF ψ θ (frSgn ε A) B f₀ → ∀ (P : PolF D X.rank M.rank) (z : WO (sgn ε M) X),
          HasDerivAt (fun t : ℝ => ω (1, h t) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z)
            (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (Y τ) P) z) 0 := by
  first | exact @GlobalTheory.LieLines.line_deriv | exact GlobalTheory.LieLines.line_deriv | (intros; apply GlobalTheory.LieLines.line_deriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarSmulMemSpanModulusDivConjugateLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AdjSrcZero

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem AAbar_ne_zero (D : D7) : D.host.AAbar ≠ 0 := by
  obtain ⟨⟨hAA, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  intro h0
  apply hAA
  rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
  intro x hx
  have h1 : star x ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  have h2 := h0 _ h1
  simpa using congrArg star h2

theorem AAbar_mul_st (G : GridData L sc) :
    D.host.AAbar * (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) = D.host.AA * shiftId G := by
  have hA := AAbar_ne_zero D
  simp only [zero_add, pow_one, Places.stA, Places.stAbar, shiftId, mul_inv, inv_inv]
  calc _ = (D.host.AAbar * D.host.AAbar⁻¹) * (D.host.AA *
        (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, one_mul]

theorem star_smul_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {n : ℕ}
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), ∀ a ∈ D.host.AA,
    ∀ s ∈ idLat (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) Λ₀,
    star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
  intro D T L sc G n Λ₀ a ha s hs
  obtain ⟨⟨-, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  have key : ∀ b ∈ D.host.AA * shiftId G, ∀ y ∈ Λ₀, b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
    intro b hb y hy
    refine FractionalIdeal.mul_induction_on (C := fun b => b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) hb ?_ ?_
    · intro i hi j hj
      refine Submodule.subset_span ⟨i, hi, j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, ?_⟩
      rw [smul_smul]
    · intro x z hx hz
      rw [add_smul]
      exact add_mem hx hz
  have hsa : star a ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  unfold idLat at hs
  refine Submodule.span_induction (p := fun z _ => star a • z ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨i, hi, y, hy, rfl⟩
    rw [smul_smul]
    exact key _ (AAbar_mul_st G ▸ FractionalIdeal.mul_mem_mul hsa hi) y hy
  · simp
  · intro x z _ _ hx hz
    rw [smul_add]
    exact add_mem hx hz
  · intro c x _ hx
    rw [smul_comm]
    exact Submodule.smul_mem _ c hx

end GlobalTheory.AdjSrcZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LiftTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem tame_congr (hψ : IsStdChar D ψ (-1)) {ℓ ℓ' : (WO S T → ℂ) → ℂ} (h : Tame ψ S T ℓ)
    (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hh : ∀ f, IsThetaFunO ψ S T f → ∀ w, ℓ' (heisO ψ S T w f) = ℓ (heisO ψ S T w f) := fun f hf w =>
    e _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hI => ?_⟩
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_smul c hf), e _ hf, h.smul c f hf]
  · simpa only [hh f hf] using h.cont f hf
  · simpa only [hh f hf] using h.bdd f hf
  · rw [e _ hI, h.sup f hf m α hα hI]
    simp only [hh f hf]

theorem finite_vol {V : HSp D} (v : GlobalTheory.Unf.Vol V) : IsFiniteMeasure (v.μ.restrict v.𝓕) := by
  have h : IntegrableOn (fun _ => (1 : ℝ)) v.𝓕 v.μ := by
    simpa using GlobalTheory.Size.integrableOn_inv_quotHeight_pow (V := V) 0 v.haar v.fund
  rcases (integrableOn_const_iff (by simp)).1 h with h | h
  · simp at h
  · exact isFiniteMeasure_restrict.2 h.ne

theorem tame_double {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om) (vT : GlobalTheory.Unf.Vol T)
    {G : GA D T → ℂ} (hG : RapidDec T G) {A : HSp D} (vA : GlobalTheory.Unf.Vol A) {φ : GA D A → ℂ} (hφ : RapidDec A φ)
    {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N)
    [IsFiniteMeasure ν] (K : GA D A → N → ℂ) (g : GA D A → N → GA D S)
    (hK : Continuous fun p : GA D A × N => K p.1 p.2) (hg : Continuous fun p : GA D A × N => g p.1 p.2)
    {C C' : ℝ} {a a' : ℕ} (hKb : ∀ h n, ‖K h n‖ ≤ C * (‖φ h‖ * quotHeight A h ^ a))
    (hgb : ∀ h n, quotHeight S (g h n) ≤ C' * quotHeight A h ^ a') :
    Tame ψ S T fun Φ => ∫ h in vA.𝓕, ∫ n, K h n * liftS om vT.μ vT.𝓕 G Φ (g h n) ∂ν ∂vA.μ := by
  obtain ⟨-, h2A, -, hbA, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, h2T, -, hbT, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  haveI := finite_vol vA
  haveI := finite_vol vT
  have hc : Continuous fun y : (GA D A × N) × GA D T => K y.1.1 y.1.2 * G y.2 :=
    (hK.comp continuous_fst).mul (hG.continuous.comp continuous_snd)
  have hg' : Continuous fun y : (GA D A × N) × GA D T => g y.1.1 y.1.2 := hg.comp continuous_fst
  obtain ⟨hI, hT⟩ := _root_.GlobalTheory.KerTame.kernel_tame D ψ S T χS χT om hom ((GA D A × N) × GA D T)
    (((vA.μ.restrict vA.𝓕).prod ν).prod (vT.μ.restrict vT.𝓕)) (fun y => K y.1.1 y.1.2 * G y.2) (fun y => g y.1.1 y.1.2)
    (fun y => y.2) (fun _ => 0) hc.measurable hg' continuous_snd continuous_const (fun k => by
      obtain ⟨M, hM⟩ := hφ.decay (a + a' * k)
      obtain ⟨M', hM'⟩ := hG.decay k
      refine Integrable.of_bound (hc.norm.mul ((((continuous_quotHeight S).comp hg').mul
        ((continuous_quotHeight T).comp continuous_snd)).pow k)).aestronglyMeasurable (|C| * |C'| ^ k * M * M')
        (Filter.Eventually.of_forall fun y => ?_)
      obtain ⟨⟨h, n⟩, t⟩ := y
      have p1 := (quotHeight_pos A h).le
      have p2 := (quotHeight_pos T t).le
      have p3 := (quotHeight_pos S (g h n)).le
      have b1 : ‖K h n‖ ≤ |C| * (‖φ h‖ * quotHeight A h ^ a) :=
        (hKb h n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      have b2 : quotHeight S (g h n) ≤ |C'| * quotHeight A h ^ a' :=
        (hgb h n).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))
      have hM0 : 0 ≤ M := le_trans (by positivity) (hM h)
      show ‖‖K h n * G t‖ * (quotHeight S (g h n) * quotHeight T t) ^ k‖ ≤ _
      rw [Real.norm_of_nonneg (by positivity), norm_mul]
      calc ‖K h n‖ * ‖G t‖ * (quotHeight S (g h n) * quotHeight T t) ^ k
          ≤ |C| * (‖φ h‖ * quotHeight A h ^ a) * ‖G t‖ * (|C'| * quotHeight A h ^ a' * quotHeight T t) ^ k := by gcongr
        _ = |C| * |C'| ^ k * (‖φ h‖ * quotHeight A h ^ (a + a' * k)) * (‖G t‖ * quotHeight T t ^ k) := by ring
        _ ≤ _ := by gcongr; exacts [hM h, hM' t])
  refine tame_congr hom.std hT fun f hf => ?_
  have h1 := hI f hf
  rw [integral_prod _ h1, integral_prod _ h1.integral_prod_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [liftS_apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  ring

theorem lift_periods_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (G : GA D W → ℂ), RapidDec W G → (∀ (ρ : ℕ) (B : BesL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om B.V W), IsWeilDatumO ψ B.V W χ χ' om → ∀ φ, RapidDec B.A φ → Tame ψ B.V W fun Φ => B.per ψ φ (liftS om vW.μ vW.𝓕 G Φ)) ∧ ∀ (ρ : ℕ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om J.W W), IsWeilDatumO ψ J.W W χ χ' om → ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (χ₁ χ₂ : (AE D)ˣ →* Circle) (omz : Om J.W₀ L'), IsWeilDatumO ψ J.W₀ L' χ₁ χ₂ omz → ∀ φ Φ₀, RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ L' Φ₀ → Tame ψ J.W W fun Φ => J.per ψ ζ' omz φ (liftS om vW.μ vW.𝓕 G Φ) Φ₀ := by
  intro D ψ W vW G hG
  refine ⟨fun ρ B χ χ' om hom φ hφ => ?_, fun ρ J χ χ' om hom L' ζ' χ₁ χ₂ omz homz φ Φ₀ hφ hΦ₀ => ?_⟩
  · obtain ⟨-, h2, -, hb, ht, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
    haveI : SecondCountableTopology (flagN B.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN B.d : Set (GA D B.V))
    haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) :=
      isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
    obtain ⟨C₁, a₁, h₁⟩ := _root_.GlobalTheory.HtWitt.quotHeight_witt D B.V B.V₀ ρ B.d
    obtain ⟨C₂, a₂, h₂⟩ := _root_.GlobalTheory.HtOrth.quotHeight_orthDec_cmp D B.V₀ B.A B.L B.o
    have hn : Continuous fun p : GA D B.A × flagN B.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have := tame_double hom vW hG B.vA hφ (B.vN.ν.restrict B.vN.𝓝)
      (fun h (n : flagN B.d) => φ h * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)) (fun h n => n.1 * embA B.d B.o h)
      ((hφ.continuous.comp continuous_fst).mul
        ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hom.std.1.1 1 (vecB B.o B.ζ)).comp hn).star)
      (hn.mul ((B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))).comp
        continuous_fst))
      (C := 1) (a := 0) (C' := |C₁| * |C₂| ^ a₁) (a' := a₂ * a₁) (fun h n => by
        have e : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) n.1‖ = 1 := hom.std.1.2.1 _
        simp [e]) (fun h n => by
        have p1 := (quotHeight_pos B.A h).le
        have p2 := (quotHeight_pos B.V₀ (B.o.emb (h, 1))).le
        have b : quotHeight B.V₀ (B.o.emb (h, 1)) ≤ |C₂| * quotHeight B.A h ^ a₂ :=
          (h₂ h).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        calc _ ≤ C₁ * quotHeight B.V₀ (B.o.emb (h, 1)) ^ a₁ := (h₁ n.1 n.2 _).2
          _ ≤ |C₁| * (|C₂| * quotHeight B.A h ^ a₂) ^ a₁ := by gcongr; exact le_abs_self _
          _ = _ := by ring)
    convert this using 2 with Φ
    unfold BesL.per besPer besFun
    congr 1; funext h; congr 1; funext n; ring
  · obtain ⟨-, h2, -, hb, ht, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
    haveI : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN J.d : Set (GA D J.W))
    haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) :=
      isFiniteMeasure_restrict.2 (by rw [J.vN.unit.2.2]; exact ENNReal.one_ne_top)
    obtain ⟨C₁, a₁, h₁⟩ := _root_.GlobalTheory.HtWitt.quotHeight_witt D J.W J.W₀ ρ J.d
    obtain ⟨C₂, a₂, h₂⟩ := GlobalTheory.SupThetaGrowth.om_sup_quotHeight D ψ J.W₀ L' χ₁ χ₂ omz homz Φ₀ hΦ₀
    have hn : Continuous fun p : GA D J.W₀ × flagN J.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have hth : ∀ n h, thetaJS ψ J.d ζ' omz Φ₀ n h =
        ψ (cenS J.d L' (zEll L' ρ ζ') n) * omz (h, 1) Φ₀ (ptS J.d L' (zEll L' ρ ζ') n) := fun n h => by
      rw [thetaJS, GlobalTheory.Unf.FB.ThLaws.jacS_zero_apply]
    have hJ : Continuous fun p : (GA D J.W₀ × GA D L') × WO J.W₀ L' => omz p.1 Φ₀ p.2 :=
      (@GlobalTheory.Unf.jointCont_all D) ψ J.W₀ L' χ₁ χ₂ omz homz Φ₀ hΦ₀
    have hthc : Continuous fun p : GA D J.W₀ × flagN J.d => thetaJS ψ J.d ζ' omz Φ₀ p.2.1 p.1 := by
      simp only [hth]
      exact (hom.std.1.1.comp ((GlobalTheory.Unf.FB.ThLaws.continuous_cenS _ _ _).comp hn)).mul
        (hJ.comp ((continuous_fst.prodMk continuous_const).prodMk ((GlobalTheory.Unf.FB.ThLaws.continuous_ptS _ _ _).comp hn)))
    have := tame_double hom vW hG J.v0 hφ (J.vN.ν.restrict J.vN.𝓝)
      (fun h (n : flagN J.d) => φ h * star (thetaJS ψ J.d ζ' omz Φ₀ n.1 h) * star (psiFlag ψ J.d n.1))
      (fun h n => n.1 * J.d.emb0 h)
      (((hφ.continuous.comp continuous_fst).mul hthc.star).mul
        ((GlobalTheory.Unf.FB.ThLaws.continuous_psiFlag hom.std.1.1 _).comp hn).star)
      (hn.mul (J.d.continuous_embed.comp continuous_fst))
      (C := C₂ * quotHeight L' 1 ^ a₂) (a := a₂) (C' := C₁) (a' := a₁) (fun h n => by
        have e : ‖psiFlag ψ J.d n.1‖ = 1 := hom.std.1.2.1 _
        rw [norm_mul, norm_mul, norm_star, norm_star, e, hth, norm_mul, hom.std.1.2.1, one_mul, mul_one]
        refine (mul_le_mul_of_nonneg_left (h₂ h 1 _) (norm_nonneg _)).trans (le_of_eq ?_)
        ring) (fun h n => (h₁ n.1 n.2 _).2)
    convert this using 2 with Φ
    unfold JacL.per fjSrc fjSrcFun
    congr 1; funext h; congr 1; funext n; ring

end GlobalTheory.LiftTame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelResidueCharacter
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open MeasureTheory
open scoped ENNReal

theorem integral_norm_sq_eq_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ _ T hA μ hμ t f
  obtain ⟨g, hg, hg0⟩ : ∃ g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ,
      g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ g 0 ≠ 0 := by
    refine ⟨_, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _, ?_⟩
    have h0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F (Fin n × Fin d) :=
      fun i _ v => zero_mem (v.adicCompletionIntegers F)
    rw [Set.indicator_of_mem h0]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : tens (evI F) f r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [snd_eq_zero hz i, add_zero]
  have hU := hW.1.1.unit μA hμA (γ (Multiplicative.ofAdd t)) (tens (evI F) f r) hS
  have hAct : om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) = tens (evI F) (T t f) r := hA t f r ⟨hr, hS⟩
  change ∫⁻ x, ‖om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) x‖ₑ ^ 2 ∂μA = _ at hU
  rw [hAct] at hU
  have h1 := ((hc (T t f)).symm.trans hU).trans (hc f)
  haveI := opensMeasurable F (Fin n × Fin d)
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, (ENNReal.mul_right_inj hc0 hct).1 h1]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelResidueCharacterPow
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open MeasureTheory
open scoped ENNReal

theorem integral_norm_sq_eq_pair_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ _ T hA μ hμ t f
  obtain ⟨g, hg, hg0⟩ : ∃ g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ,
      g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ g 0 ≠ 0 := by
    refine ⟨_, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _, ?_⟩
    have h0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F (Fin n × Fin d) :=
      fun i _ v => zero_mem (v.adicCompletionIntegers F)
    rw [Set.indicator_of_mem h0]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : tens (evI F) f r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    have h := hz (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F) (by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _)
    have h2 : (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) * ((z i).1, (z i).2)).2 =
        (0 : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 := congrArg Prod.snd (congrFun h i)
    have hz0 : (z i).2 = 0 := by simpa using h2
    rw [hz0, add_zero]
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW).unit μA hμA (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) hS
  have hAct : om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) = tens (evI F) (T t f) r := hA t f r ⟨hr, hS⟩
  change ∫⁻ x, ‖om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) x‖ₑ ^ 2 ∂μA = _ at hU
  rw [hAct] at hU
  have h1 := ((hc (T t f)).symm.trans hU).trans (hc f)
  haveI := opensMeasurable F (Fin n × Fin d)
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, (ENNReal.mul_right_inj hc0 hct).1 h1]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

