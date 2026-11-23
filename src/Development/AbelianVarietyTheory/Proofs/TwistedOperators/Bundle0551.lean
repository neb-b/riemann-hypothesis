module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.XLastLin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesUnitaryAbsolutelyConvergentModerat
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicModelInvariantSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg

def tensDeg (F : Type) [Field F] [NumberField F] (P Q R S D : ℕ) : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S) :=
  LinearMap.range (PiTensorProduct.map fun _ : InfinitePlace F =>
    (MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D).subtype)

theorem tensDeg_mono {F : Type} [Field F] [NumberField F] {P Q R S D D' : ℕ} (h : D ≤ D') :
    tensDeg F P Q R S D ≤ tensDeg F P Q R S D' := by
  have hi : MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D ≤
      MvPolynomial.restrictTotalDegree _ ℂ D' := fun x hx => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hx ⊢; omega
  rintro _ ⟨t, rfl⟩
  refine ⟨PiTensorProduct.map (fun _ => Submodule.inclusion hi) t, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rfl

theorem exists_tensDeg {F : Type} [Field F] [NumberField F] {P Q R S : ℕ} (T : GlobalTheory.RealLift.Tens F P Q R S) :
    ∃ D, T ∈ tensDeg F P Q R S D := by
  classical
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨Finset.univ.sup fun w => (m w).totalDegree, r • PiTensorProduct.tprod ℂ (fun w =>
      (⟨m w, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (Finset.le_sup (f := fun w => (m w).totalDegree)
        (Finset.mem_univ w))⟩ : MvPolynomial.restrictTotalDegree _ ℂ _)), ?_⟩
    simp [PiTensorProduct.map_tprod]
  | add x y hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    exact ⟨max D₁ D₂, Submodule.add_mem _ (tensDeg_mono (le_max_left _ _) h₁) (tensDeg_mono (le_max_right _ _) h₂)⟩

theorem exp_stable {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : GlobalTheory.RealLift.IsExp L U)
    (N : Submodule ℂ V) (hN : ∀ y ∈ N, L y ∈ N) : ∀ y ∈ N, U y ∈ N := by
  intro y hy
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
  have hpow : ∀ m : ℕ, (L ^ m) y ∈ N := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih
  have hz : ∀ m : ℕ, ((m.factorial : ℂ))⁻¹ * l ((L ^ m) y) = 0 := fun m => by
    have hm : l ((L ^ m) y) ∈ N.map l := Submodule.mem_map_of_mem (hpow m)
    rw [hl2, Submodule.mem_bot] at hm
    rw [hm, mul_zero]
  have h1 := hU y l
  simp only [hz] at h1
  exact hl1 (h1.unique hasSum_zero)

def pureL {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.SquareAgree.KFinAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedFunctionConvergesContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.JacMean

theorem handP_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ B.L Φ₀ →
    IsThetaFunO ψ J.W B.V Φ →
    (∃ (C : ℝ) (a : ℕ), ∀ h h₁, ‖handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁‖ ≤ C * (quotHeight B.A h₁ * height B.V h) ^ a) ∧
    Continuous fun q : GA D B.V × GA D B.A => handP s vL omz φ Φ₀ (flFB s (s.om (1, q.1) Φ)) q.2 := by
  intro D ψ σ J B s vL χ χz omz homz φ Φ₀ Φ hφ hΦ₀ hΦ
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  have hfin : J.v0.μ J.v0.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨K, hK⟩ : ∃ K : GA D B.V → GA D J.W₀ → GA D B.A → ℂ, K = fun h h₀ h₁ => contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := ⟨_, rfl⟩
  have hKc : Continuous fun q : GA D B.V × GA D J.W₀ × GA D B.A => K q.1 q.2.1 q.2.2 := by
    subst hK; exact _root_.GlobalTheory.KerContFB.kerFB_continuous D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨C, a, hKp⟩ : ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖K h h₀ h₁‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
    subst hK; exact _root_.GlobalTheory.PairKerBound.kernel_bound D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  have hKi : ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, K h (γ * h₀) h₁ = K h h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, K h h₀ (γ * h₁) = K h h₀ h₁ := by
    subst hK; exact _root_.GlobalTheory.KerRat.flat_kernel_rat D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  have hKq : ∀ h h₀ h₁, ‖K h h₀ h₁‖ ≤ |C| * 4 ^ a * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) ^ a := by
    intro h h₀ h₁
    obtain ⟨γ, hγ, e1⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight J.W₀ h₀
    obtain ⟨δ, hδ, e2⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight B.A h₁
    have k1 : K h h₀ h₁ = K h (γ * h₀) (δ * h₁) := by
      rw [(hKi h).2 δ hδ (γ * h₀) h₁, (hKi h).1 γ hγ h₀ h₁]
    rw [k1]
    have p1 := height_pos J.W₀ (γ * h₀)
    have p2 := height_pos B.A (δ * h₁)
    have p3 := height_pos B.V h
    have q0 := quotHeight_pos J.W₀ h₀
    have q1 := quotHeight_pos B.A h₁
    calc ‖K h (γ * h₀) (δ * h₁)‖ ≤ C * (height J.W₀ (γ * h₀) * height B.A (δ * h₁) * height B.V h) ^ a := hKp _ _ _
      _ ≤ |C| * ((2 * quotHeight J.W₀ h₀) * (2 * quotHeight B.A h₁) * height B.V h) ^ a :=
          mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (mul_pos (mul_pos p1 p2) p3).le
            (mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 p2.le (by linarith)) p3.le) a)
            (pow_pos (mul_pos (mul_pos (by linarith) (by linarith)) p3) a).le (abs_nonneg C)
      _ = _ := by
          rw [show 2 * quotHeight J.W₀ h₀ * (2 * quotHeight B.A h₁) * height B.V h =
            4 * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) by ring, mul_pow]; ring
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Grow.RapidDec.decay hφ a
  have hpt : ∀ h h₀ h₁, ‖φ h₀ * K h h₀ h₁‖ ≤ |Cφ| * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a := by
    intro h h₀ h₁
    rw [norm_mul]
    calc ‖φ h₀‖ * ‖K h h₀ h₁‖ ≤ ‖φ h₀‖ * (|C| * 4 ^ a * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) ^ a) :=
          mul_le_mul_of_nonneg_left (hKq h h₀ h₁) (norm_nonneg _)
      _ = (‖φ h₀‖ * quotHeight J.W₀ h₀ ^ a) * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a := by
          rw [mul_pow]; ring
      _ ≤ |Cφ| * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((hCφ h₀).trans (le_abs_self _)) (by positivity))
            (pow_pos (mul_pos (quotHeight_pos B.A h₁) (height_pos B.V h)) a).le
  have hPeq : ∀ h h₁, handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁ = ∫ h₀ in J.v0.𝓕, φ h₀ * K h h₀ h₁ ∂J.v0.μ := by
    subst hK; intro _ _; rfl
  refine ⟨⟨|Cφ| * (|C| * 4 ^ a) * (J.v0.μ J.v0.𝓕).toReal, a, fun h h₁ => ?_⟩, ?_⟩
  · rw [hPeq]
    have := norm_setIntegral_le_of_norm_le_const hfin fun h₀ _ => hpt h h₀ h₁
    refine this.trans (le_of_eq ?_)
    simp only [Measure.real]
    ring
  · have hmeas : ∀ q : GA D B.V × GA D B.A, AEStronglyMeasurable (fun h₀ => φ h₀ * K q.1 h₀ q.2) (J.v0.μ.restrict J.v0.𝓕) :=
      fun q => (hφ.continuous.mul (hKc.comp ((continuous_const.prodMk (continuous_id.prodMk continuous_const))))).aestronglyMeasurable
    have hc2 : Continuous fun q : GA D B.V × GA D B.A => (height B.A q.2 * height B.V q.1) ^ a :=
      (((continuous_height B.A).comp continuous_snd).mul ((continuous_height B.V).comp continuous_fst)).pow a
    refine (continuous_congr fun q : GA D B.V × GA D B.A => hPeq q.1 q.2).2 ?_
    refine continuous_iff_continuousAt.2 fun q₀ => ?_
    refine continuousAt_of_dominated (bound := fun _ => |Cφ| * (|C| * 4 ^ a) * ((height B.A q₀.2 * height B.V q₀.1) ^ a + 1))
      (.of_forall hmeas) ?_ (integrable_const _) ?_
    · filter_upwards [hc2.continuousAt.eventually (gt_mem_nhds (lt_add_one _))] with q hq
      refine .of_forall fun h₀ => (hpt q.1 h₀ q.2).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact (pow_le_pow_left₀ (mul_pos (quotHeight_pos B.A q.2) (height_pos B.V q.1)).le
        (mul_le_mul_of_nonneg_right (quotHeight_le_height B.A q.2) (height_pos B.V q.1).le) a).trans hq.le
    · exact .of_forall fun h₀ => (continuous_const.mul (hKc.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))).continuousAt

theorem conclusion₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), RapidDec J.W₀ φ → RapidDec B.V G → IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → (∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 (besFun ψ 1 B.d B.o B.ζ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G))) ∧ Continuous fun h => B.per ψ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G) := by
  intro D ψ σ J B s vL χ χz omz homz φ G Φ₀ Φ hφ hG hΦ₀ hΦ
  have hψ := homz.std
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund).ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
  obtain ⟨⟨C, a, hP⟩, hPc⟩ := GlobalTheory.JacMean.handP_law D ψ σ J B s vL χ χz omz homz φ Φ₀ Φ hφ hΦ₀ hΦ
  set P : GA D B.V → GA D B.A → ℂ := fun h h₁ => handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁ with hPdef
  obtain ⟨C1, a1, h1⟩ := _root_.GlobalTheory.HtWitt.quotHeight_witt D B.V B.V₀ σ B.d
  obtain ⟨C2, a2, h2⟩ := _root_.GlobalTheory.HtOrth.quotHeight_orthDec_cmp D B.V₀ B.A B.L B.o
  obtain ⟨C3, h3⟩ := (GlobalTheory.RTransDecay.rapidDec_rTrans D B.V G hG).2 (a1 * a2 * a)

  set bd : GA D B.V → ℝ := fun h => |C| * height B.V h ^ a * ((|C2| * |C1| ^ a2) ^ a * (|C3| * height B.V h ^ (a1 * a2 * a))) with hbd
  have hbound : ∀ h (h₁ : GA D B.A) (n : flagN B.d), ‖besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G) h₁ n‖ ≤ bd h := by
    intro h h₁ n
    have hg := h1 n.1 n.2 (B.o.emb (h₁, 1))
    have hq := (h2 h₁).1
    set g : GA D B.V := n.1 * embA B.d B.o h₁ with hgdef
    have hge : n.1 * B.d.emb0 (B.o.emb (h₁, 1)) = g := rfl
    rw [hge] at hg
    have q0 := quotHeight_pos B.V₀ (B.o.emb (h₁, 1))
    have qg := quotHeight_pos B.V g
    have qa := quotHeight_pos B.A h₁
    have ht := height_pos B.V h
    have hA : quotHeight B.A h₁ ≤ |C2| * |C1| ^ a2 * quotHeight B.V g ^ (a1 * a2) := by
      calc quotHeight B.A h₁ ≤ C2 * quotHeight B.V₀ (B.o.emb (h₁, 1)) ^ a2 := hq
        _ ≤ |C2| * (|C1| * quotHeight B.V g ^ a1) ^ a2 :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ q0.le (hg.1.trans
              (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos qg a1).le)) _) (pow_pos q0 a2).le (abs_nonneg _)
        _ = _ := by rw [mul_pow, ← pow_mul]; ring
    have hGg := h3 g h
    have hPb := hP h h₁
    have hnpsi : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) n.1‖ = 1 := hψ.1.2.1 _
    have e1 : ‖besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G) h₁ n‖ = ‖P h h₁‖ * ‖G (g * h)‖ := by
      simp only [besFun, rTrans, norm_mul, norm_star, hnpsi, mul_one]; rfl
    rw [e1]
    calc ‖P h h₁‖ * ‖G (g * h)‖ ≤ (|C| * (quotHeight B.A h₁ * height B.V h) ^ a) * ‖G (g * h)‖ :=
          mul_le_mul_of_nonneg_right (hPb.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_pos (mul_pos qa ht) a).le)) (norm_nonneg _)
      _ ≤ (|C| * ((|C2| * |C1| ^ a2 * quotHeight B.V g ^ (a1 * a2)) * height B.V h) ^ a) * ‖G (g * h)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos qa ht).le
            (mul_le_mul_of_nonneg_right hA ht.le) a) (abs_nonneg C)) (norm_nonneg _)
      _ = |C| * height B.V h ^ a * ((|C2| * |C1| ^ a2) ^ a * (‖G (g * h)‖ * quotHeight B.V g ^ (a1 * a2 * a))) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring
      _ ≤ bd h :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGg.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_pos ht _).le)) (by positivity)) (mul_nonneg (abs_nonneg _) (pow_pos ht a).le)
  have hcont : Continuous fun q : GA D B.V × (GA D B.A × flagN B.d) => besFun ψ 1 B.d B.o B.ζ (P q.1) (rTrans q.1 G) q.2.1 q.2.2 := by
    have hn : Continuous fun q : GA D B.V × (GA D B.A × flagN B.d) => (q.2.2 : GA D B.V) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact ((hPc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
      (hG.continuous.comp ((hn.mul (B.d.continuous_embed.comp (B.o.continuous_emb.comp ((continuous_fst.comp continuous_snd).prodMk continuous_const)))).mul continuous_fst))).mul
      (continuous_star.comp ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 _).comp hn))
  have hint : ∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 (besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G)) := by
    intro h
    refine Integrable.of_bound ?_ (bd h) (.of_forall fun p => hbound h p.1 p.2)
    exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  refine ⟨hint, ?_⟩
  have heq : ∀ h, B.per ψ (P h) (rTrans h G) = ∫ p, Function.uncurry (besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G)) p
      ∂((B.vA.μ.restrict B.vA.𝓕).prod (B.vN.ν.restrict B.vN.𝓝)) := fun h => by
    rw [integral_prod _ (hint h)]; rfl
  refine (continuous_congr heq).2 ?_
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  have hbc : Continuous bd := by
    exact (continuous_const.mul ((continuous_height B.V).pow a)).mul (continuous_const.mul (continuous_const.mul ((continuous_height B.V).pow _)))
  refine continuousAt_of_dominated (bound := fun _ => bd h₀ + 1) ?_ ?_ (integrable_const _) ?_
  · exact .of_forall fun h => (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hbc.continuousAt.eventually (gt_mem_nhds (lt_add_one (bd h₀)))] with h hh
    exact .of_forall fun p => (hbound h p.1 p.2).trans hh.le
  · exact .of_forall fun p => (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt

end GlobalTheory.JacMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesSummableMajorant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory

theorem poincare_sum_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) → (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) → (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V, Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A := by
  intro D θ hθ V Λ hΛ 𝔪 c
  obtain ⟨C₀, A, hC⟩ := _root_.GlobalTheory.PoinCount.poincare_count D θ hθ V Λ hΛ c
  refine ⟨C₀, A, fun u C hu hsupp hle g => ?_⟩
  have hP : ∀ x : GA D V, 0 < ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x =>
    Finset.prod_pos fun τ _ => inv_pos.2 (pow_pos (add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)) _)
  have hC0 : 0 ≤ C := by
    by_contra h
    push_neg at h
    have := hle 1
    have := hu 1
    have := mul_neg_of_neg_of_pos h (hP 1)
    linarith
  have hs : ∀ s : Finset (GQ V), ∑ γ ∈ s, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A := by
    intro s
    classical
    set t := s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ 𝔪) with ht
    have h1 : ∑ γ ∈ s, u (c * (γ : GA D V) * g) = ∑ γ ∈ t, u (c * (γ : GA D V) * g) := by
      rw [ht, Finset.sum_filter]
      refine Finset.sum_congr rfl fun γ _ => ?_
      split_ifs with h
      · rfl
      · exact hsupp _ h
    have h2 : ∑ γ ∈ t, u (c * (γ : GA D V) * g) ≤
        C * ∑ γ ∈ t, ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * g))) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun γ _ => hle _
    have h3 := hC g t (fun γ hγ => congLev_mono le_top (Finset.mem_filter.1 hγ).2)
    rw [h1, mul_assoc]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hC0)
  have hsum : Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) :=
    summable_of_sum_le (fun γ => hu _) hs
  exact ⟨hsum, hsum.tsum_le_of_sum_le hs⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSetSumApproximation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnTypeApprox

theorem norm_sub_sum_sum_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ q, J k q‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ k, ∑ q, J k q‖ < δ := by
  have hd : I - ∑ k, ∑ q, J k q = (I - ∑ k, L k) + ∑ k, (L k - ∑ q, J k q) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hd]
  have h3 : ‖∑ k, (L k - ∑ q, J k q)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ q, J k q‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ q, J k q)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ q, J k q)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

end GlobalTheory.DnTypeApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteElementConjRowLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SeeConj.exists_conj_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp _hMod
  obtain ⟨ψ0, hψ0, _hψ, π, _hπ, hmem, hchi⟩ := hGrp.levels
  obtain ⟨β₃, hfr₃, hD1⟩ := _root_.GlobalTheory.SeeConj.exists_frame_symLevel R F X h hIs hGrp ψ0 hψ0
  obtain ⟨β₂, hfr₂, hD2⟩ := _root_.GlobalTheory.SeeConjReord.exists_frame_reord R.toLevCh (R.levR F true) (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0) π hmem hchi β₃ hfr₃
  obtain ⟨t₀, ht₀, hfr₀⟩ := _root_.GlobalTheory.SelfDualFrameConj.frame_conj (Yc D 0) (R.βY 0) (R.ΛY 0) _ (hIs.βY 0 (by have := D.R.two_le_m; omega))
  obtain ⟨u, hu, hfru, hred⟩ := GlobalTheory.T.exists_unitary_matching_frames_at_nonconjugate_places (Yc D 0) R.Pg (GlobalTheory.T.levelPlaces_not_isConjPlace_realDat R F hIs hGrp) _ β₂ hfr₀ hfr₂
  have hfe : finE (Yc D 0) (u * t₀) * R.βY 0 = finE (Yc D 0) u * (finE (Yc D 0) t₀ * R.βY 0) := by
    rw [map_mul, mul_assoc]
  refine ⟨u * t₀, mul_mem hu ht₀, ?_, by rw [hfe]; exact hfru⟩
  intro (k : GA D (Yc D 0))
  have hA := _root_.GlobalTheory.FrameConj.levS_conj_frame (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (u * t₀) (mul_mem hu ht₀) k
  rw [hfe] at hA
  have hC := _root_.GlobalTheory.levS_levChi_of_frames (Yc D 0) (finE (Yc D 0) u * (finE (Yc D 0) t₀ * R.βY 0)) β₂ _ (R.dat0 (R.levR F true)) hfru hfr₂
    (fun PP hPP x => hred PP hPP x) (fun PP hPP => absurd hPP (Finset.notMem_empty _)) ((u * t₀) * k * (u * t₀)⁻¹)
  have h2 := hD2 ((u * t₀) * k * (u * t₀)⁻¹)
  have h1 := hD1 ((u * t₀) * k * (u * t₀)⁻¹)
  have hm : ∀ hk : k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), (u * t₀) * k * (u * t₀)⁻¹ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) :=
    fun hk => h2.1.1 (hC.1.1 (hA.1.1 hk))
  have key : (k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) ↔ (u * t₀) * k * (u * t₀)⁻¹ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) ∧
      (k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) → star (X.chi2 ((iotaX X h).toMulEquiv ((u * t₀) * k * (u * t₀)⁻¹)).2) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k) :=
    ⟨hA.1.trans (hC.1.trans (h2.1.trans h1.1.symm)), fun hk => by rw [h1.2 (hm hk), ← h2.2, ← hC.2, hA.2]⟩
  have e : ((u * t₀)⁻¹⁻¹ : GA D (D.sp.Y 0)) = u * t₀ := inv_inv (G := GA D (D.sp.Y 0)) _
  rw [e]
  exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGaussianVacuumProductUnitVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipVac

theorem exists_gauss_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) := by
  intro D T L sc G μ₀ hL W ρ t i j M _ e Bs Γ X om om' h hT hti
  have h₁ := ρ.vX_is i (j + 1) i.2 j.2
  have h₂ := ρ.vT_is t (i + 1) j i.2 j.2
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨f, hf⟩ := GlobalTheory.BigDat.exists_vac hL h hT hti h₁ h₂
  refine ⟨f, fun h0 => ?_, GlobalTheory.BigDat.isGauss (c := 1) h hT h₁ h₂ (by rw [hf, one_smul]),
    (isFinPart_vac hG ∅).fam.mem hG f, fun u => ?_⟩
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (GlobalTheory.BigDat.vac_ne_zero h₁)
    obtain ⟨y, hy⟩ := Function.ne_iff.1 (GlobalTheory.BigDat.vac_ne_zero h₂)
    have := congrFun hf (GlobalTheory.BigDat.ofMaps e (x, y))
    rw [h0, show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf D.host.F (GlobalTheory.BigDat.Ix G i j)) Γ.M.vac =
        (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure 0 Γ.M.vac from funext fun _ => (zero_mul _).trans (zero_mul _).symm,
      GlobalTheory.BigDat.thetaPt_smul, zero_mul, GlobalTheory.BigDat.box, GlobalTheory.BigDat.mapV_ofMaps, GlobalTheory.BigDat.mapW_ofMaps] at this
    exact mul_ne_zero hx hy this.symm
  · refine (congrFun hf u).trans ?_
    first
    | exact (one_mul _).symm.trans (Finsupp.sum_single_index (h := fun d (c : ℂ) => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e d u) (zero_mul _)).symm
    | (erw [Finsupp.sum_single_index (by exact zero_mul _), one_mul]; rfl)
    | (simp only [Finsupp.sum_single_index, zero_mul, one_mul]; rfl)

end GlobalTheory.FlipVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesPolynomialVectorsSmallPairStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDuality_realPlaces_polynomialVectors_smallPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V', ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V' Bs.emb, ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om' (k, 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    Module.rank ℂ ↥(G.M'.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N → (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype), g x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) := by
  first | exact @GlobalTheory.HoweGlobalPair.RealPlaceSmall.realTransfer' | exact GlobalTheory.HoweGlobalPair.RealPlaceSmall.realTransfer' | (intros; apply GlobalTheory.HoweGlobalPair.RealPlaceSmall.realTransfer' <;> assumption)
end

