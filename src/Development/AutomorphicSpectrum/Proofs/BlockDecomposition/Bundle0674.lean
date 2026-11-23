module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0670
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedDisintegrationComposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorph
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependent
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0659
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0618
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0671
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0581
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0594
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreIntegralEq
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

open Set

theorem setLIntegral_eq_of_vanish {V : Type} [MeasurableSpace V] (μ : Measure V) {O : Set V}
    (hO : MeasurableSet O) (f : V → ℝ≥0∞) (hf : ∀ v, v ∉ O → f v = 0) :
    ∫⁻ v in O, f v ∂μ = ∫⁻ v, f v ∂μ := by
  rw [← lintegral_indicator hO]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ O
  · rw [indicator_of_mem hv]
  · rw [indicator_of_notMem hv, hf v hv]

theorem lintegral_chart_of_continuous {V Vx Va VY : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace Vx] [MeasurableSpace Va] [MeasurableSpace VY]
    (c : Vx → Va → VY → V) (hc : Measurable fun p : Vx × VY × Va => c p.1 p.2.2 p.2.1)
    (μ : Measure V) (μx : Measure Vx) (μY : Measure VY) (μa : Measure Va)
    [SFinite μx] [SFinite μY] [SFinite μa]
    (O cell : Set V) (Ox : Set Vx) (hO : MeasurableSet O) (hOx : MeasurableSet Ox)
    (hcell : IsOpen cell) (hcO : cell ⊆ O)
    (h1 : ∀ᵐ v ∂μ, v ∈ O → v ∈ cell)
    (h2 : ∀ᵐ y ∂μY, ∀ x ∈ Ox, ∀ a, c x a y ∈ cell)
    (h3 : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ cell → (∀ v, 0 ≤ φ v) →
      Integrable φ μ ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂μ =
        ∫⁻ x, ∫⁻ a, ∫⁻ y, ENNReal.ofReal (φ (c x a y)) ∂μY ∂μa ∂μx)
    (h4 : ∀ x a y, x ∉ Ox → c x a y ∉ O)
    (g : V → ℝ≥0∞) (hg : Measurable g) (hgO : ∀ v, v ∉ O → g v = 0) :
    ∫⁻ v, g v ∂μ = ∫⁻ x, ∫⁻ y, ∫⁻ a, g (c x a y) ∂μa ∂μY ∂μx := by
  let f : Vx × VY × Va → V := fun p => c p.1 p.2.2 p.2.1
  let ρ : Measure (Vx × VY × Va) := (μx.restrict Ox).prod (μY.prod μa)
  have hf : Measurable f := hc
  have key : ∀ G : V → ℝ≥0∞, Measurable G → (∀ v, v ∉ O → G v = 0) →
      ∫⁻ v, G v ∂(ρ.map f) = ∫⁻ x, ∫⁻ y, ∫⁻ a, G (c x a y) ∂μa ∂μY ∂μx := by
    intro G hG hG0
    have e : ∀ x, ∫⁻ q, G (f (x, q)) ∂(μY.prod μa) = ∫⁻ y, ∫⁻ a, G (c x a y) ∂μa ∂μY := fun x =>
      lintegral_prod (fun q => G (f (x, q))) ((hG.comp hf).comp measurable_prodMk_left).aemeasurable
    rw [lintegral_map hG hf]
    show ∫⁻ p, G (f p) ∂((μx.restrict Ox).prod (μY.prod μa)) = _
    rw [lintegral_prod (fun p => G (f p)) (hG.comp hf).aemeasurable]
    simp only [e]
    refine setLIntegral_eq_of_vanish μx hOx _ fun x hx => ?_
    have h0 : ∀ y a, G (c x a y) = 0 := fun y a => hG0 _ (h4 x a y hx)
    simp [h0]
  have hmeq : μ.restrict O = ρ.map f := by
    refine GlobalTheory.CompanionTheory.SW.FibreUniq.measure_eq_of_lintegral_eq _ _ cell hcell ?_ ?_ ?_
    · have h : ∀ᵐ v ∂(μ.restrict O), v ∈ cell := (ae_restrict_iff' hO).2 h1
      exact h
    · rw [Measure.map_apply hf hcell.measurableSet.compl]
      have a1 : ∀ᵐ p ∂ρ, p.1 ∈ Ox :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hOx)
      have a2 : ∀ᵐ q ∂(μY.prod μa), ∀ x ∈ Ox, ∀ a, c x a q.1 ∈ cell :=
        Measure.quasiMeasurePreserving_fst.ae h2
      have a3 : ∀ᵐ p ∂ρ, ∀ x ∈ Ox, ∀ a, c x a p.2.1 ∈ cell :=
        Measure.quasiMeasurePreserving_snd.ae a2
      have h : ∀ᵐ p ∂ρ, f p ∈ cell := by
        filter_upwards [a1, a3] with p h h' using h' _ h _
      exact h
    · intro φ hφ hs hsup h0
      obtain ⟨hi, hl⟩ := h3 φ hφ hs hsup h0
      have hm : Measurable fun v => ENNReal.ofReal (φ v) :=
        ENNReal.measurable_ofReal.comp hφ.measurable
      have hv : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := fun v hv => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hv (hcO (hsup h)), ENNReal.ofReal_zero]
      refine ⟨hi.restrict, ?_⟩
      rw [key _ hm hv, setLIntegral_eq_of_vanish μ hO _ hv, hl]
      refine lintegral_congr fun x => ?_
      have hH : Measurable fun q : VY × Va => ENNReal.ofReal (φ (c x q.2 q.1)) :=
        (hm.comp hf).comp measurable_prodMk_left
      exact (lintegral_lintegral_swap hH.aemeasurable).symm
  rw [← key g hg hgO, ← hmeq, setLIntegral_eq_of_vanish μ hO g hgO]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

open Set

theorem stages_zero_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(m 0) = ∫⁻ x, ∫⁻ Y, ∫⁻ a, g (chartS R σ J x a 0 Y) ∂(coordW R b lam 1 n) ∂(m' 0) ∂(m₁ 0) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n d b lam hlam m m₁ m' hm hm₁ hm' g hg hg0
  obtain ⟨hOpen, hLI, hGr, hCh, hmeas⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell.freeCell_props F E σ hCM M J hJ R hR n
  have hOpen0 := (_root_.GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell.freeCell_props F E σ hCM M J hJ R hR 0).1
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, -⟩ := hR'
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 (n + 1) (M + 2)
  haveI := t8 1 (M + 2)
  haveI := t8 1 n
  haveI := t8 n M
  haveI : SigmaFinite (m₁ 0) :=
    GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_free σ hCM (hypOne J) R hR 1 _ _ m₁ hm₁ 0
  haveI : SigmaFinite (m' 0) :=
    GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_free σ hCM J R hR n _ _ m' hm' 0
  haveI : (coordW R b lam 1 n).IsAddHaarMeasure :=
    (_root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam).2.1 1 n
  have hOx : MeasurableSet {x : Fin 1 → Fin (M + 2) → R ⊗[F] E | IsUnit (x 0 0)} := by
    have e : {x : Fin 1 → Fin (M + 2) → R ⊗[F] E | IsUnit (x 0 0)} =
        freeCell (R ⊗[F] E) M 0 := by
      ext x
      exact ⟨fun h => ⟨h, linearIndependent_empty_type⟩, fun h => h.1⟩
    rw [e]
    exact hOpen0.measurableSet
  have hO : MeasurableSet {X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E | IsUnit (X 0 0)} := by
    have hp : Measurable fun (X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) (_ : Fin 1) => X 0 :=
      Measurable.of_eval fun _ => measurable_pi_apply 0
    exact hp hOx
  have hc : Measurable fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) ×
      (Fin 1 → Fin n → R ⊗[F] E) => chartS R σ J p.1 p.2.2 0 p.2.1 :=
    hmeas.comp (measurable_fst.prodMk ((measurable_snd.comp measurable_snd).prodMk
      (measurable_const.prodMk (measurable_fst.comp measurable_snd))))
  have c0 : ∀ᵐ X ∂(m 0), X ∈ (gramR R σ (hypOne J)) ⁻¹' {((0 : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ {X | LinearIndependent (R ⊗[F] E) X} :=
    hm.1 0
  have c1 : ∀ᵐ Y ∂(m' 0), Y ∈ (gramR R σ J) ⁻¹' {((0 : HermR R σ n) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩ {X | LinearIndependent (R ⊗[F] E) X} :=
    hm'.1 0
  refine lintegral_chart_of_continuous (fun x a Y => chartS R σ J x a 0 Y) hc (m 0) (m₁ 0) (m' 0)
    (coordW R b lam 1 n) {X | IsUnit (X 0 0)} (freeCell (R ⊗[F] E) M n)
    {x | IsUnit (x 0 0)} hO hOx hOpen (fun X hX => hX.1) ?_ ?_ ?_ ?_ g hg hg0
  · filter_upwards [c0] with X hX hu
    exact hGr X hX.2 hX.1 hu
  · filter_upwards [c1] with Y hY x hx a
    exact hCh x a 0 Y hx hY.2
  · intro φ hφ hs hsup h0
    exact ⟨(hm.2.2 φ hφ hs (hsup.trans fun X hX => hLI X hX)).1 0 (mem_univ _),
      _root_.GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero F E σ hCM M J hJ R hR n d b lam hlam m m₁ m' hm hm₁ hm' φ hφ hs hsup h0⟩
  · intro x a Y hx h
    exact hx (by simpa [chartS] using h)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d : Mx D n n) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases h1 : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases h2 : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;> rfl

def bT (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) : hermA D n :=
  ⟨bl hn z.1 x (adj x) y.1, by
    show adj (bl hn z.1 x (adj x) y.1 : Mx D n n) = _
    rw [adj_bl, adj_adj]
    have hz : adj z.1 = z.1 := z.2
    have hy : adj y.1 = y.1 := y.2
    rw [hz, hy]⟩

def dsum (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) : HermE D n :=
  ⟨bl hn b₀.1 0 0 β'.1, by
    have h1 := b₀.2
    have h2 := β'.2
    refine Matrix.ext fun i j => ?_
    simp only [bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
    rcases h1' : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
      rcases h2' : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, map_zero]
    · exact congrFun (congrFun h1 i') j'
    · exact congrFun (congrFun h2 i') j'⟩

def cg (a : GL (Fin n) D.host.E) (β : HermE D n) : HermE D n :=
  ⟨(a.1.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * β.1 * a.1, by
    have h : ∀ M : Matrix (Fin n) (Fin n) D.host.E, (M.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = Mᴴ := fun _ => rfl
    have hb : β.1ᴴ = β.1 := β.2
    rw [h, h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hb, Matrix.mul_assoc]⟩

def IsPer (Φ : hermA D n → ℂ) : Prop := ∀ γ ∈ ratHerm D n, ∀ x, Φ (γ + x) = Φ x

def chn (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) : ℂ :=
  ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))

def pm (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ) (y : hermA D p) : ℂ :=
  ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz ∂m.μ

end GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

section Transport
variable {A B : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [T2Space B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem mean_transport (Γ : AddSubgroup A) (Δ : AddSubgroup B) [Countable Γ] [Countable Δ] (T : A ≃ₜ+ B)
    (hT : ∀ a, T a ∈ Δ ↔ a ∈ Γ) (μ : Measure A) (ν : Measure B) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) (hs1 : μ s = 1) (ht1 : ν t = 1)
    (f : B → ℂ) (hf : ∀ γ ∈ Δ, ∀ x, f (γ + x) = f x) :
    ∫ a in s, f (T a) ∂μ = ∫ b in t, f b ∂ν := by
  have hm : Measurable T := T.continuous.measurable
  have hAC : (μ.map T).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ T
  have hAC2 : (ν.map T.symm).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν T.symm
  have hsm : Measure.QuasiMeasurePreserving (T.symm.toAddEquiv.toEquiv) ν μ :=
    ⟨T.symm.continuous.measurable.aemeasurable, Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩
  let eΓ : Δ ≃ Γ :=
    { toFun := fun d => ⟨T.symm d.1, (hT _).1 (by simpa using d.2)⟩
      invFun := fun c => ⟨T c.1, (hT _).2 c.2⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun c => Subtype.ext (by simp) }
  have hFD : IsAddFundamentalDomain Δ (T.toAddEquiv.toEquiv '' s) ν :=
    hs.image_of_equiv T.toAddEquiv.toEquiv hsm eΓ (fun g x => by
      show T (T.symm g.1 + x) = g.1 + T x
      simp)
  have h1 : ν (T.toAddEquiv.toEquiv '' s) = 1 := by rw [hFD.measure_eq ht, ht1]
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have h2 : μ.map T (T.toAddEquiv.toEquiv '' s) = 1 := by
    rw [hemb.map_apply, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective, hs1]
  have h3 : μ.map T = ν := by
    have h4 := Measure.isAddLeftInvariant_eq_smul (μ.map T) ν
    rw [h4] at h2
    have hc : Measure.addHaarScalarFactor (μ.map T) ν = 1 := by
      rw [Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one] at h2
      exact_mod_cast h2
    rw [h4, hc, one_smul]
  have h5 : ∫ a in s, f (T a) ∂μ = ∫ b in T.toAddEquiv.toEquiv '' s, f b ∂ν := by
    rw [← h3, hemb.setIntegral_map, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective]
  rw [h5]
  exact hFD.setIntegral_eq ht (fun g x => hf g.1 g.2 x)
end Transport
end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

def GoodPsi (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D) : Prop :=
  (∀ a ∈ v.adicCompletionIntegers D.host.F, psiV D.host.F ψ v a = 1) ∧
    ∀ ϖ : v.adicCompletionIntegers D.host.F, Irreducible ϖ →
      ∃ b : v.adicCompletionIntegers D.host.F,
        psiV D.host.F ψ v ((b : Fv D.host.F v) / (ϖ : Fv D.host.F v)) ≠ 1

def GoodChi (D : D7) (χ : (AE D)ˣ →* Circle) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Prop :=
  ∀ a : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ,
    ‖splitProj τ (a : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ =
      ‖splitProj (τ.comp D.sp.cm.sig) (a : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ →
    χ (ideleAt D.host.F D.host.E v a) = 1

abbrev sphV (D : D7) (n : ℕ) (v : Pl D) (z : ℂ) : GLoc D.sp.cm.sig (Jst D n) v → ℂ :=
  GlobalTheory.LocIntw.sphUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v)
    (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) z

def GoodPlacesOutsideFiniteSet : Prop :=
  ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ →
    ResEta D χ r → ∀ S : Finset (Pl D), ∃ v ∉ S, GoodPsi D ψ v ∧ ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, GoodChi D χ v τ

def SplitPlaceRankCutEigenvalue : Prop :=
  ∀ (D : D7) (n r t : ℕ), r + t = n → 1 ≤ r → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
    ∀ nb : hermA D n → G D n, IsNMap nb → ∀ v : Pl D, GoodPsi D ψ v → ∀ _ : D.host.E →ₐ[D.host.F] Fv D.host.F v,
    ∃ (C : Cut D n v) (c : ℂ → ℂ), C.Kills ψ r ∧ Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
      ∀ νv : Measure (KAt D n v), νv.IsHaarMeasure → IsProbabilityMeasure νv → ∀ z : ℂ,
        ∫ k : KAt D n v, ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)) ∂νv = c z

def SectionEigenfunctionMaximalCompact : Prop :=
  ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (nb : hermA D n → G D n), IsNMap nb → ∀ (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), GoodChi D χ v τ → ∀ (C : Cut D n v) (νv : Measure (KAt D n v)),
    νv.IsHaarMeasure → ∀ z c : ℂ,
    (∫ k : KAt D n v, ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)) ∂νv = c) →
    ∀ f : G D n → ℂ, IsLaw χ z f → (∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) → ∀ g : G D n,
      ∫ k : KAt D n v, cutR nb C f (g * k) ∂νv = c * f g

end GlobalTheory.CompanionTheory.Jp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ Δ : Segment k, FineJac Δ := by
  intro Δ
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have hp := Δ.len_pos
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · omega
      · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ h
      · exact @_root_.GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two k _ _ _ _ hA hZ Δ h
    · exact @GlobalTheory.T.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem occurs_topCut (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hπ : IsLSeg Δ π) {s : ℕ} (y : Fin s → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (hpos : ∀ a, 0 < (y a).1)
    (h1 : 1 ≤ jm y hd π) :
    ∃ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (_ : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm y hd π ≤ jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π ∧
        ∀ a, IsLSeg (topCut Δ c hc a) (y a).rep := by
  choose c x hx hcusp hemb using fun a =>
    _root_.GlobalTheory.CompanionTheory.SubEmb.subEmbedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  have hjx : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a => by
    obtain ⟨φ, hφ⟩ := hemb a
    have := Model.nontrivial_of_isIrreducible (y a).2.rep.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : (y a).2.rep.V)
    exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth φ
      ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩
  have hcat0 : ∑ i, (concat c x i).1 = N := by
    rw [sum_concat, ← hd]
    exact Finset.sum_congr rfl fun a _ => hx a
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hd c x hx hcat0 hjx π hsm (hasFiniteLength_of_isIrreducible hirr)
  have h1' : 1 ≤ jm (concat c x) hcat0 π := h1.trans hle
  obtain ⟨hl, hfine⟩ := (fineJac_all hA hZ Δ π hπ).2 _ (concat c x) hcat0 (fun i => hcusp _ _) h1'
  have hc : ∀ a, 0 < c a := fun a => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; infer_instance
    have := hx a
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact (hpos a).ne this
  have hxeq : x = fun a => dec (topCut Δ c hc a) :=
    concat_injective (funext fun i => (hfine i).trans (concat_dec_topCut Δ c hc hl i).symm)
  subst hxeq
  refine ⟨c, hc, hl, hcat0, hle, fun a => ?_⟩
  obtain ⟨φ, hφ⟩ := hemb a
  exact _root_.GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec hA hZ (topCut Δ c hc a) (hx a) (y a).rep (y a).2.rep.smooth (y a).2.rep.irr φ hφ

theorem lSegJacquet : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ s y hd hpos
  have hdΔ : ∑ a, (dec Δ a).1 = N := (sum_dec Δ).trans hπ.deg_eq
  have hone := (fineJac_all hA hZ Δ π hπ).1 hdΔ
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth

  have hread : ∀ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (hl : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π = 1 := fun c hc hl hcat =>
    (jm_reindex hl _ _ (concat_dec_topCut Δ c hc hl) hcat hdΔ π).trans hone
  have hB : 1 ≤ jm y hd π → ∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep := fun h1 => by
    obtain ⟨c, hc, hl, -, -, hL⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos h1
    exact ⟨topCut Δ c hc, isTopCut_topCut Δ c hc hl, hL⟩
  have hC : jm y hd π ≤ 1 := by
    by_cases h0 : jm y hd π = 0
    · rw [h0]; exact zero_le_one
    · obtain ⟨c, hc, hl, hcat, hle, -⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos (ENat.one_le_iff_ne_zero.2 h0)
      exact hle.trans (hread c hc hl hcat).le
  have hD : (∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep) → 1 ≤ jm y hd π := by
    rintro ⟨Γ, hΓ, hL⟩
    have hΓe := eq_topCut hΓ
    set c : Fin s → ℕ := fun a => (Γ a).len with hcdef
    have hc : ∀ a, 0 < c a := fun a => (Γ a).len_pos
    have hl : ∑ a, c a = Δ.len := hΓ.1
    have hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N :=
      (Fintype.sum_equiv (finCongr hl) _ _ fun i => by rw [concat_dec_topCut Δ c hc hl]; rfl).trans hdΔ
    have hxpos : ∀ a, 0 < ∑ i, (dec (topCut Δ c hc a) i).1 := fun a => by
      rw [sum_dec, deg_topCut]; exact Nat.mul_pos (hc a) Δ.d_pos
    obtain ⟨σ, hσ, hσd, h1σ⟩ := GlobalTheory.T.concatenated_jacquet_multiplicity_factorization hA c (fun a => dec (topCut Δ c hc a)) hxpos hcat π hsm
      (hasFiniteLength_of_isIrreducible hirr) (hread c hc hl hcat).ge
    have hσpos : ∀ a, 0 < (σ a).1 := fun a => (hσd a).symm ▸ hxpos a
    obtain ⟨c', hc', hl', -, -, hL'⟩ := occurs_topCut hA hZ Δ π hπ σ hσ hσpos h1σ
    have hsd : ∀ a, ∑ i : Fin (c a), (dec (topCut Δ c hc a) i).1 = c a * Δ.d := fun a =>
      (sum_dec _).trans (deg_topCut Δ c hc a)
    have hcc : c' = c := funext fun a => by
      have e1 := (hL' a).deg_eq
      rw [deg_topCut, hσd a, hsd a] at e1
      exact Nat.eq_of_mul_eq_mul_right Δ.d_pos e1
    subst hcc
    have hσy : σ = y := funext fun a => by
      have h2 : IsLSeg (topCut Δ c hc' a) (y a).rep := by
        have := hL a
        rw [hΓe] at this
        exact this
      exact eq_of_isLSeg (hL' a) h2
    subst hσy
    exact h1σ
  refine ⟨fun h => le_antisymm hC (hD h), fun h => ?_⟩
  by_contra h0
  exact h (hB (ENat.one_le_iff_ne_zero.2 h0))

end GlobalTheory.CompanionTheory.SegCoarse

end
end

