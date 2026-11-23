module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianFourierSelfDualAdelic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalProductGramFiberRankOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceFormRationalThetaIdentity
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinates
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0051
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0033

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
open GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.EulerDens

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.EstZero

attribute [local instance] GlobalTheory.CompanionTheory.SW.EulerDens.instLCv GlobalTheory.CompanionTheory.SW.EulerDens.instSCv GlobalTheory.CompanionTheory.SW.EulerDens.instBorv
  GlobalTheory.CompanionTheory.SW.EulerDens.instBorf GlobalTheory.CompanionTheory.SW.EulerDens.instLCf GlobalTheory.CompanionTheory.SW.EulerDens.instSCf

theorem hasProd_free_mass_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ a : ℕ, 0 < a → ∀ D : Af F → ℝ, Continuous D → (∀ y, 0 ≤ D y) → (∀ U : Set (Af F), MeasurableSet U → coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (D y) ∂lf) → HasProd (fun v => (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal) (D 0) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM h₀ d b lam hlam m hm lf hlf hlf1 a ha D hDc hD0 hUD
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hUD' : ∀ U : Set (Af F), MeasurableSet U →
      coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ sA b v a) ∧ qF (Af F) σ J X ∈ U} =
        ∫⁻ y in U, ENNReal.ofReal (D y) ∂lf := hUD
  rw [HasProd, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hWn : {y : Af F | |D y - D 0| < ε / 3} ∈ 𝓝 (0 : Af F) :=
    (isOpen_lt (hDc.sub continuous_const).abs continuous_const).mem_nhds (by simpa using hε3)
  obtain ⟨S₀, N, hN, hNoff, hNW⟩ := exists_box F _ hWn
  have hev := (q_int_ev (M := M) b σ J).and (scale_ev (M := M) b ha)
  have hbad := Filter.eventually_cofinite.1 hev
  refine ⟨S₀ ∪ hbad.toFinset, fun S hS => ?_⟩
  have hS' : ∀ v, v ∉ S → v ∉ S₀ ∧ ((∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ latV b v →
        qF (Fv F v) σ J X ∈ v.adicCompletionIntegers F) ∧
      ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ sA b v a ↔ X ∈ latV b v) := fun v hv => by
    refine ⟨fun h => hv (hS (Finset.mem_union_left _ h)), ?_⟩
    by_contra hc
    exact hv (hS (Finset.mem_union_right _ (hbad.mem_toFinset.2 hc)))
  obtain ⟨δ, hδ, hclose⟩ := prod_close S
    (fun v => (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (sA b v a)).toReal) hε3
  have hloc := fun v => (_root_.GlobalTheory.CompanionTheory.SW.AvgZero.avg_zero F E σ hcm M J hJ hM h₀ d b v (lam v) (hlam v) (m v) (hm v)
    (sA b v a) (sA_cpt_open σ hcm b v ha).1 (sA_cpt_open σ hcm b v ha).2).2 δ hδ
  choose Uv hUv hUv' using hloc
  have hVex := fun v => nice_nbhd (hlam v) (Filter.inter_mem (hUv v) (hN v))
  choose V hVo hVs hVpos hVfin using hVex
  have hUW : ∀ y ∈ box S V, |D y - D 0| ≤ ε / 3 := fun y hy => by
    refine le_of_lt (hNW y fun v => ?_)
    by_cases hv : v ∈ S
    · exact (hVs v (hy.1 v hv)).2
    · rw [hNoff v (hS' v hv).1]
      exact hy.2 v hv
  have hBo := box_open S V hVo
  have hL := box_meas lam hlam lf hlf hlf1 S V hVo
  have hP := box_tuple σ hcm J b lam hlam lf hlf hlf1 ha S V hVo (fun v hv => (hS' v hv).2.2)
    (fun v hv => (hS' v hv).2.1)
  rw [hUD' _ hBo.measurableSet] at hP
  have hLv : ∀ v, 0 < (lam v (V v)).toReal := fun v =>
    ENNReal.toReal_pos (hVpos v).ne' (hVfin v).ne
  have hLf : (lf (box S V)).toReal = ∏ v ∈ S, (lam v (V v)).toReal := by
    rw [hL, ENNReal.toReal_prod]
  have hLfpos : 0 < (lf (box S V)).toReal := by
    rw [hLf]
    exact Finset.prod_pos fun v _ => hLv v
  have hfin : lf (box S V) ≠ ∞ := by
    rw [hL]
    exact ENNReal.prod_ne_top fun v _ => (hVfin v).ne
  have hI : (∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal =
      ∏ v ∈ S, (coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal := by
    rw [hP, ENNReal.toReal_prod]
  have havg := avg_bound lf hBo.measurableSet hfin D (hD0 _) hε3.le hUW
  have hcl := hclose (fun v =>
    (coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal /
      (lam v (V v)).toReal) (fun v _ => by
    have h1 := hUv' v (V v) (hVo v).measurableSet (fun y hy => (hVs v hy).1)
    have h2 : (coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal /
        (lam v (V v)).toReal - (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (sA b v a)).toReal =
        ((coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal -
          (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (sA b v a)).toReal * (lam v (V v)).toReal) /
          (lam v (V v)).toReal := by
      have := (hLv v).ne'
      field_simp
    show |_ - _| ≤ δ
    rw [h2, abs_div, abs_of_pos (hLv v), div_le_iff₀ (hLv v)]
    exact h1)
  rw [Finset.prod_div_distrib, ← hI, ← hLf] at hcl
  have h3 : |(∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal / (lf (box S V)).toReal -
      D 0| ≤ ε / 3 := by
    have h4 : (∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal / (lf (box S V)).toReal -
        D 0 = ((∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal -
          D 0 * (lf (box S V)).toReal) / (lf (box S V)).toReal := by
      have := hLfpos.ne'
      field_simp
    rw [h4, abs_div, abs_of_pos hLfpos, div_le_iff₀ hLfpos]
    exact havg
  change dist (∏ v ∈ S, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (sA b v a)).toReal) _ < ε
  rw [Real.dist_eq]
  have h5 := abs_le.1 hcl
  have h6 := abs_le.1 h3
  rw [abs_lt]
  constructor <;> linarith

theorem ofF_mem_framesE_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2))
    (x : Fin M × Fin d → F) :
    ofF b x ∈ framesE σ J (0 : Matrix (Fin 1) (Fin 1) E) ↔
      x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0 := by
  obtain ⟨-, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff F E σ hσ M J hJ d b
  have hg : gramE σ J (ofF b x) = (0 : Matrix (Fin 1) (Fin 1) E) ↔
      (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0 := by
    rw [← h3 B hB 0 x]
    simp only [map_zero]
    rfl
  have hl : LinearIndependent E (ofF b x : Fin 1 → Fin M → E) ↔ x ≠ 0 := by
    rw [linearIndependent_unique_iff, ← h2 x]
    constructor
    · intro h h0
      exact h (congrFun h0 _)
    · intro h h0
      exact h (funext fun i => by rw [Subsingleton.elim i default]; exact h0)
  exact and_congr hl hg

theorem lintegral_thetaMeas_gauss_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (a : ℕ), 0 < a → ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (gaussQ e b Pm (projInf X)) ∂(thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) = ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0}, Set.indicator {x : Fin M × Fin d → F | ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b B hB ρ e hom hρ Pm μ 𝓕 hμ h𝓕 a ha
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨hR, -, -, -, -, -, -, hBor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hBor 1 M
  have hA := _root_.GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int F E σ hσ d M b a
  have hproj : Continuous (projInf : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    (_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 M).1
  have hG : Continuous fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
      ENNReal.ofReal (gaussQ e b Pm (projInf X)) :=
    ENNReal.continuous_ofReal.comp
      ((GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.continuous_gaussQ σ hσ b e hom Pm).comp hproj)
  rw [← lintegral_indicator hA]
  rw [_root_.GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord F E σ hσ M J hJ d b μ 𝓕 hμ h𝓕
    {x | x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0}
    (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))
    (fun x => ofF_mem_framesE_zero σ hσ J hJ b B hB x) _
    (hG.measurable.indicator hA)]
  refine lintegral_congr fun ω => tsum_congr fun x => ?_
  obtain ⟨hinf, hfin⟩ := _root_.GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup F E σ hσ M J hJ d b ρ e hρ ω x.1
  have hmem := _root_.GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff F E d M b a (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))))
  rw [hfin] at hmem
  have hgauss : gaussQ e b Pm (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1)))) =
      Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)) ⬝ᵥ
        (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)))) := by
    simp only [gaussQ, hinf]
  by_cases hx : ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x.1 j)) i) v ∈
      v.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (by exact hmem.2 hx), Set.indicator_of_mem (by exact hx), hgauss]
  · rw [Set.indicator_of_notMem, Set.indicator_of_notMem]
    all_goals first | exact hx | exact fun h => hx (hmem.1 h)

theorem estimate_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∃ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) (C : ℝ), Continuous φ ∧ (∀ X, 0 < φ X) ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) < ⊤ ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (φ (projInf X)) ∂(thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) = (I : ℝ≥0∞) ∧ |(I : ℝ) - (∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))).toReal * ∏' v, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM h₀ d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf hminf m hm
  obtain ⟨hF, hEc, hfin, hconj⟩ := id hCM
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis b
    simpa [hfin] using h.symm
  obtain ⟨B, hBs, hBd, hBE, hBR⟩ := _root_.GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ d b
  obtain ⟨ρ, e, hρ, he, heρ, hen, hem⟩ := _root_.GlobalTheory.CompanionTheory.SW.real_iso F hF
  have hP : ∀ w, ∃ P : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ,
      P.PosDef ∧ P * (B.map (ρ w))⁻¹ * P = B.map (ρ w) := by
    intro w
    refine _root_.GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm _ _ ?_ ?_
    · exact hBs.map _
    · have h := RingHom.map_det (ρ w) B
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero _).2 hBd
  choose Pm hPd hPm using hP
  obtain ⟨lf, hlf, hlf1⟩ := _root_.GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI := _root_.GlobalTheory.CompanionTheory.SW.BB.isProbabilityMeasure_prH F E σ hCM M J hJ μ 𝓕 hμ h𝓕
  obtain ⟨hgi, hgf⟩ := _root_.GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable F E σ hCM M J hJ d b e he
  obtain ⟨hii, hif⟩ := GlobalTheory.T.trace_form_invariance_under_unitary F E σ M J d b B ρ e heρ
    (fun h => ((hBR (AF F)).2 h _ (fun p q => rfl)).1)
  have hcard : Fintype.card (Fin M × Fin d) = 2 * M := by simp [hd, mul_comm]
  obtain ⟨C, Df, Dinf, hDf, ⟨hDc, hD0, hDd⟩, hmain⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.Core0.core_zero F hF (Fin M × Fin d) M hcard hM B hBs hBd ρ hρ Pm hPd hPm lf hlf hlf1
      (HA (AF F) σ J) (prH μ 𝓕) (ginf e σ J b) (gfin σ J b) hgi hgf hii hif
      (fun N hN => _root_.GlobalTheory.CompanionTheory.SW.BB.CountHyp.main_bound F E σ hCM M J hJ hM d b ρ e he heρ hen μ 𝓕 hμ h𝓕 N hN)
  obtain ⟨hgc, hgr⟩ := _root_.GlobalTheory.CompanionTheory.SW.BB.gaussQ_continuous_rapidDecay F E σ hCM M d b e he hen Pm
  have hinfint : ∫⁻ X, ENNReal.ofReal (gaussQ e b Pm X)
      ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) =
      ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun _ => 0)) := by
    obtain ⟨i1, i2, i3, i4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    obtain ⟨hK1, hK2, hK3⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hinf.1
    obtain ⟨t1, t2, t3, t4, t5, t6, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
    have hDcont : Continuous fun S : HermR (Ainf F) σ 1 =>
        (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) *
          Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))) := by
      refine continuous_const.mul (hDc.comp (he.continuous.comp (continuous_const.mul (t6.comp ?_))))
      exact (continuous_apply_apply 0 0).comp continuous_subtype_val
    have h := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Inf0.fibre_rapid_zero_eq_density F E σ hCM M J hJ hM h₀ d b (coordW (Ainf F) b laminf 1 M)
      (coordHerm (Ainf F) σ b laminf 1) minf (hK2 1 M) (hK3 1) hminf (gaussQ e b Pm) hgc
      (fun X => (Real.exp_pos _).le) (hgr hPd) _ hDcont
      (_root_.GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens F E σ hCM M J hJ hM d b B (hBR (Ainf F)).1 ρ e he heρ Pm laminf hinf.1
        (hem laminf hinf) Dinf hDc hD0 hDd)
    have hz : ((hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ : HermR (Ainf F) σ 1) :
        Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0 = 0 := by
      simp [hermOf, inclR]
    rw [h, hz, map_zero, mul_zero, map_zero]
    rfl
  have hκ : 0 ≤ (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun _ => 0) :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) _) (hD0 _)
  refine ⟨gaussQ e b Pm, C, hgc, fun X => Real.exp_pos _, ?_, ?_⟩
  · rw [hinfint]; exact ENNReal.ofReal_lt_top
  · intro a ha
    obtain ⟨I, hI, hIb⟩ := hmain a ha
    obtain ⟨c1, c2, c3⟩ := hDf a ha
    have hprod := hasProd_free_mass_zero F E σ hCM M J hJ hM h₀ d b lam hlam m hm lf hlf hlf1 a ha
      (Df a) c1 c2 (fun U hU => by
        rw [_root_.GlobalTheory.CompanionTheory.SW.BB.finDensity_coord F E σ hCM M J hJ d b B (hBR (Af F)).1 lf hlf a U]
        exact c3 U hU)
    refine ⟨I, ?_, ?_⟩
    · rw [lintegral_thetaMeas_gauss_frames F E σ hCM M J hJ d b B hBE ρ e he heρ Pm μ 𝓕 hμ h𝓕 a ha]
      exact hI
    · rw [hinfint, hprod.tprod_eq, ENNReal.toReal_ofReal hκ]
      convert hIb using 3
      ring

end GlobalTheory.CompanionTheory.WeilSiegel.Free.EstZero
