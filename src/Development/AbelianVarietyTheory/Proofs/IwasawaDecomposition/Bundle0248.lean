module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCuspFormMemUnitaryRapidDecayForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CuspDeriv

theorem continuous_deriv_of_bounded {G : Type} [TopologicalSpace G] {f f₁ f₂ : G → ℝ → ℂ}
    (hf : ∀ t, Continuous fun g => f g t) (h₁ : ∀ g t, HasDerivAt (f g) (f₁ g t) t)
    (h₂ : ∀ g t, HasDerivAt (f₁ g) (f₂ g t) t) {B : ℝ} (hB : ∀ g t, ‖f₂ g t‖ ≤ B) : Continuous fun g => f₁ g 0 := by
  refine continuous_iff_continuousAt.2 fun g₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB g₀ 0)
  obtain ⟨h, h0, hh⟩ : ∃ h : ℝ, 0 < h ∧ (B + B) * h < ε :=
    ⟨ε / (B + B + 1), by positivity, by rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; linarith⟩
  have hc : Continuous fun g => ‖f g h - f g₀ h‖ + ‖f g 0 - f g₀ 0‖ + (B + B) * h * h :=
    ((((hf h).sub continuous_const).norm).add ((hf 0).sub continuous_const).norm).add continuous_const
  have := (hc.tendsto g₀).eventually_lt_const (u := h * ε) (by simp only [sub_self, norm_zero, zero_add]; nlinarith)
  filter_upwards [this] with g hg
  have key := mul_norm_deriv_le (f := fun t => f g t - f g₀ t) (f₁ := fun t => f₁ g t - f₁ g₀ t)
    (f₂ := fun t => f₂ g t - f₂ g₀ t) (fun t => (h₁ g t).sub (h₁ g₀ t)) (fun t => (h₂ g t).sub (h₂ g₀ t)) h0.le
    (B := B + B) fun t _ => (norm_sub_le _ _).trans (add_le_add (hB g t) (hB g₀ t))
  rw [dist_eq_norm]
  exact lt_of_mul_lt_mul_left (key.trans_lt hg) h0.le

theorem cuspForm_mem_decay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ F,
    IsCuspForm θ V F → F ∈ Decay θ V := by
  intro hP D θ hθ V F ⟨ha, hc⟩
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hd : ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) → IsRapidDecay θ V (word θ V l F) :=
    isRapidDecay_foldr_Rder hP hθ ha.toIsAutFun ha.smooth ha.growth hc
  refine ⟨ha.smooth, ha.left, fun l hl => ⟨?_, hd l hl⟩⟩
  induction l with
  | nil => exact ha.cont
  | cons p l ih =>
    have hp := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (by simp [hq])
    have hs : word θ V l F ∈ SmFun θ V :=
      (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
        fun q hq => linOnSm_Rder (hl' q hq)).mem F ha.smooth
    obtain ⟨B, hB⟩ := (hd (p :: p :: l) (List.forall_mem_cons.2 ⟨hp, hl⟩)).bounded
    have := continuous_deriv_of_bounded (f := fun g t => word θ V l F (g * oneP θ V p.1 p.2 t))
      (fun t => (ih hl').comp (continuous_mul_const _)) (hasDerivAt_oneP hθ hp (hasDerivAt_Rder hs hp))
      (hasDerivAt_oneP hθ hp (hasDerivAt_Rder (Rder_mem hs hp) hp)) fun g t => hB _
    simp only [oneP_zero hθ, mul_one] at this
    exact this

end GlobalTheory.Mem.CuspDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTop
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem span_basis_image_adicCompletion_eq_top
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (f : v.adicCompletion K →+* v'.adicCompletion L) (hfc : Continuous f)
    (hf : ∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) :
    letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L),
      Submodule.span (v.adicCompletion K)
        (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) = ⊤ := by
  letI := f.toAlgebra
  intro n b
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  set S := Submodule.span (v.adicCompletion K)
    (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) with hS
  haveI : ContinuousSMul (v.adicCompletion K) (v'.adicCompletion L) := by
    constructor
    have : (fun p : v.adicCompletion K × v'.adicCompletion L => p.1 • p.2)
        = fun p => f p.1 * p.2 := by
      funext p; exact Algebra.smul_def _ _
    rw [this]
    exact (hfc.comp continuous_fst).mul continuous_snd
  haveI : FiniteDimensional (v.adicCompletion K) S :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hclosed : IsClosed (S : Set (v'.adicCompletion L)) := S.closed_of_finiteDimensional
  have hmem : ∀ z : L, algebraMap L (v'.adicCompletion L) z ∈ S := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap L (v'.adicCompletion L) (b.repr z i • b i)
        = (algebraMap K (v.adicCompletion K) (b.repr z i)) •
            algebraMap L (v'.adicCompletion L) (b i) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
    rw [this]
    exact S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdense := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) L v'
  have hsub : Set.range (algebraMap L (v'.adicCompletion L)) ⊆ (S : Set _) := by
    rintro _ ⟨z, rfl⟩; exact hmem z
  have huniv : (S : Set (v'.adicCompletion L)) = Set.univ := by
    have := closure_minimal hsub hclosed
    rw [hdense.closure_range] at this
    exact Set.univ_subset_iff.mp this
  exact eq_top_iff.mpr fun x _ => by
    have : x ∈ (S : Set (v'.adicCompletion L)) := huniv ▸ Set.mem_univ x
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftPolar

theorem sesq_eq_of_diag {V : Type} [AddCommGroup V] [Module ℂ V] (B B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (h : ∀ v, B v v = B' v v) (f g : V) : B f g = B' f g := by
  have h1 := h (f + g)
  have h2 := h (f + Complex.I • g)
  simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.conj_I, h f, h g] at h1 h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 + (1 / 2 : ℂ) * (B f g - B' f g - B g f + B' g f) * Complex.I_mul_I

theorem integral_mul_star_eq {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (Θ : Submodule ℂ (X → ℂ)) (hm : ∀ f ∈ Θ, Measurable f) (hb : ∀ f ∈ Θ, ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (M : Module.End ℂ (X → ℂ)) (hM : ∀ f ∈ Θ, M f ∈ Θ)
    (hn : ∀ f ∈ Θ, ∫⁻ x, ‖M f x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν) (f f' : X → ℂ) (hf : f ∈ Θ) (hf' : f' ∈ Θ) :
    ∫ x, M f x * star (M f' x) ∂ν = ∫ x, f x * star (f' x) ∂ν := by
  obtain ⟨B, hB, hN⟩ := GlobalTheory.ThetaMeanSquareForm.exists_form ν Θ hm hb
  have hr : ∀ v : Θ, ∃ r : ℝ, 0 ≤ r ∧ B v v = r := fun v =>
    ⟨∫ x, ‖(v : X → ℂ) x‖ ^ 2 ∂ν, integral_nonneg fun x => by positivity, by
      rw [hB]
      simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
      rw [integral_complex_ofReal]⟩
  let N : Θ →ₗ[ℂ] Θ := M.restrict hM
  let B' : Θ →ₗ[ℂ] Θ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v => B (N u) (N v))
    (fun _ _ _ => by simp only [map_add (f := _), LinearMap.add_apply])
    (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply])
    (fun _ _ _ => by simp only [map_add (f := _)])
    (fun _ _ _ => by simp only [map_smul, LinearMap.map_smulₛₗ])
  have hd : ∀ v : Θ, B' v v = B v v := fun v => by
    show B (N v) (N v) = B v v
    obtain ⟨r, hr0, e⟩ := hr v
    obtain ⟨s, hs0, e'⟩ := hr (N v)
    have h1 := hn v v.2
    have h2 := hN v
    have h3 := hN (N v)
    rw [e, Complex.ofReal_re] at h2
    rw [e', Complex.ofReal_re] at h3
    have h4 : ENNReal.ofReal s = ENNReal.ofReal r := h3.symm.trans (h1.trans h2)
    rw [e, e', (ENNReal.ofReal_eq_ofReal_iff hs0 hr0).1 h4]
  have key := sesq_eq_of_diag B' B hd ⟨f, hf⟩ ⟨f', hf'⟩
  exact (hB (N ⟨f, hf⟩) (N ⟨f', hf'⟩)).symm.trans (key.trans (hB ⟨f, hf⟩ ⟨f', hf'⟩))

theorem scalar_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ M : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 M hM hn f f' hf hf'
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  let Θ : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsThetaFunO ψ S T f}
      add_mem' := GlobalTheory.WeilVacMove.isTheta_add
      zero_mem' := GlobalTheory.WeilVacMove.isTheta_zero
      smul_mem' := fun c _ h => GlobalTheory.WeilVacMove.isTheta_smul c h }
  have hb : ∀ g ∈ Θ, ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := fun g (hg : IsThetaFunO ψ S T g) => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖g (γ + w)‖ = ‖g w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hg.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  exact integral_mul_star_eq (μ.restrict 𝓕) Θ (fun g (hg : IsThetaFunO ψ S T g) => hg.cont.measurable) hb M hM hn
    f f' hf hf'

end GlobalTheory.Mem.LiftPolar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.IwaCell

variable {k : Type} [Field k] {m : ℕ}

def tD (ϖ : kˣ) (a : Fin m → ℤ) : GL (Fin m) k := diagT k (Fin m) fun i => ϖ ^ a i

variable [ValuativeRel k]

def cell (ϖ : kˣ) (a : Fin m → ℤ) : Set (GL (Fin m) k) :=
  {g | ∃ u ∈ unipB k (Fin m), ∃ κ ∈ KO k (Fin m), g = u * tD ϖ a * κ}


theorem val_tD (ϖ : kˣ) (a : Fin m → ℤ) : (tD ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : kˣ) : k) :=
  val_diagT k _

theorem tD_add (ϖ : kˣ) (a b : Fin m → ℤ) : tD ϖ (a + b) = tD ϖ a * tD ϖ b := by
  rw [tD, tD, tD, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tD_zero (ϖ : kˣ) : tD ϖ (0 : Fin m → ℤ) = 1 := by
  rw [tD, ← map_one (diagT k (Fin m))]
  congr 1
  funext i
  simp

theorem tD_neg (ϖ : kˣ) (a : Fin m → ℤ) : tD ϖ (-a) = (tD ϖ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← tD_add, neg_add_cancel, tD_zero])

theorem diag_entry (ϖ : kˣ) (s t : Fin m → ℤ) {w : GL (Fin m) k} (hw : w ∈ unipB k (Fin m)) (i : Fin m) :
    (tD ϖ s * w * tD ϖ t).val i i = ((ϖ ^ (s i + t i) : kˣ) : k) := by
  rw [Units.val_mul, Units.val_mul, val_tD, val_tD, Matrix.mul_diagonal, Matrix.diagonal_mul, ((mem_unipB k).1 hw).2 i,
    mul_one, _root_.zpow_add, Units.val_mul]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x n
  have h2 : Multiplicative.toAdd (o (x ^ n)) = Multiplicative.toAdd (o x ^ n) := congrArg _ h
  simpa [o, mul_comm] using h2

theorem eq_of_mem_cell {ϖ : kˣ} (hϖ : ord k ϖ = 1) {a b : Fin m → ℤ} {g : GL (Fin m) k} (ha : g ∈ cell ϖ a)
    (hb : g ∈ cell ϖ b) : a = b := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ := ha
  obtain ⟨u', hu', κ', hκ', e⟩ := hb
  have hw : u'⁻¹ * u ∈ unipB k (Fin m) := mul_mem (inv_mem hu') hu
  have hx : tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a = κ' * κ⁻¹ := by
    rw [tD_neg]
    calc (tD ϖ b)⁻¹ * (u'⁻¹ * u) * tD ϖ a = (u' * tD ϖ b)⁻¹ * (u * tD ϖ a * κ) * κ⁻¹ := by group
      _ = (u' * tD ϖ b)⁻¹ * (u' * tD ϖ b * κ') * κ⁻¹ := by rw [e]
      _ = κ' * κ⁻¹ := by group
  have hxi : (tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a)⁻¹ = tD ϖ (-a) * (u'⁻¹ * u)⁻¹ * tD ϖ b := by
    simp only [tD_neg, _root_.mul_inv_rev, inv_inv]; group
  have hK := (GlobalTheory.SplitFlip.mem_KO_iff _).1 (hx ▸ mul_mem hκ' (inv_mem hκ))
  funext i
  have h1 := hK.1 i i
  have h2 := hK.2 i i
  rw [diag_entry ϖ _ _ hw] at h1
  rw [hxi, diag_entry ϖ _ _ (inv_mem hw)] at h2
  simp only [Pi.neg_apply] at h1 h2
  set y : kˣ := ϖ ^ (-b i + a i)
  have h2' : ((y⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
    have : (ϖ ^ (-a i + b i) : kˣ) = y⁻¹ := by rw [← _root_.zpow_neg]; congr 1; ring
    rwa [this] at h2
  have v1 : valuation k (y : k) ≤ 1 := h1
  have v2 : valuation k ((y⁻¹ : kˣ) : k) ≤ 1 := h2'
  have hv : valuation k (y : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀] at v2
    have hpos : 0 < valuation k (y : k) := zero_lt_iff.2 (by simp)
    exact le_antisymm v1 ((inv_le_one₀ hpos).1 v2)
  have h3 : ord k y = 0 := by simp [ord, hv]
  rw [ord_zpow, hϖ, mul_one] at h3
  omega

end GlobalTheory.IwaCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBot
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory


open GlobalTheory.SmGL in
theorem unipRad_stdBlocks_two_ne_bot : ∀ (R : Type) [CommRing R] [Nontrivial R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n), 0 < a → 0 < b → unipRad R (stdBlocks ![a, b] h) ≠ ⊥ := by
  intro R _ _ n a b h ha hb
  set e := stdBlocks ![a, b] h with he
  let i : Fin n := e ⟨0, ⟨0, by simpa using ha⟩⟩
  let j : Fin n := e ⟨1, ⟨0, by simpa using hb⟩⟩
  have hij : i ≠ j := by
    intro hh
    have := congrArg Sigma.fst (e.injective hh)
    simp at this
  let g : GL (Fin n) R :=
    ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by
        show Matrix.transvection i j (1 : R) * Matrix.transvection i j (-1) = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp,
      by
        show Matrix.transvection i j (-1 : R) * Matrix.transvection i j 1 = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp⟩
  have hg : (g : Matrix (Fin n) (Fin n) R) = 1 + Matrix.single i j 1 := rfl
  have hmem : g ∈ unipRad R e := by
    rw [mem_unipRad]
    refine ⟨?_, ?_⟩
    · rw [mem_parab]
      intro p q hpq
      have hne : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
      rw [hg, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
      by_cases hp : p = i
      · by_cases hq : q = j
        · subst hp; subst hq
          rw [blk_apply, blk_apply] at hpq
          exact absurd hpq (by decide)
        · rw [Matrix.single_apply, if_neg]
          rintro ⟨_, h'⟩; exact hq h'.symm
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h', _⟩; exact hp h'.symm
    · intro c x y
      rw [hg, Matrix.add_apply]
      have h1 : (1 : Matrix (Fin n) (Fin n) R) (e ⟨c, x⟩) (e ⟨c, y⟩) = (1 : Matrix _ _ R) x y := by
        by_cases hxy : x = y
        · subst hxy; simp
        · rw [Matrix.one_apply_ne, Matrix.one_apply_ne hxy]
          intro hh
          have := e.injective hh
          simp at this
          exact hxy this
      rw [h1]
      have h2 : Matrix.single i j (1 : R) (e ⟨c, x⟩) (e ⟨c, y⟩) = 0 := by
        rw [Matrix.single_apply]
        split_ifs with hh
        · obtain ⟨h3, h4⟩ := hh
          have e3 := congrArg Sigma.fst (e.injective h3)
          have e4 := congrArg Sigma.fst (e.injective h4)
          simp only at e3 e4
          rw [← e3] at e4
          exact absurd e4 (by decide)
        · rfl
      rw [h2, add_zero]
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg (fun u : GL (Fin n) R => (u : Matrix (Fin n) (Fin n) R) i j) hmem
  simp [hg, Matrix.one_apply_ne hij] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem isIrreducible_sqRep (n : ℕ) (mu : DomWeight n) : (GlobalTheory.Branching.sqRep ℂ n mu).IsIrreducible := by
  have hU := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  obtain ⟨hn, hs⟩ := (CuspRep.isIrreducible_iff _).1 hU
  exact (CuspRep.isIrreducible_iff _).2 ⟨hn, fun S hS => hs S fun u => hS _⟩

theorem rhoK_tenMul {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (u : ∀ τ, nablaSq ℂ n (lam τ)) :
    Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam u) =
      GlobalTheory.CoefIrred.tenMul lam fun τ => GlobalTheory.Branching.sqRep ℂ n (lam τ) (g τ) (u τ) := by
  apply Subtype.ext
  rw [Formalism.L2.DIV.rhoK_coe, GlobalTheory.CoefIrred.tenMul_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.actTen]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cAll_of_mem_embU {v u : InfinitePlace E} (huv : u ≠ v) {x : UA E n} (hx : x ∈ embU n v.embedding) :
    cAll x u = 1 := by
  have h := (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_iInf] at h
  have h2 := h u.embedding
  rw [Subgroup.mem_iInf] at h2
  exact h2 (by simpa using huv)

theorem embU_le_infU (τ : E →+* ℂ) : embU n τ ≤ infU E n := inf_le_left

theorem rep_tenMul_update [DecidableEq (InfinitePlace E)] (W : Wt E n) (v : InfinitePlace E) (x : infU E n)
    (hx : x.1 ∈ embU n v.embedding) (e : ∀ u, nablaSq ℂ n (W u)) (a : nablaSq ℂ n (W v)) :
    W.rep x (GlobalTheory.CoefIrred.tenMul W (Function.update e v a)) =
      GlobalTheory.CoefIrred.tenMul W (Function.update e v (GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding x.1) a)) := by
  change Formalism.L2.DIV.rhoK W (cAll x.1) _ = _
  rw [rhoK_tenMul]
  congr 1
  funext u
  by_cases h : u = v
  · subst h
    simp only [Function.update_self]
    rfl
  · simp only [Function.update_of_ne h, cAll_of_mem_embU h hx, map_one, Module.End.one_apply]

theorem hasWeightAt_of_finPart (π : AutSub E n) (W : Wt E n) {f : algForms W} (hf : f ∈ π.finPart W) (hf0 : f ≠ 0)
    (v : InfinitePlace E) : HasWeightAt π.V v.embedding (W v) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, f.1 (GlobalTheory.CoefIrred.tenMul W e) ≠ 0 := by
    by_contra hc
    push Not at hc
    have h1 : f.1 = 0 := by
      apply (Formalism.L2.DIV.bVV ℂ W).ext
      intro i
      have hb : Formalism.L2.DIV.bVV ℂ W i = GlobalTheory.CoefIrred.tenMul W
          (fun τ => GlobalTheory.CoefIrred.ssBasis ℂ (W τ) (i τ)) := by
        apply Subtype.ext
        rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe,
          Formalism.L2.DIV.bVVfun]
        simp only [GlobalTheory.CoefIrred.ssBasis_coe]
      rw [hb]
      exact hc _
    exact hf0 (Subtype.ext h1)
  refine ⟨isIrreducible_sqRep n (W v), f.1 ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v, fun h0 => he ?_, fun a => ?_,
    fun x a => ?_⟩
  · have := LinearMap.congr_fun h0 (e v)
    simpa [MultilinearMap.toLinearMap] using this
  · exact AutSub.mem_finPart.1 hf _
  · have hx : x.1 ∈ infU E n := embU_le_infU _ x.2
    have h2 := f.2.2 ⟨x.1, hx⟩ (GlobalTheory.CoefIrred.tenMul W (Function.update e v a))
    rw [rep_tenMul_update W v ⟨x.1, hx⟩ x.2] at h2
    exact h2

end GlobalTheory.DefU

end
end

