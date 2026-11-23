module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0210
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateSobolev
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTranslateSobolev

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem val_mem (x : G n) : x.val ∈ GLs n := by
  have h := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  exact h.ne_zero

def mulL (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := fun y z => Matrix.mul_add a y z
      map_smul' := fun c y => Matrix.mul_smul a c y }

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (lTr x f) (GLs n) :=
  hf.comp (mulL x.val).contDiff.contDiffOn (fun _ hy => mul_mem (val_mem x) hy)

theorem Rd_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n)
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (lTr x f) g = Rd X f (x.val * g) := by
  have hxg : x.val * g ∈ GLs n := mul_mem (val_mem x) hg
  have hd : DifferentiableAt ℝ f (mulL x.val g) :=
    (hf.contDiffAt ((isOpen_GLs n).mem_nhds hxg)).differentiableAt (by simp)
  have hc : fderiv ℝ (f ∘ mulL x.val) g = (fderiv ℝ f (mulL x.val g)).comp (mulL x.val) :=
    (hd.hasFDerivAt.comp g (mulL x.val).hasFDerivAt).fderiv
  show fderiv ℝ (f ∘ mulL x.val) g (g * X) = fderiv ℝ f (x.val * g) (x.val * g * X)
  rw [hc]
  simp [mulL, Matrix.mul_assoc]

theorem contDiffOn_Rw (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hR n).1 V (Rw w f) ih).1 (bs p)

theorem Rw_lTr (hR : RCalc) (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ∀ g ∈ GLs n, Rw w (lTr x f) g = Rw w f (x.val * g) := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have he : Rw w (lTr x f) =ᶠ[𝓝 g] lTr x (Rw w f) :=
      Filter.eventuallyEq_of_mem ((isOpen_GLs n).mem_nhds hg) (fun y hy => ih y hy)
    show Rd (bs p) (Rw w (lTr x f)) g = Rd (bs p) (Rw w f) (x.val * g)
    rw [← Rd_lTr x (contDiffOn_Rw hR hf w) (bs p) hg]
    show fderiv ℝ (Rw w (lTr x f)) g (g * bs p) = fderiv ℝ (lTr x (Rw w f)) g (g * bs p)
    rw [he.fderiv_eq]

end LeftTranslateSobolev


open LeftTranslateSobolev in
theorem ltSob : LtSob := by
  intro n _ _ μ _ V _ _ _ _ hR x f hf
  refine ⟨⟨contDiffOn_lTr x hf.1, fun w => ?_⟩, fun g hg => ?_⟩
  · have h := (hf.2 w).comp_measurePreserving (measurePreserving_mul_left μ x)
    have he : (fun y : G n => Rw w (lTr x f) y.val) = (fun y : G n => Rw w f y.val) ∘ (fun y => x * y) :=
      funext fun y => Rw_lTr hR x hf.1 w y.val (val_mem y)
    rw [he]
    exact h
  · have ht : ∀ s, gel s 2 (lTr x f) g = gel s 2 f (x.val * g) := fun s =>
      (((hR n).1 V f hf.1).2.2.2 s 2 x.val (val_mem x) g hg).1
    simp only [Om, Pi.smul_apply, Pi.add_apply, ht]

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGaloisEmbeddingExtension
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical Topology

namespace GlobalTheory.CompanionTheory.EmbBridge

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem tendsto_pow_zero (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E)
    (hx : Valued.v x < 1) : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (𝓝 0) := by
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by simp
  have : ∃ n : ℕ, (Valued.v x) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    exact exists_pow_lt₀ hx (Units.mk0 _ hpos)
  obtain ⟨n, hn⟩ := this
  refine Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨n, fun m hm => hγ ?_⟩)
  have e : Valued.v (x ^ m) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    rw [map_pow]
    exact (pow_le_pow_of_le_one zero_le' hx.le hm).trans_lt hn
  exact (Valuation.restrict_lt_iff_lt_embedding _).2 e

theorem norm_lt_one (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : Valued.v x < 1) : ‖φ x‖ < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => φ x ^ n) Filter.atTop (𝓝 0) := by
    have := (hφ.tendsto 0).comp (tendsto_pow_zero w x hx)
    simpa [Function.comp_def, map_pow] using this
  by_contra hge
  have h2 : ∀ n : ℕ, 1 ≤ ‖φ x ^ n‖ := fun n => by
    rw [norm_pow]; exact one_le_pow₀ (not_lt.1 hge)
  have h3 := h1.norm
  rw [norm_zero] at h3
  have := ge_of_tendsto' h3 h2
  linarith

theorem v_le_one (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : ‖φ x‖ < 1) : Valued.v x ≤ 1 := by
  by_contra hgt
  have hgt' := not_le.1 hgt
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hgt'
  have h1 : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hgt'
  have h2 := norm_lt_one w φ hφ _ h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx0)
  have := (one_lt_inv₀ hpos).2 hx
  linarith

theorem exists_v_lt_one (w : HeightOneSpectrum (𝓞 E)) :
    ∃ π : w.adicCompletion E, π ≠ 0 ∧ Valued.v π < 1 := by
  obtain ⟨y, hyw, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  refine ⟨algebraMap E _ (y : E), ?_, ?_⟩
  · simpa using hy0
  · have h : w.valuation E (y : E) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w y).2 hyw
    have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (y : E)
    rw [e]
    exact h

theorem isInducing (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ) :
    Topology.IsInducing φ := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm (by simpa using (hφ.tendsto 0).le_comap) ?_
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨π, hπ0, hπ⟩ := exists_v_lt_one w
  have hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (Valued.v π) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    exists_pow_lt₀ hπ (Units.mk0 _ hpos)
  have hε : 0 < ‖φ (π ^ n)‖ := norm_pos_iff.2 ((map_ne_zero φ).2 (pow_ne_zero n hπ0))
  refine Filter.mem_comap.2 ⟨Metric.ball 0 ‖φ (π ^ n)‖, Metric.ball_mem_nhds _ hε, fun x hx => hγ ?_⟩
  have hx' : ‖φ x‖ < ‖φ (π ^ n)‖ := by simpa using hx
  have h1 : ‖φ (x / π ^ n)‖ < 1 := by
    rw [map_div₀, norm_div]
    exact (div_lt_one hε).2 hx'
  have h2 := v_le_one w φ hφ _ h1
  have hv : 0 < Valued.v π ^ n := zero_lt_iff.2 (pow_ne_zero n ((Valuation.ne_zero_iff _).2 hπ0))
  rw [map_div₀, map_pow, div_le_one₀ hv] at h2
  exact (Valuation.restrict_lt_iff_lt_embedding _).2 (h2.trans_lt hn)

end GlobalTheory.CompanionTheory.EmbBridge

namespace GlobalTheory.CompanionTheory.EmbBridge

theorem embeddings_of_continuous : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 →
    ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ (φ : w.adicCompletion E →+* Om l) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), Continuous φ ∧
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) ∧
      (∀ x, ∃ hx : φ x ∈ Bw.Kw.1, ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x) ∧
      ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' ↔ τ' = τ := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hI LL' hLL j
  have hKL : Bw.Kw.1 ≤ LL'.1 := fun x hx => hLL (Bw.LL_split Bw.Kw.1.val ⟨x, hx⟩)
  obtain ⟨⟨φ, hφc⟩, hφ, -⟩ := GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced w A hA O Bw hI LL'
    (IntermediateField.inclusion hKL)
  have hφE : ∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y) := fun y => hφ y
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hKc : IsClosed (Bw.Kw.1 : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra)
  have hmem : ∀ x, φ x ∈ Bw.Kw.1 := fun x =>
    (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => φ x ∈ (Bw.Kw.1 : Set (Om l))) x
      (hKc.preimage hφc) (fun y => by
        show φ _ ∈ Bw.Kw.1
        rw [hφE]; exact Bw.j_E y)
  have hind := isInducing w φ hφc
  have hrc : IsClosed (Set.range φ) :=
    (AddMonoidHom.isUniformInducing_of_isInducing (f := φ.toAddMonoidHom) hind).isComplete_range.isClosed
  have hsurj : ∀ k : ↥Bw.Kw.1, ∃ x, φ x = k := fun k => by
    have h1 : (k : Om l) ∈ closure (Set.range fun x : E => Bw.j (algebraMap E Ω x)) := Bw.j_dense k.2
    have h2 : (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ Set.range φ := by
      rintro _ ⟨y, rfl⟩
      exact ⟨_, hφE y⟩
    exact hrc.closure_subset_iff.2 h2 h1
  let φ' : w.adicCompletion E →+* ↥Bw.Kw.1 := φ.codRestrict Bw.Kw.1 hmem
  have hbij : Function.Bijective φ' := ⟨fun a b h => φ.injective (congrArg Subtype.val h), fun k => by
    obtain ⟨x, hx⟩ := hsurj k
    exact ⟨x, Subtype.ext hx⟩⟩
  let e : w.adicCompletion E ≃+* ↥Bw.Kw.1 := RingEquiv.ofBijective φ' hbij
  have hei : Topology.IsInducing e := by
    refine Topology.IsInducing.of_comp ?_ continuous_subtype_val hind
    exact hφc.subtype_mk hmem
  have hes : Continuous e.symm := (e.toEquiv.toHomeomorphOfIsInducing hei).symm.continuous
  let ψ : ↥Bw.Kw.1 →+* Om l := j.1.comp (e.symm : ↥Bw.Kw.1 →+* w.adicCompletion E)
  have hψc : Continuous ψ := j.2.comp hes
  have hlin : ∀ a : ℚ_[l], ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a) = algebraMap ℚ_[l] (Om l) a := fun a => by
    have c1 : Continuous fun a : ℚ_[l] => ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a) :=
      hψc.comp (continuous_algebraMap ℚ_[l] ↥Bw.Kw.1)
    have c2 : Continuous fun a : ℚ_[l] => algebraMap ℚ_[l] (Om l) a := continuous_algebraMap ℚ_[l] (Om l)
    refine congrFun ((Padic.denseRange_ratCast l).equalizer c1 c2 (funext fun q => ?_)) a
    simp
  let μ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := { ψ with commutes' := hlin }
  let τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 := μ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split μ x)
  have hτ : ∀ x (hx : φ x ∈ Bw.Kw.1), ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x := fun x hx => by
    have : e.symm ⟨φ x, hx⟩ = x := e.symm_apply_apply x
    show j.1 (e.symm ⟨φ x, hx⟩) = j.1 x
    rw [this]
  have key : ∀ y : E, ((τ (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y) : ↥LL'.1) : Om l) = j.1 (algebraMap E _ y) := fun y => by
    have e1 : GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y = ⟨φ (algebraMap E _ y), hmem _⟩ := Subtype.ext (hφE y).symm
    rw [e1]
    exact hτ _ _
  have hd : DenseRange (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw) := fun k => by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, ← Set.range_comp]
    exact Bw.j_dense k.2
  have hc : ∀ t : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, Continuous fun x => ((t x : ↥LL'.1) : Om l) := fun t => by
    refine Metric.continuous_iff.2 fun b ε hε => ⟨ε, hε, fun a h => ?_⟩
    have h' : ‖(a : Om l) - (b : Om l)‖ < ε := by rwa [← dist_eq_norm]
    rw [dist_eq_norm]
    have e2 : ((t a : ↥LL'.1) : Om l) - ((t b : ↥LL'.1) : Om l) = ((t (a - b) : ↥LL'.1) : Om l) := by
      simp
    rw [e2, GlobalTheory.CompanionTheory.EmbUniq.norm_coe_algHom]
    exact h'
  refine ⟨φ, τ, hφc, hφE, fun x => ⟨hmem x, hτ x _⟩, fun τ' => ⟨fun h => ?_, ?_⟩⟩
  · refine AlgHom.ext fun x => Subtype.ext (congrFun (hd.equalizer (hc τ') (hc τ) (funext fun y => ?_)) x)
    exact (h y).symm.trans (key y).symm
  · rintro rfl y
    exact (key y).symm

end GlobalTheory.CompanionTheory.EmbBridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpIntegralAePointwise
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.LpBochner

variable {Y V : Type} [MeasurableSpace Y] {ν : Measure Y}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem integrableOn_of_memLp_two {h : Y → V} (hh : MemLp h 2 ν) {s : Set Y} (hs : ν s ≠ ⊤) :
    IntegrableOn h s ν := by
  haveI : IsFiniteMeasure (ν.restrict s) := ⟨by simpa using hs.lt_top⟩
  have h2 : MemLp h 2 (ν.restrict s) := hh.restrict s
  exact memLp_one_iff_integrable.1 (h2.mono_exponent (by norm_num))

theorem integral_norm_restrict_le {h : Y → V} (hh : MemLp h 2 ν) {s : Set Y} (hs : ν s ≠ ⊤) :
    ∫ y in s, ‖h y‖ ∂ν ≤ ((ν s) ^ (1 / 2 : ℝ)).toReal * (eLpNorm h 2 ν).toReal := by
  haveI : IsFiniteMeasure (ν.restrict s) := ⟨by simpa using hs.lt_top⟩
  have hm : AEStronglyMeasurable h (ν.restrict s) := hh.aestronglyMeasurable.restrict
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict s) (p := 1) (q := 2)
    (by norm_num) hm
  have h3 : eLpNorm h 2 (ν.restrict s) ≤ eLpNorm h 2 ν := eLpNorm_restrict_le _ _ _ _
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
    norm_num
  rw [hexp, Measure.restrict_apply_univ] at h1
  have hfin : (ν s) ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hs
  have h4 : eLpNorm h 1 (ν.restrict s) ≤ (ν s) ^ (1 / 2 : ℝ) * eLpNorm h 2 ν := by
    calc _ ≤ _ := h1
      _ ≤ eLpNorm h 2 ν * (ν s) ^ (1 / 2 : ℝ) := by gcongr
      _ = _ := mul_comm _ _
  have h5 : ∫ y in s, ‖h y‖ ∂ν = (eLpNorm h 1 (ν.restrict s)).toReal := by
    rw [integral_norm_eq_lintegral_eNorm hm, eLpNorm_one_eq_lintegral_eNorm hm]
  rw [h5, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hh.ne) h4

variable [CompleteSpace V]

def setIntegralCLM (ν : Measure Y) (s : Set Y) (hs : ν s ≠ ⊤) : Lp V 2 ν →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ y in s, h y ∂ν
      map_add' := fun f g => by
        have hf := integrableOn_of_memLp_two (Lp.memLp f) hs
        have hg := integrableOn_of_memLp_two (Lp.memLp g) hs
        rw [← integral_add hf hg]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))
      map_smul' := fun r f => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul r f)) }
    ((ν s) ^ (1 / 2 : ℝ)).toReal
    (fun h => by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine (integral_norm_restrict_le (Lp.memLp h) hs).trans ?_
      rw [Lp.norm_def])

theorem setIntegralCLM_apply (s : Set Y) (hs : ν s ≠ ⊤) (h : Lp V 2 ν) :
    setIntegralCLM ν s hs h = ∫ y in s, h y ∂ν := rfl

theorem bochner_Lp_ae (A : Type) [MeasurableSpace A] (α : Measure A) [SFinite α]
    [SigmaFinite ν] (c : A → Lp V 2 ν) (F : A → Y → V)
    (hc : Integrable c α) (hF : AEStronglyMeasurable (Function.uncurry F) (α.prod ν))
    (hcF : ∀ᵐ a ∂α, c a =ᵐ[ν] F a) :
    (⇑(∫ a, c a ∂α) : Y → V) =ᵐ[ν] fun y => ∫ a, F a y ∂α := by
  have hFs : ∀ s : Set Y, AEStronglyMeasurable (Function.uncurry F) (α.prod (ν.restrict s)) := by
    intro s
    refine hF.mono_measure ?_
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hint : ∀ s : Set Y, ν s ≠ ⊤ → Integrable (Function.uncurry F) (α.prod (ν.restrict s)) := by
    intro s hs
    rw [integrable_prod_iff (hFs s)]
    constructor
    · filter_upwards [hcF] with a ha
      exact (integrableOn_of_memLp_two (Lp.memLp (c a)) hs).congr (ae_restrict_of_ae ha)
    · refine Integrable.mono' (hc.norm.const_mul ((ν s) ^ (1 / 2 : ℝ)).toReal)
        (hFs s).norm.integral_prod_right' ?_
      filter_upwards [hcF] with a ha
      have hnn : 0 ≤ ∫ y, ‖Function.uncurry F (a, y)‖ ∂(ν.restrict s) :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn, Lp.norm_def]
      have : ∫ y, ‖Function.uncurry F (a, y)‖ ∂(ν.restrict s) = ∫ y in s, ‖c a y‖ ∂ν :=
        integral_congr_ae (ae_restrict_of_ae (ha.mono fun y hy => by simp [hy]))
      rw [this]
      exact integral_norm_restrict_le (Lp.memLp (c a)) hs
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s _ hs
    exact integrableOn_of_memLp_two (Lp.memLp _) hs.ne
  · intro s _ hs
    exact (hint s hs.ne).integral_prod_right
  · intro s hsm hs
    have h1 : ∫ y in s, (∫ a, c a ∂α) y ∂ν = ∫ a, ∫ y in s, c a y ∂ν ∂α := by
      rw [← setIntegralCLM_apply s hs.ne, ← ContinuousLinearMap.integral_comp_comm _ hc]
      rfl
    have h2 : ∫ a, ∫ y in s, c a y ∂ν ∂α = ∫ a, ∫ y in s, F a y ∂ν ∂α := by
      refine integral_congr_ae ?_
      filter_upwards [hcF] with a ha
      exact integral_congr_ae (ae_restrict_of_ae ha)
    rw [h1, h2]
    exact integral_integral_swap (hint s hs.ne)

theorem coe_integral_ae_eq : ∀ (A Y V : Type) [MeasurableSpace A] [MeasurableSpace Y] (α : Measure A) [SFinite α] (ν : Measure Y) [SigmaFinite ν] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (c : A → Lp V 2 ν) (F : A → Y → V), Integrable c α → AEStronglyMeasurable (Function.uncurry F) (α.prod ν) → (∀ᵐ a ∂α, c a =ᵐ[ν] F a) → (⇑(∫ a, c a ∂α) : Y → V) =ᵐ[ν] fun y => ∫ a, F a y ∂α := by
  intro A Y V _ _ α _ ν _ _ _ _ c F hc hF hcF
  exact bochner_Lp_ae A α c F hc hF hcF

end GlobalTheory.CompanionTheory.LpBochner
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationEvaluationContinuous
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.MolBounded

open GlobalTheory.CompanionTheory.SobGL.HaarDom

variable {n : ℕ}

theorem kernel_continuous {φ : Mat n → ℝ} (hφ : Continuous φ) (z : Mat n) :
    Continuous fun u : G n => φ (z * (u⁻¹ : G n).val) :=
  hφ.comp (continuous_const.matrix_mul (Units.continuous_val.comp continuous_inv))

theorem kernel_hasCompactSupport {φ : Mat n → ℝ} (hφ : IsTest φ) {z : Mat n} (hz : z ∈ GLs n) :
    HasCompactSupport fun u : G n => φ (z * (u⁻¹ : G n).val) := by
  obtain ⟨-, hK, hKs⟩ := hφ
  have unit_of : ∀ w ∈ GLs n, ∃ y : G n, y.val = w := by
    intro w hw
    have hd : IsUnit w := (Matrix.isUnit_iff_isUnit_det w).2 (isUnit_iff_ne_zero.2 hw)
    obtain ⟨y, hy⟩ := hd
    exact ⟨y, hy⟩
  obtain ⟨zG, rfl⟩ := unit_of z hz
  have hS : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine (isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff ?_ |>.2 hK
    intro w hw
    obtain ⟨y, hy⟩ := unit_of w (hKs hw)
    exact ⟨y, hy⟩
  have hI : IsCompact ((fun w : G n => w⁻¹ * zG) '' ((Units.val : G n → Mat n) ⁻¹' tsupport φ)) :=
    hS.image (continuous_inv.mul continuous_const)
  refine HasCompactSupport.intro hI fun u hu => ?_
  by_contra hne
  refine hu ⟨zG * u⁻¹, ?_, by group⟩
  have : (zG * u⁻¹).val ∈ Function.support φ := by
    simpa [Function.mem_support] using hne
  exact subset_tsupport φ this

theorem mol_bounded : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ z ∈ GLs n,
      ∃ L : Lp V 2 μ →L[ℝ] V, ∀ x : Lp V 2 μ, L x = Mol μ φ (⇑x) z := by
  intro n _ _ μ _ V _ _ _ _ φ hφ z hz
  set g : G n → ℝ := fun u => φ (z * (u⁻¹ : G n).val) with hgdef
  have hgc : Continuous g := kernel_continuous hφ.1.continuous z
  have hg2 : MemLp g 2 μ := hgc.memLp_of_hasCompactSupport (kernel_hasCompactSupport hφ hz)
  have hmem : ∀ x : Lp V 2 μ, MemLp (g • (x : G n → V)) 1 μ := fun x =>
    hg2.smul (Lp.memLp x)
  have hint : ∀ x : Lp V 2 μ, Integrable (fun u => g u • (x : G n → V) u) μ := fun x =>
    memLp_one_iff_integrable.1 (hmem x)
  have hb : ∀ x : Lp V 2 μ,
      ‖∫ u, g u • (x : G n → V) u ∂μ‖ ≤ (eLpNorm g 2 μ).toReal * ‖x‖ := by
    intro x
    have h1 : eLpNorm (g • (x : G n → V)) 1 μ ≤ eLpNorm g 2 μ * eLpNorm x 2 μ :=
      eLpNorm_smul_le_mul_eLpNorm hg2.aestronglyMeasurable (Lp.aestronglyMeasurable x)
    have h2 : ∫ u, ‖g u • (x : G n → V) u‖ ∂μ = (eLpNorm (g • (x : G n → V)) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm (hint x).1]
      · rfl
      · exact (hmem x).aestronglyMeasurable
    calc ‖∫ u, g u • (x : G n → V) u ∂μ‖ ≤ ∫ u, ‖g u • (x : G n → V) u‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ = (eLpNorm (g • (x : G n → V)) 1 μ).toReal := h2
      _ ≤ (eLpNorm g 2 μ * eLpNorm x 2 μ).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top hg2.ne (Lp.eLpNorm_ne_top x)) h1
      _ = (eLpNorm g 2 μ).toReal * ‖x‖ := by
          rw [ENNReal.toReal_mul, Lp.norm_def]
  let Lin : Lp V 2 μ →ₗ[ℝ] V :=
    { toFun := fun x => ∫ u, g u • (x : G n → V) u ∂μ
      map_add' := fun x y => by
        rw [← integral_add (hint x) (hint y)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add x y] with u hu
        rw [hu, Pi.add_apply, smul_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c x] with u hu
        rw [hu, Pi.smul_apply, smul_comm] }
  exact ⟨Lin.mkContinuous _ hb, fun x => rfl⟩

end GlobalTheory.CompanionTheory.PresSobA.MolBounded
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtensionStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_embedding_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      ∃! j : {j : w.adicCompletion E →+* Qbar l // Continuous j},
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' := by
  first | exact @GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced | exact GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced | (intros; apply GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced <;> assumption)
end
end

