module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SingleMemIntVec
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDataLattice
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix

namespace GlobalTheory.Member.LatData

open GlobalTheory.Up.Definite GlobalTheory.LatFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in
private theorem exists_int_mul_isIntegral_of_fg (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ Λ, ∀ a, IsIntegral ℤ ((d : E) * x a) := by
  classical
  obtain ⟨s, rfl⟩ := hΛ
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ (s.biUnion fun x => Finset.univ.image x)
  refine ⟨d, hd, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro a
    have h := hint (x a) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩)
    rwa [zsmul_eq_mul] at h
  | zero => intro a; simpa using isIntegral_zero
  | add x y _ _ hx hy => intro a; simpa [mul_add] using (hx a).add (hy a)
  | smul k x _ hx =>
    intro a
    have h : (d : E) * (k • x) a = algebraMap (𝓞 E) E k * ((d : E) * x a) := by
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
    rw [h]
    exact (RingOfIntegers.isIntegral_coe k).mul (hx a)

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in
private theorem exists_int_smul_single_mem_of_span_eq_univ (Λ : Submodule (𝓞 E) (Fin r → E))
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ b : Fin r, (c : E) • (Pi.single b 1 : Fin r → E) ∈ Λ := by
  classical
  have hmem : ∀ b : Fin r, (Pi.single b 1 : Fin r → E) ∈ Submodule.span E (Λ : Set (Fin r → E)) :=
    fun b => hspan ▸ Submodule.mem_top
  choose f t ht _ hsum using fun b => Submodule.mem_span_iff_exists_finset_subset.1 (hmem b)
  obtain ⟨c, hc, hcint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.biUnion fun b => (t b).image (f b))
  refine ⟨c, hc, fun b => ?_⟩
  have key : ∀ v ∈ t b, (c : E) • (f b v • v) ∈ Λ := by
    intro v hv
    have hI : IsIntegral ℤ ((c : E) * f b v) := by
      have h := hcint (f b v) (Finset.mem_biUnion.2 ⟨b, Finset.mem_univ _, Finset.mem_image_of_mem _ hv⟩)
      rwa [zsmul_eq_mul] at h
    have h : (c : E) • (f b v • v) = (⟨_, hI⟩ : 𝓞 E) • v := by
      rw [smul_smul]
      rfl
    rw [h]
    exact Λ.smul_mem _ (ht b hv)
  rw [← hsum b, Finset.smul_sum]
  exact Λ.sum_mem key

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem cc_intCast' (n : ℤ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (n : E) = n := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_cc, map_intCast, map_intCast]

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in
private theorem finite_GL_of_integral_bounded_scaled_entries (c : E) (hc : c ≠ 0) (B : ℝ) :
    {γ : GL (Fin r) E | ∀ a b, IsIntegral ℤ (c * (γ : Matrix (Fin r) (Fin r) E) a b) ∧
      ∀ φ : E →+* ℂ, ‖φ (c * (γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ B}.Finite := by
  have hT := Embeddings.finite_of_norm_le E ℂ B
  have hpi : (Set.univ.pi fun _ : Fin r => Set.univ.pi fun _ : Fin r =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hT
  have hinj : Function.Injective fun γ : GL (Fin r) E => fun a b => c * (γ : Matrix (Fin r) (Fin r) E) a b := by
    intro γ δ h
    ext a b
    exact mul_left_cancel₀ hc (congrFun (congrFun h a) b)
  refine (hpi.preimage hinj.injOn).subset fun γ hγ => ?_
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
  exact fun a b => hγ a b


open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.Member.LatData.exists_data_lattice : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
    ∃ X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r, X.Λ = Λ := by
  intro E _ _ _ r Λ hfg hspan
  obtain ⟨d, hd, hdint⟩ := exists_int_mul_isIntegral_of_fg Λ hfg
  obtain ⟨c, hc, hcmem⟩ := exists_int_smul_single_mem_of_span_eq_univ Λ hspan
  have hdc : ((d * c : ℤ) : E) ≠ 0 := by exact_mod_cast mul_ne_zero hd hc
  refine ⟨{ _root_.GlobalTheory.Up.Definite.data (E := E) (r := r) with
    Λ := Λ
    Λ_fg := hfg
    Λ_span := hspan
    den := (d : 𝓞 E) * (d : 𝓞 E)
    den_ne := by exact_mod_cast mul_ne_zero hd hd
    Λ_int := ?_
    Γ_stab := ?_
    Γ_index := ?_
    transv := by
      intro ξ _ hiso s _ _
      change _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) ξ ξ = 0 at hiso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h1 := congrArg φ hiso
      rw [_root_.GlobalTheory.Up.Definite.map_herm_one_self, map_zero, Complex.ofReal_eq_zero,
        Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at h1
      have hξ : ∀ a, ξ a = 0 := fun a => by simpa using h1 a (Finset.mem_univ a)
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      ext a b
      simp [_root_.GlobalTheory.Up.Definite.data, _root_.ReciprocityTheory.ChartRestriction.G.FD.transvMat, hξ, Matrix.one_apply] }, rfl⟩
  · intro x hx y hy
    show IsIntegral ℤ ((((d : 𝓞 E) * (d : 𝓞 E) : 𝓞 E) : E) * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) x y)
    rw [_root_.GlobalTheory.Up.Definite.herm_one, Finset.mul_sum]
    refine IsIntegral.sum _ fun a _ => ?_
    have h : (((d : 𝓞 E) * (d : 𝓞 E) : 𝓞 E) : E) * (x a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y a)) =
        ((d : E) * x a) * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((d : E) * y a) := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.cc_mul, cc_intCast',
        show (((d : 𝓞 E) * (d : 𝓞 E) : 𝓞 E) : E) = (d : E) * (d : E) by simp]
      ring
    rw [h]
    exact (hdint x hx a).mul (_root_.ReciprocityTheory.ChartRestriction.G.FD.isIntegral_cc (hdint y hy a))
  · intro γ hγ
    change γ ∈ (⊥ : Subgroup (GL (Fin r) E)) at hγ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab]
  · refine ⟨(finite_GL_of_integral_bounded_scaled_entries ((d * c : ℤ) : E) hdc ‖((d * c : ℤ) : ℂ)‖).toFinset,
      fun γ hγ => ⟨γ, ?_, by simp⟩⟩
    rw [Set.Finite.mem_toFinset]
    intro a b
    have hcol : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single b 1) =
        fun a => (γ : Matrix (Fin r) (Fin r) E) a b := by
      ext a; simp
    have hnorm : ∀ φ : E →+* ℂ, ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1 := by
      intro φ
      have h0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single b 1)
          ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single b 1) =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) (Pi.single b 1) (Pi.single b 1) := hγ.1 _ _
      have h1 := congrArg φ h0
      rw [_root_.GlobalTheory.Up.Definite.map_herm_one_self, _root_.GlobalTheory.Up.Definite.map_herm_one_self, hcol] at h1
      have h2 : ∑ a, ‖φ ((Pi.single b 1 : Fin r → E) a)‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single b] <;> simp +contextual
      have h3 := Complex.ofReal_injective h1
      rw [h2] at h3
      have h4 := Finset.single_le_sum (f := fun a => ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
      rw [h3] at h4
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
    refine ⟨?_, fun φ => ?_⟩
    · have hmemγ := (hγ.2 _).mp (hcmem b)
      have hi := hdint _ hmemγ a
      rw [Matrix.mulVec_smul, hcol] at hi
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      have h : ((d * c : ℤ) : E) * (γ : Matrix (Fin r) (Fin r) E) a b =
          (d : E) * ((c : E) * (γ : Matrix (Fin r) (Fin r) E) a b) := by
        push_cast
        ring
      rw [h]
      exact hi
    · rw [map_mul, norm_mul, map_intCast]
      exact mul_le_of_le_one_right (norm_nonneg _) (hnorm φ)

end GlobalTheory.Member.LatData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDensityOriginOfAlmostHomogeneous
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem _root_.GlobalTheory.densHom_scale (l : Measure V) [l.IsAddHaarMeasure] (x : V) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    l (Metric.closedBall x (s * r)) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * l (Metric.ball 0 r) := by
  rw [Measure.addHaar_closedBall_mul_of_pos l x hs r, Measure.addHaar_closedBall l 0 hr.le,
    Measure.addHaar_ball_of_pos l 0 hr]

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem _root_.GlobalTheory.densHom_tendsto_mul {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => s * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun r : ℝ => s * r) (𝓝 0) (𝓝 (s * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hs hr

end

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem closedBall_smul_div_ball_eq_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] (x : V)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ν (Metric.closedBall x (s * r)) / l (Metric.ball 0 r) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) *
        (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r))) := by
  rw [_root_.GlobalTheory.densHom_scale l x hs hr, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 (pow_pos hs _)).ne' ENNReal.ofReal_ne_top]

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem ofReal_pow_mul_le_liminf_ball_ratio (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.closedBall x (s * r)) ≤ ν (Metric.ball 0 r)) :
    ENNReal.ofReal (s ^ Module.finrank ℝ V) * D ≤
      liminf (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (le_of_eq htend.liminf_eq.symm).trans (Filter.liminf_le_liminf ?_)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem limsup_ball_ratio_le_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.ball 0 r) ≤ ν (Metric.closedBall x (s * r))) :
    limsup (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) ≤
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * D := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (Filter.limsup_le_limsup ?_).trans (le_of_eq htend.limsup_eq)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _


open MeasureTheory Filter Topology Matrix in
theorem _root_.GlobalTheory.exists_density_origin_of_almost_homogeneous : ∀ (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V)
    [l.IsAddHaarMeasure] [IsLocallyFiniteMeasure ν], (∀ r : ℝ, 0 < r → ν (Metric.ball 0 r) ≠ 0) →
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ →
      ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧
        ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) →
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  intro V _ _ _ _ _ l ν _ _ hpos halmost
  set ρ := fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r) with hρ
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ D : ENNReal, D < ⊤ ∧
      ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D ≤ liminf ρ (𝓝[>] 0) ∧
      limsup ρ (𝓝[>] 0) ≤ ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D := by
    intro ε hε hε2
    obtain ⟨δ, hδ, hx⟩ := halmost ε hε (by linarith)
    obtain ⟨x, hxmem, hxD, hxfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (Metric.measure_ball_pos l (0 : V) hδ).ne'
      (ae_restrict_of_ae ((Besicovitch.ae_tendsto_rnDeriv ν l).and (Measure.rnDeriv_lt_top ν l)))
    have hxr := hx x (mem_ball_zero_iff.1 hxmem)
    refine ⟨_, hxfin, ofReal_pow_mul_le_liminf_ball_ratio l ν (by linarith) hxD ?_,
      limsup_ball_ratio_le_ofReal_pow_mul l ν (by linarith) hxD ?_⟩
    · filter_upwards [hxr, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
      exact (measure_mono (Metric.closedBall_subset_ball (by nlinarith))).trans hr.1
    · filter_upwards [hxr] with r hr
      exact hr.2.trans (measure_mono Metric.ball_subset_closedBall)
  have hML : liminf ρ (𝓝[>] 0) ≤ limsup ρ (𝓝[>] 0) := liminf_le_limsup
  have hLtop : limsup ρ (𝓝[>] 0) < ⊤ := by
    obtain ⟨D, hD, -, hup⟩ := key (1 / 4) (by norm_num) (by norm_num)
    exact hup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD)
  have hLM : limsup ρ (𝓝[>] 0) ≤ liminf ρ (𝓝[>] 0) := by
    have hK : Tendsto (fun ε : ℝ => ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V))
        (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt (fun ε : ℝ =>
          ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V)) 0 :=
        ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by simp)
      simpa using hc.tendsto
    have hT : Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) * liminf ρ (𝓝[>] 0))
        (𝓝[>] 0) (𝓝 (liminf ρ (𝓝[>] 0))) := by
      have h1 := ENNReal.Tendsto.mul_const (b := liminf ρ (𝓝[>] 0)) (ENNReal.tendsto_ofReal hK)
        (Or.inr (hML.trans_lt hLtop).ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    obtain ⟨D, -, hlow, hup⟩ := key ε hε.1 hε.2
    have hb : 0 < (1 - 2 * ε) ^ Module.finrank ℝ V := pow_pos (by linarith [hε.2]) _
    refine hup.trans ?_
    calc ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D
        = ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) *
          (ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (by linarith [hε.1]) _) hb.le),
            div_mul_cancel₀ _ hb.ne']
      _ ≤ _ := by gcongr
  have htend : Tendsto ρ (𝓝[>] 0) (𝓝 (limsup ρ (𝓝[>] 0))) :=
    tendsto_of_liminf_eq_limsup (le_antisymm hML hLM) rfl
  refine ⟨limsup ρ (𝓝[>] 0), ?_, hLtop.ne, htend⟩
  intro hL0
  rw [hL0] at htend
  obtain ⟨δ, hδ, hx⟩ := halmost (1 / 2) (by norm_num) (by norm_num)
  have hs_le : ∀ t : NNReal, 0 < t → ν (Metric.ball 0 δ) ≤ t * l (Metric.ball 0 δ) := by
    intro t ht
    have hle := VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily ν) (t • l)
      (Measure.AbsolutelyContinuous.refl ν) (Metric.ball (0 : V) δ) ?_
    · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hle
      exact hle
    intro x hxs
    apply ((Besicovitch.tendsto_filterAt ν x).comp
      (_root_.GlobalTheory.densHom_tendsto_mul (show (0 : ℝ) < 1 / 4 by norm_num))).frequently
    refine Filter.Eventually.frequently ?_
    have hpos' : (0 : ENNReal) < t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) :=
      ENNReal.mul_pos (by exact_mod_cast ht.ne') (ENNReal.ofReal_pos.2 (by positivity)).ne'
    filter_upwards [(tendsto_order.1 htend).2 _ hpos', hx x (mem_ball_zero_iff.1 hxs),
      self_mem_nhdsWithin] with r hr hxr (hr0 : 0 < r)
    show ν (Metric.closedBall x (1 / 4 * r)) ≤ (t • l) (Metric.closedBall x (1 / 4 * r))
    have hlt : ν (Metric.ball 0 r) <
        t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) * l (Metric.ball 0 r) :=
      (ENNReal.div_lt_iff (Or.inl (Metric.measure_ball_pos l 0 hr0).ne')
        (Or.inl measure_ball_lt_top.ne)).1 hr
    rw [mul_assoc, ← _root_.GlobalTheory.densHom_scale l x (by norm_num) hr0] at hlt
    have hsub : Metric.closedBall x (1 / 4 * r) ⊆ Metric.ball x ((1 - 1 / 2) * r) :=
      Metric.closedBall_subset_ball (by linarith)
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((measure_mono hsub).trans hxr.1).trans hlt.le
  have hzero : ν (Metric.ball 0 δ) = 0 := by
    have hT : Tendsto (fun t : NNReal => (t : ENNReal) * l (Metric.ball 0 δ)) (𝓝[>] 0) (𝓝 0) := by
      have h1 := ENNReal.Tendsto.mul_const (b := l (Metric.ball 0 δ))
        (ENNReal.tendsto_coe.2 (tendsto_id (x := 𝓝 (0 : NNReal)))) (Or.inr measure_ball_lt_top.ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    exact le_antisymm (ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun t ht => hs_le t ht))
      bot_le
  exact hpos δ hδ hzero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHorizontalPrimeLeOfIsMaximal
section
namespace GlobalTheory

theorem exists_intCast_mem_of_isMaximal (R : Type*) [CommRing R] [Algebra.FiniteType ℤ R]
    (m : Ideal R) [m.IsMaximal] : ∃ p : ℤ, p ≠ 0 ∧ algebraMap ℤ R p ∈ m := by
  let := Ideal.Quotient.field m
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ _
  by_contra h
  push Not at h
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ m)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    apply h a ha0
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using ha
  have hF : IsField ℤ :=
    (Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (R ⧸ m))
  exact Int.not_isField hF

theorem exists_horizontal_prime_le_of_isMaximal :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [CharZero R] (𝔪 : Ideal R),
      𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ q : Ideal R, q.IsPrime ∧ q ≤ 𝔪 ∧ g ∉ q ∧
        CharZero (R ⧸ q) ∧ Algebra.IsAlgebraic ℤ (R ⧸ q) := by
  intro R _ _ _ _ m hm g hg
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨p₀, hp₀, hp₀m⟩ := exists_intCast_mem_of_isMaximal R m
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal (m.comap (algebraMap ℤ R))).principal
  have hp' : m.comap (algebraMap ℤ R) = Ideal.span {p} := hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    have : p₀ ∈ m.comap (algebraMap ℤ R) := hp₀m
    rw [hp'] at this
    exact hp₀ (by simpa using this)
  have hpprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp']
    infer_instance
  have hpm : algebraMap ℤ R p ∈ m := by
    have : p ∈ m.comap (algebraMap ℤ R) := hp' ▸ Ideal.mem_span_singleton_self p
    exact this
  set x : R := algebraMap ℤ R p * g with hx
  have hx0 : x ≠ 0 := mul_ne_zero (by simpa using hp0) hg
  obtain ⟨q, ⟨hqp, hqm, hxq⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ q ≤ m ∧ x ∉ q}
    ⟨⊥, Ideal.isPrime_bot, bot_le, by simpa using hx0⟩
  change Ideal R at q
  have hpq : algebraMap ℤ R p ∉ q := fun h => hxq (q.mul_mem_right _ h)
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ q)) := by
    have hq' : (q.comap (algebraMap ℤ R)).IsPrime := inferInstance
    have hbot : q.comap (algebraMap ℤ R) = ⊥ := by
      by_contra hne
      have hM : (q.comap (algebraMap ℤ R)).IsMaximal := IsPrime.to_maximal_ideal hne
      have := hM.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.comap_mono (f := algebraMap ℤ R) hqm)
      apply hpq
      have h2 : p ∈ q.comap (algebraMap ℤ R) := this ▸ hpm
      exact h2
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ q.comap (algebraMap ℤ R) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      simpa using ha
    rwa [hbot, Ideal.mem_bot] at this
  have hsurj := Ideal.Quotient.mk_surjective (I := q)
  refine ⟨q, hqp, hqm, fun h => hxq (q.mul_mem_left _ h), charZero_of_injective_algebraMap hinj, ?_⟩
  have hm' : (m.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have hcm : (m.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have h1 : (m.map (Ideal.Quotient.mk q)).height ≤ 1 := by
    refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q x)
      (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq) ?_
    intro P hP hP0 hPm
    by_contra hxP
    refine hmax (P.comap (Ideal.Quotient.mk q)) ⟨inferInstance, ?_, hxP⟩ ?_
    · exact hcm ▸ Ideal.comap_mono hPm
    · refine lt_of_le_of_ne ?_ ?_
      · intro a ha
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        exact P.zero_mem
      · intro e
        apply hP0
        rw [eq_bot_iff]
        intro b hb
        obtain ⟨a, rfl⟩ := hsurj b
        have : a ∈ q := e ▸ hb
        exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  have : Algebra.QuasiFiniteAt ℤ (m.map (Ideal.Quotient.mk q)) :=
    quasiFiniteAt_of_height_le_one _ h1 p (fun e => hp0 (hinj (by simpa using e)))
      (Ideal.mem_map_of_mem _ hpm)
  have : FaithfulSMul ℤ (R ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact isAlgebraic_of_quasiFiniteAt ℤ (R ⧸ q) (m.map (Ideal.Quotient.mk q))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaLebesgueMeasure
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.OmegaLebExists

theorem J_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [fromBlocks_conjTranspose]
  simp

end GlobalTheory.OmegaLebExists
end
end

