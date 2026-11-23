module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0006
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticIntersectionMultilinearPolar
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem combLine_intersection : MetricLocalStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ), IsArithVar P n → (∀ a, IsSmoothHerm (A a)) → (∀ r, IsSmoothHerm (combLine A (c r))) ∧ II K ι P n (fun r => combLine A (c r)) = polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) :=
  @PositivityTheory.Xgp.t_re_comb

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLatticeShiftNonzero
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem section_sub_degree : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (α : K → ℤ) (dβ : K → ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0) → ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1 - dβ κ) 1, e ≠ 0 :=
  @PositivityTheory.Xgp.t_pol_sec

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetric
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem exists_conjInvariant_line_averaged : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 :=
  @PositivityTheory.Xgp.t_line_conj

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousCuspNormFamily
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NzCont

section Emb

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)

def charVec (a : 𝓞 E) : (E →+* ℂ) → ℂ := fun s => s (algebraMap (𝓞 E) E a)

def toChar (s : E →+* ℂ) : 𝓞 E →* ℂ := (s.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ)

theorem toChar_injective : Function.Injective (toChar (E := E)) := by
  intro s s' h
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  exact DFunLike.congr_fun h a

theorem span_charVec : Submodule.span ℂ (Set.range (charVec (E := E))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ (toChar_injective (E := E))
  rw [Fintype.linearIndependent_iff] at li
  have hl := li (fun s => f fun j => if s = j then 1 else 0) (by
    funext a
    have h1 : f (charVec a) = 0 := hf (Submodule.subset_span ⟨a, rfl⟩)
    rw [LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, smul_eq_mul, Pi.zero_apply]
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_mul]
    exact mul_comm (_ : ℂ) _)
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ f v, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun s _ => (congrArg (v s • ·) (hl s)).trans (smul_zero _)


open Classical in
theorem exists_coeff (s : E →+* ℂ) : ∃ c : 𝓞 E →₀ ℂ, ∀ s' : E →+* ℂ,
    ∑ a ∈ c.support, c a * s' (algebraMap (𝓞 E) E a) = if s' = s then 1 else 0 := by
  have h : (Pi.single s 1 : (E →+* ℂ) → ℂ) ∈ Submodule.span ℂ (Set.range (charVec (E := E))) := by
    rw [span_charVec]
    trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h
  refine ⟨c, fun s' => ?_⟩
  have h2 := congrFun hc s'
  simpa [Finsupp.sum, Finset.sum_apply, charVec, Pi.single_apply] using h2

end Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem mem_eigSp_iff (R : RiemLat E g Λ) {s : 𝓞 E →+* ℂ} {x : Fin g → ℂ} :
    x ∈ eigSp R.B s ↔ ∀ a, R.B a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]


open Classical in
theorem eigComp_eq (R : RiemLat E g Λ) (s : E →+* ℂ) (c : 𝓞 E →₀ ℂ)
    (hc : ∀ s' : E →+* ℂ, ∑ a ∈ c.support, c a * s' (algebraMap (𝓞 E) E a) = if s' = s then 1 else 0)
    (u : Λ) :
    eigComp R.B (s.comp (algebraMap (𝓞 E) E)) (R.P u) = ∑ a ∈ c.support, c a • R.P (a • u) := by
  obtain ⟨-, -, h3, h4, -⟩ := _root_.LevelTowerAlt.riemann_lattice_eigen_projections E g Λ Unit R
  have hy : ∀ a : 𝓞 E, R.P (a • u) = ∑ s' : E →+* ℂ, s' (algebraMap (𝓞 E) E a) •
      eigComp R.B (s'.comp (algebraMap (𝓞 E) E)) (R.P u) := by
    intro a
    rw [R.act]
    conv_lhs => rw [← h4 (R.P u)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    exact (mem_eigSp_iff R).1 ((h3 _).1 _) a
  simp_rw [hy, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hc]
  simp [ite_smul]

variable {X : Type} [TopologicalSpace X]

theorem continuous_eigComp (R : X → RiemLat E g Λ) (hP : ∀ v, Continuous fun x => (R x).P v)
    (s : 𝓞 E →+* ℂ) (u : Λ) : Continuous fun x => eigComp (R x).B s ((R x).P u) := by
  classical
  obtain ⟨c, hc⟩ := exists_coeff (extEmb s)
  have h : ∀ x, eigComp (R x).B s ((R x).P u) = ∑ a ∈ c.support, c a • (R x).P (a • u) := by
    intro x
    have h1 := eigComp_eq (R x) (extEmb s) c hc u
    rwa [extEmb_comp] at h1
  simp_rw [h]
  exact continuous_finsetSum _ fun a _ => (hP (a • u)).const_smul (c a)

theorem continuous_ip (R : X → RiemLat E g Λ) (hH : Continuous fun x => (R x).Hm) {p q : X → Fin g → ℂ}
    (hp : Continuous p) (hq : Continuous q) : Continuous fun x => (R x).ip (p x) (q x) := by
  unfold RiemLat.ip
  exact hq.dotProduct (hH.matrix_mulVec (continuous_star.comp hp))

theorem continuous_nzOf {Ψ : Type} [Fintype Ψ] (R : X → RiemLat E g Λ)
    (hP : ∀ v, Continuous fun x => (R x).P v) (hH : Continuous fun x => (R x).Hm)
    (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) {r : ℕ} (v : Fin r → Λ) :
    Continuous fun x => (R x).nzOf σ I v := by
  unfold RiemLat.nzOf
  refine Continuous.div_const (continuous_finsetProd _ fun τ _ => ?_) _
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_matrix fun a b => ?_
  exact continuous_ip R hH (continuous_eigComp R hP _ _) (continuous_eigComp R hP _ _)

theorem continuous_nz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ)
    (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), (∀ v, Continuous fun x => (R x).P v) →
    (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ I hP hH
  by_cases h : ∃ r v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsNzFamily I r v
  · have e : (fun x => (R x).nz σ I) = fun x => (R x).nzOf σ I h.choose_spec.choose := by
      funext x
      simp only [RiemLat.nz, dif_pos h]
    rw [e]
    exact continuous_nzOf R hP hH σ I _
  · have e : (fun x => (R x).nz σ I) = fun _ => 1 := by
      funext x
      simp only [RiemLat.nz, dif_neg h]
    rw [e]
    exact continuous_const

end GlobalTheory.CompanionTheory.Ar.Cusp.NzCont
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousFirstMinimumFamily
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin

theorem sInf_range_le_mul {S : Type} [Nonempty S] (f h : S → ℝ) (hf : ∀ s, 0 ≤ f s) (c : ℝ) (hc : 0 < c)
    (hle : ∀ s, f s ≤ c * h s) : sInf (Set.range f) ≤ c * sInf (Set.range h) := by
  have hb : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨s, rfl⟩; exact hf s⟩
  have key : sInf (Set.range f) / c ≤ sInf (Set.range h) := by
    apply le_csInf (Set.range_nonempty h)
    rintro _ ⟨s, rfl⟩
    rw [div_le_iff₀' hc]
    exact (csInf_le hb ⟨s, rfl⟩).trans (hle s)
  rwa [div_le_iff₀' hc] at key

theorem eventually_form_comparison {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (Q : X → (ι → ℝ) → ℝ) (hQ : Continuous fun p : X × (ι → ℝ) => Q p.1 p.2)
    (hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a)
    (hpos : ∀ x a, a ≠ 0 → 0 < Q x a) (x₀ : X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ x in 𝓝 x₀, ∀ a, a ≠ 0 → (1 - δ) ^ 2 * Q x₀ a ≤ Q x a ∧ Q x a ≤ (1 + δ) ^ 2 * Q x₀ a := by
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere _ _
  have hQ0 : Continuous fun p : X × (ι → ℝ) => Q x₀ p.2 :=
    hQ.comp (continuous_const.prodMk continuous_snd)
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ a ∈ Metric.sphere (0 : ι → ℝ) 1,
      (1 - δ) ^ 2 * Q x₀ a < Q x a ∧ Q x a < (1 + δ) ^ 2 * Q x₀ a := by
    apply hK.eventually_forall_of_forall_eventually
    intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have hp := hpos x₀ a ha0
    have hl : (1 - δ) ^ 2 < 1 := by nlinarith
    have hu : 1 < (1 + δ) ^ 2 := by nlinarith
    have h1 : (1 - δ) ^ 2 * Q x₀ a < Q x₀ a := by nlinarith
    have h2 : Q x₀ a < (1 + δ) ^ 2 * Q x₀ a := by nlinarith
    exact ((isOpen_lt (continuous_const.mul hQ0) hQ).inter
      (isOpen_lt hQ (continuous_const.mul hQ0))).mem_nhds ⟨h1, h2⟩
  filter_upwards [hev] with x hx a ha
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hu : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hau : a = ‖a‖ • (‖a‖⁻¹ • a) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  obtain ⟨h1, h2⟩ := hx _ hu
  have hn2 : 0 < ‖a‖ ^ 2 := by positivity
  rw [hau, hhom x, hhom x₀]
  generalize ‖a‖⁻¹ • a = u at h1 h2
  constructor
  · nlinarith [mul_lt_mul_of_pos_left h1 hn2]
  · nlinarith [mul_lt_mul_of_pos_left h2 hn2]

theorem continuous_sInf_sqrt_form {X ι S : Type} [TopologicalSpace X] [Fintype ι]
    (Q : X → (ι → ℝ) → ℝ) (hQ : Continuous fun p : X × (ι → ℝ) => Q p.1 p.2)
    (hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a)
    (hpos : ∀ x a, a ≠ 0 → 0 < Q x a) (c : S → ι → ℝ) (hc : ∀ s, c s ≠ 0) :
    Continuous fun x => sInf (Set.range fun s => Real.sqrt (Q x (c s))) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp only [Set.range_eq_empty]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  set m := sInf (Set.range fun s => Real.sqrt (Q x₀ (c s))) with hm
  have hm0 : 0 ≤ m := Real.sInf_nonneg (by rintro _ ⟨s, rfl⟩; exact Real.sqrt_nonneg _)
  obtain ⟨δ, hδ, hδ1, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ * m < ε := by
    refine ⟨min (1 / 2) (ε / (2 * (m + 1))), by positivity, ?_, ?_⟩
    · exact (min_le_left _ _).trans_lt (by norm_num)
    · have h1 : min (1 / 2) (ε / (2 * (m + 1))) ≤ ε / (2 * (m + 1)) := min_le_right _ _
      have h2 : ε / (2 * (m + 1)) * m < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      exact (mul_le_mul_of_nonneg_right h1 hm0).trans_lt h2
  filter_upwards [eventually_form_comparison Q hQ hhom hpos x₀ δ hδ hδ1] with x hx
  have hlow : ∀ s, Real.sqrt (Q x₀ (c s)) ≤ (1 - δ)⁻¹ * Real.sqrt (Q x (c s)) := by
    intro s
    have h1 : 0 < 1 - δ := by linarith
    rw [inv_mul_eq_div, le_div_iff₀' h1]
    have := Real.sqrt_le_sqrt (hx _ (hc s)).1
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le] at this
  have hup : ∀ s, Real.sqrt (Q x (c s)) ≤ (1 + δ) * Real.sqrt (Q x₀ (c s)) := by
    intro s
    have h1 : 0 < 1 + δ := by linarith
    have := Real.sqrt_le_sqrt (hx _ (hc s)).2
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le] at this
  have hA := sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _
    (inv_pos.mpr (by linarith : 0 < 1 - δ)) hlow
  have hB := sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _ (by linarith : 0 < 1 + δ) hup
  rw [← hm] at hA hB
  set l := sInf (Set.range fun s => Real.sqrt (Q x (c s))) with hl
  have hA' : (1 - δ) * m ≤ l := by
    have h1 : 0 < 1 - δ := by linarith
    rw [inv_mul_eq_div, le_div_iff₀' h1] at hA
    exact hA
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem linearIndependent_periods (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) :
    LinearIndependent ℝ fun i => R.P (b i) := by
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (_root_.LevelTowerAlt.riemann_lattice_eigen_projections E g Λ Unit R).2.1
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => R.P (b i)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank htop ?_
  have h1 : Fintype.card ι = 2 * g := by
    rw [← R.rank, Module.finrank_eq_card_basis b]
  have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [h1, h2]

def comb (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : ι → Λ) (a : ι → ℝ) : Fin g → ℂ :=
  ∑ i, ((a i : ℝ) : ℂ) • R.P (b i)

theorem comb_repr (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) (v : Λ) :
    comb R b (fun i => ((b.repr v i : ℤ) : ℝ)) = R.P v := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← b.sum_repr v, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
  simp

theorem comb_ne_zero (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) (a : ι → ℝ)
    (ha : a ≠ 0) : comb R b a ≠ 0 := by
  intro h0
  apply ha
  have hli := linearIndependent_periods R b
  have h1 : ∑ i, a i • R.P (b i) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext j
    simp
  funext i
  exact Fintype.linearIndependent_iff.mp hli a h1 i

end GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin


open GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin in
theorem GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).lam1 := by
  intro E _ _ _ g Λ _ _ X _ R hP hH
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact continuous_of_const fun x => hX.elim x
  haveI := (R x₀).free
  haveI := (R x₀).fin
  let b := Module.Free.chooseBasis ℤ Λ
  let Q : X → (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) → ℝ := fun x a =>
    ((R x).ip (FirstMin.comb (R x) b a) (FirstMin.comb (R x) b a)).re
  have hL : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => FirstMin.comb (R p.1) b p.2 := by
    unfold FirstMin.comb
    refine continuous_finsetSum _ fun i _ => ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd)).smul
      ((hP (b i)).comp continuous_fst)
  have hQ : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => Q p.1 p.2 := by
    refine Complex.continuous_re.comp ?_
    exact hL.dotProduct ((hH.comp continuous_fst).matrix_mulVec hL.star)
  have hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a := by
    intro x r a
    have hc : FirstMin.comb (R x) b (r • a) = (r : ℂ) • FirstMin.comb (R x) b a := by
      unfold FirstMin.comb
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      simp
    simp only [Q, RiemLat.ip, hc, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [pow_two, mul_assoc]
  have hpos : ∀ x a, a ≠ 0 → 0 < Q x a := fun x a ha => (R x).pos _ (FirstMin.comb_ne_zero (R x) b a ha)
  have hmain := FirstMin.continuous_sInf_sqrt_form Q hQ hhom hpos
    (fun (s : {v : Λ // v ≠ 0}) i => ((b.repr s.1 i : ℤ) : ℝ)) (by
      intro s h0
      apply s.2
      apply b.repr.injective
      ext i
      have := congrFun h0 i
      simpa using this)
  convert hmain using 2 with x
  unfold RiemLat.lam1
  congr 1
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, hv⟩, ?_⟩
    simp only [Q, FirstMin.comb_repr, RiemLat.normSq]
  · rintro ⟨⟨v, hv⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    simp only [Q, FirstMin.comb_repr, RiemLat.normSq]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem degree_of_isIntersectionSystem (II : IntersectionSystem) (hII : IsIntersectionSystem II) :
    ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_iff_degree_statement.mp
    (GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_degree_form_of_existence ⟨II, hII⟩
      GroundTheory.Heights₂.Heights.Inter.Conservation.statement_holds)

theorem degree_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  fun ⟨II, hII⟩ => degree_of_isIntersectionSystem II hII.1

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBasisSubsetOfSaturatedSubmoduleStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_subset_of_saturated_submodule : ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : Submodule ℤ Λ), (∀ (v : Λ) (n : ℤ), n ≠ 0 → n • v ∈ N → v ∈ N) → ∃ (k n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n), Function.Injective f ∧ Submodule.span ℤ (Set.range fun i => b (f i)) = N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lattice.exists_basis_span_eq_of_saturated | exact GlobalTheory.CompanionTheory.Ar.Lattice.exists_basis_span_eq_of_saturated | (intros; apply GlobalTheory.CompanionTheory.Ar.Lattice.exists_basis_span_eq_of_saturated <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsDescendedRingHomOnQuotient
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.QuotUniv

theorem ringAction_descends_along_surjection
    (O : Type) [Ring O] (g g' : ℕ) (B : O →+* Module.End ℂ (Fin g → ℂ))
    (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hq : Function.Surjective q)
    (hk : ∀ (a : O) z, q z = 0 → q (B a z) = 0) :
    ∃ B' : O →+* Module.End ℂ (Fin g' → ℂ), ∀ a z, B' a (q z) = q (B a z) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqs : ∀ w, q (s w) = w := fun w => LinearMap.congr_fun hs w
  obtain ⟨F, hF⟩ : ∃ F : O → Module.End ℂ (Fin g' → ℂ), ∀ a z, F a (q z) = q (B a z) := by
    refine ⟨fun a => q ∘ₗ (B a ∘ₗ s), fun a z => ?_⟩
    have h0 : q (B a (s (q z) - z)) = 0 := hk a _ (by rw [map_sub, hqs, sub_self])
    rw [map_sub, map_sub, sub_eq_zero] at h0
    exact h0
  have hext : ∀ L M : Module.End ℂ (Fin g' → ℂ), (∀ z, L (q z) = M (q z)) → L = M := by
    intro L M h
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := hq w
    exact h z
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun a z => hF a z⟩
  · exact hext _ _ fun z => by simp [hF]
  · intro a b
    exact hext _ _ fun z => by simp [hF, Module.End.mul_apply]
  · exact hext _ _ fun z => by simp [hF]
  · intro a b
    exact hext _ _ fun z => by simp [hF]

end GlobalTheory.CompanionTheory.Ar.QuotUniv
end

