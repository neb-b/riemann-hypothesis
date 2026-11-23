module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0013
public import Lemmata.GeneralBFactBisForm.Imports

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FiniteTranslateSets
section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace FiniteTranslateSets

open NumberField Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Sh (R : ℝ) : Set E :=
  {β | ∃ α : 𝓞 E, (α : E) = (X.den : E) * β ∧ ∀ σ : E →+* ℂ, ‖σ (α : E)‖ ≤ R}

theorem Sh_finite (R : ℝ) (hR : 0 ≤ R) : (Sh X R).Finite := by
  have hS := NumberField.Embeddings.finite_of_norm_le E ℂ R
  have hd : ((X.den : 𝓞 E) : E) ≠ 0 := by exact_mod_cast X.den_ne
  refine (hS.image fun x => x / (X.den : E)).subset ?_
  rintro β ⟨α, hα, hb⟩
  refine ⟨(α : E), ⟨α.isIntegral_coe, hb⟩, ?_⟩
  show (α : E) / (X.den : E) = β
  rw [hα]
  field_simp

def Sz (T : ℝ) : Set ℤ := {n | ((n : ℝ)) ^ 2 ≤ T}

theorem Sz_finite (T : ℝ) : (Sz T).Finite := by
  refine (Set.finite_Icc (-⌈T⌉) ⌈T⌉).subset ?_
  intro n hn
  have hn' : ((n : ℝ)) ^ 2 ≤ T := hn
  have h1 : |n| ≤ n ^ 2 := by
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · have h0 : 1 ≤ |n| := Int.one_le_abs h
      nlinarith [abs_mul_abs_self n, abs_nonneg n]
  have h2 : ((|n| : ℤ) : ℝ) ≤ T := by
    have h4 : ((|n| : ℤ) : ℝ) ≤ ((n ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h4 ⊢
    linarith
  have h3 : |n| ≤ ⌈T⌉ := by exact_mod_cast h2.trans (Int.le_ceil T)
  exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le n], by linarith [le_abs_self n]⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def TS (R T : ℝ) : Set ((ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ)) :=
  {t | ∃ f : Basis ι ℤ X.Λ, ((∀ i j, (HermitianLatticeMaps.ty X f).1 i j ∈ Sh X R) ∧
    ∀ k i j, (HermitianLatticeMaps.ty X f).2 k i j ∈ Sz T) ∧ HermitianLatticeMaps.ty X f = t}

theorem TS_finite (R T : ℝ) (hR : 0 ≤ R) : (TS X (ι := ι) R T).Finite := by
  have hA : (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Sh X R).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Sh_finite X R hR
  have hB : (Set.univ.pi fun _ : Free.ChooseBasisIndex ℤ (𝓞 E) =>
      Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Sz T).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => Sz_finite T
  refine (hA.prod hB).subset ?_
  rintro t ⟨f, ⟨h1, h2⟩, rfl⟩
  exact ⟨fun i _ j _ => h1 i j, fun k _ i _ j _ => h2 k i j⟩

end FiniteTranslateSets

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMajorantFlags
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem Hf_sub_left (x : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf x τ (u - v) w = X.Hf x τ u w - X.Hf x τ v w := by
  simp only [Data.Hf_eq_jp, Data.jp_sub, hermC_sub_left]

theorem Hf_smul_left (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (k • u) w = k * X.Hf x τ u w := by
  simp only [Data.Hf_eq_jp, Data.jp_smul, hermC_smul_left]

theorem Hf_smul_right (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ u (k • w) = conj k * X.Hf x τ u w := by
  simp only [Data.Hf_eq_jp, hermC_smul_right]

theorem maj_smul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((k : ℂ) • v) = k ^ 2 * X.maj x τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hx τ, Hf_smul_left, Hf_smul_right, X.Hf_self hx τ, Complex.conj_ofReal]
  push_cast; ring

theorem ppos_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.ppos z' τ v = X.ppos z τ v := by
  have hspan := hf τ
  have hmem : X.ppos z τ v ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z' τ) (Fin.castLE X.p0_le a)) := by
    rw [← hspan]
    unfold Data.ppos
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  rw [← hβ]
  apply X.ppos_eq_of z' τ (X.gramPos_det_ne hz' τ) v β
  intro b
  rw [hβ]
  have hb : col (mat z' τ) (Fin.castLE X.p0_le b) ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z τ) (Fin.castLE X.p0_le a)) := by
    rw [hspan]; exact Submodule.subset_span ⟨b, rfl⟩
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hb
  rw [← hγ, hermC_sum_right]
  exact Finset.sum_eq_zero fun a _ => by
    rw [hermC_smul_right, X.ppos_orth z τ (X.gramPos_det_ne hz τ) v a, mul_zero]

theorem Hf_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (u w : Fin r → ℂ) : X.Hf z' τ u w = X.Hf z τ u w := by
  simp only [Data.Hf, ppos_flag X hz hz' hf]

theorem maj_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj z' τ v = X.maj z τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hz' τ, ← X.Hf_self hz τ, Hf_flag X hz hz' hf]

theorem flowMatV_mulVec (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMatV e τ s) v = v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v e) • e := by
  funext a
  simp only [Data.flowMatV, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ppos_flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.ppos (X.flowV e s z) τ v = X.ppos z τ v := by
  have hcol : ∀ a, col (mat (X.flowV e s z) τ) a =
      Matrix.mulVec (X.flowMatV (e τ) τ (s τ)) (col (mat z τ) a) :=
    fun a => Data.col_mul (X.flowMatV (e τ) τ (s τ)) (mat z τ) a
  have hT := flowMatV_mulVec X (e τ) τ (s τ)
  set β : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos z τ)⁻¹ b a with hβ
  have hp : X.ppos z τ v = ∑ a, β a • col (mat z τ) (Fin.castLE X.p0_le a) := rfl
  have hcoef : ∑ a, β a * (-(I * X.c τ * s τ) *
      hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) = 0 := by
    have : ∑ a, β a * (-(I * X.c τ * s τ) *
        hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) =
        -(I * X.c τ * s τ) * hermC τ.1 X.Gm (X.ppos z τ v) (e τ) := by
      rw [hp, hermC_sum_left, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hermC_smul_left]; ring
    rw [this, hpe, mul_zero]
  have hsum : ∑ a, β a • col (mat (X.flowV e s z) τ) (Fin.castLE X.p0_le a) = X.ppos z τ v := by
    simp only [hcol, hT, smul_add, Finset.sum_add_distrib, smul_smul]
    rw [← hp, ← Finset.sum_smul, hcoef, zero_smul, add_zero]
  rw [← hsum]
  apply X.ppos_eq_of _ τ (X.gramPos_det_ne hTz τ) v β
  intro b
  rw [hsum, hcol, hT, hermC_add_right, hermC_smul_right,
    X.ppos_orth z τ (X.gramPos_det_ne hz τ) v b, zero_add, hermC_sub_left, hve, hpe, sub_zero,
    mul_zero]

theorem maj_flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.maj (X.flowV e s z) τ v = X.maj z τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hTz τ, ← X.Hf_self hz τ]
  simp only [Data.Hf, ppos_flowV X e s hz hTz τ v hve hpe]

theorem hpe_of {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v e : Fin r → ℂ)
    (hH : X.Hf z τ e v = 0) (hh : hermC τ.1 X.Gm e v = 0) :
    hermC τ.1 X.Gm (X.ppos z τ v) e = 0 := by
  have h1 : hermC τ.1 X.Gm (X.ppos z τ e) v = 0 := by
    rw [Data.Hf_eq_two_ppos, hh, sub_zero] at hH
    simpa using hH
  rw [X.ppos_selfadj hz, ← hermC_conj τ.1 X.Gm_herm, h1, map_zero]

end ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology

noncomputable section

section Cauchy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma norm_fderiv_le {U : Set F} (hU : IsOpen U) {G : F → ℂ} (hG : DifferentiableOn ℂ G U)
    {y : F} {R C : ℝ} (hR : 0 < R) (hball : closedBall y R ⊆ U)
    (hC : ∀ z ∈ closedBall y R, ‖G z‖ ≤ C) : ‖fderiv ℂ G y‖ ≤ C / R := by
  first | exact Bl.general_b_fact_bis_form.goal1 .. | (apply Bl.general_b_fact_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_form.goal1 <;> assumption)

end Cauchy

section Param

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ}

theorem diffOn_param {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKm : MeasurableSet K)
    (A : (Fin n → ℝ) → F →L[ℂ] F) (hA : Continuous A) {U : Set F} (hU : IsOpen U)
    (hAU : ∀ t ∈ K, ∀ x ∈ U, A t x ∈ U) (G : F → ℂ) (hG : DifferentiableOn ℂ G U)
    (e : (Fin n → ℝ) → ℂ) (he : Continuous e) :
    DifferentiableOn ℂ (fun x => ∫ t in K, G (A t x) * e t) U := by
  intro x0 hx0
  have hcA : ∀ x, Continuous fun t => A t x := fun x => hA.clm_apply continuous_const
  set K0 := (fun t => A t x0) '' K with hK0def
  have hK0 : IsCompact K0 := hK.image (hcA x0)
  have hK0U : K0 ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact hAU t ht x0 hx0
  obtain ⟨δ, hδ, hδU⟩ := hK0.exists_cthickening_subset_open hU hK0U
  have hK1 : IsCompact (cthickening δ K0) := hK0.cthickening
  obtain ⟨C, hC⟩ := hK1.exists_bound_of_continuousOn (hG.continuousOn.mono hδU)
  obtain ⟨Am, hAm⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨Me, hMe⟩ := hK.exists_bound_of_continuousOn he.continuousOn
  set A1 := max Am 1 with hA1def
  have hA1 : 0 < A1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε := δ / 2 / A1 with hεdef
  have hε : 0 < ε := by positivity
  have hnear : ∀ t ∈ K, ∀ x ∈ ball x0 ε, closedBall (A t x) (δ / 2) ⊆ cthickening δ K0 := by
    intro t ht x hx z hz
    have hx' : ‖x - x0‖ < ε := by rw [← dist_eq_norm]; exact hx
    have h1 : dist (A t x) (A t x0) ≤ δ / 2 := by
      rw [dist_eq_norm, ← map_sub]
      calc ‖A t (x - x0)‖ ≤ ‖A t‖ * ‖x - x0‖ := (A t).le_opNorm _
        _ ≤ A1 * ε := mul_le_mul (le_trans (hAm t ht) (le_max_left _ _)) hx'.le (norm_nonneg _) hA1.le
        _ = δ / 2 := by rw [hεdef]; field_simp
    have h2 : dist z (A t x0) ≤ δ := by
      linarith [dist_triangle z (A t x) (A t x0), mem_closedBall.1 hz]
    exact mem_cthickening_of_dist_le z (A t x0) δ K0 ⟨t, ht, rfl⟩ h2
  have hin : ∀ t ∈ K, ∀ x ∈ ball x0 ε, A t x ∈ U := fun t ht x hx =>
    hδU (hnear t ht x hx (mem_closedBall_self (by positivity)))
  have hfd : ∀ t ∈ K, ∀ x ∈ ball x0 ε, ‖fderiv ℂ G (A t x)‖ ≤ C / (δ / 2) := fun t ht x hx =>
    norm_fderiv_le hU hG (by positivity) ((hnear t ht x hx).trans hδU)
      (fun z hz => hC z (hnear t ht x hx hz))
  have hball : ball x0 ε ∈ 𝓝 x0 := ball_mem_nhds x0 hε
  have hcont : ∀ x ∈ ball x0 ε, ContinuousOn (fun t => G (A t x) * e t) K := fun x hx =>
    (hG.continuousOn.comp (hcA x).continuousOn (fun t ht => hin t ht x hx)).mul he.continuousOn
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have m1 : Measurable fun t => fderiv ℂ G (A t x0) := (measurable_fderiv ℂ G).comp (hcA x0).measurable
  have m2 : Measurable fun t => (fderiv ℂ G (A t x0)).comp (A t) :=
    (isBoundedBilinearMap_comp.continuous.measurable).comp (m1.prodMk hA.measurable)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K)
    (F := fun x t => G (A t x) * e t)
    (F' := fun x t => e t • (fderiv ℂ G (A t x)).comp (A t))
    (bound := fun _ => Me * (C / (δ / 2) * A1)) hball
    (by filter_upwards [hball] with x hx; exact (hcont x hx).aestronglyMeasurable hKm)
    ((hcont x0 (mem_ball_self hε)).integrableOn_compact hK)
    ((he.measurable.smul m2).aestronglyMeasurable)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      calc ‖e t • (fderiv ℂ G (A t x)).comp (A t)‖
          = ‖e t‖ * ‖(fderiv ℂ G (A t x)).comp (A t)‖ := norm_smul _ _
        _ ≤ Me * (C / (δ / 2) * A1) := by
          refine mul_le_mul (hMe t ht) ?_ (norm_nonneg _) (le_trans (norm_nonneg _) (hMe t ht))
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hfd t ht x hx)
            (le_trans (hAm t ht) (le_max_left _ _)) (norm_nonneg _)
            (le_trans (norm_nonneg _) (hfd t ht x hx)))))
    (integrable_const _)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      have h1 : HasFDerivAt G (fderiv ℂ G (A t x)) (A t x) :=
        (hG.differentiableAt (hU.mem_nhds (hin t ht x hx))).hasFDerivAt
      exact (h1.comp x (A t).hasFDerivAt).mul_const (e t)))
  exact key.differentiableAt.differentiableWithinAt

end Param

section Dom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)

lemma cont_gram (τ : X.Ψ) : Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

lemma isOpen_dom : IsOpen X.dom := by
  have h : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x; simp [Data.dom, GG]
  rw [h]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det
      continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp
      ((cont_gram X τ).matrix_submatrix _ _).matrix_det))

def ZbL (b : X.Ψ → Fin 2 → Fin 2 → ℂ) : Frame X.Ψ r →L[ℂ] Frame X.Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := X.Zb u b
      map_add' x y := by
        funext τ
        show X.zmat u b τ * (mat x τ + mat y τ) = _
        rw [Matrix.mul_add]; rfl
      map_smul' c x := by
        funext τ
        show X.zmat u b τ * (c • mat x τ) = _
        rw [Matrix.mul_smul]; rfl }

lemma cont_Zb {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) (y : Frame X.Ψ r) : Continuous fun t => X.Zb u (B t) y := by
  have hB' : ∀ τ i k, Continuous fun t => B t τ i k := fun τ i k => by fun_prop
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
  simp only [Data.Zb, Data.zmat, Matrix.mul_apply, Matrix.of_apply, mat]
  fun_prop

lemma cont_ZbL {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) : Continuous fun t => ZbL X u (B t) :=
  continuous_clm_apply.2 fun y => cont_Zb X u hB y

end Dom

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HolomorphicPeriodicityExtension
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex Filter Topology

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem d4l4_c_pos {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  show 0 < 2 * ‖τ.1 X.ξ0‖
  exact mul_pos two_pos (norm_pos_iff.mpr h)

open Classical in
theorem d4l4_diff_flow {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (x : Frame X.Ψ r)
    (s : X.Ψ → ℂ) (τ0 : X.Ψ) :
    Differentiable ℂ (fun z : ℂ => X.flowV e (Function.update s τ0 z) x) := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hu : Differentiable ℂ (fun z : ℂ => Function.update s τ0 z τ) := by
    by_cases h : τ = τ0
    · subst h
      simpa using differentiable_id
    · simpa [Function.update_of_ne h] using differentiable_const (s τ)
  intro z
  simp only [Data.flowV, Matrix.mul_apply, Data.flowMatV, Matrix.of_apply, mat]
  refine DifferentiableAt.fun_sum fun k _ => ?_
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_mul
  exact hu z

theorem holomorphic_periodicity_extension : HolomorphicPeriodicityExtension (E := E) := by
  classical
  intro r X e he G hG m x hx hreal s hs
  have hdom : ∀ s' : X.Ψ → ℂ, X.flowV e s' x ∈ X.dom ↔ ∀ τ, 0 < 1 + (s' τ).im / X.ttV e x τ :=
    fun s' => (flowDomainCriterion_holds (E := E) r X e he x hx s').1
  set H : (X.Ψ → ℂ) → ℂ := fun s' =>
    G (X.flowV e s' x) - cexp (4 * Real.pi * I * ∑ τ, m τ * s' τ) * G x with hH

  suffices key : ∀ A : Finset X.Ψ, ∀ s' : X.Ψ → ℂ, (∀ τ ∉ A, (s' τ).im = 0) →
      X.flowV e s' x ∈ X.dom → H s' = 0 by
    exact sub_eq_zero.mp (key Finset.univ s (fun τ h => absurd (Finset.mem_univ τ) h) hs)
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro s' hs' _
    have hre : ∀ τ, (((s' τ).re : ℝ) : ℂ) = s' τ := fun τ =>
      Complex.ext (by simp) (by simp [hs' τ (by simp)])
    have h0 := hreal (fun τ => (s' τ).re)
    simp only [hre] at h0
    simp only [hH, h0, sub_self]
  | insert τ0 A hτ0 ih =>
    intro s' hs' hdom'
    have hcond := (hdom s').mp hdom'
    set V : Set ℂ := {z | 0 < 1 + z.im / X.ttV e x τ0} with hVdef
    have hVo : IsOpen V := isOpen_lt continuous_const (by fun_prop)
    have hVc : Convex ℝ V := by
      intro z hz w hw a b ha hb hab
      simp only [hVdef, Set.mem_setOf_eq] at hz hw ⊢
      have him : (a • z + b • w).im = a * z.im + b * w.im := by simp
      have h1 : 1 + (a * z.im + b * w.im) / X.ttV e x τ0 =
          a * (1 + z.im / X.ttV e x τ0) + b * (1 + w.im / X.ttV e x τ0) := by
        linear_combination (-1 : ℝ) * hab
      rw [him, h1]
      rcases ha.lt_or_eq with ha' | ha'
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hz) (mul_nonneg hb hw.le)
      · have hb1 : b = 1 := by linarith
        rw [← ha', hb1]
        simpa using hw
    have hreal0 : ∀ y : ℝ, (y : ℂ) ∈ V := by intro y; simp [hVdef]
    have hmaps : ∀ z ∈ V, X.flowV e (Function.update s' τ0 z) x ∈ X.dom := by
      intro z hz
      rw [hdom]
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa [hVdef] using hz
      · simpa [Function.update_of_ne h] using hcond τ
    have hu : ∀ τ, Differentiable ℂ (fun z : ℂ => Function.update s' τ0 z τ) := by
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa using differentiable_id
      · simpa [Function.update_of_ne h] using differentiable_const (s' τ)
    have hdiff : DifferentiableOn ℂ (fun z => H (Function.update s' τ0 z)) V := by
      have h1 : DifferentiableOn ℂ (fun z => G (X.flowV e (Function.update s' τ0 z) x)) V :=
        hG.comp (d4l4_diff_flow X e x s' τ0).differentiableOn (fun z hz => hmaps z hz)
      have hsum : Differentiable ℂ (fun z : ℂ => ∑ τ, m τ * Function.update s' τ0 z τ) := by
        intro z
        exact DifferentiableAt.fun_sum fun τ _ => ((hu τ) z).const_mul (m τ)
      have h2 : Differentiable ℂ (fun z : ℂ =>
          cexp (4 * Real.pi * I * ∑ τ, m τ * Function.update s' τ0 z τ) * G x) :=
        ((hsum.const_mul (4 * Real.pi * I)).cexp).mul_const (G x)
      exact h1.sub h2.differentiableOn
    have han : AnalyticOnNhd ℂ (fun z => H (Function.update s' τ0 z)) V :=
      hdiff.analyticOnNhd hVo

    have hzero_real : ∀ y : ℝ, H (Function.update s' τ0 (y : ℂ)) = 0 := by
      intro y
      apply ih
      · intro τ hτ
        by_cases h : τ = τ0
        · subst h
          simp
        · rw [Function.update_of_ne h]
          exact hs' τ (by simp [h, hτ])
      · exact hmaps _ (hreal0 y)
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), H (Function.update s' τ0 z) = 0 := by
      have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
        have h3 := Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
          (s := {(0 : ℝ)}ᶜ) (t := {(0 : ℂ)}ᶜ) (x := 0) (fun y hy => by simpa using hy)
        rwa [Complex.ofReal_zero] at h3
      exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero_real))
    have h0V : (0 : ℂ) ∈ V := by simp [hVdef]
    have hEq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hVc.isPreconnected h0V hfreq
    have h4 := hEq (hcond τ0)
    simpa using h4

end ReciprocityTheory.ChartRestriction.G.FD
end

