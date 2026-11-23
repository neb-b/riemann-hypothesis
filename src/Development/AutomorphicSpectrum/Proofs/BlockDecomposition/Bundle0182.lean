module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleOfFiniteEq
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped NumberField.AdeleRing nonZeroDivisors

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k]

theorem ideleModule_ofFinite_eq (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    (ideleModule k (ofFinite b) : ℝ) = finiteModule (ofFinite b) := by
  have h : infiniteModule (ofFinite b : IdeleGroup k) = 1 :=
    Finset.prod_eq_one fun w _ ↦ by
      rw [show ((ofFinite b : IdeleGroup k) : 𝔸[k]).1 w = 1 from rfl, norm_one, one_pow]
  rw [ideleModule_apply, h, one_mul]

theorem norm_le_one_of_mem_OH {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) (v : HeightOneSpectrum (𝓞 k)) :
    ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).1
      (mem_integralFiniteAdeles.1 hb v))

theorem finiteModule_le_one {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) : finiteModule (ofFinite b) ≤ 1 := by
  rw [finiteModule, finprod_eq_prod _ (finite_mulSupport_norm _)]
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦ norm_le_one_of_mem_OH hb v

theorem finiteModule_lt_one {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) (hu : b ∉ finiteIntegralUnits k) :
    finiteModule (ofFinite b) < 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 k), ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ < 1 := by
    by_contra hcon
    push_neg at hcon
    refine hu ((mem_finiteIntegralUnits k).2 fun v ↦ ⟨mem_integralFiniteAdeles.1 hb v, ?_⟩)
    have hv1 : ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ = 1 :=
      le_antisymm (norm_le_one_of_mem_OH hb v) (hcon v)
    have hmul : (b : FiniteAdeleRing (𝓞 k) k) v *
        ((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v = 1 :=
      congrArg (fun a : FiniteAdeleRing (𝓞 k) k ↦ a v) (Units.mul_inv b)
    have hn : ‖((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v‖ = 1 := by
      have := congrArg norm hmul
      rwa [norm_mul, hv1, one_mul, norm_one] at this
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).2
      ((Valued.toNormedField.norm_le_one_iff).1 hn.le)
  have hfin := finite_mulSupport_norm (ofFinite b : IdeleGroup k)
  have hvS : v ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
    exact hv.ne
  rw [finiteModule, finprod_eq_prod _ hfin, ← Finset.mul_prod_erase _ _ hvS]
  calc _ ≤ ‖((ofFinite b : IdeleGroup k) : 𝔸[k]).2 v‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun u _ ↦ norm_le_one_of_mem_OH hb u)
          (norm_nonneg _)
    _ < 1 := by rwa [mul_one]

def integrand (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k) (n : ℕ)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) : ℂ :=
  g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
    ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ (((n : ℝ) : ℝ) : ℂ)

theorem cpow_module_eq (b : (FiniteAdeleRing (𝓞 k) k)ˣ) (x : ℝ) :
    ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ (x : ℂ) = ((finiteModule (ofFinite b) ^ x : ℝ) : ℂ) := by
  rw [ideleModule_ofFinite_eq, Complex.ofReal_cpow (finiteModule_pos _).le]

theorem norm_integrand (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k) (n : ℕ)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    ‖integrand g ω n b‖ = ‖g fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)‖ *
      finiteModule (ofFinite b) ^ (n : ℝ) := by
  rw [integrand, cpow_module_eq, norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (finiteModule_pos _).le _)]

theorem continuous_integrand {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ}
    (hg : g ∈ GJMatrix.finiteSchwartzBruhatPi k) (ω : HeckeCharacter k) (n : ℕ) :
    Continuous (integrand g ω n) := by
  have h1 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦
      g fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k) :=
    ((GJMatrix.mem_finiteSchwartzBruhatPi k).1 hg).1.continuous.comp
      (continuous_pi fun _ ↦ Units.continuous_val)
  have h2 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ (ω.toIdele (ofFinite b) : ℂ) :=
    continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_ofFinite)
  have h3 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦
      ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      ((continuous_finiteModule.comp continuous_ofFinite).rpow_const
        fun b ↦ Or.inl (finiteModule_pos _).ne')
  have : integrand g ω n = fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) *
      (ω.toIdele (ofFinite b) : ℂ) * ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ) := by
    funext b
    rw [integrand, cpow_module_eq]
  rw [this]
  exact (h1.mul h2).mul h3

theorem norm_integrand_le {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ} (ω : HeckeCharacter k)
    (hb : ∀ t, ‖g fun _ ↦ t‖ ≤ 1 ∧ (g (fun _ ↦ t) ≠ 0 → t ∈ OH k)) {n : ℕ} (hn : 2 ≤ n)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    ‖integrand g ω n b‖ ≤ finiteZetaBound (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 2 b := by
  rw [norm_integrand]
  by_cases h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0
  · rw [h0, norm_zero, zero_mul]
    exact finiteZetaBound_nonneg _ _ _
  have hO := (hb _).2 h0
  have hL : (b : FiniteAdeleRing (𝓞 k) k) ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) := by
    rw [← SetLike.mem_coe, idealFiniteAdeles_one]
    exact hO
  rw [finiteZetaBound, if_pos hL]
  have hpow : finiteModule (ofFinite b) ^ (n : ℝ) ≤ finiteModule (ofFinite b) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (finiteModule_pos _) (finiteModule_le_one hO)
      (by exact_mod_cast hn)
  calc _ ≤ 1 * finiteModule (ofFinite b) ^ (n : ℝ) :=
        mul_le_mul_of_nonneg_right (hb _).1 (Real.rpow_nonneg (finiteModule_pos _).le _)
    _ ≤ _ := by rwa [one_mul]

theorem tendsto_integrand {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ} {ω : HeckeCharacter k}
    (hb : ∀ t, ‖g fun _ ↦ t‖ ≤ 1 ∧ (g (fun _ ↦ t) ≠ 0 → t ∈ OH k))
    (hu : ∀ u ∈ finiteIntegralUnits k,
      g (fun _ ↦ (u : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite u) : ℂ) = 1)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    Tendsto (fun n ↦ integrand g ω n b) atTop
      (𝓝 (((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
        Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b)) := by
  by_cases hW : b ∈ finiteIntegralUnits k
  · rw [Set.indicator_of_mem (SetLike.mem_coe.2 hW)]
    have hm : finiteModule (ofFinite b : IdeleGroup k) = 1 := finiteModule_eq_one_of_mem hW
    refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [integrand, cpow_module_eq, hu b hW, hm, Real.one_rpow, Complex.ofReal_one, one_mul]
  · rw [Set.indicator_of_notMem (fun h ↦ hW (SetLike.mem_coe.1 h))]
    by_cases h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0
    · refine tendsto_const_nhds.congr fun n ↦ ?_
      rw [integrand, h0, zero_mul, zero_mul]
    have hlt := finiteModule_lt_one ((hb _).2 h0) hW
    refine squeeze_zero_norm (a := fun n : ℕ ↦ finiteModule (ofFinite b) ^ n) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (finiteModule_pos _).le hlt)
    rw [norm_integrand, Real.rpow_natCast]
    calc _ ≤ 1 * finiteModule (ofFinite b) ^ n :=
          mul_le_mul_of_nonneg_right (hb _).1 (pow_nonneg (finiteModule_pos _).le _)
      _ = _ := one_mul _

theorem zFinLim : ZFinLim := by
  intro k _ _ g ω hg hb hu B
  have hlim : Tendsto (fun n : ℕ ↦ ∫ b, integrand g ω n b ∂finiteIdeleMeasure k) atTop
      (𝓝 (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
        Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k)) :=
    tendsto_integral_filter_of_dominated_convergence
      (finiteZetaBound (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 2)
      (Eventually.of_forall fun n ↦ (continuous_integrand hg ω n).aestronglyMeasurable)
      ((eventually_ge_atTop 2).mono fun n hn ↦ Eventually.of_forall (norm_integrand_le ω hb hn))
      (integrable_finiteZetaBound 1 (by norm_num))
      (Eventually.of_forall (tendsto_integrand hb hu))
  have hval : (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
      Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k) = 1 := by
    rw [integral_indicator_const _ (isOpen_finiteIntegralUnits k).measurableSet, Measure.real,
      finiteIdeleMeasure_finiteIntegralUnits]
    simp
  rw [hval] at hlim
  obtain ⟨n, hn, hB⟩ := ((hlim.eventually_ne one_ne_zero).and
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop B)).exists
  exact ⟨n, hB, hn⟩

end GlobalTheory.CompanionTheory.EisTF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteModuleOfFinite
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

namespace GlobalTheory.CompanionTheory.EisTestFun

variable {k : Type} [Field k] [NumberField k]

theorem infiniteModule_ofFinite (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    infiniteModule (ofFinite b) = 1 := by
  have h : ((ofFinite b : IdeleGroup k) : AdeleRing (𝓞 k) k).1 = (1 : AdeleRing (𝓞 k) k).1 := rfl
  unfold infiniteModule
  refine Finset.prod_eq_one fun w _ => ?_
  rw [h, adele_fst_one_apply, norm_one, one_pow]

theorem ideleModule_ofFinite (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    (ideleModule k (ofFinite b) : ℝ) = finiteModule (ofFinite b) := by
  rw [ideleModule_apply, infiniteModule_ofFinite, one_mul]

theorem line_lc_cs {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ}
    (hg : g ∈ GJMatrix.finiteSchwartzBruhatPi k) :
    IsLocallyConstant (fun t : FiniteAdeleRing (𝓞 k) k => g fun _ => t) ∧
      HasCompactSupport (fun t : FiniteAdeleRing (𝓞 k) k => g fun _ => t) := by
  obtain ⟨hlc, hcs⟩ := hg
  refine ⟨hlc.comp_continuous (continuous_pi fun _ => continuous_id), ?_⟩
  exact hcs.comp_homeomorph (Homeomorph.funUnique Unit (FiniteAdeleRing (𝓞 k) k)).symm

theorem zFinPos : ZFinPos := by
  intro K _ _ g hg hnn h1 x hx
  haveI := isHaarMeasure_finiteIdeleMeasure K
  obtain ⟨hlc, hcs⟩ := line_lc_cs hg
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hcs.isCompact
  obtain ⟨B, hB⟩ := hlc.continuous.bounded_above_of_compact_support hcs
  let G : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ := fun b => (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)).re
  let F : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ := fun b => G b * finiteZetaBound L x b
  have hG0 : ∀ b, 0 ≤ G b := by
    intro b
    obtain ⟨r, hr, hgr⟩ := hnn (b : FiniteAdeleRing (𝓞 K) K)
    simp only [G, hgr, Complex.ofReal_re]
    exact hr
  have hGc : Continuous G :=
    Complex.continuous_re.comp (hlc.continuous.comp Units.continuous_val)
  have hGB : ∀ b, ‖G b‖ ≤ B := by
    intro b
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hB _)
  have hint : Integrable F (finiteIdeleMeasure K) :=
    (integrable_finiteZetaBound L hx).bdd_mul hGc.aestronglyMeasurable
      (Filter.Eventually.of_forall hGB)
  have hF0 : 0 ≤ F := fun b => mul_nonneg (hG0 b) (finiteZetaBound_nonneg L x b)
  have hzero : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (b : FiniteAdeleRing (𝓞 K) K) ∉ idealFiniteAdeles L →
        (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = 0 := by
    intro b hb
    by_contra hne
    exact hb (hL (subset_tsupport _ hne))
  have heq : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) * ((1 : HeckeCharacter K).toIdele (ofFinite b) : ℂ) *
        ((ideleModule K (ofFinite b) : ℝ) : ℂ) ^ (x : ℂ) = ((F b : ℝ) : ℂ) := by
    intro b
    have hc : ((1 : HeckeCharacter K).toIdele (ofFinite b) : ℂ) = 1 := by
      rw [HeckeCharacter.toIdele_apply]
      rfl
    rw [hc, mul_one, ideleModule_ofFinite]
    simp only [F, G, finiteZetaBound]
    split_ifs with hb
    · obtain ⟨r, hr, hgr⟩ := hnn (b : FiniteAdeleRing (𝓞 K) K)
      rw [hgr, Complex.ofReal_re, Complex.ofReal_mul,
        Complex.ofReal_cpow (finiteModule_pos _).le]
    · rw [hzero b hb]
      simp
  have hI : zFin g 1 (x : ℂ) = ((∫ b, F b ∂finiteIdeleMeasure K : ℝ) : ℂ) := by
    unfold zFin
    exact (integral_congr_ae (Filter.Eventually.of_forall heq)).trans integral_complex_ofReal
  let U : Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
    {b | (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = g fun _ => 1}
  have hUo : IsOpen U := (hlc.comp_continuous Units.continuous_val).isOpen_fiber _
  have h1U : (1 : (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ U := by
    show (g fun _ => ((1 : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)) = g fun _ => 1
    rw [Units.val_one]
  obtain ⟨r, hr, hgr⟩ := hnn 1
  have hr0 : 0 < r := by
    refine lt_of_le_of_ne hr ?_
    rintro rfl
    exact h1 (by rw [hgr, Complex.ofReal_zero])
  have hUsub : U ⊆ Function.support F := by
    intro b hb
    have hgb : (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = r := (show _ = _ from hb).trans hgr
    have hmem : (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L := by
      by_contra hn
      have h0 := hzero b hn
      rw [hgb] at h0
      exact hr0.ne' (by exact_mod_cast h0)
    rw [Function.mem_support]
    simp only [F, G, finiteZetaBound, if_pos hmem, hgb, Complex.ofReal_re]
    exact (mul_pos hr0 (Real.rpow_pos_of_pos (finiteModule_pos _) _)).ne'
  have hpos : 0 < finiteIdeleMeasure K (Function.support F) :=
    (hUo.measure_pos _ ⟨1, h1U⟩).trans_le (measure_mono hUsub)
  rw [hI, Complex.ofReal_ne_zero]
  exact ((integral_pos_iff_support_of_nonneg hF0 hint).2 hpos).ne'

end GlobalTheory.CompanionTheory.EisTestFun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentity
section
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisMG

open MeasureTheory Topology

section SlopeTestRemainingChoices

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem leftGood_map {f : ℂ → X} {a : ℝ} (T : X →L[ℂ] Y) (h : LeftGood f a) :
    LeftGood (fun z => T (f z)) a := by
  refine ⟨T.differentiable.comp_differentiableOn h.1, fun b c hc => ?_⟩
  obtain ⟨M, hM⟩ := h.2 b c hc
  exact ⟨‖T‖ * M, fun z h1 h2 =>
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM z h1 h2) (norm_nonneg _))⟩

theorem leftGood_mono {f : ℂ → X} {a b : ℝ} (hab : b ≤ a) (h : LeftGood f a) : LeftGood f b :=
  ⟨h.1.mono fun _ hz => lt_of_lt_of_le hz hab, fun b' c hc => h.2 b' c (lt_of_lt_of_le hc hab)⟩

end SlopeTestRemainingChoices

section Eis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G)
    (t : ℂ) (w : W) : eis Γ K P c ρ Λ g (t • w) = t • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [map_smul, smul_comm]

end Eis

theorem master : AvgMem → DGood → HGood → BGood → Master := by
  intro hM hD hH hB
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar hProb Γ P P' c η η' β L J R N Φ a ζ hpar hLe hR
    hcR hcL hΦ ha haN hζ hLaw hEqR hEqL
  obtain ⟨pr, hpr⟩ : (secSp K P' c ρ).ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional _
  let T : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] secSp K P' c ρ) :=
    ((ContinuousLinearMap.compL ℂ L W _).flip J).comp (ContinuousLinearMap.compL ℂ W W _ pr)
  let TJ : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] W) := (ContinuousLinearMap.compL ℂ L W W).flip J
  obtain ⟨hHd, hHc, hHb⟩ := hH G W K ρ hK hρ μ hHaar hProb Φ hΦ
  obtain ⟨hB1, hB2⟩ := hB G W K ρ hK hρ μ hHaar hProb ζ hζ
  obtain ⟨-, hD2⟩ := hD a N ha
  have hop : LeftGood (fun z : ℂ =>
      z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) (-R) := by
    have h2 := leftGood_map T hB2
    have e : (fun z : ℂ => T (z • (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) =
        fun z : ℂ => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)) :=
      funext fun z => map_smul T z _
    rw [e] at h2
    exact leftGood_mono (by linarith) h2
  refine ⟨fun z => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)),
    fun z g => TJ ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ fun κ => Φ z (g * κ)), ?_,
    fun _ _ _ => rfl, fun z => T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)),
    leftGood_map T hB1, fun _ _ => rfl⟩
  refine
    { le := hLe, pos := hR, convR := hcR, convL := hcL, dEnt := hD2, dNe := ?_, op := hop
      hol := fun g => TJ.differentiable.comp (hHd g)
      cont := TJ.continuous.comp hHc
      bdd := ?_, eqR := ?_, eqL := ?_ }
  · obtain ⟨z, hz, haz⟩ := haN
    exact ⟨z, mul_ne_zero (sub_ne_zero.2 hz) (mul_ne_zero (Complex.exp_ne_zero _) haz)⟩
  · intro b a' g
    obtain ⟨U, hU, M, hMb⟩ := hHb b a' g
    exact ⟨U, hU, ‖TJ‖ * M, fun z h1 h2 g' hg' =>
      (TJ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hMb z h1 h2 g' hg') (norm_nonneg _))⟩
  · intro z hz g w
    have h := hEqR z hz g w
    change (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) = _
    rw [mul_smul, h, smul_smul]
    congr 1
    ring
  · intro z hz g w
    have hz' : z.re < 1 / 2 := by linarith
    have hcont : Continuous (ζ z) := by
      have h1 : Continuous fun t : K => (z, t) := by fun_prop
      exact hζ.cont.comp_continuous h1 fun t => ⟨hz', Set.mem_univ _⟩
    have hmem : avg μ ρ (ζ z) (J w) ∈ secSp K P' c ρ :=
      hM G W K ρ hK hρ μ hHaar hProb Γ P' c hpar (ζ z) hcont (hLaw z) (J w)
    have hOp : (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W) =
        (z * (Complex.exp (z ^ 2) * (z - 1))) • avg μ ρ (ζ z) (J w) := by
      have hp : ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) =
          (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w) :=
        congrArg Subtype.val
          (hpr ⟨_, (secSp K P' c ρ).smul_mem (Complex.exp (z ^ 2) * (z - 1)) hmem⟩)
      change z • ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) = _
      rw [hp, mul_smul z]
    change (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) =
      eis Γ K P' c ρ (fun x => β x - z * η' x) g
        (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W)
    rw [hOp, eis_smul, hEqL z hz g (J w), smul_smul, mul_comm z]

end GlobalTheory.CompanionTheory.RgEisMG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration
section
noncomputable section

open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMir

theorem avg_one_apply {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] (ρ : K →* (W →L[ℂ] W)) (hρ : Continuous ρ) (w : W)
    (hw : ∀ r : K, ρ r w = w) : avg μ ρ (fun _ => (1 : ℂ)) w = w := by
  have hint : Integrable (fun κ : K => (1 : ℂ) • ρ κ) μ := by
    simp only [one_smul]
    exact hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [avg]
  rw [ContinuousLinearMap.integral_apply hint]
  simp [hw]

theorem isPar_top {G : Type} [Group G] [TopologicalSpace G] (Γ K : Subgroup G) :
    IsPar Γ K ⊤ (1 : G → ℂ) := by
  refine ⟨?_, fun g => ⟨g, Subgroup.mem_top g, 1, K.one_mem, (mul_one g).symm⟩, ?_⟩
  · simp only [Subgroup.coe_top]
    exact isClosed_univ
  · exact ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => by simp,
      continuous_const.continuousOn⟩

theorem sec_top_apply {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] (K : Subgroup G) (ρ : K →* (W →L[ℂ] W)) (g : G) (w : W)
    (hw : ∀ r : K, ρ r w = w) : sec K ⊤ (1 : G → ℂ) ρ g w = w := by
  unfold sec
  rw [dite_eq_left ⟨1, Subgroup.mem_top _⟩]
  simp [hw]

theorem mirGen_of_core : SecLaw → TestSph → AvgMem → AvgInv → SideOf → TestK → Core → MirGen := by
  intro _hSec hSph hMem hInv hSide hTK hCore G _ _ _ _ _ W _ _ _ K ρ hK hρ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l hSC hMD
  haveI := hSC
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haarMeasure ⊤
  have hHaar : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hProb : IsProbabilityMeasure μ := ⟨by
    have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
    simpa using h⟩
  haveI := hProb
  have hN1 : (1 : ℝ) < Fintype.card ι := by
    have h2 := hMD.two
    exact_mod_cast (show 1 < Fintype.card ι by omega)
  obtain ⟨hS0, -, -, -⟩ := hSide G K hK k ι π Γ i₀ i₁ ω d c η η' l hMD
  obtain ⟨V, hV, hJV⟩ := hInv G W K ρ hK hρ μ hHaar hProb Γ _ c hMD.par
  obtain ⟨Ψ, Ψ₁, φ, hΨ, hΨ₁, hφc, hφ1, hφL, hφN, hzt, hz, hω1⟩ :=
    hTK G K hK k ι π Γ _ i₀ ω d c η hS0 V hV
  obtain ⟨J, hJ⟩ := hJV φ hφc hφ1 hφL hφN
  obtain ⟨R, D, Op, H, hW, ⟨dd, hdd, hD, hddN⟩, -, hH⟩ :=
    hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ ω d c η η' l hMD Ψ Ψ₁ φ _ J hΨ hΨ₁ hzt hz le_rfl hJ
  refine ⟨⟨R, D, Op, H, hW⟩, fun hω hc => ?_⟩
  subst hω
  subst hc
  have hinv : ∀ w ∈ secSp K ⊤ (1 : G → ℂ) ρ, ∀ r : K, ρ r w = w := fun w hw r => by
    simpa using hw r (Subgroup.mem_top _)
  refine ⟨?_, ?_⟩
  · obtain ⟨Ψs, Ψ₁s, hΨs, hΨ₁s, hΨ0, hsph, hnz⟩ := hSph k ι i₀
    have hzt' : ∀ s (κ : K), zt π d i₀ Ψs 1 s κ = tate Ψ₁s 1 s * (fun _ => (1 : ℂ)) κ := by
      intro s κ
      simp only [mul_one]
      unfold zt tate lineZeta
      congr 1
      funext t
      exact hsph t ⟨kap π d κ, hS0.piK κ κ.2⟩
    have hnz' : ∃ z : ℂ, (Fintype.card ι : ℝ) < z.re ∧ tate Ψ₁s 1 z ≠ 0 :=
      ⟨(((Fintype.card ι : ℝ) + 1 : ℝ) : ℂ), by simp, hnz _ (by linarith)⟩
    have hle : secSp K ⊤ (1 : G → ℂ) ρ ≤ secSp K ((stab _ {i₀}).comap π) 1 ρ :=
      fun w hw r _ => hw r (Subgroup.mem_top _)
    have havg : ∀ w : secSp K ⊤ (1 : G → ℂ) ρ,
        avg μ ρ (fun _ => (1 : ℂ)) ((secSp K ⊤ (1 : G → ℂ) ρ).subtypeL w) = w := fun w => by
      simpa using avg_one_apply μ ρ hρ (w : W) (hinv w w.2)
    obtain ⟨R', D', Op', H', hW', -, ⟨O', hO', hOp'⟩, hH'⟩ :=
      hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ 1 d 1 η η' l hMD Ψs Ψ₁s (fun _ => 1)
        (secSp K ⊤ (1 : G → ℂ) ρ) (secSp K ⊤ (1 : G → ℂ) ρ).subtypeL hΨs hΨ₁s hzt' hnz' hle havg
    obtain ⟨⟨a, ha, hH0⟩, -⟩ := hH' rfl
    refine ⟨R', D', Op', H', hW', ⟨a, ha, fun g w => ?_⟩, O', hO', hOp'⟩
    rw [hH0, hΨ0, mul_one, havg w, sec_top_apply K ρ g (w : W) (hinv w w.2)]
  · obtain ⟨-, b, hb⟩ := hH rfl
    have hmem : ∀ v, avg μ ρ (fun _ => (1 : ℂ)) v ∈ secSp K ⊤ (1 : G → ℂ) ρ :=
      hMem G W K ρ hK hρ μ hHaar hProb Γ ⊤ 1 (isPar_top Γ K) (fun _ => 1) continuous_const
        (fun _ _ _ => by simp)
    let T : secSp K ((stab _ {i₀}).comap π) 1 ρ →L[ℂ] secSp K ⊤ (1 : G → ℂ) ρ :=
      b • ((avg μ ρ (fun _ => (1 : ℂ))).comp J).codRestrict _ (fun w => hmem (J w))
    refine ⟨R, D, Op, H, hW, ⟨dd, hdd, hddN (hω1 rfl _ hN1), hD⟩, T, fun g w => ?_⟩
    rw [hb g w, sec_top_apply K ρ g _ (hinv _ (T w).2), mul_smul]
    rfl

end GlobalTheory.CompanionTheory.EisMir
end
end

