module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSpanBoxIndicatorSchrodinger
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
open Filter Topology

namespace GlobalTheory.SchrBox

theorem exists_cut {X ι : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (χ : ι → X → ℂ)
    (hχ : ∀ i x y, χ i (x + y) = χ i x * χ i y) {B : Set X} (hB : IsOpen B) (h0 : (0 : X) ∈ B)
    (hsep : ∀ z, z ∉ B → ∃ i, χ i z ≠ 1 ∧ ∀ u ∈ B, χ i u = 1) {K : Set X} (hK : IsCompact K) (x₀ : X) :
    ∃ g ∈ Algebra.adjoin ℂ (Set.range χ), (∀ x, x - x₀ ∈ B → g x = 1) ∧ ∀ x ∈ K, x - x₀ ∉ B → g x = 0 := by
  have hop : ∀ y : X, IsOpen {x | x - y ∈ B} := fun y => hB.preimage (continuous_id.sub continuous_const)
  have key := (hK.diff (hop x₀)).induction_on
    (p := fun T => ∃ g ∈ Algebra.adjoin ℂ (Set.range χ), (∀ x, x - x₀ ∈ B → g x = 1) ∧ ∀ x ∈ T, g x = 0)
    ⟨1, one_mem _, fun _ _ => rfl, fun _ h => h.elim⟩
    (fun s t hst ⟨g, hg, h1, h2⟩ => ⟨g, hg, h1, fun x hx => h2 x (hst hx)⟩)
    (fun s t hs ht => by
      obtain ⟨g, hg, h1, h2⟩ := hs
      obtain ⟨g', hg', h1', h2'⟩ := ht
      refine ⟨g * g', mul_mem hg hg', fun x hx => by simp [h1 x hx, h1' x hx], fun x hx => ?_⟩
      rcases hx with hx | hx
      · simp [h2 x hx]
      · simp [h2' x hx])
    (fun y hy => by
      obtain ⟨i, hi, hiB⟩ := hsep (y - x₀) hy.2
      have hne : 1 - χ i (y - x₀) ≠ 0 := sub_ne_zero.2 hi.symm
      have hx0 : ∀ x, χ i (-x₀) * χ i x = χ i (x - x₀) := fun x => by
        rw [← hχ]; congr 1; abel
      refine ⟨{x | x - y ∈ B}, mem_nhdsWithin_of_mem_nhds ((hop y).mem_nhds (by simpa using h0)),
        (1 - χ i (y - x₀))⁻¹ • (χ i (-x₀) • χ i - χ i (y - x₀) • 1), ?_, fun x hx => ?_, fun x hx => ?_⟩
      · exact Subalgebra.smul_mem _ (sub_mem (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _)
          (Subalgebra.smul_mem _ (one_mem _) _)) _
      · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, hiB _ hx]
        exact inv_mul_cancel₀ hne
      · have : χ i (x - x₀) = χ i (y - x₀) := by
          rw [show x - x₀ = (x - y) + (y - x₀) by abel, hχ, hiB _ hx, one_mul]
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, this, sub_self, mul_zero])
  obtain ⟨g, hg, h1, h2⟩ := key
  exact ⟨g, hg, h1, fun x hx hx' => h2 x ⟨hx, hx'⟩⟩

theorem adjoin_mul_mem {X ι : Type} [AddCommGroup ι] (χ : ι → X → ℂ) (h0 : χ 0 = 1) (hχ : ∀ i j, χ (i + j) = χ i * χ j)
    (s : X → ℂ) {g : X → ℂ} (hg : g ∈ Algebra.adjoin ℂ (Set.range χ)) :
    g * s ∈ Submodule.span ℂ (Set.range fun i => χ i * s) := by
  have key : ∀ f ∈ Submodule.span ℂ (Set.range fun i => χ i * s),
      g * f ∈ Submodule.span ℂ (Set.range fun i => χ i * s) := by
    induction hg using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro f hf
      induction hf using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨i + j, by simp only [hχ, mul_assoc]⟩
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
    | algebraMap r => intro f hf; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ hf
    | add a b _ _ ha hb => intro f hf; rw [add_mul]; exact add_mem (ha f hf) (hb f hf)
    | mul a b _ _ ha hb => intro f hf; rw [mul_assoc]; exact ha _ (hb f hf)
  exact key s (Submodule.subset_span ⟨0, by simp [h0]⟩)

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)}

theorem isOpen_ball (n : ℤ) : IsOpen {y : Fv F v | Valued.v y ≤ WithZero.exp n} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : Fv F v | Valued.v y ≤ WithZero.exp n} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_ball_subset {U : Set (Fv F v)} {x : Fv F v} (hU : U ∈ 𝓝 x) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - x) ≤ WithZero.exp (-(N : ℤ)) → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun N hN y hy => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  refine hy.trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hne]
  rw [WithZero.exp_lt_exp]
  omega

theorem exists_sep {ψ : AddChar (Fv F v) ℂ}
    (hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F)
    (n : ℤ) {z : Fv F v} (hz : ¬ Valued.v z ≤ WithZero.exp n) :
    ∃ t, ψ (z * t) ≠ 1 ∧ ∀ u, Valued.v u ≤ WithZero.exp n → ψ (u * t) = 1 := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hmem : ∀ u : Fv F v, u / c ∈ v.adicCompletionIntegers F ↔ Valued.v u ≤ WithZero.exp n := fun u => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hc, div_le_one₀ WithZero.exp_pos]
  have h1 := mt (hψ (z / c)).1 (mt (hmem z).1 hz)
  push Not at h1
  obtain ⟨y, hy, hy1⟩ := h1
  refine ⟨y / c, by rwa [show z * (y / c) = z / c * y by ring], fun u hu => ?_⟩
  rw [show u * (y / c) = u / c * y by ring]
  exact (hψ _).2 ((hmem u).2 hu) y hy

theorem indicator_box_mem_span : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  intro F _ _ v ψ hψ κ _ s hs hs0
  classical
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hs0
  have hx₀ : s x₀ ≠ 0 := hx₀
  have hU : {x | s x = s x₀} ∈ 𝓝 x₀ := (hs.1.isOpen_fiber (s x₀)).mem_nhds rfl
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, htU⟩ := hU
  choose M hM using fun i => exists_ball_subset (ht i)
  refine ⟨x₀, Finset.univ.sup M, fun N hN => ?_⟩
  have hconst : ∀ x : κ → Fv F v, (∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))) → s x = s x₀ :=
    fun x hx => htU fun i _ => hM i N ((Finset.le_sup (f := M) (Finset.mem_univ i)).trans hN) _ (hx i)
  let χ : (κ → Fv F v) → (κ → Fv F v) → ℂ := fun b x => ψ (x ⬝ᵥ b)
  have hB : IsOpen {x : κ → Fv F v | ∀ i, Valued.v (x i) ≤ WithZero.exp (-(N : ℤ))} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => (isOpen_ball (v := v) (-(N : ℤ))).preimage (continuous_apply (A := fun _ : κ => Fv F v) i)
  obtain ⟨g, hg, h1, h2⟩ := exists_cut χ (fun b x y => by simp only [χ, add_dotProduct, AddChar.map_add_eq_mul]) hB
    (by simp) (fun z hz => by
      simp only [Set.mem_ofPred_eq, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      obtain ⟨t, ht1, ht2⟩ := exists_sep hψ _ hi
      exact ⟨Pi.single i t, by simpa only [χ, dotProduct_single] using ht1,
        fun u hu => by simpa only [χ, dotProduct_single] using ht2 _ (hu i)⟩) hs.2 x₀
  have hm := adjoin_mul_mem χ (by ext x; simp [χ])
    (fun i j => by ext x; simp only [χ, dotProduct_add, AddChar.map_add_eq_mul, Pi.mul_apply]) s hg
  have hle : Submodule.span ℂ (Set.range fun b => χ b * s) ≤
      Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
    refine Submodule.span_mono ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨(0, b), by ext x; simp [schr, χ]⟩
  have := Submodule.smul_mem _ (s x₀)⁻¹ (hle hm)
  convert this using 1
  ext x
  by_cases hx : ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))
  · rw [Set.indicator_of_mem (by exact hx)]
    simp [h1 x hx, hconst x hx, hx₀]
  · rw [Set.indicator_of_notMem (by exact hx)]
    by_cases hxs : x ∈ tsupport s
    · simp [h2 x hxs hx]
    · simp [image_eq_zero_of_notMem_tsupport hxs]

end GlobalTheory.SchrBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSecondVariableRapidDecay
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

open scoped ContDiff

namespace GlobalTheory.FourierSndDecay

lemma norm_iteratedFDeriv_slice_le {U V : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : SchwartzMap (U × V) ℂ) (u : U) (q : ℕ) (t : V) :
    ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ ≤ ‖iteratedFDeriv ℝ q h (u, t)‖ := by
  have c0 : ContDiff ℝ ∞ h := h.smooth'
  have e : (fun s : V => h (u, s)) =
      (fun x : U × V => h (x + (u, 0))) ∘ (ContinuousLinearMap.inr ℝ U V) := by
    funext s; simp
  have ct : ContDiff ℝ ∞ (fun x : U × V => h (x + (u, 0))) :=
    c0.comp (contDiff_id.add contDiff_const)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ ct t (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin q, ‖(ContinuousLinearMap.inr ℝ U V)‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ U V)
  have : ContinuousLinearMap.inr ℝ U V t + (u, 0) = (u, t) := by simp
  rw [this]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

lemma one_add_pow_le_two_pow_mul (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 t) ^ n ≤ 1 + t ^ n := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ht n]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg ht n]
  calc (1 + t) ^ n ≤ (2 * max 1 t) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = 2 ^ n * (max 1 t) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (1 + t ^ n) := by gcongr

theorem fourier_snd_rapid_decay : ∀ (U V : Type) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (h : SchwartzMap (U × V) ℂ) (k : ℕ), ∃ C : ℝ,
    ∀ (u : U) (w : V), (1 + ‖u‖) ^ k * (1 + ‖w‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖ ≤ C := by
  intro U V _ _ _ _ _ _ _ _ h k
  set d := Module.finrank ℝ V with hd
  set N := k + (d + 1) with hN
  set S := 2 ^ N * ((Finset.Iic (N, k)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hSdef
  set I := ∫ t : V, (1 + ‖t‖) ^ (-((d : ℝ) + 1)) with hIdef
  have hint : Integrable (fun t : V => (1 + ‖t‖) ^ (-((d : ℝ) + 1))) :=
    integrable_one_add_norm (by linarith)
  have hpt : ∀ (u : U) (t : V) (q : ℕ), q ≤ k →
      (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖
        ≤ S * (1 + ‖t‖) ^ (-((d : ℝ) + 1)) := by
    intro u t q hq
    have hS := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, k)) (k := N) (n := q)
      le_rfl hq h (u, t)
    have hu : ‖u‖ ≤ ‖(u, t)‖ := norm_fst_le (u, t)
    have ht : ‖t‖ ≤ ‖(u, t)‖ := norm_snd_le (u, t)
    have hpos : 0 < (1 + ‖t‖) ^ ((d : ℝ) + 1) := by positivity
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
    have e : (1 + ‖t‖) ^ ((d : ℝ) + 1) = (1 + ‖t‖) ^ (d + 1) := by
      rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [e]
    calc (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ * (1 + ‖t‖) ^ (d + 1)
        ≤ (1 + ‖(u, t)‖) ^ k * ‖iteratedFDeriv ℝ q h (u, t)‖ * (1 + ‖(u, t)‖) ^ (d + 1) := by
          gcongr; exact norm_iteratedFDeriv_slice_le h u q t
      _ = (1 + ‖(u, t)‖) ^ N * ‖iteratedFDeriv ℝ q h (u, t)‖ := by rw [hN, pow_add]; ring
      _ ≤ S := hS
  have hcd : ∀ u : U, ContDiff ℝ ∞ (fun s : V => h (u, s)) := fun u =>
    h.smooth'.comp (contDiff_const.prodMk contDiff_id)
  have hintq : ∀ (u : U) (q : ℕ), q ≤ k →
      Integrable (fun t => ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖) := by
    intro u q hq
    refine (hint.const_mul S).mono'
      ((hcd u).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have := hpt u t q hq
    have h1 : 1 ≤ (1 + ‖u‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg u])
    nlinarith [norm_nonneg (iteratedFDeriv ℝ q (fun s : V => h (u, s)) t)]
  have hintb : ∀ (u : U) (q : ℕ), q ≤ k →
      (1 + ‖u‖) ^ k * ∫ t, ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ ≤ S * I := by
    intro u q hq
    calc (1 + ‖u‖) ^ k * ∫ t, ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖
        = ∫ t, (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ t : V, S * (1 + ‖t‖) ^ (-((d : ℝ) + 1)) :=
          integral_mono ((hintq u q hq).const_mul _) (hint.const_mul S) (fun t => hpt u t q hq)
      _ = S * I := integral_const_mul _ _
  have hF : ∀ (u : U) (w : V) (n : ℕ), n ≤ k →
      (1 + ‖u‖) ^ k * (‖w‖ ^ n * ‖𝓕 (fun t : V => h (u, t)) w‖) ≤ 2 ^ n * ((n + 1) * (S * I)) := by
    intro u w n hn
    have h'f : ∀ (k' m : ℕ), (k' : ℕ∞) ≤ 0 → (m : ℕ∞) ≤ (n : ℕ∞) →
        Integrable (fun v : V => ‖v‖ ^ k' * ‖iteratedFDeriv ℝ m (fun s : V => h (u, s)) v‖) := by
      intro k' m hk' hm
      have hk0 : k' = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hk'
      have hmn : m ≤ n := by exact_mod_cast hm
      subst hk0
      simpa using hintq u m (hmn.trans hn)
    have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := fun t : V => h (u, t)) (K := 0)
      (N := n) ((hcd u).of_le (by exact_mod_cast le_top)) h'f (k := 0) (n := n) le_rfl le_rfl w
    have hsum : (∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun s : V => h (u, s)) v‖)
        = ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖ := by
      rw [Finset.sum_product]; simp
    rw [hsum, norm_iteratedFDeriv_zero] at key
    simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add] at key
    have hsb : (1 + ‖u‖) ^ k *
        ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖
        ≤ (n + 1) * (S * I) := by
      rw [Finset.mul_sum]
      calc ∑ j ∈ Finset.range (n + 1),
            (1 + ‖u‖) ^ k * ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖
          ≤ ∑ _j ∈ Finset.range (n + 1), S * I := Finset.sum_le_sum fun j hj =>
            hintb u j ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hn)
        _ = (n + 1) * (S * I) := by simp
    have hu0 : 0 ≤ (1 + ‖u‖) ^ k := by positivity
    calc (1 + ‖u‖) ^ k * (‖w‖ ^ n * ‖𝓕 (fun t : V => h (u, t)) w‖)
        ≤ (1 + ‖u‖) ^ k * (2 ^ n * ∑ j ∈ Finset.range (n + 1),
            ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖) :=
          mul_le_mul_of_nonneg_left key hu0
      _ = 2 ^ n * ((1 + ‖u‖) ^ k * ∑ j ∈ Finset.range (n + 1),
            ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖) := by ring
      _ ≤ 2 ^ n * ((n + 1) * (S * I)) := by gcongr
  refine ⟨2 ^ k * (S * I + 2 ^ k * ((k + 1) * (S * I))), fun u w => ?_⟩
  have h0 := hF u w 0 (Nat.zero_le _)
  have hk := hF u w k le_rfl
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at h0
  have hw := one_add_pow_le_two_pow_mul ‖w‖ (norm_nonneg _) k
  have hu0 : 0 ≤ (1 + ‖u‖) ^ k := by positivity
  calc (1 + ‖u‖) ^ k * (1 + ‖w‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖
      ≤ (1 + ‖u‖) ^ k * (2 ^ k * (1 + ‖w‖ ^ k)) * ‖𝓕 (fun t : V => h (u, t)) w‖ := by gcongr
    _ = 2 ^ k * ((1 + ‖u‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖
          + (1 + ‖u‖) ^ k * (‖w‖ ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖)) := by ring
    _ ≤ 2 ^ k * (S * I + 2 ^ k * ((k + 1) * (S * I))) := by gcongr

end GlobalTheory.FourierSndDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorLeftFactor
section
noncomputable section
namespace GlobalTheory.SchwartzBox

theorem box_pow_mul_iteratedFDeriv_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ) (f₂ : SchwartzMap (κ' → V) ℂ) (k n : ℕ)
    (x : κ ⊕ κ' → V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ k i f₁ * SchwartzMap.seminorm ℂ 0 (n - i) f₂ +
          SchwartzMap.seminorm ℂ 0 i f₁ * SchwartzMap.seminorm ℂ k (n - i) f₂) := by
  have hs₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl)) :=
    (f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff
  have hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₂ (y ∘ Sum.inr)) :=
    (f₂.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff
  have hx : ‖x‖ ^ k ≤ ‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k := by
    have h0 : ‖x‖ ^ k ≤ (max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_max_comp x) k
    refine h0.trans ?_
    have p1 := pow_nonneg (norm_nonneg (x ∘ Sum.inl)) k
    have p2 := pow_nonneg (norm_nonneg (x ∘ Sum.inr)) k
    rcases le_total ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hL := norm_iteratedFDeriv_mul_le hs₁ hs₂ x (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖
      ≤ (‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ := by
        refine mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact norm_iteratedFDeriv_restr_le Sum.inl f₁ i x
        · exact norm_iteratedFDeriv_restr_le Sum.inr f₂ (n - i) x
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ((‖x ∘ Sum.inl‖ ^ k * ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖) *
              ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ +
           ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ *
              (‖x ∘ Sum.inr‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact SchwartzMap.le_seminorm ℂ k i f₁ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₂ _ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₁ _ _
        · exact SchwartzMap.le_seminorm ℂ k (n - i) f₂ _

theorem exists_boxCLM : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ κ' : Type) [Fintype κ]
    [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ),
    ∃ T : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ' → V) ℂ,
      ∀ f x, T f x = f₁ (x ∘ Sum.inl) * f (x ∘ Sum.inr) := by
  intro V _ _ κ κ' _ _ f₁
  refine ⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ)
    (fun (f : SchwartzMap (κ' → V) ℂ) (x : κ ⊕ κ' → V) => f₁ (x ∘ Sum.inl) * f (x ∘ Sum.inr))
    (fun f g x => by simp [mul_add]) (fun a f x => by simp; ring) (fun f => ?_) ?_, fun _ _ => rfl⟩
  · exact ((f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff).mul
      ((f.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (k + 1) ×ˢ Finset.range (n + 1),
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ k i f₁ + SchwartzMap.seminorm ℂ 0 i f₁), by positivity, fun f x => ?_⟩
    refine (box_pow_mul_iteratedFDeriv_le f₁ f k n x).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hb : ∀ a, a ≤ k → SchwartzMap.seminorm ℂ a (n - i) f ≤
        (Finset.range (k + 1) ×ˢ Finset.range (n + 1)).sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) f := by
      intro a ha
      have hm : (a, n - i) ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1) := by
        simp only [Finset.mem_product, Finset.mem_range]; omega
      exact Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ' → V) ℂ) hm
    rw [mul_assoc, add_mul]
    gcongr
    · exact hb 0 (Nat.zero_le _)
    · exact hb k le_rfl

end GlobalTheory.SchwartzBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLine
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem fixL_pos_unique_of_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 →
    ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β,
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re →
    FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z := by
  intro p _ G v hsig β hsh hR y₀ hdeg hsep z z' hz hz' hf hf'
  obtain ⟨_, _, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hsh hR
  set g0 : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) with hg0
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := (Z : Matrix (Fin G.n) (Fin G.n) ℂ) with hZm
  set Zi : Matrix (Fin G.n) (Fin G.n) ℂ := ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) with hZi
  have hZiZ : Zi * Zm = 1 := by rw [hZi, hZm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hZZi : Zm * Zi = 1 := by rw [hZi, hZm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set s : ℝ := ((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs
  have hspos : 0 < s := by rw [hs]; exact_mod_cast y₀.2.2
  have hsim0 := GlobalTheory.LKCx.grp_similitude_herm p G v β y₀
  set g : Matrix (Fin G.n) (Fin G.n) ℂ := Zm * g0 * Zi with hg
  have hsim : gᴴ * G.gram v * g = (s : ℂ) • G.gram v := by
    have e1 : gᴴ * G.gram v * g = Ziᴴ * (g0ᴴ * (Zmᴴ * G.gram v * Zm) * g0) * Zi := by
      rw [hg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, ← hZ, hsim0]
    have e2 : Ziᴴ * ((((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β) * Zi =
        (s : ℂ) • ((Zm * Zi)ᴴ * G.gram v * (Zm * Zi)) := by
      rw [hZ, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
      congr 1
      simp only [Matrix.mul_assoc]
    rw [e2, hZZi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hcp : g.charpoly.Separable := by
    have e : g = (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * g0 * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) := rfl
    rw [e, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact GlobalTheory.LKMid.charpoly_psi_separable p G v _ hdeg hsep
  have hpos : ∀ w : Fin G.n → ℂ, star (Zm *ᵥ w) ⬝ᵥ G.gram v *ᵥ (Zm *ᵥ w) = star w ⬝ᵥ (herm G v β *ᵥ w) := by
    intro w; rw [hZ, GlobalTheory.form_conjTranspose_mul_mul]
  have heig : ∀ w : Fin G.n → ℂ, FixL G v β y₀ w → ∃ μ : ℂ, g *ᵥ (Zm *ᵥ w) = μ • (Zm *ᵥ w) := by
    rintro w ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hZiZ, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hμ, Matrix.mulVec_smul]
  obtain ⟨c, hc⟩ := GlobalTheory.eigvec_pos_unique_of_similitude (G.gram v) (G.gram_herm v) (G.gram_det v) hsig g s hspos
    hsim hcp (Zm *ᵥ z) (Zm *ᵥ z') (by rw [hpos]; exact hz) (by rw [hpos]; exact hz') (heig z hf) (heig z' hf')
  refine ⟨c, ?_⟩
  have := congrArg (Zi *ᵥ ·) hc
  simp only [Matrix.mulVec_mulVec, hZiZ, Matrix.one_mulVec, Matrix.mulVec_smul] at this
  exact this

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjoint
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecCalc

theorem smooth_calculus : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → (∀ g ∈ Formalism.QuantumDeterminants.UH J, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (π g v)) ∧ (∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ∀ c : ℂ, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (v + c • w)) ∧ ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (dRep π X v) ∧ HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH J, π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v)) ∧ (∀ c : ℝ, dRep π (c • X) v = (c : ℂ) • dRep π X v) ∧ ∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ⟪dRep π X v, w⟫_ℂ = -⟪v, dRep π X w⟫_ℂ ∧ ∀ c : ℂ, dRep π X (v + c • w) = dRep π X v + c • dRep π X w := by
  intro n H _ _ J π _ hJ hπ v hv
  have hG : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  have hv' : v ∈ GlobalTheory.SmVec.smSub J π := hv
  refine ⟨fun g hg => GlobalTheory.SmVec.rep_mem hG hπ hv' hg, fun w hw c => ?_, fun X hX => ?_⟩
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    exact add_mem hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw')
  have hX' : X ∈ GlobalTheory.SmVec.lieG J := hX
  have hD := GlobalTheory.SmVec.hasDerivAt_dRep hv' hX'
  refine ⟨GlobalTheory.SmVec.dRep_mem hG hπ hv' hX', hD, fun g hg => ?_, fun c => ?_, fun w hw => ⟨?_, fun c => ?_⟩⟩
  · have hd := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
    have hY : g * X * g⁻¹ ∈ GlobalTheory.SmVec.lieG J := by
      have := GlobalTheory.SmVec.conj_mem_lieG hG (GlobalTheory.SmVec.inv_mem_UH hG hg) hX'
      rwa [Matrix.nonsing_inv_nonsing_inv _ hd] at this
    rw [GlobalTheory.SmVec.dRep_rep hG hπ hv' hg hY]
    congr 2
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
  · have h1 : HasDerivAt (fun t : ℝ => t * c) c 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
    have h2 := HasDerivAt.scomp_of_eq (0 : ℝ) hD h1 (by simp)
    rw [Complex.coe_smul]
    refine Eq.trans ?_ h2.deriv
    unfold dRep
    congr 1
    funext t
    simp [Function.comp_def, smul_smul]
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    rw [GlobalTheory.SmVec.inner_dRep hG hπ hv' hw' hX', neg_neg]
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    rw [GlobalTheory.SmVec.dRep_add hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw') hX', GlobalTheory.SmVec.dRep_smul c hw' hX']

end GlobalTheory.SmVecCalc

end
end

