module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavinLineLimit
section
namespace GroundTheory.Automorphic

open MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff

namespace WeakLimit

theorem integral_fourier_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hf hg)

theorem integral_fourierInv_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x := by
  rw [Real.fourierInv_eq_fourier_comp_neg, integral_fourier_mul_eq hf.comp_neg hg,
    ← integral_neg_eq_self (fun x => f x * 𝓕⁻ g x)]
  congr 1; funext x
  simp [Real.fourierInv_eq_fourier_neg]

theorem norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

theorem exists_smooth_near (a b : ℝ) {ψ : ℝ → ℂ} (hψ : Continuous ψ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ' : ℝ → ℂ, ContDiff ℝ ∞ ψ' ∧ HasCompactSupport ψ' ∧ ∀ t ∈ Icc a b, ‖ψ t - ψ' t‖ ≤ η := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).re)
    (Complex.continuous_re.comp hψ).continuousOn (η / 2) (by positivity)
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).im)
    (Complex.continuous_im.comp hψ).continuousOn (η / 2) (by positivity)
  have hpd : ∀ r : Polynomial ℝ, ContDiff ℝ ∞ (fun t : ℝ => r.eval t) := fun r => by
    simpa [Polynomial.coe_aeval_eq_eval] using r.contDiff_aeval (𝕜 := ℝ) ∞
  let χ : ContDiffBump ((a + b) / 2) := ⟨|b - a| + 1, |b - a| + 2, by positivity, by linarith⟩
  refine ⟨fun t => (χ t : ℂ) * (((p.eval t : ℝ) : ℂ) + ((q.eval t : ℝ) : ℂ) * Complex.I), ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul
      ((Complex.ofRealCLM.contDiff.comp (hpd p)).add
        ((Complex.ofRealCLM.contDiff.comp (hpd q)).mul contDiff_const))
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro t ht
    have hχ : χ t = 1 := by
      apply χ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq]
      have := ht.1; have := ht.2
      rw [abs_le]; constructor <;> cases abs_cases (b - a) <;> linarith
    show ‖ψ t - (χ t : ℂ) * _‖ ≤ η
    rw [hχ, Complex.ofReal_one, one_mul]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h1 := hp t ht
    have h2 := hq t ht
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add]
    rw [abs_sub_comm] at h1 h2
    linarith

end WeakLimit

theorem exists_smooth_weak_limit {K : ℕ → ℝ → ℝ} {a b : ℝ} (hKi : ∀ N, Integrable (K N))
    (hK0 : ∀ N t, 0 ≤ K N t) (hK1 : ∀ N, ∫ t, K N t ≤ 1)
    (hKs : ∀ N, Function.support (K N) ⊆ Icc a b)
    (hconv : ∀ ξ : ℝ, ∃ l : ℂ, Tendsto (fun N => 𝓕 (fun t => (K N t : ℂ)) ξ) atTop (𝓝 l))
    (hdecay : ∀ m : ℕ, ∃ C N₀, ∀ N ≥ N₀, ∀ ξ : ℝ,
      ‖𝓕 (fun t => (K N t : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ))) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ tsupport g ⊆ Icc a b ∧
      ∀ ψ : ℝ → ℂ, Continuous ψ →
        Tendsto (fun N => ∫ t, ψ t * K N t) atTop (𝓝 (∫ t, ψ t * g t)) := by
  set Kc : ℕ → ℝ → ℂ := fun N t => (K N t : ℂ) with hKc
  have hKci : ∀ N, Integrable (Kc N) := fun N => (hKi N).ofReal
  have hKn : ∀ N ξ, ‖𝓕 (Kc N) ξ‖ ≤ 1 := by
    intro N ξ
    refine (WeakLimit.norm_fourier_le _ ξ).trans ?_
    simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N _)]
    exact hK1 N
  choose Φ hΦ using hconv
  have hΦd : ∀ m : ℕ, ∃ C, ∀ ξ, ‖Φ ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ)) := by
    intro m
    obtain ⟨C, N₀, hC⟩ := hdecay m
    exact ⟨C, fun ξ => le_of_tendsto ((hΦ ξ).norm) (eventually_atTop.2 ⟨N₀, fun N hN => hC N hN ξ⟩)⟩
  have hΦm : AEStronglyMeasurable Φ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable)
      (ae_of_all _ hΦ)
  have hΦint : ∀ n : ℕ, Integrable (fun ξ : ℝ => ‖ξ‖ ^ n * ‖Φ ξ‖) := by
    intro n
    obtain ⟨C, hC⟩ := hΦd (n + 2)
    have hI : Integrable (fun ξ : ℝ => C * (1 + ‖ξ‖) ^ (-(2 : ℝ))) :=
      (integrable_one_add_norm (by norm_num)).const_mul C
    refine hI.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul hΦm.norm)
      (ae_of_all _ fun ξ => ?_)
    have h1 : 0 < 1 + |ξ| := by positivity
    rw [norm_mul, norm_pow, norm_norm, norm_norm, Real.norm_eq_abs]
    calc |ξ| ^ n * ‖Φ ξ‖ ≤ (1 + |ξ|) ^ n * (C * (1 + |ξ|) ^ (-((n + 2 : ℕ) : ℝ))) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (by linarith) n) (hC ξ) (norm_nonneg _)
            (by positivity)
      _ = C * (1 + |ξ|) ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add h1]
          congr 2; push_cast; ring
  have hΦi : Integrable Φ := (integrable_norm_iff hΦm).1 (by simpa using hΦint 0)
  set g : ℝ → ℂ := 𝓕⁻ Φ with hgdef
  have hg : ContDiff ℝ ∞ g := by
    rw [hgdef, Real.fourierInv_eq_fourier_comp_neg]
    exact Real.contDiff_fourier fun n _ => by simpa using (hΦint n).comp_neg

  have hsmooth : ∀ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Tendsto (fun N => ∫ t, ψ t * Kc N t) atTop (𝓝 (∫ t, ψ t * g t)) := by
    intro ψ hψ hψc
    let ψS := hψc.toSchwartzMap hψ
    have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
    have hθi : Integrable (𝓕⁻ ψ) := by
      have := (𝓕⁻ ψS).integrable (μ := volume)
      rwa [SchwartzMap.fourierInv_coe] at this
    have hFψ : Integrable (𝓕 ψ) := by
      have := (𝓕 ψS).integrable (μ := volume)
      rwa [SchwartzMap.fourier_coe] at this
    have hinv : 𝓕 (𝓕⁻ ψ) = ψ := hψ.continuous.fourier_fourierInv_eq hψi hFψ
    have e1 : ∀ N, ∫ t, ψ t * Kc N t = ∫ ξ, 𝓕⁻ ψ ξ * 𝓕 (Kc N) ξ := by
      intro N
      conv_lhs => rw [← hinv]
      exact WeakLimit.integral_fourier_mul_eq hθi (hKci N)
    have e2 : ∫ t, ψ t * g t = ∫ ξ, 𝓕⁻ ψ ξ * Φ ξ :=
      (WeakLimit.integral_fourierInv_mul_eq hψi hΦi).symm
    simp_rw [e1, e2]
    refine tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕⁻ ψ ξ‖) (fun N => ?_)
      hθi.norm (fun N => ae_of_all _ fun ξ => ?_) (ae_of_all _ fun ξ => (hΦ ξ).const_mul _)
    · exact hθi.aestronglyMeasurable.mul
        (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hKn N ξ)

  have hgi : LocallyIntegrable g := hg.continuous.locallyIntegrable
  have hsupp : Function.support g ⊆ Icc a b := by
    have hae : ∀ᵐ x, x ∈ (Icc a b)ᶜ → g x = 0 := by
      refine isClosed_Icc.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hgi.locallyIntegrableOn _) fun φ hφ hφc hφs => ?_
      have hlim := hsmooth (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ)
        (hφc.comp_left Complex.ofReal_zero)
      have h0 : ∀ N, ∫ t, (φ t : ℂ) * Kc N t = 0 := by
        intro N
        refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
        by_cases ht : t ∈ Icc a b
        · have : φ t = 0 := image_eq_zero_of_notMem_tsupport fun h' => hφs h' ht
          simp [this]
        · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
          simp [Kc, this]
      simp_rw [h0] at hlim
      simp_rw [Complex.real_smul]
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    intro x hx
    by_contra hxI
    have hopen : IsOpen ((Icc a b)ᶜ ∩ Function.support g) :=
      isClosed_Icc.isOpen_compl.inter hg.continuous.isOpen_support
    have hnull : volume ((Icc a b)ᶜ ∩ Function.support g) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      exact hae.mono fun y hy hy' => hy'.2 (hy hy'.1)
    exact (hopen.measure_ne_zero volume ⟨x, hxI, hx⟩) hnull
  refine ⟨g, hg, closure_minimal hsupp isClosed_Icc, fun ψ hψ => ?_⟩
  have hgc : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) (closure_minimal hsupp isClosed_Icc)
  have hIK : ∀ φ : ℝ → ℂ, Continuous φ → ∀ N, Integrable (fun t => φ t * Kc N t) := by
    intro φ hφ N
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ.continuousOn
    refine ((hKi N).const_mul B).mono' (hφ.aestronglyMeasurable.mul (hKci N).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ Icc a b
    · rw [norm_mul]
      simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]
      exact mul_le_mul_of_nonneg_right (hB t ht) (hK0 N t)
    · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
      simp [Kc, this]
  have hIg : ∀ φ : ℝ → ℂ, Continuous φ → Integrable (fun t => φ t * g t) := fun φ hφ =>
    (hφ.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  set L := ∫ t, ‖g t‖ with hLdef
  have hL : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set η := δ / (4 * (L + 2)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ψ', hψ', hψ'c, hψψ'⟩ := WeakLimit.exists_smooth_near a b hψ hηpos
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hsmooth ψ' hψ' hψ'c) (δ / 2) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hdiffK : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ ≤ η := by
    rw [← integral_sub (hIK ψ hψ N) (hIK ψ' hψ'.continuous N)]
    refine (norm_integral_le_of_norm_le ((hKi N).const_mul η) (ae_of_all _ fun t => ?_)).trans ?_
    · rw [← sub_mul, norm_mul]
      by_cases ht : t ∈ Icc a b
      · simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]
        exact mul_le_mul_of_nonneg_right (hψψ' t ht) (hK0 N t)
      · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
        simp [Kc, this]
    · rw [integral_const_mul]
      exact mul_le_of_le_one_right hηpos.le (hK1 N)
  have hdiffg : ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖ ≤ η * L := by
    rw [← integral_sub (hIg ψ' hψ'.continuous) (hIg ψ hψ), hLdef, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hg.continuous.norm.integrable_of_hasCompactSupport hgc.norm).const_mul η) (ae_of_all _ fun t => ?_)
    rw [← sub_mul, norm_mul]
    by_cases ht : t ∈ Icc a b
    · rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_right (hψψ' t ht) (norm_nonneg _)
    · have : g t = 0 := Function.notMem_support.1 fun h' => ht (hsupp h')
      simp [this]
  have hmid : dist (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t) < δ / 2 := hN₀ N hN
  rw [dist_eq_norm] at hmid ⊢
  have h3 : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ ≤
      ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ +
        ‖(∫ t, ψ' t * Kc N t) - ∫ t, ψ' t * g t‖ + ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖ :=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by
      linarith [norm_sub_le_norm_sub_add_norm_sub (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t)
        (∫ t, ψ t * g t)])
  have h4 : η + η * L < δ / 2 := by
    have hpos : 0 < 4 * (L + 2) := by positivity
    have h5 : η * (4 * (L + 2)) = δ := by rw [hη]; field_simp
    nlinarith [mul_nonneg hηpos.le hL]
  show ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ < δ
  linarith

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.FiniteLengthLattice
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

def HasFiniteLength (ρ : Representation ℂ G V) : Prop :=
  IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule

variable {ρ : Representation ℂ G V}

theorem hasFiniteLength_iff :
    HasFiniteLength ρ ↔
      WellFoundedLT (Subrepresentation ρ) ∧ WellFoundedGT (Subrepresentation ρ) := by
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff, IsArtinian]
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨e.strictMono.wellFoundedLT, e.strictMono.wellFoundedGT⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e.symm.strictMono.wellFoundedGT, e.symm.strictMono.wellFoundedLT⟩

theorem HasFiniteLength.wellFoundedLT (h : HasFiniteLength ρ) :
    WellFoundedLT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).1

theorem HasFiniteLength.wellFoundedGT (h : HasFiniteLength ρ) :
    WellFoundedGT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).2

theorem hasFiniteLength_of_strictMono {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, PartialOrder (α i)] [∀ i, WellFoundedLT (α i)] [∀ i, WellFoundedGT (α i)]
    (Λ : Subrepresentation ρ → ∀ i, α i) (hΛ : StrictMono Λ) : HasFiniteLength ρ := by
  rw [hasFiniteLength_iff]
  refine ⟨hΛ.wellFoundedLT, ?_⟩
  have h1 : WellFoundedLT (∀ i, (α i)ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i, α i) := h1
  exact hΛ.wellFoundedGT

theorem hasFiniteLength_of_subsingleton [Subsingleton V] : HasFiniteLength ρ := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  exact IsFiniteLength.of_subsingleton

theorem hasFiniteLength_of_isIrreducible [ρ.IsIrreducible] : HasFiniteLength ρ := by
  classical
  have : Finite (Subrepresentation ρ) := Finite.of_equiv _ IsSimpleOrder.equivBool.symm
  rw [hasFiniteLength_iff]
  exact ⟨Finite.to_wellFoundedLT, Finite.to_wellFoundedGT⟩

section MapComap

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}

def subrepMap (f : Representation.IntertwiningMap ρ σ) (A : Subrepresentation ρ) :
    Subrepresentation σ where
  toSubmodule := A.toSubmodule.map f.toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, A.apply_mem_toSubmodule g hx, Representation.IntertwiningMap.isIntertwining _ _ f g x⟩

def subrepComap (f : Representation.IntertwiningMap ρ σ) (B : Subrepresentation σ) :
    Subrepresentation ρ where
  toSubmodule := B.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g x hx := by
    show f (ρ g x) ∈ B.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact B.apply_mem_toSubmodule g hx

theorem subrepMap_mono (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepMap f) :=
  fun _ _ h _ ⟨x, hx, hxy⟩ => ⟨x, h hx, hxy⟩

theorem subrepComap_mono (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepComap f) :=
  fun _ _ h _ hx => h hx

theorem hasFiniteLength_of_injective (f : Representation.IntertwiningMap ρ σ)
    (hf : Injective f) (hσ : HasFiniteLength σ) : HasFiniteLength ρ := by
  have := hσ.wellFoundedLT
  have := hσ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation σ)
    (fun A _ => subrepMap f A) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepMap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun x hx => ?_
  obtain ⟨y, hy, hyx⟩ : f x ∈ subrepMap f A := by
    show f x ∈ subrepMap f A
    rw [show subrepMap f A = subrepMap f B from h1]
    exact ⟨x, hx, rfl⟩
  rw [← hf hyx]
  exact hy

theorem hasFiniteLength_of_surjective (f : Representation.IntertwiningMap ρ σ)
    (hf : Surjective f) (hρ : HasFiniteLength ρ) : HasFiniteLength σ := by
  have := hρ.wellFoundedLT
  have := hρ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation ρ)
    (fun B _ => subrepComap f B) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepComap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun y hy => ?_
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ subrepComap f B := hy
  rw [← show subrepComap f A = subrepComap f B from h1] at hx
  exact hx

end MapComap

section Filtration

theorem hasFiniteLength_of_filtration {k : ℕ} (Vf : ℕ → Submodule ℂ V)
    (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ g)) (h0 : Vf 0 = ⊥) (hk : Vf k = ⊤)
    {W : Fin k → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (σ : ∀ j, Representation ℂ G (W j))
    (Ψ : ∀ j : Fin k, Representation.IntertwiningMap (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1)))
      (σ j))
    (hΨ : ∀ (j : Fin k) x, Ψ j x = 0 ↔ (x : V) ∈ Vf j) (hσ : ∀ j, HasFiniteLength (σ j)) :
    HasFiniteLength ρ := by
  classical
  have := fun j => (hσ j).wellFoundedLT
  have := fun j => (hσ j).wellFoundedGT

  let cut : ∀ j : Fin k, Subrepresentation ρ →
      Subrepresentation (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1))) := fun j A =>
    ⟨A.toSubmodule.comap (Vf (j + 1)).subtype, fun g x hx => A.apply_mem_toSubmodule g hx⟩
  refine hasFiniteLength_of_strictMono (α := fun j => Subrepresentation (σ j))
    (fun A j => subrepMap (Ψ j) (cut j A)) fun A B hAB => ?_
  have hmono' : ∀ j, subrepMap (Ψ j) (cut j A) ≤ subrepMap (Ψ j) (cut j B) := fun j =>
    subrepMap_mono _ (fun x hx => hAB.le hx)
  rw [Pi.lt_def]
  refine ⟨hmono', ?_⟩

  have hex : ∃ j, j < k ∧ ∃ x ∈ B, x ∈ Vf (j + 1) ∧ x ∉ A := by
    obtain ⟨x, hxB, hxA⟩ := IsConcreteLE.exists_of_lt hAB
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [h0] at hk
      exact hxA (by
        have : x ∈ (⊤ : Submodule ℂ V) := trivial
        rw [← hk] at this
        rw [(Submodule.mem_bot ℂ).1 this]
        exact A.toSubmodule.zero_mem)
    refine ⟨k - 1, by omega, x, hxB, ?_, hxA⟩
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), hk]
    trivial
  let j₀ := Nat.find hex
  obtain ⟨hj₀k, x, hxB, hxV, hxA⟩ := Nat.find_spec hex
  have hbelow : ∀ y ∈ B, y ∈ Vf j₀ → y ∈ A := by
    intro y hyB hyV
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h, h0] at hyV
      rw [(Submodule.mem_bot ℂ).1 hyV]
      exact A.toSubmodule.zero_mem
    · by_contra hyA
      obtain ⟨m, hm⟩ : ∃ m, j₀ = m + 1 := ⟨j₀ - 1, by omega⟩
      have := Nat.find_min hex (m := m) (by omega)
      exact this ⟨by omega, y, hyB, by rw [← hm]; exact hyV, hyA⟩
  refine ⟨⟨j₀, hj₀k⟩, lt_of_le_of_ne (hmono' _) fun heq => hxA ?_⟩
  have hmem : Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩ ∈ subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B) :=
    ⟨⟨x, hxV⟩, hxB, rfl⟩
  have heq' : subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ A) =
      subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B) := heq
  rw [← heq'] at hmem
  obtain ⟨y, hyA, hyx⟩ := hmem
  have hyx' : Ψ ⟨j₀, hj₀k⟩ y = Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩ := hyx
  have hd : Ψ ⟨j₀, hj₀k⟩ (⟨x, hxV⟩ - y) = 0 := by rw [map_sub, hyx', sub_self]
  rw [hΨ] at hd
  have hyA' : (y : V) ∈ A := hyA
  have hdB : ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) ∈ B :=
    B.toSubmodule.sub_mem hxB (hAB.le hyA')
  have := hbelow _ hdB hd
  have hx' : x = ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) + y := by simp
  rw [hx']
  exact A.toSubmodule.add_mem this hyA'

end Filtration

end GroundTheory.Automorphic
end
end

