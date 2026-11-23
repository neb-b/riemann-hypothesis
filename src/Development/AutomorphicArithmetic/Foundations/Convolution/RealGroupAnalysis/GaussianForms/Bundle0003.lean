module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamReal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma half_root (a : ℂ) (ha : 0 < a.re) :
    (a ^ (1 / 2 : ℂ)) ^ 2 = a ∧ 0 < (a ^ (1 / 2 : ℂ)).re ∧
      |(a ^ (1 / 2 : ℂ)).im| < (a ^ (1 / 2 : ℂ)).re := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h2 : (a ^ (1 / 2 : ℂ)) ^ 2 = a := by
    have := Complex.cpow_nat_inv_pow a (n := 2) two_ne_zero
    simpa [one_div] using this
  have hpos : 0 < (a ^ (1 / 2 : ℂ)).re := by
    have harg : |a.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl ha)
    have harg' := abs_lt.1 harg
    rw [Complex.cpow_def_of_ne_zero ha0, Complex.exp_re]
    have him : (Complex.log a * (1 / 2 : ℂ)).im = a.arg / 2 := by
      simp [Complex.log_im]
      ring
    rw [him]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> linarith [Real.pi_pos]
  refine ⟨h2, hpos, ?_⟩
  generalize a ^ (1 / 2 : ℂ) = w at h2 hpos
  have hre : a.re = w.re ^ 2 - w.im ^ 2 := by
    rw [← h2, pow_two, Complex.mul_re]
    ring
  apply abs_lt_of_sq_lt_sq _ hpos.le
  linarith

private lemma lamR_props (β : ℝ) (hβ : β ≠ 0) :
    lamR β ^ 2 = 1 / (2 * Complex.I * (β : ℂ)) ∧ 0 < (lamR β).re := by
  have hr : 0 < √|β| := Real.sqrt_pos.2 (abs_pos.2 hβ)
  have hrc : ((√|β| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hbc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hsq : ((√|β| : ℝ) : ℂ) ^ 2 = ((|β| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (abs_nonneg β)]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rcases lt_or_gt_of_ne hβ with h | h
  · have hs : ((SignType.sign β : SignType) : ℂ) = -1 := by simp [sign_neg h]
    have hab : ((|β| : ℝ) : ℂ) = -(β : ℂ) := by
      rw [abs_of_neg h]; push_cast; ring
    constructor
    · simp only [lamR, hs]
      push_cast
      rw [div_pow, mul_pow, hsq, hab]
      field_simp
      linear_combination (-(2 + Complex.I)) * hI
    · simp only [lamR, hs]
      rw [Complex.div_ofReal_re]
      simp
      positivity
  · have hs : ((SignType.sign β : SignType) : ℂ) = 1 := by simp [sign_pos h]
    have hab : ((|β| : ℝ) : ℂ) = (β : ℂ) := by
      rw [abs_of_pos h]
    constructor
    · simp only [lamR, hs]
      push_cast
      rw [div_pow, mul_pow, hsq, hab]
      field_simp
      linear_combination (Complex.I - 2) * hI
    · simp only [lamR, hs]
      rw [Complex.div_ofReal_re]
      simp
      positivity

theorem UpperTheory.ConvolutionTheory.R2.C.lamReal :
    ∀ β : ℝ, β ≠ 0 → abelian₂ (volume : Measure ℝ) (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * (x : ℂ) ^ 2)) (fun x => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) = lamR β := by
  intro β hβ
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hbc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  obtain ⟨D, hDdef⟩ : ∃ D : ℂ, D = 1 + 2 * Complex.I * (β : ℂ) := ⟨_, rfl⟩
  have hDre : D.re = 1 := by simp [hDdef]
  have hDim : D.im = 2 * β := by simp [hDdef]
  have hD : D ≠ 0 := by
    intro h
    rw [h] at hDre
    simp at hDre
  have hnsq : 0 < Complex.normSq D := Complex.normSq_pos.2 hD
  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = 2 * Complex.I * (β : ℂ) / D := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by
    rw [hsdef]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hI0) hbc) hD
  have hsre : 0 < s.re := by
    rw [hsdef, Complex.div_re]
    have e1 : (2 * Complex.I * (β : ℂ)).re = 0 := by simp
    have e2 : (2 * Complex.I * (β : ℂ)).im = 2 * β := by simp
    rw [e1, e2, hDim, zero_mul, zero_div, zero_add]
    have : 0 < 2 * β * (2 * β) := by
      have := mul_self_pos.2 (mul_ne_zero two_ne_zero hβ)
      simpa using this
    exact div_pos this hnsq
  have hinvD : 0 < (1 / D).re := by
    rw [one_div, Complex.inv_re, hDre]
    exact div_pos one_pos hnsq
  have hinvs : 0 < (1 / s).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos hsre (Complex.normSq_pos.2 hs0)
  have hb : (-(Real.pi : ℂ) * D).re < 0 := by
    simp [hDre, hDim, Real.pi_pos]
  have hinner : ∀ y : ℝ,
      (∫ x : ℝ, Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * ((x + y : ℝ) : ℂ) ^ 2)) =
      (1 / D) ^ (1 / 2 : ℂ) * Complex.exp (-((Real.pi : ℂ) * s) * (y : ℂ) ^ 2) := by
    intro y
    have hfun : (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * ((x + y : ℝ) : ℂ) ^ 2)) =
        fun x : ℝ => Complex.exp ((-(Real.pi : ℂ) * D) * (x : ℂ) ^ 2 +
          (-(4 * Real.pi * Complex.I * (β : ℂ) * (y : ℂ))) * (x : ℂ) +
          (-(2 * Real.pi * Complex.I) * (β : ℂ) * (y : ℂ) ^ 2)) := by
      funext x
      rw [← Complex.exp_add, hDdef]
      congr 1
      push_cast
      ring
    rw [hfun, integral_cexp_quadratic hb]
    congr 1
    · congr 1
      field_simp
    · congr 1
      rw [hsdef, hDdef]
      have hD' : (1 + 2 * Complex.I * (β : ℂ)) ≠ 0 := hDdef ▸ hD
      field_simp
      ring
  unfold abelian₂
  simp only [hinner]
  rw [integral_const_mul]
  have houter : (∫ y : ℝ, Complex.exp (-((Real.pi : ℂ) * s) * (y : ℂ) ^ 2)) = (1 / s) ^ (1 / 2 : ℂ) := by
    have hre : 0 < ((Real.pi : ℂ) * s).re := by
      simpa using mul_pos Real.pi_pos hsre
    rw [integral_gaussian_complex hre]
    congr 1
    field_simp
  rw [houter]
  obtain ⟨hA2, hApos, hAim⟩ := half_root _ hinvD
  obtain ⟨hB2, hBpos, hBim⟩ := half_root _ hinvs
  obtain ⟨hL2, hLpos⟩ := lamR_props β hβ
  generalize (1 / D) ^ (1 / 2 : ℂ) = A at hA2 hApos hAim
  generalize (1 / s) ^ (1 / 2 : ℂ) = B at hB2 hBpos hBim
  have hsq : (A * B) ^ 2 = lamR β ^ 2 := by
    rw [mul_pow, hA2, hB2, hL2, hsdef]
    field_simp
  have hzre : 0 < (A * B).re := by
    rw [Complex.mul_re]
    have h1 : A.im * B.im ≤ |A.im| * |B.im| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 : |A.im| * |B.im| < A.re * B.re :=
      mul_lt_mul'' hAim hBim (abs_nonneg _) (abs_nonneg _)
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact h
  · exfalso
    rw [h, Complex.neg_re] at hzre
    linarith
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NLevel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem psi_eq_one {F : Type} [Field F] [NumberField F] (x : A F) (hx : x.1 = 0)
    (hU : x.2 ∈ finiteInvDifferent F) : ψ x = 1 := by
  have hxe : x = finiteAdeleInr x.2 := Prod.ext (by simpa using hx) (by simp)
  have h := finiteAdelicChar_eq_one_of_mem hU
  rw [finiteAdelicChar_apply, ← hxe] at h
  simp [ψ, h]

private theorem tensor_case {F : Type} [Field F] [NumberField F] (δ : F)
    (f : SchwartzMap (Fin 4 → mixedEmbedding.mixedSpace F) ℂ) {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F) :
    ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v,
      ψ (b * q4 δ v) * schwartzBruhatTensorPi f g v = schwartzBruhatTensorPi f g v := by
  have hc : IsCompact (tsupport g) := ((mem_finiteSchwartzBruhatPi F).1 hg).2
  let qf : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → FiniteAdeleRing (𝓞 F) F :=
    fun w => w 2 ^ 2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * w 3 ^ 2 - w 1 * w 0
  have hqf : Continuous qf := by
    have h (i : Fin 4) : Continuous fun w : Fin 4 → FiniteAdeleRing (𝓞 F) F => w i := continuous_apply i
    exact (((h 2).pow 2).sub (continuous_const.mul ((h 3).pow 2))).sub ((h 1).mul (h 0))
  have hU := isOpen_finiteInvDifferent F
  have h0 : ∀ᶠ a in 𝓝 (0 : FiniteAdeleRing (𝓞 F) F), ∀ y ∈ qf '' tsupport g,
      a * y ∈ (finiteInvDifferent F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    refine (hc.image hqf).eventually_forall_of_forall_eventually (fun y _ => ?_)
    have hcont : Continuous fun z : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F => z.1 * z.2 :=
      continuous_mul
    exact hcont.continuousAt.eventually (hU.mem_nhds (by simpa using zero_mem (finiteInvDifferent F)))
  have h1 : ∀ᶠ b in 𝓝 (0 : A F), ∀ y ∈ qf '' tsupport g,
      b.2 * y ∈ (finiteInvDifferent F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (continuous_snd.tendsto (0 : A F)).eventually h0
  filter_upwards [h1] with b hb hb1 v
  by_cases hv : g (finPartPi v) = 0
  · simp [schwartzBruhatTensorPi, hv]
  · have hmem : finPartPi v ∈ tsupport g := subset_tsupport g hv
    have hq : (b * q4 δ v).2 = b.2 * qf (finPartPi v) := by
      have hp (x : A F) : (x ^ 2).2 = x.2 ^ 2 := rfl
      have hs (x y : A F) : (x - y).2 = x.2 - y.2 := rfl
      have hm (x y : A F) : (x * y).2 = x.2 * y.2 := rfl
      have ha : (algebraMap F (A F) δ).2 = algebraMap F (FiniteAdeleRing (𝓞 F) F) δ := rfl
      simp [q4, qf, finPartPi, hp, hs, hm, UpperTheory.ConvolutionTheory.R2.rt, ha]
    have hone : ψ (b * q4 δ v) = 1 := by
      refine psi_eq_one _ (by simp [hb1]) ?_
      rw [hq]
      exact hb _ ⟨_, hmem, rfl⟩
    rw [hone, one_mul]

private theorem span_case {F : Type} [Field F] [NumberField F] (δ : F) {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v, ψ (b * q4 δ v) * f v = f v := by
  refine Submodule.span_induction (p := fun f _ =>
    ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v, ψ (b * q4 δ v) * f v = f v) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨p, g, hg, rfl⟩
    exact tensor_case δ p hg
  · exact Eventually.of_forall fun b _ v => by simp
  · intro x y _ _ hx hy
    filter_upwards [hx, hy] with b h1 h2 hb v
    rw [Pi.add_apply, mul_add, h1 hb v, h2 hb v]
  · intro c x _ hx
    filter_upwards [hx] with b h1 hb v
    rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, h1 hb v]

theorem UpperTheory.ConvolutionTheory.R2.C.nLevel :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (φ : S4 F), ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v, ψ (b * q4 δ v) * φ.1 v = φ.1 v := by
  intro F _ _ δ φ
  exact span_case δ φ.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.OneSide
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem one_side {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] (μ : Measure G) [SFinite μ]
    [μ.IsAddLeftInvariant] (γ φ₁ φ₂ : G → ℂ) (h2 : Integrable φ₂ μ) (hP : Integrable (fun y => ∫ x, φ₁ x * γ (x + y) ∂μ) μ) :
    (∫ y, ∫ x, φ₁ x * γ (x + y) ∂μ ∂μ) * ∫ x, φ₂ x ∂μ = ∫ y, ∫ z, ∫ x, φ₂ z * (φ₁ x * γ (x + (z + y))) ∂μ ∂μ ∂μ := by
  have h3 := ((measurePreserving_prod_add μ μ).integrable_comp_of_integrable (h2.mul_prod hP))
  have h4 := integral_integral_swap (f := fun z y => φ₂ z * ∫ x, φ₁ x * γ (x + (z + y)) ∂μ) h3
  simp only [integral_const_mul] at h4 ⊢
  rw [← h4, mul_comm, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_add_left_eq_self (fun y => ∫ x, φ₁ x * γ (x + y) ∂μ) z]

theorem UpperTheory.ConvolutionTheory.R2.C.symm :
    ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G] (μ : Measure G) [SFinite μ] [μ.IsAddLeftInvariant] (γ φ₁ φ₂ : G → ℂ),
    Measurable γ → (∀ x, ‖γ x‖ ≤ 1) → Integrable φ₁ μ → Integrable φ₂ μ → Integrable (fun y => ∫ x, φ₁ x * γ (x + y) ∂μ) μ →
    Integrable (fun y => ∫ x, φ₂ x * γ (x + y) ∂μ) μ → abelian₂ μ γ φ₁ * ∫ x, φ₂ x ∂μ = abelian₂ μ γ φ₂ * ∫ x, φ₁ x ∂μ := by
  intro G _ _ _ _ μ _ _ γ φ₁ φ₂ hγ hb h1 h2 hP1 hP2
  refine (one_side μ γ φ₁ φ₂ h2 hP1).trans (Eq.trans ?_ (one_side μ γ φ₂ φ₁ h1 hP2).symm)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hm : Measurable fun p : G × G => γ (p.2 + (p.1 + y)) := hγ.comp (by fun_prop)
  have h3 := (h2.mul_prod h1).mul_bdd (c := 1) hm.aestronglyMeasurable (Eventually.of_forall fun p => hb _)
  have h4 := integral_integral_swap (f := fun z x => φ₂ z * φ₁ x * γ (x + (z + y))) h3
  simp only [mul_assoc] at h4
  refine h4.trans (integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun z => ?_)))
  simp only
  rw [add_left_comm]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ResBig
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma natCast_ne_zero_res {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (hm : v.valuation F (m : F) = 1) :
    ((m : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ 0 := by
  have hval : Valued.v (((m : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1 := by
    have hc : (((m : v.adicCompletionIntegers F)) : v.adicCompletion F)
        = algebraMap F (v.adicCompletion F) (m : F) := by
      rw [map_natCast]; exact map_natCast (v.adicCompletionIntegers F).subtype m
    rw [hc]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (m : F)).trans hm
  have hu : IsUnit (m : v.adicCompletionIntegers F) :=
    (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one.2 hval
  intro h0
  have h1 : IsLocalRing.residue (v.adicCompletionIntegers F) (m : v.adicCompletionIntegers F) = 0 := by
    simpa using h0
  rw [IsLocalRing.residue_eq_zero_iff] at h1
  exact (IsLocalRing.notMem_maximalIdeal.2 hu) h1

private lemma lt_card_of_inj {k : Type*} (n : ℕ) (f : Fin (n + 1) → k) (hf : Function.Injective f) :
    (n : ℕ∞) < ENat.card k := by
  rcases finite_or_infinite k with h | h
  · have := Nat.card_le_card_of_injective f hf
    rw [ENat.card_eq_coe_natCard]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact_mod_cast this
  · rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top n

theorem UpperTheory.ConvolutionTheory.R2.C.resBig :
    ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (n : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  intro F _ _ n
  have hne : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [Filter.eventually_cofinite]
  refine (GlobalTheory.QNorm.finite_valuation_ne_one F (Units.mk0 _ hne)).subset ?_
  intro v hv h1
  apply hv
  have h1' : v.valuation F ((n.factorial : ℕ) : F) = 1 := by simpa using h1
  have hfac := natCast_ne_zero_res v _ h1'
  refine lt_card_of_inj n (fun i => ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F))) ?_
  have key : ∀ i j : ℕ, i < j → j ≤ n →
      ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ (j : ℕ) := by
    intro i j hij hj heq
    have hd : ((j - i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = 0 := by
      rw [Nat.cast_sub hij.le, heq, sub_self]
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hij) ((Nat.sub_le j i).trans hj)
    apply hfac
    rw [hc, Nat.cast_mul, hd, zero_mul]
  intro a b hab
  rcases lt_trichotomy (a : ℕ) b with h | h | h
  · exact absurd hab (key _ _ h (Nat.lt_succ_iff.1 b.2))
  · exact Fin.ext h
  · exact absurd hab.symm (key _ _ h (Nat.lt_succ_iff.1 a.2))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SgnEx
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.sgnEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ a : (A F)ˣ, IsSgn a ∧ a * a = 1 ∧ ab a = 1 := by
  intro F _ _ _
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set s : TR.Rinf F := fun w => if w = w₀ then -1 else 1 with hs
  have hss : s * s = 1 := by
    funext w
    by_cases h : w = w₀ <;> simp [hs, h]
  have hx : ((TR.infEq F s, 1) : A F) * (TR.infEq F s, 1) = 1 := by
    have h1 : TR.infEq F s * TR.infEq F s = 1 := by rw [← map_mul, hss, map_one]
    exact Prod.ext h1 (mul_one _)
  let a : (A F)ˣ := ⟨(TR.infEq F s, 1), (TR.infEq F s, 1), hx, hx⟩
  have haa : a * a = 1 := Units.ext hx
  refine ⟨a, ⟨rfl, w₀, fun w => ?_⟩, haa, ?_⟩
  · change (TR.infEq F).symm (TR.infEq F s) w = _
    rw [RingEquiv.symm_apply_apply]
  · have h1 : IdeleGroup.ideleModule F (a * a) = 1 := by rw [haa, map_one]
    rw [map_mul] at h1
    have h2 : ab a * ab a = 1 := by
      have := congrArg (fun r : {r : ℝ // 0 < r} => (r : ℝ)) h1
      simpa [ab] using this
    have h3 : 0 < ab a := (IdeleGroup.ideleModule F a).2
    nlinarith
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SplitA
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private noncomputable def hI (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (InfinitePlace F → ℝ) ≃ₜ InfiniteAdeleRing F where
  toEquiv := (TR.infEq F).toEquiv
  continuous_toFun := TR.continuous_infEq F
  continuous_invFun := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem map_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ c : ENNReal, (infiniteAdeleMeasure F).map (hI F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := by
  have hH : ((infiniteAdeleMeasure F).map (hI F).symm).IsAddHaarMeasure :=
    (TR.infEq F).symm.toAddEquiv.isAddHaarMeasure_map (infiniteAdeleMeasure F)
      (hI F).symm.continuous (hI F).continuous
  have h := Measure.isAddLeftInvariant_eq_smul ((infiniteAdeleMeasure F).map (hI F).symm)
    (volume : Measure (InfinitePlace F → ℝ))
  obtain ⟨c, hν⟩ : ∃ c : NNReal, (infiniteAdeleMeasure F).map (hI F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := ⟨_, h⟩
  refine ⟨(c : ENNReal), hν.trans ?_⟩
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

private theorem psi_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (y : InfinitePlace F → ℝ) :
    adelicChar F (infiniteAdeleInl (TR.infEq F y)) = Real.fourierChar (-∑ w, y w) := by
  rw [adelicChar_infiniteAdeleInl, ← Finset.sum_neg_distrib, addChar_map_finsetSum]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [infiniteAdelicChar_apply_of_isReal (IsTotallyReal.isReal w)]
  have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
      (TR.infEq F y w) = y w :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)
  rw [e2]

theorem UpperTheory.ConvolutionTheory.R2.C.splitA :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∃ (e : A F ≃ᵐ (InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F) (c : ENNReal), (∀ x, e x = (TR.pInf F x, x.2)) ∧
      (adeleMeasure F).map e = c • (volume : Measure (InfinitePlace F → ℝ)).prod (finiteAdeleMeasure F)) ∧
    ∀ x : A F, ψ x = (∏ w, Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F x w : ℝ) : ℂ))) * ((finiteAdelicChar F x.2 : Circle) : ℂ) := by
  intro F _ _ _
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨c, hc⟩ := map_inf F
    let e : A F ≃ᵐ (InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F :=
      MeasurableEquiv.prodCongr (hI F).symm.toMeasurableEquiv (MeasurableEquiv.refl _)
    refine ⟨e, c, fun x => rfl, ?_⟩
    have h1 : ((infiniteAdeleMeasure F).map (hI F).symm).prod
        ((finiteAdeleMeasure F).map id) =
        ((infiniteAdeleMeasure F).prod (finiteAdeleMeasure F)).map (Prod.map (hI F).symm id) :=
      Measure.map_prod_map _ _ (hI F).symm.measurable measurable_id
    rw [Measure.map_id, hc, Measure.prod_smul_left] at h1
    exact h1.symm
  · have hx : x = infiniteAdeleInl (TR.infEq F (TR.pInf F x)) + finiteAdeleInr x.2 := by
      have h0 : TR.infEq F (TR.pInf F x) = x.1 := (TR.infEq F).apply_symm_apply x.1
      rw [h0]
      exact (infiniteAdeleInl_add_finiteAdeleInr x).symm
    have h1 : ψ x = ((Real.fourierChar (-∑ w, TR.pInf F x w) : Circle) : ℂ) *
        ((finiteAdelicChar F x.2 : Circle) : ℂ) := by
      rw [ψ]
      conv_lhs => rw [hx]
      rw [AddChar.map_add_eq_mul, Circle.coe_mul, psi_inf, finiteAdelicChar_apply]
    rw [h1, Real.fourierChar_apply, ← Complex.exp_sum]
    congr 2
    push_cast
    rw [← Finset.mul_sum]
    ring_nf
end

