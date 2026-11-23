module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0031
public import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0019
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscHadamard
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_hadamard (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (a b : KTp K d.D d.N)
    (hab : d.IsPres hd h a b) (sg : K →+* ℂ) :
    d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg ≤
      d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) := by
  haveI : MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) :=
    ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (Nat.succ_pos _)
  have he := hd.a4.choose_spec.1
  have hF : ∀ c, MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        -Real.log (d.nrm c d.wF (hd.a4.choose c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
    intro c
    have := ((d.int_Nsg hd h hI2be c sg).1 d.wF (hd.a4.choose c) (by simp) (he c).1 (he c).2).neg
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.neg_apply]
    rw [← finsum_neg_distrib]
    congr 1; ext P
    rw [← finsum_neg_distrib]
    rfl
  have hR : MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      (d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          -Real.log (d.nrm c d.wF (hd.a4.choose c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) :=
    (MeasureTheory.integrable_const _).add
      ((MeasureTheory.integrable_finsetSum _ fun c _ => hF c).const_mul 2)
  have hmono := MeasureTheory.integral_mono_ae (d.integrable_log_norm_sub_log_norm hd h a b hab sg) hR
    (d.disc_pointwise hd h a b hab sg)
  have hc : ∫ _z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1),
      ((d.del : ℝ) * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))))
        ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) =
      (d.del : ℝ) * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) := by simp
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _)
      ((MeasureTheory.integrable_finsetSum _ fun c _ => hF c).const_mul 2),
    hc, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ fun c _ => hF c] at hmono
  have hN : d.Nsg d.wF hd.a4.choose sg = ∑ c, ∫ z, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
      -Real.log (d.nrm c d.wF (hd.a4.choose c) P) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := rfl
  have hm : d.mSgP sg a b = ∫ z, (Real.log ‖d.evT sg 0 (d.tOf z) a‖ -
      Real.log ‖d.evT sg 0 (d.tOf z) b‖) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := rfl
  rw [hN, hm]
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntegralLeOfAeLeAffine
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

open MeasureTheory

theorem be_pos (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) : 0 < d.be c P := by
  unfold Data.be
  apply Real.sqrt_pos.mpr
  have h1 := hd.nrm_pos c P (hd.w_mem (d.jc c) c) (hd.w_base c)
  exact lt_of_lt_of_le (pow_pos h1 2)
    (Finset.single_le_sum (f := fun j => d.nrm c d.wL (d.w j c) P ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ (d.jc c)))

theorem fneg {α : Type*} (s : Set α) (g : α → ℝ) : ∑ᶠ x ∈ s, -g x = -∑ᶠ x ∈ s, g x := by
  simp only [finsum_neg_distrib]

theorem integral_le_of_ae_le_affine {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (F1 F2 F3 : X → ℝ) (C r : ℝ) (I1 : Integrable F1 μ) (I2 : Integrable F2 μ) (I3 : Integrable F3 μ)
    (hle : ∀ᵐ x ∂μ, F1 x ≤ F2 x + C + r * F3 x) :
    ∫ x, F1 x ∂μ ≤ ∫ x, F2 x ∂μ + C + r * ∫ x, F3 x ∂μ := by
  have hC : Integrable (fun _ : X => C) μ := integrable_const C
  have h2C : Integrable (fun x => F2 x + C) μ := I2.add hC
  have hI : Integrable (fun x => F2 x + C + r * F3 x) μ := h2C.add (I3.const_mul r)
  calc ∫ x, F1 x ∂μ ≤ ∫ x, (F2 x + C + r * F3 x) ∂μ := integral_mono_ae I1 hI hle
    _ = ∫ x, F2 x ∂μ + C + r * ∫ x, F3 x ∂μ := by
      rw [integral_add h2C (I3.const_mul r), integral_const_mul, integral_add I2 hC]
      simp

theorem int_neg (c : ι) (sg : K →+* ℂ) (g : (Ω c →+* ℂ) → ℝ)
    (hI : Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)), g P)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) :
    Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)), -g P)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  exact hI.neg.congr (ae_of_all _ fun z => by simp only [Pi.neg_apply, fneg])

theorem sg_one (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) (c : ι) (sg : K →+* ℂ) :
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
      -Real.log (d.nrm c d.wL (f c) P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) ≤
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
      -Real.log (d.nrm c d.wL (f c) P / d.be c P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) +
    d.delc c * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) + d.cc / d.i *
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
      -Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  haveI := ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (B := d.D) (Nat.succ_pos d.N)
  have hint := d.int_Nsg hd h hI2be c sg
  have I1 := d.int_neg c sg (fun P => Real.log (d.nrm c d.wL (f c) P))
    (hint.1 d.wL (f c) (by simp) (hf c).1 (hf c).2)
  have I2 := d.int_neg c sg (fun P => Real.log (d.nrm c d.wL (f c) P / d.be c P))
    (hint.2 (f c) (hf c).1 (hf c).2)
  have I3 := d.int_neg c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P))
    (hint.1 (d.n1 • d.wde) (d.et c) (by simp) (hd.et_mem c) (hd.et_ne c))
  set κ := d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo
  refine integral_le_of_ae_le_affine _ _ _ _ _ _ I1 I2 I3 ?_
  filter_upwards [d.hint_fs hd h c sg] with z hz
  obtain ⟨s, hcard, -, hsum⟩ := hz
  change d.hintSm c sg (fun P => -Real.log (d.nrm c d.wL (f c) P)) z ≤
    d.hintSm c sg (fun P => -Real.log (d.nrm c d.wL (f c) P / d.be c P)) z +
    d.delc c * κ + d.cc / d.i *
      d.hintSm c sg (fun P => -Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) z
  simp only [hsum]
  have e : (d.delc c : ℝ) * κ = ∑ P ∈ s, κ := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [e, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun P _ => ?_
  have hn := hd.nrm_pos c P (hf c).1 (hf c).2
  have hb := d.be_pos hd c P
  have hI := hI2be c P
  rw [Real.log_div hn.ne' hb.ne']
  simp only [κ]
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrdEqValuationRatioBaseAdd
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def translatedForm (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) : KTp K d.D d.N :=
  MvPolynomial.aeval (fun v : TVar d.D d.N =>
    if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F

noncomputable def localHeightAtPrime (h : d.S1) (f : ∀ c, A c) (c : ι)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ordMM c (d.Wres c w) (f c) : ℝ)

noncomputable def localHeightAtEmbedding (f : ∀ c, A c) (c : ι) (sg : K →+* ℂ) : ℝ :=
  ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
    -Real.log (d.nrm c d.wL (f c) P / d.be c P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

def heightSubstitutionCondition (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι) (F : KTp K d.D d.N) (κ : K) : Prop :=
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F * algebraMap K (KTf K d.D d.N) κ *
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
        (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) =
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F) *
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)

theorem ratio_eq_of_eq_smul_field {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V}
    (hg : g ≠ 0) {a : Ω'} (hf : f = a • g) : ratio (Ω := Ω') f g = a := by
  classical
  have h : ∃ b : Ω', f = b • g := ⟨a, hf⟩
  unfold ratio
  rw [dite_eq_left h]
  exact smul_left_injective Ω' hg (h.choose_spec.symm.trans hf)

theorem eq_ratio_base_smul (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) :
    f = ratio (Ω := Ω c) f (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hw := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hw⟩ : 𝒜 c d.wL)
    (by simpa using hw0)).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • d.w (d.jc c) c := by
    have h1 := congrArg Subtype.val ha
    simp only [SetLike.val_smul] at h1
    exact h1.symm
  rw [ratio_eq_of_eq_smul_field hw0 hfa]
  exact hfa

theorem ratio_base_ne_zero (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ratio (Ω := Ω c) f (d.w (d.jc c) c) ≠ 0 := by
  intro h0
  apply hf0
  rw [d.eq_ratio_base_smul hd c hf, h0, zero_smul]

theorem linearCombination_mem_section (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  unfold wx
  rw [Finset.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem ord_eq_valuation_ratio_base_add (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ((d.ord c v d.wL f : ℤ) : WithTop ℤ) =
      v (ratio (Ω := Ω c) f (d.w (d.jc c) c)) + (d.ord c v d.wL (d.w (d.jc c) c) : WithTop ℤ) := by
  have hfa := d.eq_ratio_base_smul hd c hf
  have ha := d.ratio_base_ne_zero hd c hf hf0
  conv_lhs => rw [hfa]
  exact hd.ord_smul c v hv _ (hd.w_mem _ c) (hd.w_base c) ha

theorem eq_ratio_smul_of_mem (hd : d.AxH 𝒜) (c : ι) {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL)
    (hg0 : g ≠ 0) : f = ratio (Ω := Ω c) f g • g := by
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hg⟩ : 𝒜 c d.wL)
    (by simpa using hg0)).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • g := by
    have h1 := congrArg Subtype.val ha
    simp only [SetLike.val_smul] at h1
    exact h1.symm
  rw [ratio_eq_of_eq_smul_field hg0 hfa]
  exact hfa

theorem ratio_ne_zero_of_ne_zero (hd : d.AxH 𝒜) (c : ι) {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL)
    (hg0 : g ≠ 0) (hf0 : f ≠ 0) : ratio (Ω := Ω c) f g ≠ 0 := by
  intro h0
  apply hf0
  rw [d.eq_ratio_smul_of_mem hd c hf hg hg0, h0, zero_smul]

theorem ord_eq_valuation_ratio_add (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL) (hg0 : g ≠ 0) (hf0 : f ≠ 0) :
    ((d.ord c v d.wL f : ℤ) : WithTop ℤ) =
      v (ratio (Ω := Ω c) f g) + (d.ord c v d.wL g : WithTop ℤ) := by
  have hfa := d.eq_ratio_smul_of_mem hd c hf hg hg0
  have ha := d.ratio_ne_zero_of_ne_zero hd c hf hg hg0 hf0
  conv_lhs => rw [hfa]
  exact hd.ord_smul c v hv _ hg hg0 ha

theorem ratio_mul_ratio_height (hd : d.AxH 𝒜) (c : ι) {f g e : A c} (hf : f ∈ 𝒜 c d.wL)
    (hg : g ∈ 𝒜 c d.wL) (he : e ∈ 𝒜 c d.wL) (hg0 : g ≠ 0) (he0 : e ≠ 0) :
    ratio (Ω := Ω c) f e = ratio (Ω := Ω c) f g * ratio (Ω := Ω c) g e := by
  have h1 := d.eq_ratio_smul_of_mem hd c hf hg hg0
  have h2 := d.eq_ratio_smul_of_mem hd c hg he he0
  apply ratio_eq_of_eq_smul_field he0
  rw [mul_smul, ← h2, ← h1]

theorem coe_untopD_of_ne_top {v : WithTop ℤ} (hv : v ≠ ⊤) : ((v.untopD 0 : ℤ) : WithTop ℤ) = v := by
  obtain ⟨x, rfl⟩ := WithTop.ne_top_iff_exists.1 hv
  rw [WithTop.untopD_coe]

theorem ordMinMax_eq_ratio_untop_sub (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hint : ∀ j, 0 ≤ v (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c v f = (v (ratio (Ω := Ω c) f (d.w (d.jc c) c))).untopD 0 -
      (v (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))).untopD 0 := by
  have key : ∀ {g : A c}, g ∈ 𝒜 c d.wL → g ≠ 0 → d.ord c v d.wL g =
      (v (ratio (Ω := Ω c) g (d.w (d.jc c) c))).untopD 0 + d.ord c v d.wL (d.w (d.jc c) c) := by
    intro g hg hg0
    have h := d.ord_eq_valuation_ratio_base_add hd c v hv hg hg0
    have hne : v (ratio (Ω := Ω c) g (d.w (d.jc c) c)) ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]
      exact d.ratio_base_ne_zero hd c hg hg0
    rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
    exact WithTop.coe_inj.1 h
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = d.ord c v d.wL (d.w j0 c) := by
    apply le_antisymm
    · exact ciInf_le (Set.finite_range _).bddBelow (⟨j0, hj0⟩ : {j // d.w j c ≠ 0})
    · haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨j0, hj0⟩⟩
      refine le_ciInf fun j => ?_
      have h := d.ord_eq_valuation_ratio_add hd c v hv (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      have hnn := hint j.1
      have hne : v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c)) ≠ ⊤ := by
        rw [Ne, AddValuation.top_iff]
        exact d.ratio_ne_zero_of_ne_zero hd c (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
      have h' := WithTop.coe_inj.1 h
      rw [← coe_untopD_of_ne_top hne] at hnn
      have h0 : 0 ≤ (v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c))).untopD 0 := by exact_mod_cast hnn
      omega
  unfold ordMM
  rw [hinf, key hf hf0, key (hd.w_mem j0 c) hj0]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

