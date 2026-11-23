module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0019

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AGFrameNonneg
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem aG_frame_nonneg (hd : d.AxH 𝒜) (h : d.S1) : 0 ≤ d.aG h d.wF hd.a4.choose := by
  classical
  have hespec := hd.a4.choose_spec
  unfold aG
  refine Finset.sum_nonneg fun c _ => ?_
  have hec : hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hespec.1 c
  have hk : ∃ k, d.thp (hd.sel k) c ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨q, hq, p, hp⟩ := hespec.2.2 (fun _ => 1)
    have e1 := hp c
    simp only [mul_one] at e1
    apply hq c
    rw [e1]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hno k, ratio_eq_of_eq_smul hec.2 (zero_smul (Ω c) (hd.a4.choose c)).symm, map_zero, mul_zero]
  obtain ⟨k, hk⟩ := hk
  have htm : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  have hr := eq_ratio_smul_on_line d (hd := hd) htm hec.1 hec.2
  have hr0 : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) ≠ 0 := by
    intro h0
    apply hk
    rw [hr, h0, zero_smul]
  have hthpmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  have hord : ∀ v, d.admitted c v → 0 ≤ d.ord c v d.wF (d.thp (hd.sel k) c) :=
    fun v hv => hd.ord_nonneg_Thp c v hv _ hthpmem hk
  have x2 := d.good_primes_properties hd h c
  have hsplit : ∀ p ∈ d.HtOne, d.nP h c d.wF (d.thp (hd.sel k) c) p =
      d.nP h c d.wF (hd.a4.choose c) p +
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) *
          WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c))) := by
    intro p hp
    have e2 := d.nP_smul hd h c hec.1 hec.2 hr0 hp
    rw [← hr] at e2
    exact e2
  have hkey := d.key_degree hd h c _ hr0
  have hfe := x2.2.2.1 _ _ hec.1 hec.2
  have hfm := d.use₈ hd h c _ hr0
  have eq1 : (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ)) =
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c d.wF (hd.a4.choose c) p * (d.dg (d.gen p) : ℤ)) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          (d.fze h c w : ℤ) *
            WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c)))) *
          (d.dg (d.gen p) : ℤ) := by
    rw [← finsum_mem_add_distrib' ?_ ?_]
    · exact finsum_mem_congr rfl fun p hp => by rw [hsplit p hp, add_mul]
    · refine hfe.subset ?_
      rintro p ⟨hp, hne⟩
      exact ⟨hp, fun h0 => hne (by simp [h0])⟩
    · refine hfm.subset ?_
      rintro p ⟨hp, hne⟩
      exact ⟨hp, fun h0 => hne (by simp [h0])⟩
  have hnn : 0 ≤ ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ) :=
    finsum_nonneg fun p => finsum_nonneg fun hp =>
      mul_nonneg (d.nP_nonneg hd h c hp _ _ hord) (Nat.cast_nonneg _)
  rw [eq1, hkey, add_zero] at hnn
  exact hnn

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogHeightGeneratorLowerBound
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

theorem h0_zero : ReciprocityTheory.MultiplicativeHeights.h0 (0 : KTp K d.D d.N) = 0 := by
  simp [ReciprocityTheory.MultiplicativeHeights.h0, ReciprocityTheory.MultiplicativeHeights.gaussAbs, ReciprocityTheory.MultiplicativeHeights.blockSphereMean]

theorem lr_nonneg : (0 : ℝ) ≤ Real.log (d.N + 1 : ℕ) + 1 / 2 := by
  have h := Real.log_natCast_nonneg (d.N + 1)
  linarith

theorem logHeight_generator_lower_bound (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (hg : ∃ w, w ∈ d.GoodP c p) :
    -((d.D : ℝ) * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤ ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) := by
  by_cases h0 : d.gen p = 0
  · rw [h0, d.h0_zero]
    have : d.dg 0 = 0 := by simp [dg]
    rw [this]; simp
  · have hm := (d.good_primes_properties hd h c).2.1 p hp hg
    have := ReciprocityTheory.MultiplicativeHeights.Closed.sphere_height_lower_bound K (d.D + 1) (d.N + 1) _ (d.gen p) (Nat.succ_pos _) h0 hm
    rw [Fin.sum_univ_succ] at this
    simp only [Fin.succ_ne_zero, if_false, if_true, Nat.cast_zero, zero_mul, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    convert this using 2
    ring

theorem multiplicity_mul_logHeight_le (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) :
    (d.Ep h c p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) ≤
      d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) +
        d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) *
          (d.nP h c (d.n1 • d.wde) (d.et c) p * d.dg (d.gen p)) := by
  by_cases hg : ∃ w, w ∈ d.GoodP c p
  · have hL := d.logHeight_generator_lower_bound hd h c hp hg
    have hE0 : (0 : ℝ) ≤ d.Ep h c p := by exact_mod_cast d.Ep_nonneg hd h c hp
    have hE := d.Ep_le hd h hF1d c hp
    have hn0 : (0 : ℝ) ≤ d.nP h c (d.n1 • d.wde) (d.et c) p := by
      exact_mod_cast d.nP_nonneg hd h c hp _ _ fun v hv => hd.ord_nonneg_et c v hv
    have hi : (0 : ℝ) ≤ d.cc / d.i := div_nonneg hd.cc_nonneg (Nat.cast_nonneg _)
    have hE' : (d.Ep h c p : ℝ) ≤ d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p := by
      have : d.cc / (2 * d.i) = (d.cc / d.i) / 2 := by ring
      rw [this] at hE; nlinarith
    have hlr := d.lr_nonneg
    have hX : (0 : ℝ) ≤ d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by positivity
    set r := d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) - d.Ep h c p
    have hr0 : 0 ≤ r := by linarith
    have hrle : r ≤ d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) := by linarith
    have k1 : -(r * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)) ≤ r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) := by
      nlinarith
    have k2 : r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤
        d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) *
          (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) :=
      mul_le_mul_of_nonneg_right hrle hX
    have : (d.Ep h c p : ℝ) = d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p - r := by ring
    rw [this]
    nlinarith
  · push_neg at hg
    have hG : d.GoodP c p = ∅ := Set.eq_empty_iff_forall_notMem.mpr hg
    have e1 : d.Ep h c p = 0 := by unfold Ep; rw [hG]; simp
    have e2 : d.nP h c (d.n1 • d.wde) (d.et c) p = 0 := by unfold nP; rw [hG]; simp
    rw [e1, e2]; simp

theorem logHeight_section_bound (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    d.h0f h d.wL f ≤ d.mahlerMeasureHeight h f + d.cc / d.i * d.h0f h (d.n1 • d.wde) d.et +
      d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) := by
  classical
  unfold h0f mahlerMeasureHeight aG
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have x2 := d.good_primes_properties hd h c
  have hfin : {p | p ∈ d.HtOne ∧ (d.nP h c d.wL (f c) p ≠ 0 ∨ d.nPMM h c (f c) p ≠ 0 ∨
      d.Ep h c p ≠ 0 ∨ d.nP h c (d.n1 • d.wde) (d.et c) p ≠ 0)}.Finite := by
    refine (((x2.2.2.1 _ _ (hf c).1 (hf c).2).union (x2.2.2.2 _ (hf c).1 (hf c).2)).union
      ((d.Ep_ne hd h c _ (hf c).1 (hf c).2).union
        (x2.2.2.1 _ _ (hd.et_mem c) (hd.et_ne c)))).subset ?_
    rintro p ⟨hp, h1 | h1 | h1 | h1⟩
    · exact Or.inl (Or.inl ⟨hp, h1⟩)
    · exact Or.inl (Or.inr ⟨hp, h1⟩)
    · exact Or.inr (Or.inl ⟨hp, h1⟩)
    · exact Or.inr (Or.inr ⟨hp, h1⟩)
  set S := hfin.toFinset
  have mem : ∀ p, p ∈ d.HtOne → (d.nP h c d.wL (f c) p ≠ 0 ∨ d.nPMM h c (f c) p ≠ 0 ∨
      d.Ep h c p ≠ 0 ∨ d.nP h c (d.n1 • d.wde) (d.et c) p ≠ 0) → p ∈ S := fun p hp h1 => by
    simp only [S, Set.Finite.mem_toFinset]; exact ⟨hp, h1⟩
  rw [fsum_eq_sum _ S (fun p => (d.nP h c d.wL (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p))
      (fun p hp h0 => mem p hp (Or.inl fun e => h0 (by simp [e]))),
    fsum_eq_sum _ S (fun p => (d.nPMM h c (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p))
      (fun p hp h0 => mem p hp (Or.inr (Or.inl fun e => h0 (by simp [e])))),
    fsum_eq_sum _ S (fun p => (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p))
      (fun p hp h0 => mem p hp (Or.inr (Or.inr (Or.inr fun e => h0 (by simp [e]))))),
    fsum_eq_sum _ S (fun p => d.nP h c (d.n1 • d.wde) (d.et c) p * (d.dg (d.gen p) : ℤ))
      (fun p hp h0 => mem p hp (Or.inr (Or.inr (Or.inr fun e => h0 (by simp [e])))))]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p ∈ d.HtOne
  · simp only [Set.indicator_of_mem hp]
    have e := d.nP_split hd h c hp (f c)
    have k := d.multiplicity_mul_logHeight_le hd h hF1d c hp
    rw [e]; push_cast
    push_cast at k
    linarith
  · simp [Set.indicator_of_notMem hp]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogNormNonneg
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

theorem logNorm_nonneg (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 0 ≤ logNorm la := by
  unfold logNorm
  exact Real.log_natCast_nonneg _

theorem NlaG_nonneg (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    0 ≤ d.NlaG h (d.n1 • d.wde) d.et la :=
  Finset.sum_nonneg fun c _ => finsum_nonneg fun w => finsum_nonneg fun hw =>
    mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hd.ord_nonneg_et c _ (d.admissible_over_prime hd h la c w hw).1)

theorem Nla_le (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (f : ∀ c, A c)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    d.NlaG h d.wL f la ≤ d.NlaMM h f la + d.del * d.nu la +
      d.cc / d.i * d.NlaG h (d.n1 • d.wde) d.et la := by
  have hnn := d.NlaG_nonneg hd h la
  have hi : (0 : ℝ) ≤ d.cc / d.i := div_nonneg hd.cc_nonneg (Nat.cast_nonneg _)
  suffices key : d.NlaG h d.wL f la ≤ d.NlaMM h f la + d.del * d.nu la +
      d.cc / (2 * d.i) * d.NlaG h (d.n1 • d.wde) d.et la by
    have : d.cc / (2 * d.i) * d.NlaG h (d.n1 • d.wde) d.et la ≤ d.cc / d.i * d.NlaG h (d.n1 • d.wde) d.et la := by
      have : d.cc / (2 * d.i) = (d.cc / d.i) / 2 := by ring
      rw [this]; nlinarith
    linarith
  unfold NlaG NlaMM del
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have hfin := (d.places_over_la hd h la c).1
  have hsum := (d.places_over_la hd h la c).2
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum ⊢
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsumR : (d.delc c : ℝ) = ∑ w ∈ hfin.toFinset, (d.fze h c w : ℝ) * (ramIdx (K := K) (d.Wres c w) la : ℝ) := by
    have e := congrArg (fun z : ℤ => (z : ℝ)) hsum
    push_cast at e
    linarith
  rw [hsumR, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  have hs := d.admissible_over_prime hd h la c w hw
  have h3 := hH1.2.2.2 c (d.Wres c w) la hs.1 hs.2.1
  have hf : (0 : ℝ) ≤ d.fze h c w := Nat.cast_nonneg _
  unfold ordMM
  push_cast
  have e : ((⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c) : ℤ) : ℝ) =
    (d.Emin c (d.Wres c w) : ℝ) := rfl
  rw [e] at h3 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h3 hf]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.X4v4RatioSpec
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

theorem x4v4_ratio_spec {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V}
    (hg : g ≠ 0) {a : Ω'} (hf : f = a • g) : ratio (Ω := Ω') f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, hf⟩
  unfold ratio
  rw [dite_eq_left hex]
  have h2 : hex.choose • g = a • g := hex.choose_spec.symm.trans hf
  exact smul_left_injective Ω' hg h2

theorem x4v4_eq_smul (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) :
    f = ratio (Ω := Ω c) f (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hw0 : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have hv : (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL) ≠ 0 := by
    intro h0
    apply hw0
    simpa using congrArg Subtype.val h0
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • d.w (d.jc c) c := by
    have h1 := congrArg Subtype.val ha
    simpa using h1.symm
  rw [x4v4_ratio_spec hw0 hfa]
  exact hfa

theorem x4v4_ratio_ne (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ratio (Ω := Ω c) f (d.w (d.jc c) c) ≠ 0 := by
  intro h0
  apply hf0
  rw [x4v4_eq_smul d hd c hf, h0, zero_smul]

theorem x4v4_wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  have e : d.wx x c = ∑ j, x j • d.w j c := by
    simp only [Data.wx, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem x4v4_gen_ne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := by
  refine (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ?_
  obtain ⟨hprime, hh⟩ := hp
  have hpr := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
  unfold gen
  rw [dite_eq_left hpr]
  intro h0
  exact p.ne_bot_of_height_eq_one hh ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)

theorem x4v4_ordMM (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) {f : A c}
    (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c (d.Wres c w) f = WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c))) +
      d.ordMM c (d.Wres c w) (d.w (d.jc c) c) := by
  have hA := d.good_adm hd h c hp hw
  have e : ((d.ord c (d.Wres c w) d.wL f : ℤ) : WithTop ℤ) =
      d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) +
        (d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : WithTop ℤ) := by
    conv_lhs => rw [d.x4v4_eq_smul hd c hf]
    exact hd.ord_smul c _ hA _ (hd.w_mem _ _) (hd.w_base c) (d.x4v4_ratio_ne hd c hf hf0)
  have hfin : d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) =
      ((d.ord c (d.Wres c w) d.wL f - d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : ℤ) : WithTop ℤ) := by
    revert e
    generalize d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) = t
    intro e
    induction t using WithTop.recTopCoe with
    | top => simp at e
    | coe t =>
      have e' : d.ord c (d.Wres c w) d.wL f = t + d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) := by
        exact_mod_cast e
      rw [e']
      congr 1
      ring
  unfold ordMM
  rw [hfin, WithTop.untopD_coe]
  ring

theorem x4v4_split (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.nPMM h c f p =
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)))) +
      d.nPMM h c (d.w (d.jc c) c) p := by
  have hfin := d.goodP_finite hd h c hp
  unfold nPMM
  rw [← finsum_mem_add_distrib hfin]
  refine finsum_mem_congr rfl fun w hw => ?_
  rw [d.x4v4_ordMM hd h c hp hw hf hf0]
  ring

theorem norm_ratio_pi (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (x : Fin (d.N + 1) → K)
    (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
            (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p) := by
  classical
  have hmem := d.x4v4_wx_mem hd x c
  have hg0 := d.x4v4_ratio_ne hd c hmem hx
  obtain ⟨κ, hκ, hN⟩ := (d.norm_factorization hd h).1 c _ hg0
  refine ⟨κ, hκ, ?_⟩
  rw [hN, mul_assoc]
  congr 1
  set na : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0
        (d.Wres c w (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) with hna
  set G : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p =>
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hG
  have hsplit : ∀ p ∈ d.HtOne, d.nPMM h c (d.wx x c) p = na p + d.nPMM h c (d.w (d.jc c) c) p :=
    fun p hp => d.x4v4_split hd h c hp hmem hx
  have hSx := (d.good_primes_properties hd h c).2.2.2 _ hmem hx
  have hSj := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  have hfa : (d.HtOne ∩ Function.mulSupport fun p => G p ^ na p).Finite := by
    refine (hSx.union hSj).subset fun p hp => ?_
    have hn : na p ≠ 0 := by
      intro h0; apply hp.2; simp only [h0, zpow_zero]
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    apply hn
    have e := hsplit p hp.1
    rw [hc.1 hp.1, hc.2 hp.1] at e
    omega
  have hfj : (d.HtOne ∩ Function.mulSupport fun p => G p ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hSj.subset fun p hp => ⟨hp.1, ?_⟩
    intro h0; apply hp.2; simp only [h0, zpow_zero]
  show (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ na p) *
      (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.w (d.jc c) c) p) =
    ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.wx x c) p
  rw [← finprod_mem_mul_distrib' hfa hfj]
  refine finprod_mem_congr rfl fun p hp => ?_
  rw [hsplit p hp, zpow_add₀ (d.x4v4_gen_ne hp)]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

