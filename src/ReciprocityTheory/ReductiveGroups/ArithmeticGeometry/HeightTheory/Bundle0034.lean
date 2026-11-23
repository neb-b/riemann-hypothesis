module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationGenericRatioEqRestriction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ExistsSmallSaturatingVector

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HFour
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

theorem h_ind (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) :
    (∀ (G : WT) (ta ta' : ∀ c, A c),
      G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) → (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) →
      d.Hgt h G ta = d.Hgt h G ta') ∧
    (∀ f f' : ∀ c, A c, (∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) → (∀ c, f' c ∈ 𝒜 c d.wL ∧ f' c ≠ 0) →
      d.HgtMM h f = d.HgtMM h f') ∧
    (∀ x : Fin (d.N + 1) → K, (∀ c, d.wx x c ≠ 0) →
      (d.n1 : ℝ) * d.Hgt h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.Hgt h (d.n1 • d.wde) d.et =
        2 * d.n1 * d.Hgt h d.wL (d.wx x)) ∧
    (∀ (x : Fin (d.N + 1) → K) (ta' : ∀ c, A c), (∀ c, d.wx x c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) →
      d.Hgt h d.wF ta' + d.Hgt h d.G2 d.ta2 = (d.D + 4) * d.Hgt h d.wL (d.wx x)) := by
  exact d.h_ind' hd h hI2be

theorem h_four (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0)
    (hord : ∀ c (v : AddValuation (Ω c) (WithTop ℤ)), d.admitted c v → 0 ≤ d.ord c v G (ta c))
    (hbdd : ∀ sg : K →+* ℂ, BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (ta p.1) p.2))
    (hint : ∀ (c : ι) (sg : K →+* ℂ), MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c G (ta c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) :
    -(d.del * meanK (fun sg => Real.log (d.supN sg G ta))) -
        d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2) ≤ d.Hgt h G ta ∧
      (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤
        d.Hgt h G ta + d.del * meanK (fun sg => Real.log (d.supN sg G ta)) +
          d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by
  exact d.h_four' hd h G ta hta hord hbdd hint

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightProdPowMultiHomogeneous
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.MultiplicativeHeights

theorem isMultiHomogeneous_mul' {R : Type*} [CommSemiring R] {B n : ℕ} {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin n) R} (hf : IsMultiHomogeneous a f)
    (hg : IsMultiHomogeneous a' g) : IsMultiHomogeneous (a + a') (f * g) := by
  classical
  unfold IsMultiHomogeneous at *
  intro s hs b
  obtain ⟨s1, hs1, s2, hs2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hs)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf s1 hs1 b, hg s2 hs2 b]

theorem isMultiHomogeneous_one {R : Type*} [CommSemiring R] {B n : ℕ} :
    IsMultiHomogeneous (0 : Fin B → ℕ) (1 : MvPolynomial (Fin B × Fin n) R) := by
  classical
  unfold IsMultiHomogeneous
  intro s hs b
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hs
  split_ifs at hs with h
  · subst h
    simp
  · exact absurd rfl hs

theorem height_one_eq_zero {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) :
    h0 (1 : MvPolynomial (Fin B × Fin n) K) = 0 := by
  classical
  first
    | simp [h0, gaussAbs, blockSphereMean]
    | simp [h0, gaussAbs, blockSphereMean, MvPolynomial.support_one]

theorem height_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n)
    {g : MvPolynomial (Fin B × Fin n) K} {a : Fin B → ℕ} (hg0 : g ≠ 0)
    (hg : IsMultiHomogeneous a g) (e : ℕ) :
    g ^ e ≠ 0 ∧ IsMultiHomogeneous (e • a) (g ^ e) ∧ h0 (g ^ e) = e * h0 g := by
  induction e with
  | zero => simp [height_one_eq_zero hn, isMultiHomogeneous_one]
  | succ e ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨pow_ne_zero _ hg0, ?_, ?_⟩
    · rw [pow_succ, succ_nsmul]; exact isMultiHomogeneous_mul' h2 hg
    · rw [pow_succ, (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn h1 hg0 h2 hg).1, h3]
      push_cast; ring

theorem height_prod_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) {ι' : Type*}
    (T : Finset ι') (g : ι' → MvPolynomial (Fin B × Fin n) K) (e : ι' → ℕ)
    (hg : ∀ i ∈ T, g i ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (g i)) :
    (∏ i ∈ T, g i ^ e i) ≠ 0 ∧ (∃ a, IsMultiHomogeneous a (∏ i ∈ T, g i ^ e i)) ∧
      h0 (∏ i ∈ T, g i ^ e i) = ∑ i ∈ T, (e i : ℝ) * h0 (g i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [height_one_eq_zero hn]; exact ⟨0, isMultiHomogeneous_one⟩
  | insert q T hq ih =>
    obtain ⟨h1, ⟨a1, h2⟩, h3⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    obtain ⟨hq0, aq, hqa⟩ := hg q (Finset.mem_insert_self q T)
    obtain ⟨p1, p2, p3⟩ := height_pow_multiHomogeneous hn hq0 hqa (e q)
    rw [Finset.prod_insert hq, Finset.sum_insert hq]
    refine ⟨mul_ne_zero p1 h1, ⟨_, isMultiHomogeneous_mul' p2 h2⟩, ?_⟩
    rw [(ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn p1 h1 p2 h2).1, p3, h3]

namespace Data

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

variable (d : Data K ι Ω WT A)

private lemma ratio_eq_of_eq_smul' {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V} {a : Ω'}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, h⟩
  unfold ratio
  rw [dite_eq_left hex]
  have hc := hex.choose_spec
  exact smul_left_injective Ω' hg (hc.symm.trans h)

theorem ratio_linearCombination_expand (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  haveI := hd.tower c
  have hg : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have hspan : ∀ f ∈ 𝒜 c d.wL, ∃ a : Ω c, f = a • d.w (d.jc c) c := by
    intro f hf
    have hne : (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL) ≠ 0 := by
      intro h0
      exact hg (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp (hd.finrank_one c d.wL) ⟨f, hf⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  choose r hr using fun j => hspan (d.w j c) (hd.w_mem j c)
  have hrat : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = r j := fun j => ratio_eq_of_eq_smul' hg (hr j)
  simp only [hrat]
  apply ratio_eq_of_eq_smul' hg
  rw [Finset.sum_smul]
  unfold Data.wx
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.smul_apply, mul_smul, algebraMap_smul]
  conv_lhs => rw [hr j]

theorem untopD_le_untopD {u v : WithTop ℤ} (hu : u ≠ ⊤) (hv : v ≠ ⊤) (h : u ≤ v) :
    u.untopD 0 ≤ v.untopD 0 := by
  lift u to ℤ using hu
  lift v to ℤ using hv
  simpa using h

theorem ordMinMax_nonneg (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι)
    (hx : d.wx x c ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) :
    0 ≤ d.ordMM c (d.Wres c w) (d.wx x c) := by
  rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with htr | ⟨hA, htriv, j0, hj0, hint, _⟩
  · obtain ⟨a, ha, hne⟩ := hw.2
    exact absurd (htr a ha) hne
  have hmem := d.linearCombination_mem_section hd x c
  rw [d.ordMinMax_eq_ratio_untop_sub hd c _ hA j0 hj0 hint hmem hx, sub_nonneg]
  set v := d.Wres c w
  have hb := hd.w_base c
  have hm := hd.w_mem (d.jc c) c
  apply untopD_le_untopD (hA.1.1 _ (d.ratio_base_ne_zero hd c (hd.w_mem j0 c) hj0))
    (hA.1.1 _ (d.ratio_base_ne_zero hd c hmem hx))
  rw [d.ratio_linearCombination_expand hd x c]
  apply AddValuation.map_le_sum
  intro j _
  by_cases hxj : x j = 0
  · rw [hxj, map_zero, zero_mul, v.map_zero]; exact le_top
  rw [v.map_mul, htriv _ hxj, zero_add,
    d.ratio_mul_ratio_height hd c (hd.w_mem j c) (hd.w_mem j0 c) hm hj0 hb, v.map_mul]
  exact le_add_of_nonneg_left (hint j)

theorem multiplicity_nonneg (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι)
    (hx : d.wx x c ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    0 ≤ d.nPMM h c (d.wx x c) p := by
  unfold Data.nPMM
  apply finsum_nonneg
  intro w
  apply finsum_nonneg
  intro hw
  refine mul_nonneg ?_ (d.ordMinMax_nonneg hd h x c hx hp hw)
  first
    | positivity
    | exact Nat.cast_nonneg _

theorem height_substituted_eq_finsum (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    d.translatedForm x F ≠ 0 ∧
    ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nPMM h c (d.wx x c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) =
      ReciprocityTheory.MultiplicativeHeights.h0 (d.translatedForm x F) := by
  classical
  have hmem := d.linearCombination_mem_section hd x c
  obtain ⟨κ1, hκ1, e1⟩ := d.SpecialFibreFactorization hd h c F hF x (hx c)
  have hS := (d.good_primes_properties hd h c).2.2.2 _ hmem (hx c)
  set T := hS.toFinset
  set n : Ideal (KTp K d.D d.N) → ℤ := fun p => d.nPMM h c (d.wx x c) p with hn
  have hT : ∀ p, p ∈ T ↔ p ∈ d.HtOne ∧ n p ≠ 0 := fun p => by rw [Set.Finite.mem_toFinset]; rfl
  have hgood : ∀ p ∈ T, d.gen p ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (d.gen p) := by
    intro p hpT
    obtain ⟨hp, hnp⟩ := (hT p).mp hpT
    refine ⟨d.gen_ne_zero_of_htOne hp, _, (d.good_primes_properties hd h c).2.1 p hp ?_⟩
    obtain ⟨w, hw, _⟩ := exists_ne_zero_of_finsum_mem_ne_zero' hnp
    exact ⟨w, hw⟩
  set e : Ideal (KTp K d.D d.N) → ℕ := fun p => (n p).toNat with he
  have hne : ∀ p ∈ d.HtOne, n p = (e p : ℤ) := fun p hp =>
    (Int.toNat_of_nonneg (d.multiplicity_nonneg hd h x c (hx c) hp)).symm
  obtain ⟨P0, ⟨aP, hPm⟩, hPh⟩ := height_prod_pow_multiHomogeneous (K := K) (Nat.succ_pos d.N) T (fun p => d.gen p) e hgood
  have hprod : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ p ∈ T, d.gen p ^ e p) := by
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq _ (t := T), map_prod]
    · refine Finset.prod_congr rfl fun p hpT => ?_
      rw [hne p ((hT p).mp hpT).1, zpow_natCast, map_pow]
    · ext p
      simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe, hT]
      constructor
      · rintro ⟨hp, h1⟩
        refine ⟨⟨hp, fun h0 => h1 ?_⟩, h1⟩
        rw [h0, zpow_zero]
      · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩
  have hFx : d.translatedForm x F = MvPolynomial.C κ1 * ∏ p ∈ T, d.gen p ^ e p := by
    apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
    unfold translatedForm
    rw [e1, hprod, map_mul, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N)]
  refine ⟨by rw [hFx]; exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hκ1) P0, ?_⟩
  rw [hFx, (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) aP aP _ _ (Nat.succ_pos _) P0 P0 hPm hPm).2
    κ1 hκ1, hPh]
  rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := T)]
  · refine Finset.sum_congr rfl fun p hpT => ?_
    rw [show ((d.nPMM h c (d.wx x c) p : ℤ) : ℝ) = ((e p : ℤ) : ℝ) from
      congrArg _ (hne p ((hT p).mp hpT).1)]
    simp
  · ext p
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.mem_coe, hT]
    constructor
    · rintro ⟨hp, h1⟩
      refine ⟨⟨hp, fun h0 => h1 ?_⟩, h1⟩
      simp only [hn] at h0; rw [h0]; simp
    · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩

theorem fZ_and_substituted_ne_zero (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    F ≠ 0 ∧ d.translatedForm x F ≠ 0 := by
  have hne := (d.height_substituted_eq_finsum hd h x hx c F hF).1
  refine ⟨fun h0 => hne ?_, hne⟩
  rw [h0]
  first
    | simp [Data.translatedForm]
    | exact map_zero _

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HupsTwCoeffCoeff
section
namespace ReciprocityTheory.ChartRestriction.G.T0


open Polynomial in
noncomputable def hupsTw {σ R : Type*} [CommRing R] (w : σ → ℕ) :
    MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  MvPolynomial.aeval fun v => Polynomial.C (MvPolynomial.X v) * Polynomial.X ^ (w v)

def hupsWt {σ : Type*} (w : σ → ℕ) (s : σ →₀ ℕ) : ℕ := s.sum fun v k => k * w v

theorem hupsTw_monomial {σ R : Type*} [CommRing R] (w : σ → ℕ) (s : σ →₀ ℕ) (a : R) :
    hupsTw w (MvPolynomial.monomial s a) =
      Polynomial.C (MvPolynomial.monomial s a) * Polynomial.X ^ hupsWt w s := by
  rw [hupsTw, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, hupsWt, Finsupp.prod, Finsupp.sum, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]
  simp only [mul_comm (w _) _]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem hupsTw_eq {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R) :
    hupsTw w p = ∑ s ∈ p.support,
      Polynomial.C (MvPolynomial.monomial s (p.coeff s)) * Polynomial.X ^ hupsWt w s := by
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [hupsTw_monomial]

theorem hupsTw_coeff_coeff {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R)
    (j : ℕ) (s : σ →₀ ℕ) :
    ((hupsTw w p).coeff j).coeff s = if hupsWt w s = j then p.coeff s else 0 := by
  classical
  rw [hupsTw_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [MvPolynomial.coeff_sum]
  simp only [apply_ite (AddMonoidAlgebra.coeff · s), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]
  rw [Finset.sum_eq_single s]
  · by_cases h : hupsWt w s = j
    · rw [if_pos h.symm, if_pos h, if_pos rfl]
    · simp [h, Ne.symm h]
  · intro t _ hts
    simp [hts, MvPolynomial.coeff_monomial]
  · intro hs
    rw [MvPolynomial.mem_support_iff, not_not] at hs
    simp [hs]

theorem hupsTw_ne_zero {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R}
    {s : σ →₀ ℕ} (hs : s ∈ p.support) : (hupsTw w p).coeff (hupsWt w s) ≠ 0 := by
  intro h
  have e := hupsTw_coeff_coeff w p (hupsWt w s) s
  rw [h, MvPolynomial.coeff_zero, if_pos rfl] at e
  exact (MvPolynomial.mem_support_iff.mp hs) e.symm

theorem hupsTw_hom {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R} {a : ℕ}
    (hp : ∀ s ∈ p.support, hupsWt w s = a) :
    hupsTw w p = Polynomial.C p * Polynomial.X ^ a := by
  ext j s
  rw [hupsTw_coeff_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hs : s ∈ p.support
  · rw [hp s hs]
    by_cases hj : j = a
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  · rw [MvPolynomial.mem_support_iff, not_not] at hs
    split_ifs <;> simp [hs]

theorem hups_hom_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} (hF : F ≠ 0) {a n : ℕ} (hFa : ∀ s ∈ F.support, hupsWt w s = a)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s = n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + a = n := by
  have h1 : hupsTw w (F * P) = Polynomial.C (F * P) * Polynomial.X ^ n := hupsTw_hom w hFP
  have h2 : hupsTw w F = Polynomial.C F * Polynomial.X ^ a := hupsTw_hom w hFa
  rw [map_mul, h2, map_mul] at h1
  have hCF : (Polynomial.C F : Polynomial (MvPolynomial σ R)) ≠ 0 := Polynomial.C_ne_zero.mpr hF
  have h3 : Polynomial.X ^ a * hupsTw w P = Polynomial.C P * Polynomial.X ^ n := by
    apply mul_left_cancel₀ hCF
    rw [← mul_assoc, ← mul_assoc]
    exact h1
  have h4 := congrArg (fun q => q.coeff (hupsWt w s0 + a)) h3
  simp only [Polynomial.coeff_X_pow_mul, Polynomial.coeff_C_mul_X_pow] at h4
  by_contra hne
  rw [if_neg hne] at h4
  exact hupsTw_ne_zero w hs0 h4

theorem hups_deg_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} {u n : ℕ} {sF : σ →₀ ℕ} (hsF : sF ∈ F.support)
    (hFu : hupsWt w sF = u)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s ≤ n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + u ≤ n := by
  have hTF : (hupsTw w F).coeff u ≠ 0 := by
    rw [← hFu]
    exact hupsTw_ne_zero w hsF
  have hTP : (hupsTw w P).coeff (hupsWt w s0) ≠ 0 := hupsTw_ne_zero w hs0
  have hF0 : hupsTw w F ≠ 0 := fun h => hTF (by rw [h, Polynomial.coeff_zero])
  have hP0 : hupsTw w P ≠ 0 := fun h => hTP (by rw [h, Polynomial.coeff_zero])
  have hdeg : (hupsTw w (F * P)).natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    ext s
    rw [hupsTw_coeff_coeff, MvPolynomial.coeff_zero]
    split_ifs with h
    · by_contra hc
      have := hFP s (MvPolynomial.mem_support_iff.mpr hc)
      omega
    · rfl
  rw [map_mul, Polynomial.natDegree_mul hF0 hP0] at hdeg
  have h1 := Polynomial.le_natDegree_of_ne_zero hTF
  have h2 := Polynomial.le_natDegree_of_ne_zero hTP
  omega

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.MinkSat
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem mink_sat (K : Type) [Field K] [NumberField K] (r k : ℕ) (b : Fin k → Fin r → K)
    (hb : LinearIndependent K b) (hbL : ∀ j, b j ∈ stdLat K r) (hk : k < r) :
    ∃ q : Fin r → 𝓞 K, (fun i => (q i : K)) ∉ Submodule.span K (Set.range b) ∧
      meanK (fun σ => Real.log (qdist σ b (fun i => (q i : K)))) ≤
        ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b) b /
            ((Module.finrank ℚ K : ℝ) * ((r - k : ℕ) : ℝ)) +
          1 / 2 * Real.log ((r - k : ℕ) : ℝ) +
          1 / 2 * Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) :=
  exists_small_saturating_vector K r k b hb hbL hk

end ReciprocityTheory.ChartRestriction.G.T0
end

