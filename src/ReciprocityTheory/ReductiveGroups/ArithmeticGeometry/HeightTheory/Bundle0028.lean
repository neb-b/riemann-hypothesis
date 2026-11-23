module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FZEqConstMulIrreduciblePow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DePres

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscProduct
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_product (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (a b : KTp K d.D d.N)
    (hab : d.IsPres hd h a b) (Om : KTp K d.D d.N)
    (hOm : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h) :
    (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
        (Module.finrank ℚ K : ℝ) =
      meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg) -
        ReciprocityTheory.MultiplicativeHeights.h0 Om + 2 * d.Hgt h d.wF hd.a4.choose := by
  classical
  set e := hd.a4.choose with hedef
  have he := hd.a4.choose_spec.1
  obtain ⟨hb0, hab', m, hm0, hma, hmb⟩ := hab
  have hDe : d.De hd h ≠ 0 := (d.disc_lattice hd h).1
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab'
    exact mul_ne_zero hDe ((map_ne_zero_iff _ hinj).2 hb0) hab'.symm
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ

  have hla : ∀ la, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) -
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) =
        -((d.gOrd la (d.De hd h) : ℝ) * logNorm la) :=
    fun la => d.log_gaussAbs_sub_of_fraction la a b ha0 hb0 _ hab'
  have hlog : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), logNorm la ≠ 0 := fun la => by
    have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm la
    exact (Real.log_pos (by exact_mod_cast h1)).ne'
  have hgfin : (Function.support fun la => d.gOrd la (d.De hd h)).Finite := by
    refine (((ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite a ha0).union
      (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite b hb0)).preimage
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn).subset ?_
    intro la hla0
    have h1 : Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) -
        Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) ≠ 0 := by
      rw [hla]
      exact neg_ne_zero.2 (mul_ne_zero (by exact_mod_cast hla0) (hlog la))
    by_contra hn'
    apply h1
    simp only [Set.mem_preimage, Set.mem_union, Function.mem_support, not_or, not_not] at hn'
    change Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) = 0 ∧
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) = 0 at hn'
    rw [hn'.1, hn'.2, sub_zero]
  have hNfin : (Function.support fun la => d.NlaG h d.wF e la).Finite :=
    (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ord c v d.wF (e c))
      (hd.a3' c (he c).1 (he c).2)).subset (d.aNla_supp hd h (fun c v f => d.ord c v d.wF f) e)
  refine ⟨hgfin, hNfin, ?_⟩

  obtain ⟨U, V, hU0, hV0, ⟨eU, hUm⟩, ⟨eV, hVm⟩, hpres, hh0f⟩ := d.finite_height_fraction_repr hd h
  have hpoly : Om * (b * V ^ 2) = a * U ^ 2 := by
    apply hinj
    simp only [map_mul, map_pow]
    rw [hOm, omE, hab', ← hpres]
    ring
  have hOm0 : Om ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hpoly
    exact mul_ne_zero ha0 (pow_ne_zero _ hU0) hpoly.symm
  have hnp : 0 < d.N + 1 := Nat.succ_pos _
  have E1 : ReciprocityTheory.MultiplicativeHeights.h0 Om = ReciprocityTheory.MultiplicativeHeights.h0 a + 2 * ReciprocityTheory.MultiplicativeHeights.h0 U -
      (ReciprocityTheory.MultiplicativeHeights.h0 b + 2 * ReciprocityTheory.MultiplicativeHeights.h0 V) := by
    rw [logHeight_div_multihomogeneous _ _ hOm0 (mul_ne_zero hb0 (pow_ne_zero _ hV0))
      (multi_mul hmb (multi_pow hVm 2)) (multi_mul hma (multi_pow hUm 2)) hpoly,
      (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) _ _ a (U ^ 2) hnp ha0 (pow_ne_zero _ hU0) hma
        (multi_pow hUm 2)).1,
      (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) _ _ b (V ^ 2) hnp hb0 (pow_ne_zero _ hV0) hmb
        (multi_pow hVm 2)).1,
      h0_pow_of_isMultiHomogeneous hnp hU0 hUm, h0_pow_of_isMultiHomogeneous hnp hV0 hVm]
    push_cast; ring
  have E2 : ReciprocityTheory.MultiplicativeHeights.h0 a - ReciprocityTheory.MultiplicativeHeights.h0 b =
      (-(∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) + ∑ sg, d.mSgP sg a b) /
        (Module.finrank ℚ K : ℝ) := by
    have hfinp : (∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w a)) -
        ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w b) =
        -(∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) := by
      rw [← finsum_sub_distrib (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite a ha0)
        (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite b hb0)]
      have := finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
        (f := fun w => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w a) - Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w b))
      rw [← this, ← finsum_neg_distrib]
      exact finsum_congr fun la => hla la
    have harch : ∑ sg : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg a) -
        ∑ sg : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg b) =
        ∑ sg, d.mSgP sg a b := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun sg _ => d.sphereMean_sub_archimedean a b m hm0 ha0 hb0 hma hmb sg
    unfold ReciprocityTheory.MultiplicativeHeights.h0
    rw [← hfinp, ← harch]
    ring
  have E4 : meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF e sg) =
      (∑ sg, d.mSgP sg a b) / (Module.finrank ℚ K : ℝ) - 2 * meanK (d.Nsg d.wF e) := by
    unfold meanK
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcard]
    ring
  have hsG : (Function.support fun la => (d.gOrd la (d.De hd h) : ℝ) * logNorm la).Finite :=
    hgfin.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0]
  have hsN : (Function.support fun la => d.NlaG h d.wF e la * logNorm la).Finite :=
    hNfin.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0]
  have E5 : (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF e la) * logNorm la) =
      (∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) +
        2 * ∑ᶠ la, d.NlaG h d.wF e la * logNorm la := by
    rw [mul_finsum, ← finsum_add_distrib hsG (hsN.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0])]
    exact finsum_congr fun la => by ring
  rw [E5, E4, Hgt, hh0f]
  have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := hn.ne'
  linear_combination E1 + E2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumLeOf
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

theorem fsum_le_of {α : Type*} (s : Set α) (f g : α → ℤ) (hf : {x | x ∈ s ∧ f x ≠ 0}.Finite)
    (hg : {x | x ∈ s ∧ g x ≠ 0}.Finite) (r : ℝ) (hle : ∀ x ∈ s, (f x : ℝ) ≤ r * g x) :
    ((∑ᶠ x ∈ s, f x : ℤ) : ℝ) ≤ r * ((∑ᶠ x ∈ s, g x : ℤ) : ℝ) := by
  classical
  set u : Finset α := (hf.union hg).toFinset with hu
  have hus : ∀ x ∈ u, x ∈ s := by
    intro x hx
    simp only [hu, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with h | h
    · exact h.1
    · exact h.1
  have ef : ∑ᶠ x ∈ s, f x = ∑ x ∈ u, f x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  have eg : ∑ᶠ x ∈ s, g x = ∑ x ∈ u, g x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  rw [ef, eg, Int.cast_sum, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => hle x (hus x hx)

theorem wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  unfold wx
  rw [Finset.sum_apply]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem pow_mem_ne (hd : d.AxH 𝒜) {G : WT} {ta : ∀ c, A c} (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0)
    (n : ℕ) : ∀ c, (ta ^ (n + 1)) c ∈ 𝒜 c ((n + 1) • G) ∧ (ta ^ (n + 1)) c ≠ 0 := by
  intro c
  haveI := hd.graded c
  induction n with
  | zero => simpa using hta c
  | succ n ih =>
    rw [pow_succ, Pi.mul_apply, succ_nsmul G (n + 1)]
    exact ⟨SetLike.mul_mem_graded ih.1 (hta c).1, hd.mul_ne_zero c ih.1 (hta c).1 ih.2 (hta c).2⟩

private lemma finsum_mem_const_mul {α : Type*} (s : Set α) (f : α → ℤ) (k : ℤ) (hk : k ≠ 0) :
    ∑ᶠ x ∈ s, k * f x = k * ∑ᶠ x ∈ s, f x := by
  classical
  have hs : s ∩ Function.support (fun x => k * f x) = s ∩ Function.support f := by
    ext x
    simp [hk]
  by_cases hf : (s ∩ Function.support f).Finite
  · rw [finsum_mem_eq_sum_of_inter_support_eq (fun x => k * f x) (t := hf.toFinset) (by
        ext x
        simp [hk]
        try tauto),
      finsum_mem_eq_sum_of_inter_support_eq f (t := hf.toFinset) (by
        ext x
        simp
        try tauto),
      Finset.mul_sum]
  · rw [finsum_mem_eq_zero_of_infinite hf, finsum_mem_eq_zero_of_infinite (by rwa [hs]), mul_zero]

private lemma nP_pow_succ_eq_succ_mul (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (n : ℕ) : d.nP h c ((n + 1) • G) ((ta ^ (n + 1)) c) p = ((n : ℤ) + 1) * d.nP h c G (ta c) p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (ta ^ (n + 1 + 1)) c = (ta ^ (n + 1)) c * ta c := by rw [pow_succ, Pi.mul_apply]
    rw [e, succ_nsmul G (n + 1), d.nP_mul hd h c (d.pow_mem_ne hd hta n c).1 (hta c).1
      (d.pow_mem_ne hd hta n c).2 (hta c).2 hp, ih]
    push_cast
    ring

theorem aG_pow (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (n : ℕ) :
    d.aG h ((n + 1) • G) (ta ^ (n + 1)) = (n + 1) * d.aG h G ta := by
  unfold aG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← finsum_mem_const_mul _ (fun p => d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ)) ((n : ℤ) + 1) (by positivity)]
  refine finsum_mem_congr rfl fun p hp => ?_
  rw [nP_pow_succ_eq_succ_mul d hd h hta c hp n, mul_assoc]

theorem aG_nonneg (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hord : ∀ c v, d.admitted c v → 0 ≤ d.ord c v G (ta c)) : 0 ≤ d.aG h G ta := by
  unfold aG
  refine Finset.sum_nonneg fun c _ => ?_
  refine finsum_nonneg fun p => finsum_nonneg fun hp => ?_
  exact mul_nonneg (d.nP_nonneg hd h c hp G (ta c) (hord c)) (by positivity)

private lemma ratio_zero_left {F0 V0 : Type*} [Field F0] [AddCommGroup V0] [Module F0 V0] {g : V0}
    (hg : g ≠ 0) : ratio (Ω := F0) (0 : V0) g = 0 := by
  unfold ratio
  split_ifs with h0
  · rcases smul_eq_zero.1 h0.choose_spec.symm with h1 | h1
    · exact h1
    · exact absurd h1 hg
  · rfl

theorem thp_ne (hd : d.AxH 𝒜) (c : ι) : ∃ k, d.thp k c ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨e, he, -, hy⟩ := hd.a4
  obtain ⟨q, hq, p, hp⟩ := hy 1
  have key := hp c
  simp only [Pi.one_apply, mul_one] at key
  rw [Finset.sum_eq_zero] at key
  · exact hq c key
  · intro k _
    rw [hcon, ratio_zero_left (he c).2, map_zero, mul_zero]

theorem aG_sb (hd : d.AxH 𝒜) (h : d.S1) :
    d.aG h d.wL (fun c => d.w (d.jc c) c) =
      d.del + ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.Ep h c p * (d.dg (d.gen p) : ℤ) := by
  unfold aG del
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨F, -, -, -, h4, -⟩ := d.componentForm_properties hd h c
  have hf := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  have hE := d.Ep_ne hd h c _ (hd.w_mem _ c) (hd.w_base c)
  rw [← h4, ← finsum_mem_add_distrib']
  · exact finsum_mem_congr rfl fun p hp => by rw [d.nP_split hd h c hp]; ring
  · exact hf.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [h0])⟩
  · exact hE.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [h0])⟩

theorem aG_wx (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (hx : ∀ c, d.wx x c ≠ 0) :
    d.aG h d.wL (d.wx x) = d.aG h d.wL (fun c => d.w (d.jc c) c) :=
  (d.norm_factorization hd h).2.1 _ _ _ (fun c => ⟨d.wx_mem hd x c, hx c⟩) (fun c => ⟨hd.w_mem _ c, hd.w_base c⟩)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IrreducibleFactorStructure
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

theorem irreducible_factor_structure (hd : d.AxH 𝒜) (h : d.S1) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) (c : ι)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 (F c)) :
    ∃ (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (κ : K)
      (a m deF : ℕ), κ ≠ 0 ∧ 1 ≤ m ∧ m * deF ≤ d.delc c ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d.delc c) ∧
      bilinearSubstitution (F c) = MvPolynomial.C κ * MvPolynomial.X (Sum.inr 0) ^ a * F1 ^ m ∧
      d.linearSubstitution c (bilinearSubstitution (F c)) = 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := by

  obtain ⟨F0, κ0, m0, hκ0, hm0, hirr0, hFeq, hker⟩ := d.fZ_eq_const_mul_irreducible_pow hd h c (F c) (hF c) hpos
  obtain ⟨F', hF', -, hmh', -⟩ := d.componentForm_properties hd h c
  have hFF : F c = F' := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) ((hF c).trans hF'.symm)
  have hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := hFF ▸ hmh'
  have hmh1 : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (MvPolynomial.C κ0 * F0 ^ m0) := by
    rw [← hFeq]; exact hmh
  obtain ⟨d0, hd0, hmh0⟩ :=
    MHF.isMH_of_pow (Nat.succ_pos _) F0 κ0 m0 (d.delc c) hm0 hκ0 hirr0.ne_zero hmh1
  obtain ⟨a0, F1, deF, hG0, hirr1, hxh, hdeF, hU⟩ := d.substitution_split_irreducible hd c F0 hirr0 d0 hmh0 hker
  have hg : bilinearSubstitution (F c) = MvPolynomial.C κ0 * bilinearSubstitution F0 ^ m0 := by
    rw [hFeq]; simp only [bilinearSubstitution, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  refine ⟨F1, κ0, a0 * m0, m0, deF, hκ0, hm0, ?_, hirr1, hxh, ?_, ?_, ?_, hmh⟩
  · calc m0 * deF ≤ m0 * d0 := Nat.mul_le_mul_left _ hdeF
      _ = d.delc c := hd0
  · intro s hs
    refine (hU s hs).trans (Nat.mul_le_mul_left _ ?_)
    calc d0 ≤ m0 * d0 := Nat.le_mul_of_pos_left _ hm0
      _ = d.delc c := hd0
  · rw [hg, hG0, mul_pow, pow_mul]; ring
  · rw [hg, map_mul, map_pow, d.substitution_vanishes_of_relation hd c F0 ((hker F0).2 dvd_rfl), zero_pow (by omega), mul_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OmPoly
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

theorem om_poly (hd : d.AxH 𝒜) (h : d.S1) :
    0 ≤ d.aG h d.wF hd.a4.choose ∧ (∃ a b : KTp K d.D d.N, d.IsPres hd h a b) ∧
    ∃ Om : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h ∧ Om ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
        (fun b : Fin (d.D + 1) => if b = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat) Om := by
  exact ⟨d.aG_frame_nonneg hd h, d.de_pres hd h, d.om_is_poly hd h⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

