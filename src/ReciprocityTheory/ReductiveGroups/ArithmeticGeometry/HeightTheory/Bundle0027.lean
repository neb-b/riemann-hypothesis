module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UnitAtIntAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DePres
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BlockDegOfScale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ProdZpowEqZpowSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ComponentFormProperties
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

theorem componentForm_properties (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ F : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c ∧ F ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 → ∃ κ : K, κ ≠ 0 ∧
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
          (MvPolynomial.aeval (fun v : TVar d.D d.N =>
            if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p := by
  obtain ⟨F, hF, hF0⟩ := d.componentForm_poly hd h c
  obtain ⟨hmh, hmm⟩ := d.DegreeSumIdentity hd h c F hF
  exact ⟨F, hF, hF0, hmh, hmm, fun x hx => d.SpecialFibreFactorization hd h c F hF x hx⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteHeightFractionRepr
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem gen_ne_zero_of_mem_htOne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hh⟩ := hp
  haveI := hpr
  obtain ⟨g, hg, hpg⟩ := ValUFD.heightOne_principal p hh
  have hPr : p.IsPrincipal := ⟨⟨g, hpg⟩⟩
  unfold gen
  rw [dite_eq_left hPr]
  intro h0
  have hbot : p = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).2 h0
  rw [hbot] at hpg
  exact hg.ne_zero (Ideal.span_singleton_eq_bot.1 hpg.symm)

theorem finite_height_fraction_repr (hd : d.AxH 𝒜) (h : d.S1) :
    ∃ U V : KTp K d.D d.N, U ≠ 0 ∧ V ≠ 0 ∧ (∃ eU, IsMultiHomogeneous eU U) ∧
      (∃ eV, IsMultiHomogeneous eV V) ∧
      d.fDivE hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) V =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) U ∧
      d.h0f h d.wF hd.a4.choose = h0 U - h0 V := by
  classical
  have hspec : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hd.a4.choose_spec.1
  have hfin : ∀ c, {p | p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0}.Finite := fun c =>
    (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (hspec c).1 (hspec c).2
  obtain ⟨T, hmemT⟩ : ∃ T : ι → Finset (Ideal (KTp K d.D d.N)),
      ∀ c p, p ∈ T c ↔ p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0 :=
    ⟨fun c => (hfin c).toFinset, fun c p => by simp⟩
  have hmemS : ∀ x ∈ Finset.univ.sigma T,
      x.2 ∈ d.HtOne ∧ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 ≠ 0 := by
    intro x hx
    rw [Finset.mem_sigma] at hx
    exact (hmemT _ _).1 hx.2
  have hne : ∀ x ∈ Finset.univ.sigma T, d.gen x.2 ≠ 0 := fun x hx => d.gen_ne_zero_of_mem_htOne (hmemS x hx).1
  have hmh : ∀ x ∈ Finset.univ.sigma T,
      IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen x.2)) (d.gen x.2) := by
    intro x hx
    obtain ⟨hp, hn⟩ := hmemS x hx
    refine (d.good_primes_properties hd h x.1).2.1 x.2 hp ?_
    by_contra hw
    push_neg at hw
    apply hn
    simp [nP, hw]
  have halg : ∀ x ∈ Finset.univ.sigma T,
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).2 (hne x hx)
  have key : ∀ (a : KTf K d.D d.N), a ≠ 0 → ∀ m : ℤ, a ^ m * a ^ (-m).toNat = a ^ m.toNat := by
    intro a ha m
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
    congr 1
    omega
  refine ⟨∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    ∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩,
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩, ?_, ?_⟩
  · have hfac : ∀ c, (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p) =
        ∏ p ∈ T c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
          d.nP h c d.wF (hd.a4.choose c) p := by
      intro c
      apply finprod_mem_eq_prod_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_mulSupport] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', zpow_zero])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hf : d.fDivE hd h = ∏ x ∈ Finset.univ.sigma T,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ^ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 := by
      rw [Finset.prod_sigma]
      unfold fDivE
      exact Finset.prod_congr rfl fun c _ => hfac c
    rw [hf, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [map_pow, map_pow]
    exact key _ (halg x hx) _
  · have hsum : ∀ c, (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p)) =
        ∑ p ∈ T c, (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p) := by
      intro c
      apply finsum_mem_eq_sum_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_support] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', Int.cast_zero, zero_mul])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hn0 : 0 < d.N + 1 := Nat.succ_pos _
    have hU : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    have hV : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    rw [hU, hV, ← Finset.sum_sub_distrib, Finset.sum_sigma]
    unfold h0f
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsum c]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← sub_mul]
    congr 1
    exact_mod_cast (Int.toNat_sub_toNat_neg _).symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FprodNeZero
section
set_option linter.style.haveILetI false

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

private theorem gen_ne_zero_of_mem_htOne_heightData {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hht⟩ := hp
  have hne : p ≠ ⊥ := by
    rintro rfl
    first
      | (simp at hht; done)
      | (rw [Ideal.height_bot] at hht; exact zero_ne_one hht)
  obtain ⟨q, hqp, hq⟩ := hpr.exists_mem_prime_of_ne_bot hne
  have hqi : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  have hle : Ideal.span {q} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hqp
  have hbot : (⊥ : Ideal (KTp K d.D d.N)) < Ideal.span {q} :=
    bot_lt_iff_ne_bot.mpr (by simpa using hq.ne_zero)
  haveI := hpr
  haveI := hqi
  have hspan : Ideal.span {q} = p := by
    by_contra hne'
    have hlt : Ideal.span {q} < p := lt_of_le_of_ne hle hne'
    have h3 : (Ideal.span {q}).height < 1 := by
      have hp1 : p.height ≤ (1 : ℕ) := by rw [hht]; rfl
      exact (Ideal.height_le_iff.mp hp1) _ hqi hlt
    have h0 : (Ideal.span {q}).height ≤ (0 : ℕ) := by
      rw [ENat.lt_one_iff_eq_zero] at h3
      rw [h3]; rfl
    have h2 := (Ideal.height_le_iff.mp h0) ⊥ Ideal.isPrime_bot hbot
    first
      | (simp at h2; done)
      | exact absurd h2 (not_lt_of_ge bot_le)
      | exact ENat.not_lt_zero _ h2
  have hprin : p.IsPrincipal := ⟨⟨q, hspan.symm⟩⟩
  haveI := hprin
  simp only [Data.gen, dif_pos hprin]
  intro h0
  exact hne ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)

theorem fprod_ne_zero (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite) :
    (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) ≠ 0 := by
  refine finprod_mem_induction (fun x => x ≠ 0) one_ne_zero (fun x y hx hy => mul_ne_zero hx hy) ?_
  intro q hq
  apply zpow_ne_zero
  have hg := gen_ne_zero_of_mem_htOne_heightData d hq
  first
    | exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg
    | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hg
    | exact (map_ne_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective _ _)).mpr hg
    | (simpa using hg)

theorem sig_fprod (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite)
    (hg : ∀ q ∈ d.HtOne, E q ≠ 0 → ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
      (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q)) (d.gen q))
    (bb : Fin (d.D + 1)) (u : Kˣ) :
    sigF (K := K) (D := d.D) (N := d.N) bb u (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) =
      algebraMap K (KTf K d.D d.N) (u : K) ^ (∑ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) *
      ∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q := by
  classical
  have h1 : d.HtOne ∩ Function.mulSupport (fun q =>
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) ⊆ hE.toFinset := by
    rintro q ⟨hq, hs⟩
    rw [Set.Finite.coe_toFinset]
    exact ⟨hq, fun h0 => hs (by simp only [h0, zpow_zero])⟩
  have h1' : d.HtOne ∩ Function.support (fun q =>
      E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) ⊆ hE.toFinset := by
    rintro q ⟨hq, hs⟩
    rw [Set.Finite.coe_toFinset]
    exact ⟨hq, fun h0 => hs (by simp only [h0, zero_mul])⟩
  have h2 : (hE.toFinset : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := by
    intro q hq
    rw [Set.Finite.coe_toFinset] at hq
    exact hq.1
  rw [finprod_mem_eq_prod_of_subset _ h1 h2, finsum_mem_eq_sum_of_subset _ h1' h2, map_prod]
  have hκ : algebraMap K (KTf K d.D d.N) (u : K) ≠ 0 :=
    (map_ne_zero _).mpr u.ne_zero
  rw [← HDiscOmL.prod_zpow hκ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q hq => ?_
  have hq' : q ∈ d.HtOne ∧ E q ≠ 0 := by
    rw [Set.Finite.mem_toFinset] at hq
    exact hq
  have hs : sigP (N := d.N) bb u (d.gen q) =
      MvPolynomial.C ((u : K) ^ (if bb = 0 then 0 else d.dg (d.gen q))) * d.gen q :=
    scale_multiHomogeneous bb u (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q))
      (d.gen q) (hg q hq'.1 hq'.2)
  have hs' : sigF (K := K) (D := d.D) (N := d.N) bb u
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q)) =
      algebraMap K (KTf K d.D d.N) (u : K) ^ ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) := by
    rw [d.sigF_algebraMap, hs, map_mul, ← d.algebraMap_K_KTf, map_pow, zpow_natCast]
  rw [map_zpow₀, hs', mul_zpow, ← zpow_mul, mul_comm (E q)]

theorem om_is_poly (hd : d.AxH 𝒜) (h : d.S1) :
    ∃ Om : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h ∧ Om ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
        (fun b : Fin (d.D + 1) => if b = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat) Om := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  have hfin : ∀ c, {q | q ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) q ≠ 0}.Finite := fun c =>
    (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (he c).1 (he c).2

  have hint : ∀ p ∈ d.HtOne, LocAt.IntAt p (d.omE hd h) := by
    intro p hp
    haveI := hp.1
    have hs : ∀ c, ∃ V : KTf K d.D d.N, LocAt.UnitAt p V ∧
        (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ d.nP h c d.wF (hd.a4.choose c) q) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p * V :=
      fun c => d.split_at _ (hfin c) hp
    choose V hV hVe using hs
    have hX0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (d.gen_prime' hp).ne_zero
    have hf : d.fDivE hd h = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        (∑ c, d.nP h c d.wF (hd.a4.choose c) p) * ∏ c, V c := by
      simp only [fDivE]
      rw [Finset.prod_congr rfl fun c _ => hVe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0]
    have h2 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p) =
        (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
          (∑ c, d.nP h c d.wF (hd.a4.choose c) p)) ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    have hom : d.omE hd h = (d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p)) * (∏ c, V c) ^ 2 := by
      rw [omE, hf, h2]
      ring
    rw [hom]
    exact LocAt.intAt_mul (d.de_local hd h hp)
      (LocAt.unitAt_intAt (LocAt.unitAt_pow (LocAt.unitAt_prod _ _ fun c _ => hV c) 2))
  obtain ⟨Om, hOm⟩ := ufd_mem_of_forall_prime (R := KTp K d.D d.N) (d.omE hd h) (fun q hq => by
    have hp : Ideal.span {q} ∈ d.HtOne :=
      ⟨(Ideal.span_singleton_prime hq.ne_zero).mpr hq, ValUFD.height_span_prime hq⟩
    obtain ⟨a, s, hs, e⟩ := hint _ hp
    exact ⟨a, s, fun hdv => hs (Ideal.mem_span_singleton.mpr hdv), e⟩)

  have hf0 : d.fDivE hd h ≠ 0 := by
    simp only [fDivE]
    rw [Finset.prod_ne_zero_iff]
    exact fun c _ => d.fprod_ne_zero _ (hfin c)
  have hom0 : d.omE hd h ≠ 0 :=
    mul_ne_zero (d.disc_lattice hd h).1 (pow_ne_zero 2 hf0)
  have hOm0 : Om ≠ 0 := by
    rintro rfl
    rw [map_zero] at hOm
    exact hom0 hOm
  refine ⟨Om, hOm.symm, hOm0, ?_⟩

  obtain ⟨a, b, hb0, hab, m, -, ha, hbm⟩ := d.de_pres hd h
  have hsigDe : ∀ (bb : Fin (d.D + 1)) (u : Kˣ),
      sigF (K := K) (D := d.D) (N := d.N) bb u (d.De hd h) = d.De hd h := by
    intro bb u
    have e1 := congrArg (sigF (K := K) (D := d.D) (N := d.N) bb u) hab
    have sa : sigP (N := d.N) bb u a = MvPolynomial.C ((u : K) ^ m bb) * a :=
      scale_multiHomogeneous bb u m a ha
    have sb : sigP (N := d.N) bb u b = MvPolynomial.C ((u : K) ^ m bb) * b :=
      scale_multiHomogeneous bb u m b hbm
    rw [d.sigF_algebraMap, map_mul, d.sigF_algebraMap, sa, sb, map_mul, map_mul, hab,
      ← d.algebraMap_K_KTf] at e1
    have hC : algebraMap K (KTf K d.D d.N) ((u : K) ^ m bb) ≠ 0 :=
      (map_ne_zero _).mpr (pow_ne_zero _ u.ne_zero)
    have hB : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
    apply mul_right_cancel₀ (mul_ne_zero hC hB)
    linear_combination -e1
  set Eb : Fin (d.D + 1) → ℤ := fun bb => ∑ c, ∑ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
    d.nP h c d.wF (hd.a4.choose c) q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ) with hEb
  have hsigf : ∀ (bb : Fin (d.D + 1)) (u : Kˣ),
      sigF (K := K) (D := d.D) (N := d.N) bb u (d.fDivE hd h) =
        algebraMap K (KTf K d.D d.N) (u : K) ^ Eb bb * d.fDivE hd h := by
    intro bb u
    have hκ : algebraMap K (KTf K d.D d.N) (u : K) ≠ 0 := (map_ne_zero _).mpr u.ne_zero
    simp only [fDivE, hEb]
    rw [map_prod, Finset.prod_congr rfl fun c _ => d.sig_fprod _ (hfin c) (fun q hq hn =>
      (d.good_primes_properties hd h c).2.1 q hq (by
        by_contra hno
        apply hn
        simp only [nP]
        rw [finsum_mem_def]
        refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
        rw [Set.indicator_apply, if_neg (fun hw => hno ⟨w, hw⟩)])) bb u,
      Finset.prod_mul_distrib, HDiscOmL.prod_zpow hκ]
  have hEb : ∀ bb : Fin (d.D + 1), 2 * Eb bb =
      ((if bb = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat : ℕ) : ℤ) := by
    intro bb
    by_cases hbb : bb = 0
    · simp [hEb, hbb]
    · simp only [hEb, hbb, if_false]
      rw [Nat.cast_mul, Int.toNat_of_nonneg (d.aG_frame_nonneg hd h)]
      rfl
  intro s hs bb
  refine block_deg_of_scale bb _ Om (fun u => ?_) s hs
  apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  change algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (sigP (N := d.N) bb u Om) =
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C ((u : K) ^
      (if bb = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat)) * Om)
  rw [← d.sigF_algebraMap, map_mul, ← hOm, ← d.algebraMap_K_KTf, map_pow, ← zpow_natCast, ← hEb bb]
  have hk : algebraMap K (KTf K d.D d.N) (u : K) ^ (2 * Eb bb) =
      (algebraMap K (KTf K d.D d.N) (u : K) ^ Eb bb) ^ 2 := by
    rw [mul_comm, zpow_mul]
    norm_cast
  simp only [omE]
  rw [map_mul, map_pow, hsigDe, hsigf, hk]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

