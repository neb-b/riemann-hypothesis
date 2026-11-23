module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocAtRatio
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

noncomputable section

section Loc

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K' : Type} [Field K'] [Algebra k K']
  {N : ℕ} {x : Fin (N + 1) → Ω} {x' : Fin (N + 1) → K'}
  (hsp : Kleiman.primeOf (S := k) x ≤ Kleiman.primeOf (S := k) x')
include hsp

theorem locAt_ratio {c : Fin (N + 1)} (hc : x' c ≠ 0) (a : Fin (N + 1)) :
    x a / x c ∈ Kleiman.locAt k x x' ∧ Kleiman.redAt k x x' (x a / x c) = x' a / x' c := by
  have hsy : aeval x' (X c : Kleiman.Poly k N) ≠ 0 := by rw [aeval_X]; exact hc
  have h1 := Kleiman.mem_locAt (x := x) (isHomogeneous_X k a) (isHomogeneous_X k c) hsy
  have h2 := Kleiman.redAt_eq hsp (isHomogeneous_X k a) (isHomogeneous_X k c) hsy
  simp only [aeval_X] at h1 h2
  exact ⟨h1, h2⟩

theorem locAt_zpow {a : Ω} (ha : a ∈ Kleiman.locAt k x x') (hr : Kleiman.redAt k x x' a ≠ 0) (n : ℤ) :
    a ^ n ∈ Kleiman.locAt k x x' ∧ Kleiman.redAt k x x' (a ^ n) = Kleiman.redAt k x x' a ^ n := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa only [zpow_natCast] using Kleiman.locAt_pow hsp ha n
  · have hp := Kleiman.locAt_pow hsp ha n
    have hpr : Kleiman.redAt k x x' (a ^ n) ≠ 0 := by rw [hp.2]; exact pow_ne_zero _ hr
    obtain ⟨-, h1, h2⟩ := Kleiman.locAt_inv hsp hp.1 hpr
    simp only [zpow_neg, zpow_natCast]
    rw [← hp.2]
    exact ⟨h1, h2⟩

end Loc

theorem GraphRestrict.full : GraphRestrict.Statement := by
  intro k _ N Ω _ _ x Q n m s K' _ _ x' s' hxy hgen hle ⟨i₀, hi₀⟩ ⟨j₁, hj₁⟩
  classical
  have hsp : Kleiman.primeOf (S := k) x ≤ Kleiman.primeOf (S := k) x' := by
    rw [← comap_mIdealOver_graph x s, ← comap_mIdealOver_graph x' s']
    exact Ideal.comap_mono hle
  obtain ⟨γ, hγ0, hg, hb⟩ := Kleiman.exists_restrict_gen hsp hxy Q

  have hmemQ : ∀ (I : Kleiman.Chart x') {i : Fin (N + 1)}, i ∈ I.1 → ∀ b,
      x i ^ (-n) * s b ∈ Q.sub (Kleiman.liftChart hxy I) := by
    intro I i hi b
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp ((Kleiman.liftChart hxy I).2.2 hi)
    have hsb : s b ∈ (Q.twist (Kleiman.twistSys k x n)).sub (Kleiman.liftChart hxy I) := by
      rw [← hgen]; exact Submodule.subset_span ⟨b, rfl⟩
    obtain ⟨q, hq, hqb⟩ :=
      (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n (Kleiman.liftChart hxy I) hi (s b)).mp hsb
    rw [hqb, smul_eq_mul, ← mul_assoc, ← zpow_add₀ hxi, neg_add_cancel, zpow_zero, one_mul]
    exact hq
  have hi₀I : i₀ ∈ (Kleiman.singleChart hi₀).1 := Finset.mem_singleton_self i₀
  have hx₀ : x i₀ ≠ 0 := hxy i₀ hi₀
  obtain ⟨t, ht⟩ : ∃ t : Fin m → Ω, t = fun b => x i₀ ^ (-n) * s b / γ := ⟨_, rfl⟩
  have htL : ∀ b, t b ∈ Kleiman.locAt k x x' := fun b => by
    rw [ht]; exact hg (Kleiman.singleChart hi₀) _ (hmemQ _ hi₀I b)

  obtain ⟨l₀, hl₀⟩ : ∃ l, Kleiman.redAt k x x' (t l) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b₀, -, hb₀L, hb₀r, hb₀Q⟩ := hb (Kleiman.singleChart hi₀)
    have hmem : x i₀ ^ n • (b₀ * γ) ∈
        (Q.twist (Kleiman.twistSys k x n)).sub (Kleiman.liftChart hxy (Kleiman.singleChart hi₀)) :=
      (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hi₀I _).mpr ⟨_, hb₀Q, rfl⟩
    rw [← hgen, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨a, ha⟩ := hmem
    simp only [Subalgebra.smul_def, smul_eq_mul] at ha
    have haL : ∀ b, (a b : Ω) ∈ Kleiman.locAt k x x' := fun b =>
      (Kleiman.chartRing_sub_locAt hsp hxy _ (a b).2).1
    have hsum : b₀ = ∑ b, (a b : Ω) * t b := by
      have hxn : x i₀ ^ n ≠ 0 := zpow_ne_zero n hx₀
      have : ∑ b, (a b : Ω) * t b = x i₀ ^ (-n) / γ * ∑ b, (a b : Ω) * s b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by rw [ht]; ring
      rw [this, ha, zpow_neg]
      field_simp
    have hL := Kleiman.locAt_sum hsp Finset.univ (fun b => (a b : Ω) * t b) fun b _ =>
      (Kleiman.locAt_mul hsp (haL b) (htL b)).1
    apply hb₀r
    rw [hsum, hL.2]
    exact Finset.sum_eq_zero fun b _ => by
      rw [(Kleiman.locAt_mul hsp (haL b) (htL b)).2, hcon b, mul_zero]

  have htl0 : t l₀ ≠ 0 := (Kleiman.locAt_inv hsp (htL l₀) hl₀).1
  have hsl0 : s l₀ ≠ 0 := fun h0 => htl0 (by rw [ht]; simp [h0])
  have hkey : ∀ b, s' b * Kleiman.redAt k x x' (t l₀) = s' l₀ * Kleiman.redAt k x x' (t b) := by
    intro b
    obtain ⟨hdL, hdr⟩ := Kleiman.locAt_div hsp (htL b) (htL l₀) hl₀
    obtain ⟨f, h, e, hf, hh, hhy, hfh⟩ := hdL
    have hhx := Kleiman.aeval_ne_zero_of_primeOf_le hsp hh hhy
    have hr2 : Kleiman.redAt k x x' (t b) / Kleiman.redAt k x x' (t l₀) = aeval x' f / aeval x' h := by
      rw [← hdr, hfh, Kleiman.redAt_eq hsp hf hh hhy]
    have hst : t b / t l₀ = s b / s l₀ := by
      rw [div_eq_div_iff htl0 hsl0, ht]; dsimp only; ring
    rw [hst, div_eq_div_iff hsl0 hhx] at hfh
    have hgr := graphEq_of_le hle hf hh b l₀ (by rw [hfh]; ring)
    rw [div_eq_div_iff hl₀ hhy] at hr2
    apply mul_right_cancel₀ hhy
    linear_combination Kleiman.redAt k x x' (t l₀) * hgr - s' l₀ * hr2
  have hlam : s' l₀ ≠ 0 := by
    intro h0
    apply hj₁
    have := hkey j₁
    rw [h0, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_right hl₀
  obtain ⟨μ, hμdef⟩ : ∃ μ : K', μ = s' l₀ / (Kleiman.redAt k x x' (t l₀) * x' i₀ ^ n) := ⟨_, rfl⟩
  have hμ : μ ≠ 0 := by
    rw [hμdef]; exact div_ne_zero hlam (mul_ne_zero hl₀ (zpow_ne_zero n hi₀))

  let Q'' : Kleiman.LineBundle k x' :=
    Kleiman.LineBundle.mk
      (Kleiman.SubFamily.mk (Kleiman.redSys hxy Q.toSubSystem γ) (Kleiman.redSys_mem_iff hsp hxy hg))
      (fun I => by
        obtain ⟨S0, hS0⟩ := Q.fg (Kleiman.liftChart hxy I)
        change (Kleiman.redSys hxy Q.toSubSystem γ).sub I |>.FG
        rw [Kleiman.redSys_sub_eq_span hsp hxy hg I hS0]
        exact Submodule.fg_span (S0.finite_toSet.image _))
      (fun I => Kleiman.redSys_invertible hsp hxy hγ0 hg I (hb I))
  have hR'' : Kleiman.RestrictData Q.toSubSystem hxy Q''.toSubSystem
      (fun q => Kleiman.redAt k x x' (q / γ)) := Kleiman.restrictData_redSys hsp hxy hg Q'' rfl
  have hR' := restrictData_scale hR'' μ hμ
  refine ⟨scaleBundle Q'' μ hμ, fun q => μ * Kleiman.redAt k x x' (q / γ), hR', ?_⟩
  intro I
  obtain ⟨i, hi⟩ := I.2.1
  have hxi' : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
  have hxi : x i ≠ 0 := hxy i hxi'

  have hc : ∀ b, x i ^ (-n) * s b / γ ∈ Kleiman.locAt k x x' ∧
      Kleiman.redAt k x x' (x i ^ (-n) * s b / γ) = (x' i₀ / x' i) ^ n * Kleiman.redAt k x x' (t b) := by
    intro b
    obtain ⟨hr1, hr2⟩ := locAt_ratio hsp hxi' i₀
    have hr0 : Kleiman.redAt k x x' (x i₀ / x i) ≠ 0 := by rw [hr2]; exact div_ne_zero hi₀ hxi'
    obtain ⟨hz1, hz2⟩ := locAt_zpow hsp hr1 hr0 n
    have hxn : x i ^ n ≠ 0 := zpow_ne_zero n hxi
    have hxn₀ : x i₀ ^ n ≠ 0 := zpow_ne_zero n hx₀
    have heq : x i ^ (-n) * s b / γ = (x i₀ / x i) ^ n * t b := by
      rw [ht, div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [heq, ← hr2, ← hz2]
    exact Kleiman.locAt_mul hsp hz1 (htL b)

  have hval : ∀ b, s' b = x' i ^ n * (μ * Kleiman.redAt k x x' (x i ^ (-n) * s b / γ)) := by
    intro b
    have hk := hkey b
    have hxn : x' i ^ n ≠ 0 := zpow_ne_zero n hxi'
    have hxn₀ : x' i₀ ^ n ≠ 0 := zpow_ne_zero n hi₀
    rw [(hc b).2, hμdef, div_zpow]
    field_simp
    linear_combination hk
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, TranslateEq.mem_twist_twistSys_iff _ n I hi]
    exact ⟨_, hR'.mem I _ (hmemQ I hi b), by rw [smul_eq_mul]; exact hval b⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (TranslateEq.mem_twist_twistSys_iff _ n I hi z).mp hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_span_singleton_mul.mp hw
    obtain ⟨q, hq, rfl⟩ := (Kleiman.mem_redSys_iff hsp hxy hg I v).mp hv
    have hxq : x i ^ n • q ∈ (Q.twist (Kleiman.twistSys k x n)).sub (Kleiman.liftChart hxy I) :=
      (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hi _).mpr ⟨q, hq, rfl⟩
    rw [← hgen, Submodule.mem_span_range_iff_exists_fun] at hxq
    obtain ⟨a, ha⟩ := hxq
    simp only [Subalgebra.smul_def, smul_eq_mul] at ha
    have haL : ∀ b, (a b : Ω) ∈ Kleiman.locAt k x x' ∧ Kleiman.redAt k x x' (a b) ∈ Kleiman.chartRing k x' I :=
      fun b => Kleiman.chartRing_sub_locAt hsp hxy I (a b).2
    have hqs : q / γ = ∑ b, (a b : Ω) * (x i ^ (-n) * s b / γ) := by
      have hxn : x i ^ n ≠ 0 := zpow_ne_zero n hxi
      have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b / γ) = x i ^ (-n) / γ * ∑ b, (a b : Ω) * s b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, ha, zpow_neg]
      field_simp
    have hsumL := Kleiman.locAt_sum hsp Finset.univ (fun b => (a b : Ω) * (x i ^ (-n) * s b / γ))
      fun b _ => (Kleiman.locAt_mul hsp (haL b).1 (hc b).1).1
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun b => ⟨Kleiman.redAt k x x' (a b), (haL b).2⟩, ?_⟩
    simp only [Subalgebra.smul_def, smul_eq_mul]
    rw [hqs, hsumL.2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(Kleiman.locAt_mul hsp (haL b).1 (hc b).1).2, hval b]
    ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemMIdealOverIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Homog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem aeval_mul_block (v : (Σ k, ι k) → Ω) (c : K → Ω) (b : K → ℕ) (g : MvPolynomial (Σ k, ι k) S)
    (hg : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) g b) :
    aeval (fun p => v p * c p.1) g = aeval v g * ∏ k, c k ^ b k := by
  have hb : ∀ e ∈ g.support, ∀ k, ∑ i, e ⟨k, i⟩ = b k := by
    intro e he k
    rw [sum_block_eq_blockWeight, hg (mem_support_iff.mp he)]
  have h2 : ((MvPolynomial.aeval c : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars S).comp (mConeMapOver S v) =
      aeval fun p => v p * c p.1 := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver]
  rw [← h2, AlgHom.comp_apply, AlgHom.restrictScalars_apply, mConeMapOver_eq_of_block v hb, map_mul, map_prod,
    aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_pow, aeval_X]

theorem mem_mIdealOver_iff (y : (Σ k, ι k) → Ω) (f : MvPolynomial (Σ k, ι k) S) :
    f ∈ mIdealOver S y ↔
      ∀ b : K → ℕ, aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) = 0 := by
  constructor
  · intro hf b
    rw [← coeff_mConeMapOver, RingHom.mem_ker.mp hf, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · intro h
    refine RingHom.mem_ker.mpr (MvPolynomial.ext _ _ fun d => ?_)
    have := coeff_mConeMapOver (S := S) y (⇑d) f
    rw [Finsupp.equivFunOnFinite_symm_coe] at this
    rw [this, h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

end Homog

theorem CurveLift.full : CurveLift.Statement := by
  intro k _ N Ω _ _ x Q n m s _hx hgen pp e hW
  have hpp := hW.isPrime
  obtain ⟨i, hXi⟩ := hW.relevant
  have hi : x i ≠ 0 := fun h0 => hXi (hW.le (by
    rw [Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X, h0]))
  have hPt := Kleiman.PrimeFiltration.Point.proof k Ω N x pp hpp hW.homog hW.le i hi hXi

  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra k K')
      (ψ : Kleiman.chartRing k x (Kleiman.singleChart hi) →ₐ[k] K'),
      RingHom.ker ψ = Kleiman.chartPrime pp hi := by
    have : (Kleiman.chartPrime pp hi).IsPrime := hPt.1
    refine ⟨FractionRing (Kleiman.chartRing k x (Kleiman.singleChart hi) ⧸ Kleiman.chartPrime pp hi),
      inferInstance, inferInstance,
      (IsScalarTower.toAlgHom k _ _).comp (Ideal.Quotient.mkₐ k (Kleiman.chartPrime pp hi)), ?_⟩
    ext a
    rw [RingHom.mem_ker]
    change algebraMap _ (FractionRing (Kleiman.chartRing k x (Kleiman.singleChart hi) ⧸ Kleiman.chartPrime pp hi))
      (Ideal.Quotient.mk (Kleiman.chartPrime pp hi) a) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hy : Kleiman.primeOf (S := k) (fun a => ψ (Kleiman.ratio hi a)) = pp := hPt.2 K' ψ hker

  have hiI : i ∈ (Kleiman.singleChart hi).1 := Finset.mem_singleton_self i
  let g : Fin m → Ω := fun b => x i ^ (-n) * s b
  have hgQ : Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi)) (Set.range g) =
      Q.sub (Kleiman.singleChart hi) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      have hb : s b ∈ (Q.twist (Kleiman.twistSys k x n)).sub (Kleiman.singleChart hi) := by
        rw [← hgen]; exact Submodule.subset_span ⟨b, rfl⟩
      obtain ⟨y, hy, hyb⟩ := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hiI (s b)).mp hb
      have : g b = y := by
        simp only [g, hyb, smul_eq_mul, zpow_neg]
        field_simp
      rw [SetLike.mem_coe, this]
      exact hy
    · intro y hy
      have hy' : x i ^ n * y ∈ Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi)) (Set.range s) := by
        rw [hgen]
        exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hiI _).mpr ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy'
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨a, ?_⟩
      simp only [g, Subalgebra.smul_def, smul_eq_mul] at ha ⊢
      have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b) = x i ^ (-n) * ∑ b, (a b : Ω) * s b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, ha, zpow_neg]
      field_simp

  obtain ⟨Q', hQQ⟩ := Q.invertible (Kleiman.singleChart hi)
  rw [← hgQ] at hQQ
  have hone : (1 : Ω) ∈ Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi)) (Set.range g) * Q' := by
    rw [hQQ]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_
    · intro q hq q' hq'
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hq
      refine ⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
    · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
      refine ⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_add]
  have hgA : ∀ a b, g a * w b ∈ Kleiman.chartRing k x (Kleiman.singleChart hi) := by
    intro a b
    have h := Submodule.mul_mem_mul
      (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi))
        (Set.range g)) (hwQ b)
    rw [hQQ, Submodule.mem_one] at h
    obtain ⟨z, hz⟩ := h
    rw [← hz]
    exact z.2

  obtain ⟨j0, hj0⟩ : ∃ j0, ψ ⟨g j0 * w j0, hgA j0 j0⟩ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : Kleiman.chartRing k x (Kleiman.singleChart hi)) = ∑ j, ⟨g j * w j, hgA j j⟩ :=
      Subtype.ext (by simp [hsum])
    have h2 := congrArg ψ h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_one, map_sum] at h2
    simp [hcon] at h2
  let t : Fin m → K' := fun b => ψ ⟨g b * w j0, hgA b j0⟩
  refine ⟨mIdealOver k (graphVec (fun a => ψ (Kleiman.ratio hi a)) t),
    isMultiProjPrime_mIdealOver_graph _ _ ⟨i, ?_⟩ ⟨j0, hj0⟩, ?_, by rw [comap_mIdealOver_graph, hy]⟩
  · have : Kleiman.ratio (S := k) hi i = 1 := Subtype.ext (div_self hi)
    rw [this, map_one]
    exact one_ne_zero
  · intro f hf
    rw [mem_mIdealOver_iff] at hf ⊢
    intro b
    have hfb := weightedHomogeneousComponent_isWeightedHomogeneous (w := NumbersDVR.blockWeight (graphIdx N m)) b f
    let u : (Σ c, graphIdx N m c) → Kleiman.chartRing k x (Kleiman.singleChart hi) := fun p =>
      match p with
      | ⟨Sum.inl (), a⟩ => Kleiman.ratio hi a
      | ⟨Sum.inr (), c⟩ => ⟨g c * w j0, hgA c j0⟩
    have hu : (fun p => (u p : Ω)) = fun p => graphVec x s p *
        (Sum.elim (fun _ : Unit => (x i)⁻¹) (fun _ : Unit => x i ^ (-n) * w j0)) p.1 := by
      funext p
      rcases p with ⟨⟨⟩ | ⟨⟩, a⟩
      · change x a / x i = x a * (x i)⁻¹
        rw [div_eq_mul_inv]
      · change x i ^ (-n) * s a * w j0 = s a * (x i ^ (-n) * w j0)
        ring
    have h0 : aeval u (weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) b f) = 0 := by
      apply Subtype.ext
      change (Kleiman.chartRing k x (Kleiman.singleChart hi)).val (aeval u _) = 0
      rw [comp_aeval_apply]
      change aeval (fun p => (u p : Ω)) _ = 0
      rw [hu, aeval_mul_block _ _ b _ hfb, hf b, zero_mul]
    have hψu : (fun p => ψ (u p)) = graphVec (fun a => ψ (Kleiman.ratio hi a)) t := by
      funext p
      rcases p with ⟨⟨⟩ | ⟨⟩, a⟩ <;> rfl
    rw [← hψu, ← comp_aeval_apply, h0, map_zero]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreFibresNef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

theorem segreFibresNef_of_map (hA : SegreLiftComap.Statement) (hB : SegreLiftPrime.Statement)
    (hC : SegreLiftRelDim.Statement) (hN : SegreLiftIntNum.Statement)
    (hD : SegreFibreIdeal.Statement) (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (F : Type) [Field F] (φ : O →+* F) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (β : K → ℤ) :
    IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal F ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ))
                              (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
      IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal F ((mIdealOver O y).map (MvPolynomial.map φ)) β := by
  obtain ⟨hrel, hle, hlift⟩ := hD O Ω F φ K ι y
  constructor
  · intro h W hW hPW hdim
    have hpos := h (segreLift ι F W) (hB F K ι W hW) (hlift W hPW)
      (by rw [hC F K ι W hW]; exact hdim)
    rwa [hN F K ι W hW β] at hpos
  · intro h W' hW' hPW' hdim
    obtain ⟨hWp, heq⟩ := hA F K ι W' hW' fun g hg => hPW' (hrel hg)
    have hPW : (mIdealOver O y).map (MvPolynomial.map φ) ≤ W'.comap (segreIncl ι F) :=
      hle.trans (Ideal.comap_mono hPW')
    have hdimW : relDim (W'.comap (segreIncl ι F)) = ((1 : ℕ) : WithBot (WithTop ℤ)) := by
      rw [← hC F K ι _ hWp, ← heq]
      exact hdim
    have hpos := h _ hWp hPW hdimW
    rw [heq, hN F K ι _ hWp β]
    exact hpos

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RelDimMIdealOverEqTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open GroundTheory.Heights₂.Heights.NumbersDVR (segreVec)

theorem relDim_mIdealOver_eq_trdeg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ t : ℕ, Algebra.trdeg F (chartRingOver F y c) = t ∧
      relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ)) := by
  have hy := trdeg_quotient_mIdealOver (F := F) y c hc
  have _ : (mIdealOver F y).IsPrime := RingHom.ker_isPrime _
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)
  rw [hy] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) =
      ((t + Fintype.card K : ℕ) : ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]
    simp
  refine ⟨t, ht, ?_⟩
  unfold relDim
  rw [dimy]
  have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
      ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
      (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  rw [e₁, Nat.cast_add, add_sub_cancel_right]
  rfl

theorem SegreDim.proof : SegreDim.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y hy
  choose c hc using hy
  obtain ⟨t, ht, hrel⟩ := relDim_mIdealOver_eq_trdeg (F := F) y c hc
  obtain ⟨t', ht', hrel'⟩ := relDim_mIdealOver_eq_trdeg (F := F) (segreJoin y) (segreChart c c)
    (segreChart_adm y (segreVec_ne_zero y hc) hc)
  have heq : chartRingOver F (segreJoin y) (segreChart c c) = chartRingOver F y c :=
    le_antisymm (segre_diag_le (S := F) y c) (chartRingOver_le_segre (S := F) y c c)
  rw [heq, ht] at ht'
  have htt : t = t' := by exact_mod_cast ht'
  rw [hrel, hrel', htt]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

