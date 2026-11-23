module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisLogTeichmullerAssociatedSubOneOnDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

open Filter Topology

namespace GlobalTheory.BSP.SeedT

section Gen

variable (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)

theorem norm_intCast_le (z : ℤ) : ‖(z : Disc l u ρ)‖ ≤ 1 := by
  have := norm_toDisc_le (l := l) (u := u) (ρ := ρ) (z : A)
  rwa [map_intCast] at this

theorem norm_natCast_le (z : ℕ) : ‖(z : Disc l u ρ)‖ ≤ 1 := by
  have := norm_toDisc_le (l := l) (u := u) (ρ := ρ) (z : A)
  rwa [map_natCast] at this

theorem norm_lpow_mul (e : ℕ) (y : Disc l u ρ) : ‖((l : Disc l u ρ)) ^ e * y‖ = ‖y‖ / (l : ℝ) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', mul_assoc, DiscBasic.norm_l_mul l u ρ, ih, pow_succ']
    field_simp

theorem norm_coprime_mul (n : ℕ) (h : Nat.Coprime l n) (x : Disc l u ρ) : ‖(n : Disc l u ρ) * x‖ = ‖x‖ := by
  haveI := DiscBasic.isUltrametricDist_disc l u ρ
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hc := congrArg (Int.cast : ℤ → Disc l u ρ) hab
  push_cast at hc
  have e : x = (a : Disc l u ρ) * ((l : Disc l u ρ) * x) + (b : Disc l u ρ) * ((n : Disc l u ρ) * x) := by
    linear_combination (-x) * hc
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  apply le_antisymm
  · exact (norm_mul_le _ _).trans (by nlinarith [norm_natCast_le l u ρ n, norm_nonneg x])
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : ‖(a : Disc l u ρ) * ((l : Disc l u ρ) * x)‖ ≤ ‖x‖ / l := by
      rw [← DiscBasic.norm_l_mul l u ρ x]
      exact (norm_mul_le _ _).trans (by nlinarith [norm_intCast_le l u ρ a, norm_nonneg ((l : Disc l u ρ) * x)])
    have h2 : ‖(b : Disc l u ρ) * ((n : Disc l u ρ) * x)‖ ≤ ‖(n : Disc l u ρ) * x‖ :=
      (norm_mul_le _ _).trans (by nlinarith [norm_intCast_le l u ρ b, norm_nonneg ((n : Disc l u ρ) * x)])
    have h3 := IsUltrametricDist.norm_add_le_max ((a : Disc l u ρ) * ((l : Disc l u ρ) * x))
      ((b : Disc l u ρ) * ((n : Disc l u ρ) * x))
    rw [← e] at h3
    have h0 := norm_nonneg ((n : Disc l u ρ) * x)
    rcases le_max_iff.1 h3 with h4 | h4
    · have : ‖x‖ ≤ ‖x‖ / l := h4.trans h1
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    · linarith

theorem isUnit_coprime (n : ℕ) (h : Nat.Coprime l n) : IsUnit (n : Disc l u ρ) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hc := congrArg (Int.cast : ℤ → Disc l u ρ) hab
  push_cast at hc
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hn : ‖(a : Disc l u ρ) * (l : Disc l u ρ)‖ < 1 := by
    rw [mul_comm, DiscBasic.norm_l_mul l u ρ, div_lt_one (by linarith)]
    linarith [norm_intCast_le l u ρ a]
  have hu : IsUnit ((b : Disc l u ρ) * (n : Disc l u ρ)) := by
    refine ⟨Units.oneSub _ hn, ?_⟩
    rw [Units.val_oneSub]
    linear_combination -hc
  exact isUnit_of_mul_isUnit_right hu

theorem isUnit_natCast (n : ℕ) (hn : n ≠ 0) : IsUnit (n : Disc l u ρ) := by
  obtain ⟨e, n', hd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  push_cast
  exact ((isUnit_l_disc l u ρ).pow e).mul (isUnit_coprime l u ρ n' ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hd))

theorem norm_le_natCast_mul (n : ℕ) (hn : n ≠ 0) (x : Disc l u ρ) : ‖x‖ ≤ n * ‖(n : Disc l u ρ) * x‖ := by
  obtain ⟨e, n', hd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hn' : n' ≠ 0 := by rintro rfl; simp at hn
  have hle : (l : ℝ) ^ e ≤ ((l ^ e * n' : ℕ) : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ n' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn'
    nlinarith [pow_pos (show (0 : ℝ) < l by exact_mod_cast hl.out.pos) e]
  have hpos : (0 : ℝ) < (l : ℝ) ^ e := pow_pos (by exact_mod_cast hl.out.pos) e
  have key : ‖((l ^ e * n' : ℕ) : Disc l u ρ) * x‖ = ‖x‖ / (l : ℝ) ^ e := by
    push_cast
    rw [mul_assoc, norm_lpow_mul, norm_coprime_mul l u ρ n' ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hd)]
  rw [key]
  calc ‖x‖ = (l : ℝ) ^ e * (‖x‖ / (l : ℝ) ^ e) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)

end Gen

end GlobalTheory.BSP.SeedT

namespace GlobalTheory.BSP.SeedT

theorem gamma_partial {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (μ : Ainf l) (n : ℕ) (s : Per.Acris0 l)
    (hs : ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) μ) ^ (k + 1)) :
    γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      ∑ k ∈ Finset.range n, (-1) ^ k * bk.iA μ ^ (k + 1) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
  set P : Ainf l := ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Ainf l) * μ ^ (k + 1) with hP
  have h1 : ((n.factorial : ℕ) : Per.Acris0 l) * s = algebraMap (Ainf l) (Per.Acris0 l) P := by
    apply Subtype.ext
    change ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) = algebraMap (Ainf l) (Per.AinfP l) P
    rw [hs, hP]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_mul, map_pow, map_natCast, map_neg, map_one]
  have h2 := congrArg (fun x => γ (algebraMap (Per.Acris0 l) (Per.Acris l) x)) h1
  simp only [map_mul, map_natCast] at h2
  rw [show algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Ainf l) (Per.Acris0 l) P) =
    algebraMap (Ainf l) (Per.Acris l) P from (GlobalTheory.RingIface.tower l P).symm, hγ, hP] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, map_natCast, map_neg, map_one] at h2
  have hu := isUnit_natCast l (bk.ev X) bk.ρ₀ n.factorial (Nat.factorial_ne_zero n)
  refine hu.mul_left_cancel (h2.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  have hd : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) hk'
  have hv := isUnit_natCast l (bk.ev X) bk.ρ₀ (k + 1) (Nat.succ_ne_zero k)
  have hq : ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀) =
      ((n.factorial : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
    calc ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀)
        = ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀) *
            (((k + 1 : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀)) := by
          rw [Ring.mul_inverse_cancel _ hv, mul_one]
      _ = ((n.factorial / (k + 1) * (k + 1) : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
          push_cast; ring
      _ = _ := by rw [Nat.div_mul_cancel hd]
  rw [hq]
  ring

theorem t_assoc_mu : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l)
    (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) →
    (∀ x, ‖γ x‖ ≤ 1) → Associated (γ C.t) (bk.iA (mu C.ε)) := by
  intro l hl K bk C γ hγ hγn
  haveI := DiscBasic.isUltrametricDist_disc l (bk.ev X) bk.ρ₀
  set m := bk.iA (mu C.ε) with hm_def
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hm : ‖m‖ ≤ 1 / 3 := by
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.BSP.BK.norm_iA_mu_le l K bk C.ε (core_isEps l C)
    by_cases h : l = 2
    · exact (h2 h).trans (by norm_num)
    · have h3 : (3 : ℝ) ≤ l := by
        have := hl.out.two_le
        exact_mod_cast (show 3 ≤ l by omega)
      refine h1.trans ?_
      rw [one_div]
      exact inv_anti₀ (by norm_num) h3
  set f : ℕ → bk.DA bk.ρ₀ := fun k => (-m) ^ (k + 1) * Ring.inverse ((k + 2 : ℕ) : bk.DA bk.ρ₀) with hf_def
  have hf : ∀ k, ‖f k‖ ≤ (2 / 3 : ℝ) ^ (k + 1) := by
    intro k
    have hu := isUnit_natCast l (bk.ev X) bk.ρ₀ (k + 2) (by omega)
    have e : ((k + 2 : ℕ) : bk.DA bk.ρ₀) * f k = (-m) ^ (k + 1) := by
      rw [hf_def, mul_left_comm, Ring.mul_inverse_cancel _ hu, mul_one]
    have h1 := norm_le_natCast_mul l (bk.ev X) bk.ρ₀ (k + 2) (by omega) (f k)
    rw [e] at h1
    have h2 : ‖(-m) ^ (k + 1)‖ ≤ ‖m‖ ^ (k + 1) := by
      rw [← norm_neg m]; exact norm_pow_le' _ (Nat.succ_pos k)
    have h3 : ‖m‖ ^ (k + 1) ≤ (1 / 3 : ℝ) ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) hm _
    have h4 : ((k + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      have : k + 2 ≤ 2 ^ (k + 1) := Nat.lt_two_pow_self
      exact_mod_cast this
    calc ‖f k‖ ≤ ((k + 2 : ℕ) : ℝ) * ‖(-m) ^ (k + 1)‖ := h1
      _ ≤ (2 : ℝ) ^ (k + 1) * (1 / 3 : ℝ) ^ (k + 1) :=
          mul_le_mul h4 (h2.trans h3) (norm_nonneg _) (by positivity)
      _ = (2 / 3 : ℝ) ^ (k + 1) := by rw [← mul_pow]; norm_num
  have hsum : Summable f := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (2 / 3 : ℝ) < 1)).mul_left (2 / 3)) fun k => ?_
    rw [← pow_succ']
    exact hf k
  set y := ∑' k, f k with hy_def
  have hy : ‖y‖ ≤ 2 / 3 :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun k =>
      (hf k).trans (pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero k))
  have hunit : IsUnit (1 + y) := by
    refine ⟨Units.oneSub (-y) (by rw [norm_neg]; linarith), ?_⟩
    rw [Units.val_oneSub, sub_neg_eq_add]
  set S : ℕ → bk.DA bk.ρ₀ := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * m ^ (k + 1) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) with hS_def
  have hS : ∀ n, S (n + 1) = m * (1 + ∑ k ∈ Finset.range n, f k) := by
    intro n
    induction n with
    | zero => simp [hS_def]
    | succ n ih =>
      have e1 : S (n + 1 + 1) = S (n + 1) + (-1) ^ (n + 1) * m ^ (n + 1 + 1) *
          Ring.inverse ((n + 1 + 1 : ℕ) : bk.DA bk.ρ₀) := by
        simp only [hS_def]; rw [Finset.sum_range_succ]
      rw [e1, ih, Finset.sum_range_succ, hf_def]
      simp only
      rw [neg_pow]
      ring
  have hlim1 : Tendsto (fun n => S (n + 1)) atTop (𝓝 (m * (1 + y))) := by
    simp_rw [hS]
    exact (tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat).const_mul m
  have hlim2 : Tendsto (fun n => S (n + 1)) atTop (𝓝 (γ C.t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε hlinv
    obtain ⟨N, hN⟩ := C.t_log r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨s, hs1, z, hz⟩ := hN (n + 1) (by omega)
    have key := gamma_partial bk γ hγ (mu C.ε) (n + 1) s hs1
    rw [dist_eq_norm, norm_sub_rev]
    have e2 : γ C.t - S (n + 1) = (l : bk.DA bk.ρ₀) ^ r * γ z := by
      rw [hS_def]
      simp only
      rw [← key, ← map_sub, hz, map_mul, map_pow, map_natCast]
    rw [e2, norm_lpow_mul]
    calc ‖γ z‖ / (l : ℝ) ^ r ≤ 1 / (l : ℝ) ^ r :=
          div_le_div_of_nonneg_right (hγn z) (by positivity)
      _ = (l : ℝ)⁻¹ ^ r := by rw [inv_pow, one_div]
      _ < ε := hr
  have heq : γ C.t = m * (1 + y) := tendsto_nhds_unique hlim2 hlim1
  refine ⟨hunit.unit⁻¹, ?_⟩
  rw [heq, mul_assoc, IsUnit.mul_val_inv, mul_one]

end GlobalTheory.BSP.SeedT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Adm8AtOfUnramifiedHecke
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.AdmFrobTriple

theorem not_mem_placesOver_of_ne (E : Type) [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ≠ q) {v : HeightOneSpectrum (𝓞 E)} (h1 : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro h2
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 h)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1' : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 E) ∈ v.asIdeal := h2
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1') (Ideal.mul_mem_left _ _ h2')

theorem continuous_algebraMap_padicInt {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (I : Ideal O) (hI : IsAdic I) (hO : (l : O) ∈ I) :
    Continuous (algebraMap ℤ_[l] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[l] O) ?_
  rw [ContinuousAt, map_zero, hI.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO n)

theorem sum_coeff_charpolyRev {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∑ k ∈ Finset.range (n + 1), M.charpolyRev.coeff k = (1 - M).det := by
  have hdeg : M.charpolyRev.natDegree < n + 1 := by
    rw [← Matrix.reverse_charpoly]
    have := Polynomial.reverse_natDegree_le M.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    omega
  have h1 := Polynomial.eval_eq_sum_range' hdeg (1 : R)
  simp only [one_pow, mul_one] at h1
  rw [← h1, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, RingHom.mapMatrix_apply]
  split_ifs <;> simp

variable {D : D7}

theorem l_mem (i : D.ntw.Tw) : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (D.ntw.O0 i) (D.ntw.O i))
  rw [map_natCast] at h2
  exact D.ntw.O_l i h2

theorem continuous_twistCyclotomicCharacter (i : D.ntw.Tw) :
    Continuous fun g : Gen.GE D.nd => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
  (continuous_algebraMap_padicInt _ (D.ntw.twistBaseCoefficientRing_isAdic i) (l_mem i)).comp
    (Units.continuous_val.comp (continuous_cycZ D.host.E D.nd.Om (D.ntw.l i)))

theorem pD_not (i : D.ntw.Tw) (v) (hv : v ∈ D.ntw.pD i) :
    v ∉ placesOver D.host.E (D.ntw.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have h2 : v ∈ (D.ntw.pD i : Set _) := hv
  rw [D.ntw.pD_eq] at h2
  have hl := (D.ntw.lPrime i).out
  split_ifs at h2 with h
  · refine ⟨not_mem_placesOver_of_ne _ D.host.pde'_prime hl ?_ h2, fun k =>
      not_mem_placesOver_of_ne _ D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h2⟩
    rw [h]; exact D.host.pde_ne.symm
  · exact ⟨not_mem_placesOver_of_ne _ D.host.pde_prime hl (Ne.symm h) h2, fun k =>
      not_mem_placesOver_of_ne _ D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h2⟩

end GlobalTheory.AdmFrobTriple

namespace GlobalTheory.AdmFrobTriple

theorem eta_smul {D : D7} (i : D.ntw.Tw) (s : D.ntw.Sig i) (σ : Gen.GE D.nd) :
    ((((eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) •
      ((D.ntw.rhoS i s σ : GL (Fin D.R.r) (D.ntw.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) =
    (((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s σ := by
  simp only [Tmat, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, mul_smul]

theorem adm8At_of_hkFrob : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HkFrob i s →
    characterTwistExists D.ntw D.nexp i s := by
  intro D i s hU hH _
  refine ⟨(eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous fun g : Gen.GE D.nd => (((chiS i s g)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      simp_rw [← map_inv]
      exact (D.ntw.twistCharacterFamily_continuous i _ _).comp continuous_inv
    have he : (fun g : Gen.GE D.nd => ((((eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹) g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) =
        fun g => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t *
          (((chiS i s g)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      funext g
      simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
        Units.val_pow_eq_pow_val]
    rw [he]
    exact ((continuous_twistCyclotomicCharacter i).pow _).mul hc
  · intro P hP _ A hA σ hσ
    have hPl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)
    have hPg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k h => hP (D.ntw.placesOver_subset_exceptional i k h)
    have hPd : P ∉ D.ntw.pD i := fun h => hP (D.ntw.primes_subset_exceptional i h)
    have h1 : D.ntw.rhoS i s σ = 1 := hU P hPl hPg A hA σ hσ
    have h2 : chiS i s σ = 1 := D.ntw.twistCharacterFamily_unramified i _ _ P hPl hPg hPd A hA σ hσ
    have h3 : eps0 D.ntw i σ = 1 := (GlobalTheory.TripleGal.eps0_unram_frob D i P hPl A hA).1 σ hσ
    simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1, h2, h3]
  · intro v hv A hA
    obtain ⟨hl, hg⟩ := pD_not i v hv
    have h1 : ∀ σ ∈ Ine (F := D.host.E) A, D.ntw.rhoS i s σ = 1 := fun σ hσ => hU v hl hg A hA σ hσ
    have h3 : ∀ σ ∈ Ine (F := D.host.E) A, eps0 D.ntw i σ = 1 := (GlobalTheory.TripleGal.eps0_unram_frob D i v hl A hA).1
    have h2 := D.ntw.twistCharacterFamily_at_auxiliaryPlaces i (D.ntw.jS i s) (D.ntw.side i s) v hv A hA
    cases hb : D.ntw.side i s
    · left
      intro σ hσ
      have h2' : chiS i s σ = (D.ntw.delta i σ)⁻¹ := by
        have := h2 σ hσ; rw [hb] at this; simpa [chiS, hb] using this
      simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1 σ hσ, h2', h3 σ hσ]
    · right
      intro σ hσ
      have h2' : chiS i s σ = D.ntw.delta i σ := by
        have := h2 σ hσ; rw [hb] at this; simpa [chiS, hb] using this
      simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1 σ hσ, h2', h3 σ hσ]
  · intro P hP hs σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eta_smul, ← sum_coeff_charpolyRev, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact hH P hP hs σ hσ k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end GlobalTheory.AdmFrobTriple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDecompIffDecompStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDecomp_iff_decomp : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π ↔ ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
  first | exact @GlobalTheory.DecompForms.main | exact GlobalTheory.DecompForms.main | (intros; apply GlobalTheory.DecompForms.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionary
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AdmissibleDictionary

theorem main : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  intro D i
  exact GlobalTheory.TameFixedLift.main D.nd i

end GlobalTheory.AdmissibleDictionary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisation
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.admissible_shape_and_epsilon_at_every_localisation

theorem main : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible (D := D) i ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  intro D i
  refine ⟨fun w hw => ?_, GlobalTheory.TameFixedLift.main D.nd i⟩
  exact UpperTheory.KStar.Cyc.kw_le_roots D.host.toHostRaw (D.nbr i w hw)

end GlobalTheory.admissible_shape_and_epsilon_at_every_localisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicCharacterOfAdm
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.AlgCharFromGal

theorem charpoly_fin_one {K : Type*} [CommRing K] (M : Matrix (Fin 1) (Fin 1) K) :
    M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

end GlobalTheory.AlgCharFromGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeInduction
section
namespace GlobalTheory.BaseChangeInduction

theorem baseChange_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : GlobalTheory.Prism.SemiBC u)
    (p : N → Prop) (hzero : p 0) (hadd : ∀ y z, p y → p z → p (y + z))
    (hsmul : ∀ (r : B) (y : N), p y → p (r • y)) (himg : ∀ x : M, p (u x)) (y : N) : p y := by
  let S : Submodule B N :=
    { carrier := {n | p n}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => hadd a b ha hb
      smul_mem' := fun r n hn => hsmul r n hn }
  have hq : S.mkQ = 0 := by
    refine (h (N ⧸ S) 0).unique (fun x => ?_) (fun x => rfl)
    exact (Submodule.Quotient.mk_eq_zero S).2 (himg x)
  have hy : S.mkQ y = 0 := by rw [hq]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 hy

end GlobalTheory.BaseChangeInduction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphismStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T T' : Lat a O K ϖ) (I : Ident t ϖ P T) (I' : Ident t ϖ Q T'), IsBK I → IsBK I' → ∀ f : LatHom T.L T'.L, ∃ F, IsMapOf I I' f F := by
  first | exact @GlobalTheory.BKReal.Full.main | exact GlobalTheory.BKReal.Full.main | (intros; apply GlobalTheory.BKReal.Full.main <;> assumption)
end

