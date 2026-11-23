module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLocalInverseOfInjOn
section
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.InjHol

theorem analyticAt_of_differentiableOn_euclidean {n : ℕ} {W : Set (V n)} {g : V n → V n} {a : V n}
    (hW : IsOpen W) (ha : a ∈ W) (hg : DifferentiableOn ℂ g W) : AnalyticAt ℂ g a := by
  let e : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' W) := hW.preimage e.symm.continuous
  have hf : DifferentiableOn ℂ (fun x => e (g (e.symm x))) (e.symm ⁻¹' W) :=
    e.differentiable.comp_differentiableOn
      (hg.comp e.symm.differentiable.differentiableOn (fun _ hx => hx))
  have ha' : e a ∈ e.symm ⁻¹' W := by simpa using ha
  have han : AnalyticAt ℂ (fun x => e (g (e.symm x))) (e a) := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n _ (fun x => e (g (e.symm x)) i) hU
      (differentiableOn_pi.mp hf i) _ ha'
  have h2 : AnalyticAt ℂ (fun y => e.symm (e (g (e.symm (e y))))) a :=
    ((e.symm : (Fin n → ℂ) →L[ℂ] V n).analyticAt _).comp
      (han.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt a))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h2

theorem exists_local_inverse_of_injOn :
    ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W →
      DifferentiableOn ℂ g W → Set.InjOn g W →
      ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by
  intro n W g a hW ha hg hinj
  have han := analyticAt_of_differentiableOn_euclidean hW ha hg
  have hi : Function.Injective (fderiv ℂ g a) :=
    localStatement n _ _ (by simp) (by simp) g a han ⟨W, hW.mem_nhds ha, hinj⟩
  have hs : Function.Surjective (fderiv ℂ g a) := LinearMap.injective_iff_surjective.mp
    (show Function.Injective (fderiv ℂ g a : V n →ₗ[ℂ] V n) from hi)
  let f' : V n ≃L[ℂ] V n := ContinuousLinearEquiv.ofBijective (fderiv ℂ g a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  have hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) a := han.differentiableAt.hasFDerivAt
  have hc : ContDiffAt ℂ 1 g a := han.contDiffAt
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hG := hc.to_localInverse hf' hn
  have hGv := hc.localInverse_apply_image hf' hn
  refine ⟨hc.localInverse hf' hn, ?_⟩
  have hT : Filter.Tendsto (hc.localInverse hf' hn) (𝓝 (g a)) (𝓝 a) := by
    have := hG.continuousAt.tendsto
    rwa [hGv] at this
  have hr : ∀ᶠ u in 𝓝 (g a), g (hc.localInverse hf' hn u) = u :=
    (hc.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  filter_upwards [hT.eventually (hW.mem_nhds ha), hr, hG.eventually (by simp)] with u h1 h2 h3
  exact ⟨h1, h2, h3.differentiableAt hn⟩

end GlobalTheory.InjHol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReversedCharpolyCoeffNotMemPrime
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem exists_normCoeff_not_mem {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (hQ₀ : ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥)
    (p : Ideal A) (hp : p.IsPrime) (hb : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) :
    ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  set K := FractionRing A
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.NormalDescent.exists_map_eq_charK (K := K) φ hφ b
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hdeg : (charK φ hφ K b).natDegree = P.natDegree := by
    rw [← hP]; exact natDegree_map_eq_of_injective hinj P
  have hmon : P.Monic := by
    have h1 := charK_monic φ hφ K b
    rw [← hP] at h1
    apply hinj
    rw [Monic, leadingCoeff_map_of_injective hinj] at h1
    simpa using h1
  by_contra hcon
  push_neg at hcon

  have hcoeff : ∀ j < P.natDegree, P.coeff j ∈ p := by
    intro j hj
    have hk : 1 ≤ P.natDegree - j := by omega
    have hrev : (charK φ hφ K b).reverse.coeff (P.natDegree - j) = algebraMap A K (P.coeff j) := by
      rw [coeff_reverse, hdeg, revAt_le (by omega), show P.natDegree - (P.natDegree - j) = j by omega,
        ← hP, coeff_map]
    have hex : ∃ a : A, algebraMap A K a = (charK φ hφ K b).reverse.coeff (P.natDegree - j) :=
      ⟨P.coeff j, hrev.symm⟩
    have := algebraMap_normCoeff φ hφ b _ hex
    rw [hrev] at this
    have := hinj this
    rw [← this]
    exact hcon _ hk

  set M := TensorProduct A K B
  have hCH : Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b) = 0 := by
    have h := LinearMap.aeval_self_charpoly (Algebra.lmul K M ((1 : K) ⊗ₜ[A] b))
    have h2 : Algebra.lmul K M (Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b)) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]; exact h
    have h3 := LinearMap.congr_fun h2 1
    simpa using h3
  have hker : Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B) (Polynomial.aeval b P) = 0 := by
    rw [← Polynomial.aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply,
      ← Polynomial.aeval_map_algebraMap K, hP]
    exact hCH

  let I : Ideal B := RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B))
  have hI : I.comap (algebraMap A B) ≤ p := by
    intro a ha
    obtain ⟨Q₀, hQ₀p, hQ₀c⟩ := hQ₀
    have ha' : (1 : K) ⊗ₜ[A] (algebraMap A B a) = 0 := ha
    have := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)
      (TensorProduct.mk A K B 1)).1 ha'
    obtain ⟨⟨s, hs⟩, hs0⟩ := this
    have hs0' : φ (s * a) = 0 := by
      rw [map_mul]; simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hs0
    have hmem : s * a ∈ Q₀.comap φ := by simp [Ideal.mem_comap, hs0']
    rw [hQ₀c, Ideal.mem_bot] at hmem
    have hs' : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have : a = 0 := by
      rcases mul_eq_zero.1 hmem with h | h
      · exact absurd h hs'
      · exact h
    rw [this]; exact p.zero_mem
  haveI : Algebra.IsIntegral A B := inferInstance
  obtain ⟨Q, hQI, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) p I hI
  have hPQ : Polynomial.aeval b P ∈ Q := hQI (by simpa [I, RingHom.mem_ker] using hker)
  have hbd : b ^ P.natDegree ∈ Q := by
    have hsum := hmon.as_sum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_add (f := _), map_pow, aeval_X, map_sum] at hPQ
    refine (Q.add_mem_iff_left ?_).1 hPQ
    refine Q.sum_mem fun j hj => ?_
    rw [map_mul, aeval_C, aeval_X_pow]
    refine Q.mul_mem_right _ ?_
    have : P.coeff j ∈ Q.comap (algebraMap A B) := by
      change P.coeff j ∈ Ideal.under A Q
      rw [hQc]; exact hcoeff j (Finset.mem_range.1 hj)
    exact this
  exact hb Q hQp hQc (hQp.mem_of_pow_mem _ hbd)

end GlobalTheory.NormalDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set

namespace GlobalTheory.Mem.RayPrimes

theorem log_bounded (g : ℝ → ℂ) (L : ℂ → ℂ) (hL : Continuous L) (h1 : L 1 ≠ 0)
    (hg : ContinuousOn g (Ioi 1)) (he : ∀ s : ℝ, 1 < s → cexp (g s) = L s) :
    g =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hc : Continuous (fun s : ℝ => L s / L 1 - 1) := by fun_prop (disch := exact h1)
  have ht : ∀ᶠ s : ℝ in 𝓝 1, ‖L s / L 1 - 1‖ < 1 / 2 := by
    have := (hc.norm.tendsto 1)
    simp only [ofReal_one, div_self h1, sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 ht
  have hb' : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), ‖L s / L 1 - 1‖ < 1 / 2 := fun s hs => hb (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  have hslit : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), 1 + (L s / L 1 - 1) ∈ slitPlane := fun s hs =>
    mem_slitPlane_of_norm_lt_one (by linarith [hb' s hs])
  set k : ℝ → ℂ := fun s => g s - log (1 + (L s / L 1 - 1)) with hk
  have hkc : ContinuousOn k (Ioo 1 (1 + δ)) :=
    (hg.mono Ioo_subset_Ioi_self).sub
      (ContinuousOn.clog (continuous_const.add hc).continuousOn hslit)
  have hke : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), cexp (k s) = L 1 := fun s hs => by
    have hne : L s ≠ 0 := by rw [← he s hs.1]; exact exp_ne_zero _
    simp only [hk]
    rw [exp_sub, exp_log (slitPlane_ne_zero (hslit s hs)), he s hs.1, add_sub_cancel]
    field_simp
  have hconst : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), k s = k (1 + δ / 2) := fun s hs =>
    Complex.isCoveringMap_exp.constOn_of_comp isPreconnected_Ioo hkc
      (fun a ha b hb => Subtype.ext (by simp only; rw [hke a ha, hke b hb])) hs
      ⟨by linarith, by linarith⟩
  refine IsBigO.of_bound (‖k (1 + δ / 2)‖ + 1) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ by linarith)] with s hs
  have h2 : g s = k (1 + δ / 2) + log (1 + (L s / L 1 - 1)) := by
    rw [← hconst s hs]; simp [hk]
  have h3 := norm_log_one_add_half_le_self (hb' s hs).le
  rw [h2, norm_one, mul_one]
  refine (norm_add_le _ _).trans ?_
  linarith [hb' s hs]

section series

variable {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (a : ι → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
include hn ha

theorem norm_term_le (v : ι) {s t : ℝ} (hst : t ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ) ^ (-t) := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  rw [norm_mul, norm_natCast_cpow_of_pos (by linarith [hn v])]
  simp only [neg_re, ofReal_re]
  calc ‖a v‖ * (n v : ℝ) ^ (-s) ≤ 1 * (n v : ℝ) ^ (-t) := by
        gcongr
        · exact ha v
        · linarith
    _ = _ := one_mul _

theorem norm_term_le_inv (v : ι) {s : ℝ} (hs : 1 ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ)⁻¹ := by
  have := norm_term_le n hn a ha v hs
  rwa [Real.rpow_neg_one] at this

theorem norm_term_le_half (v : ι) {s : ℝ} (hs : 1 ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  refine (norm_term_le_inv n hn a ha v hs).trans ?_
  rw [one_div]; gcongr

theorem continuousOn_logSum (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) :
    ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi 1) := by
  intro s hs1
  obtain ⟨t, ht1, hts⟩ := exists_between (show (1 : ℝ) < s from hs1)
  have : ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi t) := by
    refine continuousOn_tsum (u := fun v => 3 / 2 * (n v : ℝ) ^ (-t)) ?_ ((hs t ht1).mul_left _) ?_
    · intro v
      refine ContinuousOn.neg (ContinuousOn.clog ?_ ?_)
      · have h0 : (n v : ℂ) ≠ 0 := by
          have := hn v
          exact_mod_cast (by omega : n v ≠ 0)
        refine (continuous_const.sub (continuous_const.mul ?_)).continuousOn
        exact Continuous.const_cpow (by fun_prop) (Or.inl h0)
      · intro x hx
        rw [sub_eq_add_neg]
        refine mem_slitPlane_of_norm_lt_one ?_
        rw [norm_neg]
        linarith [norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx))]
    · intro v x hx
      rw [norm_neg, sub_eq_add_neg]
      have h := norm_log_one_add_half_le_self (z := -(a v * (n v : ℂ) ^ (-(x : ℂ))))
        (by rw [norm_neg]; exact norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx)))
      rw [norm_neg] at h
      linarith [norm_term_le n hn a ha v (le_of_lt hx)]
  exact (this.continuousAt (Ioi_mem_nhds hts)).continuousWithinAt

theorem summable_term (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) {s : ℝ} (h : 1 < s) :
    Summable fun v => a v * (n v : ℂ) ^ (-(s : ℂ)) :=
  Summable.of_norm_bounded (hs s h) fun v => norm_term_le n hn a ha v le_rfl

theorem logSum_sub_bounded (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) :
    (fun s : ℝ => (∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) - ∑' v, a v * (n v : ℂ) ^ (-(s : ℂ)))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  refine IsBigO.of_bound (∑' v, (n v : ℝ) ^ (-(2 : ℝ))) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs1
  have hs1 : 1 < s := hs1
  have hb : ∀ v, ‖-log (1 - a v * (n v : ℂ) ^ (-(s : ℂ))) - a v * (n v : ℂ) ^ (-(s : ℂ))‖
      ≤ (n v : ℝ) ^ (-(2 : ℝ)) := by
    intro v
    set z := a v * (n v : ℂ) ^ (-(s : ℂ)) with hz
    have h1 : ‖z‖ ≤ 1 / 2 := norm_term_le_half n hn a ha v hs1.le
    have h2 : ‖z‖ ≤ (n v : ℝ)⁻¹ := norm_term_le_inv n hn a ha v hs1.le
    have h3 := norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]; linarith)
    have h4 : -log (1 - z) - z = -(log (1 + -z) - -z) := by rw [← sub_eq_add_neg 1 z]; ring
    rw [h4, norm_neg]
    refine h3.trans ?_
    rw [norm_neg, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, ← inv_pow]
    have h5 : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h6 : ‖z‖ ^ 2 ≤ ((n v : ℝ)⁻¹) ^ 2 := by gcongr
    have h7 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ 2 * 2 := by gcongr
    linarith
  have hsum := summable_term n hn a ha hs hs1
  have hd := Summable.of_norm_bounded (hs 2 (by norm_num)) hb
  have hl : Summable fun v => -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ))) := by
    simpa using hd.add hsum
  rw [← hl.tsum_sub hsum, norm_one, mul_one]
  exact tsum_of_norm_bounded (hs 2 (by norm_num)).hasSum hb

end series

section orth

variable {G : Type} [CommGroup G] [Fintype G]

theorem norm_char (χ : G →* ℂˣ) (x : G) : ‖(χ x : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G) ?_ Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

theorem sum_char_eq_zero [Fintype (G →* ℂˣ)] {x : G} (hx : x ≠ 1) :
    ∑ χ : G →* ℂˣ, (χ x : ℂ) = 0 := by
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hx
  let f : (G →* ℂˣ) →* ℂ :=
    { toFun := fun χ => (χ x : ℂ), map_one' := by simp, map_mul' := by simp }
  refine sum_hom_units_eq_zero f ?_
  intro h
  apply hφ
  have := DFunLike.congr_fun h φ
  simpa [f] using this

theorem not_summable_class {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (cl : ι → G)
    (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s))
    (hχ : ∀ χ : G →* ℂˣ, χ ≠ 1 → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s →
      cexp (∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))) = L s)
    (Z : ℂ → ℂ) (hZ : Continuous Z) (hZ1 : Z 1 ≠ 0)
    (h1 : ∀ s : ℝ, 1 < s → Z s = (s - 1) *
      cexp (∑' v, -log (1 - ((1 : G →* ℂˣ) (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))))
    (c : G) : ¬ Summable fun v : {v // cl v = c} => (n v : ℝ)⁻¹ := by
  classical
  intro hc
  have : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  let g : (G →* ℂˣ) → ℝ → ℂ := fun χ s => ∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))
  let P : (G →* ℂˣ) → ℝ → ℂ := fun χ s => ∑' v, (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ))
  have hgP : ∀ χ, (fun s => g χ s - P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := fun χ =>
    logSum_sub_bounded n hn _ (fun v => (norm_char χ _).le) hs
  have hP : ∀ χ, χ ≠ 1 → P χ =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    intro χ h
    obtain ⟨L, hL, hL1, hL2⟩ := hχ χ h
    have := log_bounded (g χ) L hL hL1
      (continuousOn_logSum n hn _ (fun v => (norm_char χ _).le) hs) hL2
    simpa using this.sub (hgP χ)
  have hS : (fun s => ∑ χ, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have hc' := (summable_subtype_iff_indicator (f := fun v => (n v : ℝ)⁻¹)
      (s := {v | cl v = c})).1 hc
    have hc'' := hc'.mul_left (Fintype.card (G →* ℂˣ) : ℝ)
    refine IsBigO.of_bound (∑' v, (Fintype.card (G →* ℂˣ) : ℝ) *
      ({v | cl v = c}).indicator (fun v => (n v : ℝ)⁻¹) v) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs1
    have hs1 : 1 < s := hs1
    have hsum : ∀ χ : G →* ℂˣ, Summable fun v =>
        (χ c⁻¹ : ℂ) * ((χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ))) := fun χ =>
      (summable_term n hn _ (fun v => (norm_char χ _).le) hs hs1).mul_left _
    simp only [P, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun χ _ => hsum χ), norm_one, mul_one]
    refine tsum_of_norm_bounded hc''.hasSum fun v => ?_
    by_cases hv : cl v = c
    · rw [indicator_of_mem (by exact hv)]
      refine (norm_sum_le _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.card_univ]
      refine Finset.sum_le_card_nsmul _ _ _ fun χ _ => ?_
      rw [norm_mul, norm_char, one_mul]
      exact norm_term_le_inv n hn (fun v => (χ (cl v) : ℂ)) (fun v => (norm_char χ _).le) v hs1.le
    · rw [indicator_of_notMem (by exact hv)]
      have : c⁻¹ * cl v ≠ 1 := fun h => hv (inv_mul_eq_one.1 h).symm
      have h0 := sum_char_eq_zero this
      simp only [map_mul, Units.val_mul] at h0
      simp only [← mul_assoc, ← Finset.sum_mul, h0]
      simp
  have hP1 : P 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have h2 : (fun s => ∑ χ ∈ Finset.univ.erase 1, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1]
        (fun _ => (1 : ℝ)) :=
      (IsBigO.sum fun χ hχ => (hP χ (Finset.ne_of_mem_erase hχ)).const_mul_left
        (χ c⁻¹ : ℂ)).congr_left fun s => Finset.sum_apply _ _ _
    refine (hS.sub h2).congr_left fun s => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G →* ℂˣ))]
    simp
  have hg1 : g 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    simpa using (hgP 1).add hP1
  obtain ⟨B, hB⟩ := hg1.bound
  have hlim : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1)) := by
    have : Continuous fun s : ℝ => Z s := by fun_prop
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B) ?_ ?_
    · filter_upwards [hB, self_mem_nhdsWithin] with s h hs1
      rw [h1 s hs1, norm_mul, norm_exp]
      gcongr
      rw [norm_one, mul_one] at h
      exact (re_le_norm _).trans h
    · have : Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B := by fun_prop
      simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  exact hZ1 (tendsto_nhds_unique hlim hlim0)

end orth

section field

variable {K : Type} [Field K] [NumberField K]

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

end field

end GlobalTheory.Mem.RayPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
section
open IsLocalRing

namespace GlobalTheory.RegularCompletion

theorem isRegularLocalRing_adicCompletion :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T],
      IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by
  intro T _ _
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal T) T) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)
  set S := AdicCompletion (maximalIdeal T) T

  obtain ⟨s, hcard, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal T).fg_of_isNoetherianRing
  set xs := s.toList
  have hofl : Ideal.ofList xs = maximalIdeal T := by
    rw [← hs]; unfold Ideal.ofList; congr 1; ext x; simp [xs]
  have hlen : xs.length = (maximalIdeal T).spanFinrank := by simp [xs, hcard]
  have hreg : RingTheory.Sequence.IsRegular T xs := GlobalTheory.isRegular_of_length_eq_spanFinrank hofl hlen
  have hmem : ∀ r ∈ xs.map (algebraMap T S), r ∈ maximalIdeal S := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ (hofl ▸ Ideal.subset_span hx)
  have hregS : RingTheory.Sequence.IsRegular S (xs.map (algebraMap T S)) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
      (hreg.toIsWeaklyRegular.of_flat)
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hregS
  have hnt : Nontrivial (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    apply hregS.2
    simp [htop]
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq, ← hdim]
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [List.length_map, hlen]
  calc ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞)
      = 0 + ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞) := (zero_add _).symm
    _ ≤ _ := add_le_add_left h0 _

end GlobalTheory.RegularCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffMapOfIsPushout
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem reverse_map_of_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem normCoeff_map_of_isPushout {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hα : Function.Injective α) (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ) :
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  have hbc := @GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout
  have hint := @_root_.GlobalTheory.NormalDescent.exists_map_eq_charK
  let ι : FractionRing A →+* FractionRing A' := IsLocalization.map (FractionRing A') α
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective α hα)
  have hι : ∀ a : A, ι (algebraMap A (FractionRing A) a) = algebraMap A' (FractionRing A') (α a) :=
    fun a => IsLocalization.map_eq _ _
  have hc := hbc φ α β φ' H hφ hφ' ι hι b
  have spec : ∀ {R S : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] (ψ : R →+* S)
      (hψ : ψ.Finite) (s : S), algebraMap R (FractionRing R) (normCoeff ψ hψ s k) =
        (charK ψ hψ (FractionRing R) s).reverse.coeff k := by
    intro R S _ _ _ _ ψ hψ s
    obtain ⟨P, hP⟩ := hint (K := FractionRing R) ψ hψ s
    refine algebraMap_normCoeff ψ hψ s k ⟨P.reverse.coeff k, ?_⟩
    rw [← hP, reverse_map_of_injective _ (IsFractionRing.injective R (FractionRing R)), coeff_map]
  apply IsFractionRing.injective A' (FractionRing A')
  rw [← hι, spec, spec, hc, reverse_map_of_injective ι ι.injective, coeff_map]

end GlobalTheory.NormalDescent
end

