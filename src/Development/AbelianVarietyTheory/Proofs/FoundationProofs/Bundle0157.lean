module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSumIccPeriodicMulInvFloorDiv
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.FloorTelescope

lemma sum_Icc_sub (G : ℤ → ℂ) (R : ℕ) :
    ∑ d ∈ Finset.Icc (-(R:ℤ)) R, (G (d+1) - G d) = G ((R:ℤ)+1) - G (-(R:ℤ)) := by
  have himg : Finset.Icc (-(R:ℤ)) R = (Finset.range (2*R+1)).image (fun k : ℕ => (k:ℤ) - R) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(d + R).toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [himg, Finset.sum_image (by intro a _ b _ h; simp only at h; omega)]
  have := Finset.sum_range_sub (fun k : ℕ => G ((k:ℤ) - R)) (2*R+1)
  convert this using 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 2; push_cast; ring
  · congr 2 <;> push_cast <;> ring

theorem tendsto_sum_Icc_div (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ) (hL : 0 < L) (hz : 0 < z.im)
    (h0 : hat φ 0 = 0) :
    Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R:ℤ)) R, φ d * (z + (L * (d / L) : ℤ))⁻¹) atTop (𝓝 0) := by
  have hsum : ∑ y ∈ Finset.range L, φ y = 0 := by simpa [hat] using h0
  have hLz : (0:ℤ) < L := by exact_mod_cast hL
  obtain ⟨u, hu⟩ : ∃ u : ℤ → ℂ, ∀ d, u d = (z + ((L * (d / L) : ℤ) : ℂ))⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℤ → ℂ, ∀ d, Φ d = ∑ e ∈ Finset.range (d % L).toNat, φ e := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ℂ, ∀ d, F d = Φ d * u d := ⟨_, fun _ => rfl⟩
  have key : ∀ d : ℤ, φ d * u d = F (d+1) - F d := by
    intro d
    have hdiv := Int.mul_ediv_add_emod d L
    have h1 := Int.emod_nonneg d hLz.ne'
    have h2 := Int.emod_lt_of_pos d hLz
    have hcast : (((d % L).toNat : ℕ) : ZMod L) = (d : ZMod L) := by
      have : ((((d % L).toNat : ℕ) : ℤ) : ZMod L) = ((d % L : ℤ) : ZMod L) := by
        rw [Int.toNat_of_nonneg h1]
      rw [Int.cast_natCast] at this
      rw [this, ZMod.intCast_mod]
    rcases lt_or_eq_of_le (show d % L + 1 ≤ L by omega) with hlt | heq
    · have hq : (d+1) / L = d / L := by
        have h3 : d + 1 = (d % L + 1) + L * (d / L) := by omega
        rw [h3, Int.add_mul_ediv_left _ _ hLz.ne', Int.ediv_eq_zero_of_lt (by omega) hlt, zero_add]
      have hr : (d+1) % L = d % L + 1 := by
        have := Int.mul_ediv_add_emod (d+1) L
        rw [hq] at this; omega
      have hu' : u (d+1) = u d := by rw [hu, hu, hq]
      have hΦ' : Φ (d+1) = Φ d + φ d := by
        rw [hΦ, hΦ, hr, show (d % L + 1).toNat = (d % L).toNat + 1 by omega, Finset.sum_range_succ, hcast]
      rw [hF, hF, hu', hΦ']; ring
    · have hq : (d+1) / L = d / L + 1 := by
        rw [show d + 1 = L * (d / L + 1) by linarith, Int.mul_ediv_cancel_left _ hLz.ne']
      have hr : (d+1) % L = 0 := by
        have := Int.mul_ediv_add_emod (d+1) L
        rw [hq] at this; linarith
      have hΦ0 : Φ (d+1) = 0 := by rw [hΦ, hr]; simp
      have hn : (d % L).toNat = L - 1 := by omega
      have hs := Finset.sum_range_succ (fun e : ℕ => φ (e : ZMod L)) (L-1)
      rw [Nat.sub_add_cancel hL, ← hn, hcast, hsum] at hs
      have hΦd : Φ d = - φ d := by rw [hΦ]; linear_combination -hs
      rw [hF, hF, hΦ0, hΦd]; ring
  have hfun : (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R:ℤ)) R, φ d * (z + (L * (d / L) : ℤ))⁻¹)
      = fun R : ℕ => F ((R:ℤ)+1) - F (-(R:ℤ)) := by
    funext R
    rw [← sum_Icc_sub]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← key, hu]
  rw [hfun]
  set M : ℝ := ∑ y ∈ Finset.range L, ‖φ y‖
  have hM : ∀ d, ‖Φ d‖ ≤ M := by
    intro d
    rw [hΦ]
    have h2 := Int.emod_lt_of_pos d hLz
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega)) (fun _ _ _ => norm_nonneg _))
  have uLim : ∀ m : ℕ → ℤ, (∀ R : ℕ, (R:ℝ) - L ≤ |((m R : ℤ) : ℝ)|) →
      Tendsto (fun R : ℕ => (z + ((m R : ℤ) : ℂ))⁻¹) atTop (𝓝 0) := by
    intro m hm
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    apply Tendsto.inv_tendsto_atTop
    refine tendsto_atTop_mono (fun R => ?_)
      (tendsto_atTop_add_const_right _ (-(L:ℝ) - ‖z‖) tendsto_natCast_atTop_atTop)
    have h1 : ‖((m R : ℤ) : ℂ)‖ ≤ ‖z + ((m R : ℤ) : ℂ)‖ + ‖z‖ := by
      calc ‖((m R : ℤ) : ℂ)‖ = ‖(z + ((m R : ℤ) : ℂ)) - z‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [Complex.norm_intCast] at h1
    linarith [hm R]
  have hFb : ∀ x, ‖F x‖ ≤ M * ‖(z + ((L * (x / L) : ℤ) : ℂ))⁻¹‖ := by
    intro x
    rw [hF, norm_mul, ← hu]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  have hA : Tendsto (fun R : ℕ => F ((R:ℤ)+1)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun R => hFb _) ?_
    have hm : ∀ R : ℕ, (R:ℝ) - L ≤ |(((L * (((R:ℤ)+1) / L) : ℤ)) : ℝ)| := by
      intro R
      have e1 := Int.mul_ediv_add_emod ((R:ℤ)+1) L
      have e2 := Int.emod_lt_of_pos ((R:ℤ)+1) hLz
      have : (R:ℤ) - L ≤ L * (((R:ℤ)+1) / L) := by linarith
      have := (Int.cast_le (R := ℝ)).2 this
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
      exact this.trans (le_abs_self _)
    simpa only [norm_zero, mul_zero] using ((uLim _ hm).norm.const_mul M)
  have hB : Tendsto (fun R : ℕ => F (-(R:ℤ))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun R => hFb _) ?_
    have hm : ∀ R : ℕ, (R:ℝ) - L ≤ |(((L * ((-(R:ℤ)) / L) : ℤ)) : ℝ)| := by
      intro R
      have e1 := Int.mul_ediv_add_emod (-(R:ℤ)) L
      have e2 := Int.emod_nonneg (-(R:ℤ)) hLz.ne'
      have : (R:ℤ) - L ≤ -(L * ((-(R:ℤ)) / L)) := by linarith
      have := (Int.cast_le (R := ℝ)).2 this
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_neg] at this
      exact this.trans (neg_le_abs _)
    simpa only [norm_zero, mul_zero] using ((uLim _ hm).norm.const_mul M)
  simpa using hA.sub hB

end GlobalTheory.FloorTelescope
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
section
open GlobalTheory.NeedB Polynomial

noncomputable section

namespace GlobalTheory
namespace TsenLang

variable {k : Type} [Field k]

def genSub (n s : ℕ) (j : Fin n) : (MvPolynomial (Fin n × Fin (s + 1)) k)[X] :=
  ∑ t : Fin (s + 1), Polynomial.monomial (t : ℕ) (MvPolynomial.X (j, t))

def genEval (n s : ℕ) (g : MvPolynomial (Fin n) k[X]) : (MvPolynomial (Fin n × Fin (s + 1)) k)[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom MvPolynomial.C) (genSub n s) g

theorem map_genEval (n s : ℕ) (φ : MvPolynomial (Fin n × Fin (s + 1)) k →+* k)
    (hφ : ∀ a, φ (MvPolynomial.C a) = a) (g : MvPolynomial (Fin n) k[X]) :
    (genEval n s g).map φ = MvPolynomial.eval (fun j => (genSub n s j).map φ) g := by
  unfold genEval
  rw [← Polynomial.coe_mapRingHom, MvPolynomial.hom_eval₂, Polynomial.mapRingHom_comp]
  have h : φ.comp (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (s + 1)) k) = RingHom.id k :=
    RingHom.ext hφ
  rw [h, Polynomial.mapRingHom_id]
  rfl

theorem natDegree_genSub_le (n s : ℕ) (j : Fin n) : (genSub (k := k) n s j).natDegree ≤ s := by
  unfold genSub
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro t _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp t.2)

theorem natDegree_genEval_le (n s d m : ℕ) (g : MvPolynomial (Fin n) k[X])
    (hg : ∀ μ, g.coeff μ ≠ 0 → μ.degree = d ∧ (g.coeff μ).natDegree ≤ m) :
    (genEval n s g).natDegree ≤ d * s + m := by
  unfold genEval
  rw [MvPolynomial.eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro μ hμ
  obtain ⟨h1, h2⟩ := hg μ (MvPolynomial.mem_support_iff.mp hμ)
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hA : (Polynomial.mapRingHom (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (s + 1)) k)
      (g.coeff μ)).natDegree ≤ m := (Polynomial.natDegree_map_le).trans h2
  have hB : (∏ j, genSub (k := k) n s j ^ μ j).natDegree ≤ d * s := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ j, (genSub (k := k) n s j ^ μ j).natDegree ≤ ∑ j, μ j * s :=
          Finset.sum_le_sum fun j _ =>
            (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (natDegree_genSub_le n s j))
      _ = (∑ j, μ j) * s := by rw [Finset.sum_mul]
      _ = d * s := by rw [← h1, Finsupp.degree_eq_sum]
  omega

theorem genSub_map_constantCoeff (n s : ℕ) (j : Fin n) :
    (genSub (k := k) n s j).map MvPolynomial.constantCoeff = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [genSub, Polynomial.map_sum]

theorem coeff_genSub_map_eval (n s : ℕ) (c : Fin n × Fin (s + 1) → k) (j : Fin n) (t : Fin (s + 1)) :
    ((genSub (k := k) n s j).map (MvPolynomial.eval c)).coeff t = c (j, t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [genSub, Polynomial.map_sum, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Fin.val_inj]

theorem constantCoeff_coeff_genEval (n s d : ℕ) (hd : 0 < d) (g : MvPolynomial (Fin n) k[X])
    (hg : ∀ μ, g.coeff μ ≠ 0 → μ.degree = d) (e : ℕ) :
    MvPolynomial.constantCoeff ((genEval n s g).coeff e) = 0 := by
  have h := map_genEval (k := k) n s MvPolynomial.constantCoeff (fun a => by simp) g
  have h2 : (fun j => (genSub (k := k) n s j).map MvPolynomial.constantCoeff) = 0 := by
    funext j; exact genSub_map_constantCoeff n s j
  rw [h2, MvPolynomial.eval_zero] at h
  have h3 : MvPolynomial.constantCoeff g = 0 := by
    by_contra hne
    have := hg 0 (by rwa [← MvPolynomial.constantCoeff_eq])
    simp at this; omega
  rw [h3] at h
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p e) h
  simpa [Polynomial.coeff_map] using this

theorem exists_ne_zero_polynomial_common_zero [IsAlgClosed k] (n r d m : ℕ)
    (g : Fin r → MvPolynomial (Fin n) k[X])
    (hg : ∀ i μ, (g i).coeff μ ≠ 0 → μ.degree = d ∧ ((g i).coeff μ).natDegree ≤ m)
    (hd : 0 < d) (hn : r * d < n) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (g i) = 0 := by
  classical
  set s := r * (m + 1) with hs
  set E := d * s + m + 1 with hE
  let F : Fin r × Fin E → MvPolynomial (Fin n × Fin (s + 1)) k :=
    fun p => (genEval n s (g p.1)).coeff p.2
  let e1 : Fin (r * E) ≃ Fin r × Fin E := finProdFinEquiv.symm
  let e2 : Fin (n * (s + 1)) ≃ Fin n × Fin (s + 1) := finProdFinEquiv.symm
  let F' : Fin (r * E) → MvPolynomial (Fin (n * (s + 1))) k :=
    fun q => MvPolynomial.rename e2.symm (F (e1 q))
  have hF' : ∀ q, MvPolynomial.constantCoeff (F' q) = 0 := by
    intro q
    simp only [F', MvPolynomial.constantCoeff_rename, F]
    exact constantCoeff_coeff_genEval n s d hd _ (fun μ h => (hg _ μ h).1) _
  have hlt : r * E < n * (s + 1) := by
    have h1 : r * d + 1 ≤ n := hn
    have h2 : (r * d + 1) * (s + 1) ≤ n * (s + 1) := Nat.mul_le_mul_right _ h1
    have h3 : r * E < (r * d + 1) * (s + 1) := by
      rw [hE, hs]; ring_nf; nlinarith
    omega
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_common_zero_of_constantCoeff_eq_zero k _ _ F' hF' hlt
  set c' : Fin n × Fin (s + 1) → k := c ∘ e2.symm with hc'
  refine ⟨fun j => (genSub n s j).map (MvPolynomial.eval c'), ?_, ?_⟩
  · intro h0
    obtain ⟨q, hq⟩ : ∃ q, c q ≠ 0 := by
      by_contra hh; push_neg at hh; exact hc0 (funext hh)
    have := congrArg (fun x : Fin n → k[X] => (x (e2 q).1).coeff (e2 q).2) h0
    simp only [coeff_genSub_map_eval, Pi.zero_apply, Polynomial.coeff_zero] at this
    apply hq
    simpa [hc'] using this
  · intro i
    rw [← map_genEval n s (MvPolynomial.eval c') (fun a => by simp)]
    ext e
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases he : e < E
    · have := hc (e1.symm (i, ⟨e, he⟩))
      simpa [F', F, MvPolynomial.eval_rename, hc'] using this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, map_zero]
      have := natDegree_genEval_le n s d m (g i) (hg i)
      omega

end TsenLang


open TsenLang in
theorem tsenLang_ratFunc :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) (RatFunc k)),
      (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
        ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r d f hf hd hn
  classical
  let S : Finset (RatFunc k) := Finset.univ.biUnion fun i => (f i).support.image fun μ => (f i).coeff μ
  obtain ⟨⟨b, hb⟩, hbS⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors k[X]) S
  let numer : RatFunc k → k[X] := fun a =>
    if h : IsLocalization.IsInteger k[X] (b • a) then (RingHom.mem_rangeS.mp h).choose else 0
  have hnumer : ∀ a ∈ S, algebraMap k[X] (RatFunc k) (numer a) = b • a := by
    intro a ha
    have h := hbS a ha
    simp only [numer, dif_pos h]
    exact (RingHom.mem_rangeS.mp h).choose_spec
  let g : Fin r → MvPolynomial (Fin n) k[X] := fun i =>
    ∑ μ ∈ (f i).support, MvPolynomial.monomial μ (numer ((f i).coeff μ))
  have hgc : ∀ i μ, (g i).coeff μ = if μ ∈ (f i).support then numer ((f i).coeff μ) else 0 := by
    intro i μ
    simp only [g, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hgmap : ∀ i, MvPolynomial.map (algebraMap k[X] (RatFunc k)) (g i) =
      MvPolynomial.C (algebraMap k[X] (RatFunc k) b) * f i := by
    intro i
    ext μ
    rw [MvPolynomial.coeff_map, hgc, MvPolynomial.coeff_C_mul]
    split_ifs with hμ
    · rw [hnumer _ (by simp only [S, Finset.mem_biUnion, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, μ, hμ, rfl⟩),
        Algebra.smul_def]
    · rw [MvPolynomial.notMem_support_iff.mp hμ]; simp
  let m : ℕ := Finset.univ.sup fun i => (g i).support.sup fun μ => ((g i).coeff μ).natDegree
  have hg : ∀ i μ, (g i).coeff μ ≠ 0 → μ.degree = d ∧ ((g i).coeff μ).natDegree ≤ m := by
    intro i μ hμ
    refine ⟨?_, ?_⟩
    · have hmem : μ ∈ (f i).support := by
        by_contra h; rw [hgc, if_neg h] at hμ; exact hμ rfl
      have := hf i (MvPolynomial.mem_support_iff.mp hmem)
      rwa [Finsupp.degree_eq_weight_one]
    · exact le_trans (Finset.le_sup (f := fun μ => ((g i).coeff μ).natDegree)
          (MvPolynomial.mem_support_iff.mpr hμ))
        (Finset.le_sup (f := fun i => (g i).support.sup fun μ => ((g i).coeff μ).natDegree)
          (Finset.mem_univ i))
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_polynomial_common_zero n r d m g hg hd hn
  have hinj : Function.Injective (algebraMap k[X] (RatFunc k)) := IsFractionRing.injective k[X] (RatFunc k)
  have hb0 : algebraMap k[X] (RatFunc k) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨fun j => algebraMap k[X] (RatFunc k) (y j), ?_, ?_⟩
  · intro h
    apply hy0
    funext j
    have := congrFun h j
    exact hinj (by simpa using this)
  · intro i
    have h1 : algebraMap k[X] (RatFunc k) (MvPolynomial.eval y (g i)) =
        MvPolynomial.eval (fun j => algebraMap k[X] (RatFunc k) (y j))
          (MvPolynomial.map (algebraMap k[X] (RatFunc k)) (g i)) := by
      rw [MvPolynomial.eval_map]
      first
        | (simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂]; rfl)
        | exact MvPolynomial.eval₂_comp_left _ _ _ _
        | simp [MvPolynomial.eval₂_comp_left]
    rw [hy i, map_zero, hgmap, map_mul, MvPolynomial.eval_C] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hb0

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIterated
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

def ptXY (p : ℝ × ℝ) : ℍ := ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)

theorem measurable_ofComplex_hp : Measurable (ofComplex : ℂ → ℍ) := by
  classical
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have h : (UpperHalfPlane.coe ∘ (ofComplex : ℂ → ℍ)) =
      fun w : ℂ => if 0 < w.im then w else ((ofComplex 0 : ℍ) : ℂ) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [hw, ofComplex_apply_of_im_pos hw]
    · simp only [Function.comp, hw, if_false]
      rw [ofComplex_apply_of_im_nonpos (not_lt.mp hw),
        ofComplex_apply_of_im_nonpos (le_refl _ : (0 : ℂ).im ≤ 0)]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id
    measurable_const

theorem ptXY_eq (p : ℝ × ℝ) : ptXY p = ofComplex (Complex.measurableEquivRealProd.symm p) := by
  unfold ptXY
  congr 1
  apply Complex.ext <;> simp

theorem measurable_ptXY : Measurable ptXY := by
  simp only [funext ptXY_eq]
  exact measurable_ofComplex_hp.comp Complex.measurableEquivRealProd.symm.measurable

theorem volume_eq_map_ptXY : (volume : Measure ℍ) = Measure.map ptXY
    (((volume : Measure ℝ).prod (volume.restrict (Set.Ioi 0))).withDensity
      fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  have hm := measurable_ptXY
  ext s hs
  have hp : (volume : Measure ℝ).prod (volume.restrict (Set.Ioi (0 : ℝ))) =
      (volume : Measure (ℝ × ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hset : ptXY ⁻¹' s ∩ Set.univ ×ˢ Set.Ioi 0 =
      Complex.measurableEquivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' s) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ioi, Set.mem_image, ptXY_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by simpa using h2
      refine ⟨_, h1, ?_⟩
      rw [ofComplex_apply_of_im_pos h3]
    · rintro ⟨z, hz, hzp⟩
      refine ⟨?_, ?_⟩
      · rw [← hzp, ofComplex_apply]; exact hz
      · have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by
          rw [← hzp]; exact z.im_pos
        simpa using h3
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), hp, Measure.restrict_restrict (hm hs), hset,
    volume_eq_lintegral,
    ← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp

theorem measurableSet_strip : MeasurableSet strip := by
  have h : strip = (fun z : ℍ => z.re) ⁻¹' (Set.Ico 0 1) := rfl
  rw [h]
  exact UpperHalfPlane.continuous_re.measurable measurableSet_Ico

theorem ptXY_re (x y : ℝ) (hy : 0 < y) : (ptXY (x, y)).re = x := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ptXY, ofComplex_apply_of_im_pos h]
  simp [UpperHalfPlane.re]

theorem restrict_strip_eq_map : (volume : Measure ℍ).restrict strip = Measure.map ptXY
    ((((volume : Measure ℝ).restrict (Set.Ico 0 1)).prod (volume.restrict (Set.Ioi 0))).withDensity
      fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  have hm := measurable_ptXY
  have hS := hm measurableSet_strip
  have h1 : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have h2 : ptXY ⁻¹' strip ∩ Set.univ ×ˢ Set.Ioi 0 = Set.Ico 0 1 ×ˢ Set.Ioi 0 := by
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ioi, Set.mem_Ico, strip, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [ptXY_re x y hy] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [ptXY_re x y hy]
      exact ⟨h, hy⟩
  rw [volume_eq_map_ptXY, Measure.restrict_map hm measurableSet_strip, restrict_withDensity hS, h1,
    Measure.restrict_restrict hS, h2, Measure.prod_restrict]

theorem strip_iterated :
    (∀ F : ℍ → ENNReal, Measurable F → ∫⁻ τ in strip, F τ = ∫⁻ y in Set.Ioi (0 : ℝ),
      (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) * ENNReal.ofReal (1 / y ^ 2)) ∧
    ∀ F : ℍ → ℂ, IntegrableOn F strip → ∫ τ in strip, F τ = ∫ y in Set.Ioi (0 : ℝ),
      (∫ x in (0 : ℝ)..1, F (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
  have hm := measurable_ptXY
  have hd : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) := by fun_prop
  refine ⟨fun F hF => ?_, fun H hH => ?_⟩
  · rw [restrict_strip_eq_map, lintegral_map hF hm, lintegral_withDensity_eq_lintegral_mul _ hd (g := fun a => F (ptXY a)) (hF.comp hm)]
    simp only [Pi.mul_apply]
    rw [lintegral_prod_symm (fun a => ENNReal.ofReal (1 / a.2 ^ 2) * F (ptXY a))
      ((hd.mul (hF.comp hm)).aemeasurable)]
    refine lintegral_congr fun y => ?_
    rw [lintegral_const_mul (ENNReal.ofReal (1 / y ^ 2)) (f := fun x : ℝ => F (ptXY (x, y)))
      (hF.comp (hm.comp (measurable_id.prodMk measurable_const))), mul_comm]
    rfl
  · unfold IntegrableOn at hH
    rw [restrict_strip_eq_map] at hH ⊢
    have hI := (integrable_map_measure hH.1 hm.aemeasurable).1 hH
    rw [integral_map hm.aemeasurable hH.1,
      integral_withDensity_eq_integral_toReal_smul hd (by simp)]
    rw [integrable_withDensity_iff_integrable_smul' hd (by simp)] at hI
    have key : ∀ y : ℝ, ∫ x in Set.Ico (0 : ℝ) 1, (ENNReal.ofReal (1 / y ^ 2)).toReal • (H ∘ ptXY) (x, y) =
        (∫ x in (0 : ℝ)..1, H (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
      intro y
      rw [integral_smul, ENNReal.toReal_ofReal (by positivity), intervalIntegral.integral_of_le zero_le_one,
        integral_Ico_eq_integral_Ioc, Complex.real_smul]
      simp only [Function.comp_apply, ptXY]
      push_cast
      ring
    refine (integral_prod_symm _ hI).trans ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => key y)

end GlobalTheory.EisM

end
end

