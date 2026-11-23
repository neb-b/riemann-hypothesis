module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.GaussDefinite

theorem add_pow_split {R : Type} [CommRing R] (x p : R) (j m : ℕ) :
    ∃ u v : R, (x + p) ^ j = x ^ m * u + p ^ (j - m) * v := by
  induction j generalizing m with
  | zero => exact ⟨0, 1, by simp⟩
  | succ j ih =>
    rcases m with _ | m
    · exact ⟨(x + p) ^ (j + 1), 0, by simp⟩
    obtain ⟨u, v, h⟩ := ih m
    obtain ⟨u', v', h'⟩ := ih (m + 1)
    obtain ⟨d, hd⟩ : ∃ d, j - (m + 1) + 1 = j - m + d := ⟨j - (m + 1) + 1 - (j - m), by omega⟩
    refine ⟨u + p * u', x * v + p ^ d * v', ?_⟩
    rw [show j + 1 - (m + 1) = j - m by omega]
    have e : p * p ^ (j - (m + 1)) = p ^ (j - m) * p ^ d := by rw [← pow_add, ← hd, pow_succ']
    calc (x + p) ^ (j + 1) = x * (x + p) ^ j + p * (x + p) ^ j := by ring
      _ = x * (x ^ m * u + p ^ (j - m) * v) + p * (x ^ (m + 1) * u' + p ^ (j - (m + 1)) * v') := by
        rw [← h, ← h']
      _ = _ := by linear_combination v' * e

variable (l : ℕ) [hl : Fact l.Prime]

theorem exists_flat : ∃ x : Per.Fl l, x.untilt = (l : Per.OC l) := by
  have hr : ∀ a : Per.OC l, ∃ b : Per.OC l, b ^ l = a := by
    intro a
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl.out.pos
    have h1 : ‖b‖ ^ l ≤ 1 := by rw [← norm_pow, hb]; exact (GlobalTheory.RingBasics.mem_OC _).1 a.2
    exact ⟨⟨b, (GlobalTheory.RingBasics.mem_OC _).2 ((pow_le_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h1)⟩,
      Subtype.ext hb⟩
  choose r hr using hr
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l) (fun n => r^[n] (l : Per.OC l)) (fun n => by
    rw [Function.iterate_succ_apply', hr])
  exact ⟨e, he 0⟩

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem norm_root (x : Per.Fl l) (i : ℕ) :
    ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) =
      ‖(((((frobeniusEquiv (Per.Fl l) l).symm ^ i) x).untilt : Per.OC l) : ℂ_[l])‖ := by
  have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x i
  have e : ((frobeniusEquiv (Per.Fl l) l).symm ^ i) x = ((frobeniusEquiv (Per.Fl l) l).symm)^[i] x := by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Function.iterate_succ_apply', ← ih (PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x i)]; rfl
  rw [← h, e]
  push_cast
  rw [norm_pow, one_div, ← Nat.cast_pow, Real.pow_rpow_inv_natCast (norm_nonneg _)
    (pow_ne_zero _ hl.out.ne_zero)]

theorem split_of_small (a : Per.Ainf l) (M m : ℕ)
    (h : ∀ i : ℕ, ‖(((a.coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) * ((l : ℝ)⁻¹) ^ i ≤
      ((l : ℝ)⁻¹) ^ M) :
    ∃ c : Per.Ainf l, a - (l : Per.Ainf l) ^ (M - m) * c ∈ RingHom.ker (Per.θ l) ^ m := by
  obtain ⟨w, hw⟩ := exists_flat l
  have hk : Per.tm w - (l : Per.Ainf l) ∈ RingHom.ker (Per.θ l) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller, hw, sub_self]
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hl.out.pos)
  have key : ∀ i ∈ Finset.Iic M, ∃ c : Per.Ainf l,
      Per.tm (((frobeniusEquiv (Per.Fl l) l).symm ^ i) (a.coeff i)) * (l : Per.Ainf l) ^ i -
        (l : Per.Ainf l) ^ (M - m) * c ∈ RingHom.ker (Per.θ l) ^ m := by
    intro i hi
    rw [Finset.mem_Iic] at hi
    have h1 := h i
    rw [norm_root] at h1
    set y := ((frobeniusEquiv (Per.Fl l) l).symm ^ i) (a.coeff i)
    have h2 : ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (M - i) := by
      rw [norm_l]
      refine le_of_mul_le_mul_right ?_ (pow_pos hl0 i)
      rwa [← pow_add, Nat.sub_add_cancel hi]
    rw [← GlobalTheory.RingBasics.mem_span_pow_OC, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hw,
      ← map_pow] at h2
    obtain ⟨z, hz⟩ := GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd h2
    obtain ⟨u, v, huv⟩ := add_pow_split (Per.tm w - (l : Per.Ainf l)) (l : Per.Ainf l) (M - i) m
    obtain ⟨d, hd⟩ : ∃ d, M - i - m + i = M - m + d := ⟨M - i - m + i - (M - m), by omega⟩
    have e : (l : Per.Ainf l) ^ (M - i - m) * (l : Per.Ainf l) ^ i =
        (l : Per.Ainf l) ^ (M - m) * (l : Per.Ainf l) ^ d := by rw [← pow_add, hd, pow_add]
    refine ⟨(l : Per.Ainf l) ^ d * v * Per.tm z, ?_⟩
    have e2 : Per.tm y * (l : Per.Ainf l) ^ i - (l : Per.Ainf l) ^ (M - m) * ((l : Per.Ainf l) ^ d * v * Per.tm z)
        = (Per.tm w - (l : Per.Ainf l)) ^ m * (u * Per.tm z * (l : Per.Ainf l) ^ i) := by
      rw [sub_add_cancel] at huv
      rw [hz, Per.tm, map_mul, map_pow]
      change Per.tm w ^ (M - i) * Per.tm z * _ - _ = _
      rw [huv]
      linear_combination (v * Per.tm z) * e
    rw [e2]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk m)
  choose! c hc using key
  obtain ⟨t, ht⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) a M
  obtain ⟨d, hd⟩ : ∃ d, M + 1 = M - m + d := ⟨M + 1 - (M - m), by omega⟩
  refine ⟨∑ i ∈ Finset.Iic M, c i + (l : Per.Ainf l) ^ d * t, ?_⟩
  have := Ideal.sum_mem _ hc
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
  rw [hd, pow_add] at ht
  convert this using 1
  linear_combination ht

theorem map_mem_kerP (a : Per.Ainf l) (m : ℕ) (h : a ∈ RingHom.ker (Per.θ l) ^ m) :
    algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ m := by
  have h1 : RingHom.ker (Per.θ l) ≤ (Per.kerP l).comap (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
    intro x hx
    exact Ideal.mem_comap.2 (GlobalTheory.RingIface.alg_mem_kerP l (RingHom.mem_ker.1 hx))
  exact Ideal.le_comap_pow _ m (Ideal.pow_right_mono h1 m h)

theorem term_le_one (a : Per.Ainf l) (i : ℕ) :
    ‖(((a.coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) * ((l : ℝ)⁻¹) ^ i ≤ 1 := by
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_le
  rw [norm_root]
  exact mul_le_one₀ ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.property _)) (by positivity)
    (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1))

theorem gauss_pow_le (k : ℕ) :
    ⨆ i : ℕ, ‖(((((l : Per.Ainf l) ^ k).coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) *
      ((l : ℝ)⁻¹) ^ i ≤ ((l : ℝ)⁻¹) ^ k := by
  refine ciSup_le fun i => ?_
  rw [norm_root]
  by_cases h : i = k
  · subst h
    exact mul_le_of_le_one_left (by positivity) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.property _))
  · have h0 : (0 : Per.Fl l).untilt = 0 := by
      rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]
    rw [WittVector.coeff_p_pow_eq_zero _ _ h, map_zero, h0]
    simp

theorem envelope_split (N : Per.Acris l → ℝ) (h0 : ∀ x, 0 ≤ N x) (hm : ∀ x y, N (x * y) = N x * N y)
    (hA : ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n)
    (s : Per.Acris0 l) (k m : ℕ) (hs : N (algebraMap (Per.Acris0 l) (Per.Acris l) s) ≤ ((l : ℝ)⁻¹) ^ (k + m)) :
    ∃ c : Per.Ainf l, (s : Per.AinfP l) - algebraMap (Per.Ainf l) (Per.AinfP l) ((l : Per.Ainf l) ^ k * c) ∈
      Per.kerP l ^ m := by
  obtain ⟨K, a, ha⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
  have e0 : s * algebraMap (Per.Ainf l) (Per.Acris0 l) ((l : Per.Ainf l) ^ K) =
      algebraMap (Per.Ainf l) (Per.Acris0 l) a := Subtype.ext (by rw [← map_pow] at ha; exact ha)
  have hc : ∀ x, algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) =
      algebraMap (Per.Ainf l) (Per.Acris l) x := fun x => (GlobalTheory.RingIface.tower l x).symm
  have e1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e0
  rw [map_mul, hc, hc] at e1
  have hN : N (algebraMap (Per.Ainf l) (Per.Acris l) a) ≤ ((l : ℝ)⁻¹) ^ (k + m + K) := by
    rw [← e1, hm, pow_add]
    refine mul_le_mul hs ?_ (h0 _) (by positivity)
    rw [hA]
    exact gauss_pow_le l K
  rw [hA] at hN
  obtain ⟨c, hc⟩ := split_of_small l a (k + m + K) m fun i =>
    (le_ciSup (f := fun n : ℕ => ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) *
      ((l : ℝ)⁻¹) ^ n) ⟨1, by rintro _ ⟨i, rfl⟩; exact term_le_one l a i⟩ i).trans hN
  refine ⟨c, ?_⟩
  have h2 := map_mem_kerP l _ m hc
  rw [show k + m + K - m = k + K by omega, map_sub, ← ha, map_natCast] at h2
  rw [← Ideal.unit_mul_mem_iff_mem _ ((GlobalTheory.RingBasics.isUnit_l l).pow K)]
  convert h2 using 1
  simp only [map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.MemLoc.GaussDefinite

namespace GlobalTheory.MemLoc

theorem gauss_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, b ≠ 0 → N (l : ℝ)⁻¹ b ≠ 0 := by
  intro l hl N hN b hb hb0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  obtain ⟨h01, hadd, hneg, hm, hA⟩ := hN _ le_rfl (inv_lt_one_of_one_lt₀ hl1)
  obtain ⟨j, hj⟩ := exists_isCrisP l
  refine hb (crisP_injective l j hj ?_)
  rw [map_zero]
  refine GlobalTheory.RingIface.ev_ext l _ _ fun m => ?_
  rw [map_zero]
  obtain ⟨N₀, hN₀⟩ := hj.bdd m
  obtain ⟨a, ha⟩ := hN₀ b
  have hu : IsUnit (Per.ev l m (((l : ℕ) : Per.BdRp l) ^ N₀)) := by
    have := ((GlobalTheory.RingBasics.isUnit_l l).pow N₀).map (Ideal.Quotient.mk (Per.kerP l ^ m))
    rw [map_pow, map_natCast] at this ⊢
    exact this
  rw [← hu.mul_right_eq_zero, ← map_mul, ha, Ideal.Quotient.eq_zero_iff_mem]
  refine image_kerP_pow_separated l m a fun k => ?_
  obtain ⟨s, z, hs⟩ := (acris_basic l).2.2.1 b (k + m)
  have hz : N (l : ℝ)⁻¹ (-((l : Per.Acris l) ^ (k + m) * z)) ≤ ((l : ℝ)⁻¹) ^ (k + m) := by
    rw [hneg, hm, ← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)), ← map_pow, hA]
    exact (mul_le_mul (GaussDefinite.gauss_pow_le l _) (h01 z).2 (h01 z).1 (by positivity)).trans
      (mul_one _).le
  have hs' : N (l : ℝ)⁻¹ (algebraMap (Per.Acris0 l) (Per.Acris l) s) ≤ ((l : ℝ)⁻¹) ^ (k + m) := by
    have e : algebraMap (Per.Acris0 l) (Per.Acris l) s = b + -((l : Per.Acris l) ^ (k + m) * z) := by
      rw [hs]; ring
    rw [e]
    refine (hadd _ _).trans (max_le ?_ hz)
    rw [hb0]
    positivity
  obtain ⟨c, hc⟩ := GaussDefinite.envelope_split l (N (l : ℝ)⁻¹) (fun x => (h01 x).1) hm hA s k m hs'
  obtain ⟨a', ha'⟩ := hN₀ z
  have hev : Per.ev l m (algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) =
      Ideal.Quotient.mk _ (s : Per.AinfP l) := GlobalTheory.RingIface.ev_alg l m _
  refine ⟨(l : Per.Ainf l) ^ N₀ * c + (l : Per.Ainf l) ^ m * a', ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hc ⊢
  rw [hs] at ha
  simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, hj.on0, hev] at ha ha' hc ⊢
  linear_combination -ha + (l : Per.AinfP l ⧸ Per.kerP l ^ m) ^ (k + m) * ha' +
    (l : Per.AinfP l ⧸ Per.kerP l ^ m) ^ N₀ * hc

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfFrobeniusUnitEigenvectorGaloisLine
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.UnitLine

theorem exists_fixed {R : Type} [CommRing R] (φ σ : R →+* R) (h : ∀ a, φ (σ a) = σ (φ a)) (w c : R)
    (hw : IsUnit w) (hc : IsUnit c) (hσ : σ c = c) (hφ : φ w = c * w) :
    ∃ a, φ a = a ∧ σ w = a * w := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  have e : σ w = σ w * v * w := by linear_combination (-σ w) * hv
  refine ⟨σ w * v, ?_, e⟩
  have h1 := congrArg φ e
  rw [map_mul φ _ w, h, hφ, map_mul σ, hσ] at h1
  apply (hc.mul hw).mul_right_cancel
  rw [← h1]
  linear_combination (-c * σ w) * hv

theorem sigma_unit_eigen : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  intro l _ w u hw hφ g
  obtain ⟨-, -, -, -, -, h6, -, h8, -⟩ := ActLaws.act_laws l
  obtain ⟨a, ha, e⟩ := exists_fixed (Per.φA l) (Per.σA g) (ActLaws.φA_σA g) w (Per.zA l u) hw
    (u.isUnit.map _) (h8 g u) hφ
  obtain ⟨z, hz⟩ := phi_fixed_eq_padicInt l (algebraMap (Per.Ainf l) (Per.Acris l) a)
    ((PhiFix.phiA_alg l a).trans (congrArg _ ha))
  have hb : Per.aB l a = Per.zB l z := by
    rw [GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, hz]
  exact ⟨z, by rw [h6, e, map_mul, hb]⟩

end GlobalTheory.UnitLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfInvPiModXiPowBoundedDenominator
section
section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.CompanionTheory.InertiaEigenvalues.LPow


end GlobalTheory.CompanionTheory.InertiaEigenvalues.LPow

end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

private theorem xi_eq_sum_choose_mul_pi_pow_lemma_2 {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l}
    (AI : _root_.Formalism.BasicNotions.LocAinf l P) :
    AI.ξ = ∑ i ∈ Finset.range l, ((l.choose (i + 1) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ i := by
  have h := congrArg (Polynomial.eval AI.π₁)
    (Polynomial.geom_sum_X_comp_X_add_one_eq_sum (R := _root_.Formalism.BasicNotions.Loc.Ainf l) l)
  simp only [Polynomial.eval_comp, Polynomial.eval_finsetSum, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_natCast] at h
  rw [← h]
  unfold _root_.Formalism.BasicNotions.LocAinf.ξ _root_.Formalism.BasicNotions.LocAinf.π₁
  simp

private theorem xi_eq_pi_pow_add_prime_mul_lemma {l : ℕ} [hl : Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l}
    (AI : _root_.Formalism.BasicNotions.LocAinf l P) :
    ∃ w, AI.ξ = AI.π₁ ^ (l - 1) + (l : _root_.Formalism.BasicNotions.Loc.Ainf l) * (1 + AI.π₁ * w) := by
  have hp := hl.out
  obtain ⟨m, hm⟩ : ∃ m, l = m + 2 := ⟨l - 2, by have := hp.two_le; omega⟩
  refine ⟨∑ i ∈ Finset.range m, ((l.choose (i + 2) / l : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ i, ?_⟩
  rw [xi_eq_sum_choose_mul_pi_pow_lemma_2, show Finset.range l = Finset.range (m + 1 + 1) by rw [hm],
    Finset.sum_range_succ, Finset.sum_range_succ',
    show l.choose (m + 1 + 1) = 1 by rw [show m + 1 + 1 = l by omega]; simp]
  have hd : ∀ i ∈ Finset.range m, ((l.choose (i + 1 + 1) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ (i + 1) =
      (l : _root_.Formalism.BasicNotions.Loc.Ainf l) * (AI.π₁ * (((l.choose (i + 2) / l : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ i)) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hdvd : l ∣ l.choose (i + 2) := hp.dvd_choose_self (by omega) (by omega)
    rw [show ((l.choose (i + 1 + 1) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) =
        ((l * (l.choose (i + 2) / l) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) by rw [Nat.mul_div_cancel' hdvd]]
    push_cast
    ring
  rw [Finset.sum_congr rfl hd, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [zero_add, Nat.choose_one_right, pow_zero, mul_one, Nat.cast_one, one_mul]
  rw [show m + 1 = l - 1 by omega]
  ring

theorem _root_.GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l)
    (AI : _root_.Formalism.BasicNotions.LocAinf l P) (k n M : ℕ), 1 ≤ M → k ≤ (l - 1) * n →
    ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) ^ (n + M - 1) ∈ Ideal.span {AI.π₁ ^ k, AI.ξ ^ M} := by
  intro l _ P AI k n M hM hk
  obtain ⟨w, hw⟩ := xi_eq_pi_pow_add_prime_mul_lemma AI
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  set q := Ideal.Quotient.mk (Ideal.span {AI.π₁ ^ k, AI.ξ ^ M})
  have hπ : q AI.π₁ ^ k = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hξ : q AI.ξ ^ M = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hu : IsUnit (q (1 + AI.π₁ * w)) := by
    rw [map_add (f := _), map_one, map_mul]
    exact IsNilpotent.isUnit_one_add ⟨k, by rw [mul_pow, hπ, zero_mul]⟩
  have hneg : (-(q AI.π₁ ^ (l - 1))) ^ n = 0 := by
    rw [neg_pow, ← pow_mul, pow_eq_zero_of_le hk hπ, mul_zero]
  have hsum := (Commute.all (q AI.ξ) (-(q AI.π₁ ^ (l - 1)))).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
    hξ hneg (k := n + M - 1) (by omega)
  rw [← sub_eq_add_neg, congrArg q hw, map_add (f := _), map_pow, add_sub_cancel_left, map_mul,
    mul_pow] at hsum
  rw [map_pow, map_natCast]
  exact ((hu.pow _).mul_left_eq_zero).1 hsum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem algHom_ext_of_constantCoeff_zero {O : Type} [CommRing O]
    (f g : PowerSeries O →ₐ[O] PowerSeries O) (h : f PowerSeries.X = g PowerSeries.X)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) : f = g := by
  have key : ∀ (n : ℕ) (a : PowerSeries O), PowerSeries.X ^ n ∣ f a - g a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      obtain ⟨b, hb⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
        rw [PowerSeries.X_dvd_iff]; simp
      have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
        rw [← hb, PowerSeries.algebraMap_eq]; ring
      have : f a - g a = f PowerSeries.X * (f b - g b) := by
        conv_lhs => rw [ha]
        rw [map_add (f := _), map_add (f := _), map_mul, map_mul, f.commutes, g.commutes, ← h]; ring
      rw [this, pow_succ']
      exact mul_dvd_mul (PowerSeries.X_dvd_iff.2 h0) (ih b)
  ext a n
  have := (PowerSeries.X_pow_dvd_iff.1 (key (n + 1) a)) n (Nat.lt_succ_self n)
  rw [map_sub] at this
  exact sub_eq_zero.1 this

theorem constantCoeff_algHom {O : Type} [CommRing O]
    (f : PowerSeries O →ₐ[O] PowerSeries O)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) (a : PowerSeries O) :
    PowerSeries.constantCoeff (f a) = PowerSeries.constantCoeff a := by
  obtain ⟨b, hb⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]; simp
  have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
    rw [← hb, PowerSeries.algebraMap_eq]; ring
  conv_lhs => rw [ha]
  rw [map_add (f := _), map_mul, f.commutes, map_add (f := _), map_mul, h0, PowerSeries.algebraMap_eq]
  simp

theorem eq_of_commute_pow {O : Type} [CommRing O] [IsDomain O] (l : ℕ) (hl0 : (l : O) ≠ 0)
    (hlu : ¬ IsUnit (l : O)) (φ f g : PowerSeries O →ₐ[O] PowerSeries O)
    (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1)
    (hf : φ (f PowerSeries.X) = f (φ PowerSeries.X))
    (hg : φ (g PowerSeries.X) = g (φ PowerSeries.X))
    (hf0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0)
    (hg0 : PowerSeries.constantCoeff (g PowerSeries.X) = 0)
    (h1 : PowerSeries.coeff 1 (f PowerSeries.X) = PowerSeries.coeff 1 (g PowerSeries.X)) :
    f PowerSeries.X = g PowerSeries.X := by
  set F := f PowerSeries.X with hF
  set G := g PowerSeries.X with hG
  have hφ0 : PowerSeries.constantCoeff (φ PowerSeries.X) = 0 := by rw [hφ]; simp
  have hp : φ PowerSeries.X = PowerSeries.X *
      ∑ i ∈ Finset.range l, (1 + PowerSeries.X : PowerSeries O) ^ i := by
    rw [hφ, ← geom_sum_mul]; ring
  have hd : φ (F - G) = (F - G) * ∑ i ∈ Finset.range l, (1 + F) ^ i * (1 + G) ^ (l - 1 - i) := by
    rw [map_sub, hf, hg, hφ]
    have := (Commute.all (1 + F) (1 + G)).mul_geom_sum₂ l
    simp only [map_sub, map_pow, map_add (f := _), map_one, ← hF, ← hG]
    rw [show (1 + F) - (1 + G) = F - G by ring] at this
    rw [this]; ring
  have key : ∀ n : ℕ, PowerSeries.X ^ (n + 2) ∣ F - G := by
    intro n
    induction n with
    | zero =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [hf0, hg0]
      · rw [map_sub, h1, sub_self]
    | succ n ih =>
      obtain ⟨e, he⟩ := ih
      rw [he, map_mul, map_pow, hp, mul_pow, mul_assoc, mul_assoc] at hd
      have hc := congrArg PowerSeries.constantCoeff
        (mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) hd)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_pow, map_sum, map_add (f := _), map_one, PowerSeries.constantCoeff_X, hf0, hg0,
        add_zero, one_pow, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        constantCoeff_algHom φ hφ0] at hc
      have he0 : PowerSeries.constantCoeff e = 0 := by
        by_contra hne
        have h2 : (l : O) * ((l : O) ^ (n + 1) - 1) * PowerSeries.constantCoeff e = 0 := by
          linear_combination hc
        rcases mul_eq_zero.1 h2 with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · exact hl0 h4
          · exact hlu (IsUnit.of_pow_eq_one (sub_eq_zero.1 h4) (Nat.succ_ne_zero n))
        · exact hne h3
      rw [he, show n + 1 + 2 = n + 2 + 1 from rfl, pow_succ]
      exact mul_dvd_mul_left _ (PowerSeries.X_dvd_iff.2 he0)
  ext n
  have := (PowerSeries.X_pow_dvd_iff.1 (key n)) n (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.1 this

theorem act_unique : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (f : PowerSeries O →ₐ[O] PowerSeries O) (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (c : ℤ_[l]), φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 → (∀ a, φ₀ (f a) = f (φ₀ a)) → PowerSeries.constantCoeff (f PowerSeries.X) = 0 → PowerSeries.coeff 1 (f PowerSeries.X) = algebraMap ℤ_[l] O c → φ₀ = phi l O ∧ f = act l O c := by
  intro l _ O _ _ _ _ _ hl0 hlu f φ₀ c hφ hcomm hf0 hf1
  obtain ⟨hX, hmul, -, hnat, hlin, -⟩ := _root_.GlobalTheory.Cyc.act_laws l O
  have hφe : φ₀ = phi l O := by
    refine algHom_ext_of_constantCoeff_zero _ _ ?_ (by rw [hφ]; simp)
    rw [hφ, phi, hX, hnat]
  refine ⟨hφe, algHom_ext_of_constantCoeff_zero _ _ ?_ hf0⟩
  refine eq_of_commute_pow l hl0 hlu φ₀ f (act l O c) hφ (hcomm _) ?_ hf0 ?_ ?_
  · rw [hφe, phi, hmul, hmul, mul_comm]
  · rw [hX, cyc_const]
  · rw [hX, hlin, hf1]

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticeQuotPrimePowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lattice_quot_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ), Nat.card (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
  first | exact @GlobalTheory.LatticeCard.card_lattice_quot_pow | exact GlobalTheory.LatticeCard.card_lattice_quot_pow | (intros; apply GlobalTheory.LatticeCard.card_lattice_quot_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupOneCocyclesAnticommUpToCoboundaryStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_one_cocycles_anticomm_up_to_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, (CobL (P.PD K) (cupL A'.ρ m a b) ↔ CobL (P.PD K) (cupL A.ρ m.flip b a)) ∧ (a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ → CobL (P.PD K) (cupL A'.ρ m a b)) := by
  first | exact @GlobalTheory.cupL_anticomm_cobL | exact GlobalTheory.cupL_anticomm_cobL | (intros; apply GlobalTheory.cupL_anticomm_cobL <;> assumption)
end

