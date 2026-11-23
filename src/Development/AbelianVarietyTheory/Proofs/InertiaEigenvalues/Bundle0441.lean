module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0061
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonSubOneDvdAinfCoeffZeroOfThetaVanishing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKGal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.EpsCoeff

variable {l : ℕ} [hl : Fact l.Prime]

abbrev rt (ε : OCb l) (n : ℕ) : OCb l := ((frobeniusEquiv (OCb l) l).symm)^[n] ε

theorem rt_pow (ε : OCb l) (n k : ℕ) : rt ε (n + k) ^ (l ^ k) = rt ε n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', pow_mul]
    congr 1
    rw [rt, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

theorem frob_iter_teich (x : OCb l) (m : ℕ) :
    (⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[m] (WittVector.teichmuller l x) =
      WittVector.teichmuller l (x ^ (l ^ m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]

def xin (ε : OCb l) (n : ℕ) : Ainf l :=
  ∑ i ∈ Finset.range l, (WittVector.teichmuller l (rt ε (n + 1))) ^ i

theorem frob_iter_xin (ε : OCb l) (n k : ℕ) :
    (⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n + k] (xin ε n) =
      ∑ i ∈ Finset.range l, (WittVector.teichmuller l (rt ε 1 ^ (l ^ k))) ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [xin, ← RingHom.coe_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, RingHom.coe_pow, frob_iter_teich, pow_add, pow_mul, add_comm n 1, rt_pow]

theorem xi_eq (ε : OCb l) (n : ℕ) :
    GlobalTheory.MemLoc.xi ε = (⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n] (xin ε n) := by
  have h := frob_iter_xin ε n 0
  rw [Nat.add_zero] at h
  rw [h]
  simp [GlobalTheory.MemLoc.xi, rt]

theorem natCast_ne_zero : ((l : ℕ) : Per.OC l) ≠ 0 := by
  intro h
  apply GlobalTheory.RingBasics.p_ne_zero (p := l)
  have := congrArg Subtype.val h
  simpa using this

theorem theta_frob_xin (ε : OCb l) (hε : ε.untilt = 1) (n j : ℕ) :
    Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n + (j + 1)] (xin ε n)) = l := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [frob_iter_xin, map_sum]
  have h1 : (rt ε 1 ^ (l ^ (j + 1))).untilt = 1 := by
    rw [pow_succ', pow_mul]
    have : rt ε 1 ^ l = ε := by
      have h := rt_pow ε 0 1
      rw [zero_add, pow_one] at h
      exact h
    rw [this, map_pow, hε, one_pow]
  rw [Finset.sum_congr rfl (fun i _ => by rw [map_pow, WittVector.fontaineTheta_teichmuller, h1, one_pow])]
  simp

theorem xin_dvd (ε : OCb l) (hε : GlobalTheory.MemLoc.IsEps ε) (n : ℕ) (b : Ainf l)
    (hb : Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n] b) = 0) : xin ε n ∣ b := by
  obtain ⟨y, hy⟩ := (GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd l ε hε _).1 hb
  have hbij := (WittVector.frobenius_bijective l (OCb l)).iterate n
  obtain ⟨y', rfl⟩ := hbij.2 y
  refine ⟨y', hbij.1 ?_⟩
  rw [hy, ← RingHom.coe_pow, map_mul, RingHom.coe_pow, xi_eq ε n]

theorem coeff_xin (ε : OCb l) (n : ℕ) :
    (xin ε n).coeff 0 * (rt ε (n + 1) - 1) = rt ε n - 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← WittVector.constantCoeff_apply, xin, map_sum]
  simp only [map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  rw [geom_sum_mul]
  have := rt_pow ε n 1
  rw [pow_one] at this
  rw [this]

theorem step (ε : OCb l) (hε : GlobalTheory.MemLoc.IsEps ε) (a : Ainf l)
    (ha : ∀ n : ℕ, Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n] a) = 0) (n : ℕ) :
    ∃ b c : Ainf l, a = c * b ∧
      (∀ m, n ≤ m → Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[m] c) ≠ 0) ∧
      c.coeff 0 * (rt ε n - 1) = ε - 1 := by
  induction n with
  | zero =>
    refine ⟨a, 1, (one_mul a).symm, fun m _ => ?_, ?_⟩
    · rw [← RingHom.coe_pow, map_one, map_one]; exact one_ne_zero
    · simp [rt]
  | succ n ih =>
    obtain ⟨b, c, rfl, hc, h0⟩ := ih
    have hb : ∀ m, n ≤ m → Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[m] b) = 0 :=
      fun m hm => by
        have := ha m
        rw [← RingHom.coe_pow, map_mul, map_mul, RingHom.coe_pow] at this
        exact (mul_eq_zero.1 this).resolve_left (hc m hm)
    obtain ⟨b', rfl⟩ := xin_dvd ε hε n b (hb n le_rfl)
    refine ⟨b', c * xin ε n, by ring, fun m hm => ?_, ?_⟩
    · rw [← RingHom.coe_pow, map_mul, map_mul, RingHom.coe_pow]
      refine mul_ne_zero (hc m (by omega)) ?_
      obtain ⟨j, rfl⟩ : ∃ j, m = n + (j + 1) := ⟨m - n - 1, by omega⟩
      rw [theta_frob_xin ε hε.1]
      exact natCast_ne_zero
    · rw [WittVector.mul_coeff_zero, mul_assoc, coeff_xin, h0]

theorem memLoc_isEps {ε : OCb l} (h : IsEps ε) : GlobalTheory.MemLoc.IsEps ε := by
  obtain ⟨h1, δ, hδ, hne⟩ := h
  have : (frobeniusEquiv (OCb l) l).symm ε = δ :=
    (RingEquiv.symm_apply_eq _).2 (by rw [frobeniusEquiv_def, hδ])
  exact ⟨h1, by rw [this]; exact hne⟩

theorem norm_untilt_mul (x y : OCb l) :
    ‖(((x * y).untilt : OC l) : ℂ_[l])‖ =
      ‖((x.untilt : OC l) : ℂ_[l])‖ * ‖((y.untilt : OC l) : ℂ_[l])‖ := by
  rw [map_mul, MulMemClass.coe_mul, norm_mul]

theorem norm_untilt_le_one (x : OCb l) : ‖((x.untilt : OC l) : ℂ_[l])‖ ≤ 1 :=
  (GlobalTheory.RingBasics.mem_OC _).1 x.untilt.2

theorem norm_rt_pow (x : OCb l) (n : ℕ) :
    ‖(((rt x n).untilt : OC l) : ℂ_[l])‖ ^ (l ^ n) = ‖((x.untilt : OC l) : ℂ_[l])‖ := by
  have h := rt_pow x 0 n
  rw [zero_add] at h
  rw [← norm_pow, ← SubmonoidClass.coe_pow, ← map_pow, h]
  rfl

theorem norm_le_of_dvd (a b : OCb l) (hb : b ≠ 0) (h : ∀ n, b ∣ a * rt b n) :
    ‖((a.untilt : OC l) : ℂ_[l])‖ ≤ ‖((b.untilt : OC l) : ℂ_[l])‖ := by
  set A := ‖((a.untilt : OC l) : ℂ_[l])‖ with hAdef
  set B := ‖((b.untilt : OC l) : ℂ_[l])‖ with hBdef
  have hB : 0 < B := by
    refine norm_pos_iff.2 fun h0 => GlobalTheory.FrobInt.sharpRoot_ne_zero b hb 0 ?_
    exact_mod_cast h0
  by_contra hlt
  push_neg at hlt
  have hA : 0 < A := hB.trans hlt
  have key : ∀ n : ℕ, A ^ (l ^ n) * B ≤ B ^ (l ^ n) := by
    intro n
    obtain ⟨c, hc⟩ := h n
    have h1 := congrArg (fun x : OCb l => ‖((x.untilt : OC l) : ℂ_[l])‖ ^ (l ^ n)) hc
    simp only [norm_untilt_mul, mul_pow, norm_rt_pow] at h1
    have hc1 : ‖((c.untilt : OC l) : ℂ_[l])‖ ^ (l ^ n) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_untilt_le_one c)
    calc A ^ (l ^ n) * B = B ^ (l ^ n) * ‖((c.untilt : OC l) : ℂ_[l])‖ ^ (l ^ n) := h1
      _ ≤ B ^ (l ^ n) := mul_le_of_le_one_right (by positivity) hc1
  have hr : B / A < 1 := (div_lt_one hA).2 hlt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hB hr
  have h2 : (B / A) ^ (l ^ n) ≤ (B / A) ^ n :=
    pow_le_pow_of_le_one (by positivity) hr.le (Nat.lt_pow_self hl.out.one_lt).le
  have h3 : B ≤ (B / A) ^ (l ^ n) := by
    rw [div_pow, le_div_iff₀ (by positivity), mul_comm]
    exact key n
  linarith

theorem dvd_of_norm_le (x y : OC l) (hx : x ≠ 0) (h : ‖(y : ℂ_[l])‖ ≤ ‖(x : ℂ_[l])‖) : x ∣ y := by
  have hx' : (x : ℂ_[l]) ≠ 0 := fun h0 => hx (by exact_mod_cast h0)
  refine ⟨⟨(y : ℂ_[l]) / x, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, div_le_one (norm_pos_iff.2 hx')]
    exact h
  · show (y : ℂ_[l]) = (x : ℂ_[l]) * ((y : ℂ_[l]) / x)
    field_simp

theorem dvd_of_forall_dvd_mul_rt (a b : OCb l) (hb : b ≠ 0) (h : ∀ n, b ∣ a * rt b n) : b ∣ a := by
  refine GlobalTheory.FrobInt.dvd_of_sharpRoot_dvd b a (GlobalTheory.FrobInt.sharpRoot_ne_zero b hb) fun k => ?_
  refine dvd_of_norm_le _ _ (GlobalTheory.FrobInt.sharpRoot_ne_zero b hb k) ?_
  have hbk : rt b k ≠ 0 := by
    intro h0
    apply hb
    apply (frobeniusEquiv (OCb l) l).symm.injective.iterate k
    rw [iterate_map_zero]
    exact h0
  refine norm_le_of_dvd (rt a k) (rt b k) hbk fun n => ?_
  obtain ⟨c, hc⟩ := h n
  refine ⟨rt c k, ?_⟩
  have := congrArg (((frobeniusEquiv (OCb l) l).symm)^[k]) hc
  rw [iterate_map_mul, iterate_map_mul] at this
  have hcomm : rt (rt b k) n = rt (rt b n) k := by
    simp only [rt, ← Function.iterate_add_apply, add_comm]
  rw [hcomm]
  exact this

end GlobalTheory.EpsCoeff

namespace GlobalTheory


open GlobalTheory.EpsCoeff in
theorem eps_sub_one_dvd_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (ε : OCb l), IsEps ε → ∀ a : Ainf l,
    (∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0) → (ε - 1) ∣ a.coeff 0 := by
  intro l _ ε hε a ha
  have hε' := memLoc_isEps hε
  have hne : ε - 1 ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    apply hε'.2
    rw [h0, map_one, map_one]
  refine dvd_of_forall_dvd_mul_rt _ _ hne fun n => ?_
  obtain ⟨b, c, rfl, -, h0⟩ := step ε hε' a ha n
  refine ⟨b.coeff 0, ?_⟩
  have hr : rt (ε - 1) n = rt ε n - 1 := by simp only [rt, iterate_map_sub, iterate_map_one]
  rw [hr, WittVector.mul_coeff_zero, ← h0]
  ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallySubMemPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisGal

open Filter Topology

variable {l : ℕ} [hl : Fact l.Prime]

private theorem sigO_coe_pt (g : Per.Gq l) (y : Per.OC l) :
    ((Per.σO g y : Per.OC l) : ℂ_[l]) = Per.σC g (y : ℂ_[l]) := by
  apply GlobalTheory.RingIface.sigO_coe

private theorem tower_pt (x : Per.Ainf l) : algebraMap (Per.Acris0 l) (Per.Acris l)
    (algebraMap (Per.Ainf l) (Per.Acris0 l) x) = ainfToAcris l x := by
  change _ = algebraMap (Per.Ainf l) (Per.Acris l) x
  symm
  apply GlobalTheory.RingIface.tower

theorem eventually_norm_σC_sub_lt (y : ℂ_[l]) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ g : GQ l in 𝓝 1, ‖Per.σC g y - y‖ < ε := by
  have hd : DenseRange (fun x : Om l => (x : ℂ_[l])) := UniformSpace.Completion.denseRange_coe
  obtain ⟨x, hx⟩ := hd.exists_dist_lt y (half_pos hε)
  rw [dist_eq_norm] at hx
  filter_upwards [GlobalTheory.Cyc.eventually_apply_eq x 1] with g hg
  have e : Per.σC g y - y = Per.σC g (y - x) - (y - x) := by
    rw [map_sub, GlobalTheory.RingBasics.σC_coe, hg, AlgEquiv.one_apply]; ring
  rw [e]
  calc ‖Per.σC g (y - x) - (y - x)‖ ≤ ‖Per.σC g (y - x)‖ + ‖y - x‖ := norm_sub_le _ _
    _ < ε := by rw [GlobalTheory.RingBasics.norm_σC]; linarith

theorem exists_eq_l_mul (z : Per.OC l) (hz : ‖(z : ℂ_[l])‖ ≤ ‖((l : ℕ) : ℂ_[l])‖) :
    ∃ c : Per.OC l, z = (l : Per.OC l) * c := by
  have h0 : ((l : ℕ) : ℂ_[l]) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  refine ⟨⟨(z : ℂ_[l]) / l, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div]; exact div_le_one_of_le₀ hz (norm_nonneg _)
  · change (z : ℂ_[l]) = ((l : Per.OC l) : ℂ_[l]) * ((z : ℂ_[l]) / l)
    have : ((l : Per.OC l) : ℂ_[l]) = l := by simp
    rw [this]; field_simp

variable {ξ : Per.Ainf l}

theorem eventually_sub_mem_one (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, Per.σA g y - y ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} := by
  have hl0 : (0 : ℝ) < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  filter_upwards [eventually_norm_σC_sub_lt ((Per.θ l y : Per.OC l) : ℂ_[l]) hl0] with g hg
  have h1 : Per.θ l (Per.σA g y - y) = Per.σO g (Per.θ l y) - Per.θ l y := by rw [map_sub, GlobalTheory.RingBasics.θ_σA]
  obtain ⟨c, hc⟩ := exists_eq_l_mul (Per.σO g (Per.θ l y) - Per.θ l y)
    (by rw [AddSubgroupClass.coe_sub, sigO_coe_pt]; exact hg.le)
  obtain ⟨c', rfl⟩ := GlobalTheory.MemLoc.ThetaD.θ_surj l c
  have hk : Per.σA g y - y - (l : Per.Ainf l) * c' ∈ RingHom.ker (Per.θ l) := by
    rw [RingHom.mem_ker, map_sub, h1, hc, map_mul, map_natCast, sub_self]
  rw [hξ, Ideal.mem_span_singleton'] at hk
  obtain ⟨d, hd⟩ := hk
  rw [Ideal.mem_span_pair]
  exact ⟨c', d, by linear_combination hd⟩

theorem eventually_sub_mem_pow (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (N : ℕ) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, Per.σA g y - y ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} ^ (N + 1) := by
  set I : Ideal (Per.Ainf l) := Ideal.span {((l : ℕ) : Per.Ainf l), ξ} with hI
  have hlI : ((l : ℕ) : Per.Ainf l) ∈ I := Ideal.subset_span (by simp)
  have ht : ∀ z : Per.Fl l, ∀ᶠ g : GQ l in 𝓝 1,
      Per.σA g (WittVector.teichmuller l z) - WittVector.teichmuller l z ∈ I ^ (N + 1) := by
    intro z
    obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv (Per.Fl l) l N).surjective z
    filter_upwards [eventually_sub_mem_one hξ (WittVector.teichmuller l w)] with g hg
    have := SModEq.sub_mem.1 ((SModEq.sub_mem.2 hg).pow_pow_add_one hlI N)
    rw [iterateFrobeniusEquiv_def, map_pow, map_pow]
    exact this
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff y N
  have hall := (Filter.eventually_all_finset (Finset.Iic N)).2
    (fun i _ => ht ((((_root_.frobeniusEquiv (Per.Fl l) l).symm ^ i) (y.coeff i))))
  filter_upwards [hall] with g hg
  rw [sub_eq_iff_eq_add] at hc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, map_add (f := _), map_mul, map_pow, map_natCast, map_sum, add_sub_add_comm, ← mul_sub,
    ← Finset.sum_sub_distrib]
  refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlI _)) (sum_mem fun i hi => ?_)
  rw [map_mul, map_pow, map_natCast, ← sub_mul]
  exact Ideal.mul_mem_right _ _ (hg i hi)

theorem dvd_of_mem (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (N : ℕ) {z : Per.Ainf l}
    (hz : z ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} ^ (N + l * N)) :
    (l : Per.Acris l) ^ N ∣ ainfToAcris l z := by
  have hθ : Per.θ l ξ = 0 := by rw [← RingHom.mem_ker, hξ]; exact Ideal.mem_span_singleton_self ξ
  have hxl : (l : Per.Acris l) ∣ ainfToAcris l ξ ^ l := by
    rw [← factorial_mul_dpow ξ hθ l]
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hl.out.pos le_rfl
    rw [hk]; push_cast
    exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
  rw [Ideal.span_insert] at hz
  have h1 := Ideal.sup_pow_add_le_pow_sup_pow hz
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Submodule.mem_sup] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, pow_mul]
  exact dvd_add (Dvd.intro_left _ rfl) (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hxl N) _)

theorem eventually_dvd_ainf (N : ℕ) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g (ainfToAcris l y) - ainfToAcris l y := by
  obtain ⟨ξ, hξ, -, -⟩ := GlobalTheory.Prism.exists_generator l
  filter_upwards [eventually_sub_mem_pow hξ (N + l * N) y] with g hg
  have h := dvd_of_mem hξ N (Ideal.pow_le_pow_right (Nat.le_succ _) hg)
  have e : galC g (ainfToAcris l y) = ainfToAcris l (Per.σA g y) := (GlobalTheory.CrisMaps.sigA_extends g).alg y
  rwa [e, ← map_sub]

theorem eventually_dvd_dpow {x : Per.Ainf l} (hx : Per.θ l x = 0) (k N : ℕ) :
    ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g (dpow x hx k) - dpow x hx k := by
  choose c hc using GlobalTheory.RingBasics.exists_pow_div_factorial l
  have hc' : ∀ n : ℕ, (n.factorial : Per.Acris l) * algebraMap ℤ_[l] _ (c n) = (l : Per.Acris l) ^ n :=
    fun n => by
      simpa only [map_mul, map_natCast, map_pow] using congrArg (algebraMap ℤ_[l] (Per.Acris l)) (hc n)
  filter_upwards [eventually_dvd_ainf (N + 1) x] with g ⟨D, hD⟩
  set X := ainfToAcris l x with hX
  set Y := ∑ m ∈ Finset.range (k + 1), dpow x hx m * (algebraMap ℤ_[l] (Per.Acris l) (c (k - m)) *
    (l : Per.Acris l) ^ (N * (k - m)) * D ^ (k - m)) with hYdef
  have hY : (k.factorial : Per.Acris l) * Y = (X + (l : Per.Acris l) ^ (N + 1) * D) ^ k := by
    rw [hYdef, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    rw [← Nat.choose_mul_factorial_mul_factorial hmk, ← factorial_mul_dpow x hx m, mul_pow, ← pow_mul,
      show (N + 1) * (k - m) = (k - m) + N * (k - m) by ring, pow_add, ← hc' (k - m)]
    push_cast
    ring
  have hσ : galC g (dpow x hx k) = Y := by
    have h1 := congrArg (galC g) (factorial_mul_dpow x hx k)
    rw [map_mul, map_natCast, map_pow, ← hX, show galC g X = X + (l : Per.Acris l) ^ (N + 1) * D by
      rw [← hD]; ring] at h1
    exact sub_eq_zero.1 (acris_nat_cancel k.factorial_ne_zero (by rw [mul_sub, h1, hY, sub_self]))
  have hc0 : algebraMap ℤ_[l] (Per.Acris l) (c 0) = 1 := by simpa using hc' 0
  rw [hσ, hYdef, Finset.sum_range_succ, Nat.sub_self, hc0, pow_zero, mul_zero, pow_zero, mul_one, mul_one,
    mul_one, add_sub_cancel_right]
  refine Finset.dvd_sum fun m hm => Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left
    (pow_dvd_pow _ (Nat.le_mul_of_pos_right N (by have := Finset.mem_range.1 hm; omega))) _) _) _


variable (l) in
def fixNear : Subring (Per.Acris l) where
  carrier := {x | ∀ N : ℕ, ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g x - x}
  mul_mem' {a b} ha hb N := by
    filter_upwards [ha N, hb N] with g ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨galC g a * v + u * b, ?_⟩
    rw [map_mul]
    linear_combination galC g a * hv + b * hu
  one_mem' N := .of_forall fun g => ⟨0, by simp⟩
  add_mem' {a b} ha hb N := by
    filter_upwards [ha N, hb N] with g ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u + v, by rw [map_add (f := _)]; linear_combination hu + hv⟩
  zero_mem' N := .of_forall fun g => ⟨0, by simp⟩
  neg_mem' {a} ha N := by
    filter_upwards [ha N] with g ⟨u, hu⟩
    exact ⟨-u, by rw [map_neg]; linear_combination -hu⟩

theorem algebraMap_mem_fixNear (s : Per.Acris0 l) :
    algebraMap (Per.Acris0 l) (Per.Acris l) s ∈ fixNear l := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.exists_isEps_for_inj l
  have hx : Per.θ l (GlobalTheory.MemLoc.xi e) = 0 := (_root_.GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd l e he _).2 dvd_rfl
  obtain ⟨s, hs⟩ := s
  have key : ∀ y ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n},
      ∀ hy : y ∈ Per.Acris0 l, algebraMap (Per.Acris0 l) (Per.Acris l) ⟨y, hy⟩ ∈ fixNear l := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro hy0
      obtain ⟨n, hn⟩ := hy
      have h1 : (n.factorial : Per.Acris0 l) * ⟨y, hy0⟩ =
          algebraMap (Per.Ainf l) (Per.Acris0 l) (GlobalTheory.MemLoc.xi e) ^ n := Subtype.ext (by simpa using hn)
      have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1
      rw [map_mul, map_natCast, map_pow, tower_pt] at h2
      rw [eq_dpow hx h2]
      exact fun N => eventually_dvd_dpow hx n N
    | zero =>
      intro h0
      have e0 : (⟨0, h0⟩ : Per.Acris0 l) = 0 := Subtype.ext rfl
      rw [e0, map_zero]; exact zero_mem _
    | add y z hy hz ihy ihz =>
      intro h0
      have hy0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy
      have hz0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he z).2 hz
      have e0 : (⟨y + z, h0⟩ : Per.Acris0 l) = ⟨y, hy0⟩ + ⟨z, hz0⟩ := Subtype.ext rfl
      set_option synthInstance.maxHeartbeats 200000 in
        rw [e0, map_add (f := _)]; exact add_mem (ihy hy0) (ihz hz0)
    | smul r y hy ihy =>
      intro h0
      have hy0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy
      have e0 : (⟨r • y, h0⟩ : Per.Acris0 l) = algebraMap (Per.Ainf l) (Per.Acris0 l) r * ⟨y, hy0⟩ :=
        Subtype.ext (Algebra.smul_def r y)
      rw [e0, map_mul, tower_pt]
      exact mul_mem (fun N => eventually_dvd_ainf N r) (ihy hy0)
  exact key s ((GlobalTheory.MemLoc.mem_Acris0_iff_span l e he s).1 hs) hs

theorem galC_sub_dvd_mem_nhds : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Acris l) (n : ℕ),
    {g : GQ l | (l : Per.Acris l) ^ n ∣ galC g x - x} ∈ nhds (1 : GQ l) := by
  intro l _ x n
  obtain ⟨s, z, rfl⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x n
  filter_upwards [algebraMap_mem_fixNear s n] with g ⟨u, hu⟩
  refine ⟨u + (galC g z - z), ?_⟩
  rw [map_add (f := _), map_mul, map_pow, map_natCast]
  linear_combination hu

end GlobalTheory.AcrisGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldContainsUnramifiedWittTameDescen
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoeff

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l,
    (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  intro l _ a e _ h1 h2 LL
  refine ⟨?_, fun hU => ?_⟩
  · have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have : FiniteDimensional ℚ_[l] ↥(Kunr l a) := (unrExt l a).2
    exact ⟨⟨LL.1 ⊔ Kunr l a, inferInstance⟩, le_sup_left, ⟨le_sup_right⟩⟩
  · obtain ⟨_, ω, hω, -, -⟩ := exists_gen l a
    have hlt := one_lt_pow_l l a
    have hmem : ω ∈ LL.1 := HasUnr.le (a := a) (IntermediateField.subset_adjoin _ _ (show ω ^ l ^ a = ω by
      rw [← Nat.sub_add_cancel hlt.le, pow_succ, hω.pow_eq_one, one_mul]))
    have he : e = l ^ a - 1 := by omega
    exact
      { succ_eq := h1
        not_dvd := h2
        finite := LL.2
        prim := ⟨⟨ω, hmem⟩, he ▸ (IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val)
          Subtype.val_injective).1 hω⟩ }

end GlobalTheory.TameCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrClassOfCocycleValuesStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herr_class_of_cocycle_values : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ := by
  first | exact @GlobalTheory.NL.HerrClassUniq.class_of_values | exact GlobalTheory.NL.HerrClassUniq.class_of_values | (intros; apply GlobalTheory.NL.HerrClassUniq.class_of_values <;> assumption)
end

