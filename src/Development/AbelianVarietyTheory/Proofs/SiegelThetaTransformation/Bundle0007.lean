module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.HaarAlg

variable {K : Type} [Field K] {κ ι : Type}

theorem intM_add {x y : Matrix κ ι K} (hx : IntM x) (hy : IntM y) : IntM (x + y) :=
  fun k i => (hx k i).add (hy k i)

theorem intM_natCast_smul (n : ℕ) {x : Matrix κ ι K} (hx : IntM x) : IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul, ← nsmul_eq_mul]
  exact (hx k i).nsmul n

theorem hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (S : ℕ) :
    HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (intM_natCast_smul S hy)

theorem exists_common_level {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ∃ R : ℕ, 0 < R ∧ HasLevel R φ ∧ HasLevel R ψ := by
  obtain ⟨R, hR, h1⟩ := hφ
  obtain ⟨S, hS, h2⟩ := hψ
  exact ⟨R * S, Nat.mul_pos hR hS, hasLevel_mul h1 S, mul_comm S R ▸ hasLevel_mul h2 R⟩

theorem hasLevel_map₂ {R : ℕ} {φ ψ : Matrix κ ι K → ℂ} (h1 : HasLevel R φ) (h2 : HasLevel R ψ)
    (f : ℂ → ℂ → ℂ) (hf : f 0 0 = 0) : HasLevel R fun x => f (φ x) (ψ x) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_cases a : φ x = 0
    · by_cases b : ψ x = 0
      · exact (hx (by simp only [a, b, hf])).elim
      · exact h2.1 x b
    · exact h1.1 x a
  · simp only [h1.2 x y hy, h2.2 x y hy]

theorem apply_add_of_mem_perSub {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ)
    {p : Matrix κ ι K} (hp : p ∈ perSub K κ ι R) : ∀ x, φ (x + p) = φ x := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact fun x => h.2 x y hy
  | zero => simp
  | add p q _ _ hp hq => intro x; rw [← add_assoc, hq, hp]
  | neg p _ hp => intro x; rw [← hp (x + -p)]; simp

theorem apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    φ (Quotient.out (QuotientAddGroup.mk x : Matrix κ ι K ⧸ perSub K κ ι R)) = φ x := by
  obtain ⟨p, hp⟩ := QuotientAddGroup.mk_out_eq_mul (perSub K κ ι R) x
  rw [hp]
  exact apply_add_of_mem_perSub h p.2 x

theorem exists_natCast_smul_intM [NumberField K] [Fintype κ] [Fintype ι] (b : Matrix κ ι K) :
    ∃ N : ℕ, 0 < N ∧ IntM ((N : K) • b) := by
  classical
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : κ × ι => b p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, fun k i => ?_⟩
  have h := hy (b k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e, Int.cast_natCast] at h; exact h
  · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at h
    simpa using h.neg

theorem hasLevel_translate {R N : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) {b : Matrix κ ι K}
    (hb : IntM ((N : K) • b)) : HasLevel (R * N) fun x => φ (x - b) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have e : ((R * N : ℕ) : K) • x = (N : K) • ((R : K) • (x - b)) + (R : K) • ((N : K) • b) := by
      rw [Nat.cast_mul]; module
    rw [e]
    exact intM_add (intM_natCast_smul N (h.1 _ hx)) (intM_natCast_smul R hb)
  · show φ _ = φ _
    rw [add_sub_right_comm]
    exact (hasLevel_mul h N).2 _ y hy

theorem finsum_translate {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (b : Matrix κ ι K) :
    ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ (q.out - b) =
      ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ q.out := by
  rw [← finsum_comp_equiv (Equiv.subRight (QuotientAddGroup.mk b :
    Matrix κ ι K ⧸ perSub K κ ι R)) (f := fun q => φ q.out)]
  refine finsum_congr fun q => ?_
  rw [← apply_out_mk h (q.out - b), QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq']
  rfl

end GlobalTheory.SW.HaarAlg


open GlobalTheory.SW.HaarAlg in
theorem GlobalTheory.SW.isSB_algebra_haar_linear : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by
  intro K κ ι _ _ _ _ φ ψ hφ hψ
  obtain ⟨R, hR, h1, h2⟩ := exists_common_level hφ hψ
  have hadd : HasLevel R (φ + ψ) := hasLevel_map₂ h1 h2 (fun a b => a + b) (by simp)
  have hsmul : ∀ c : ℂ, HasLevel R (c • φ) := fun c =>
    hasLevel_map₂ h1 h2 (fun a _ => c * a) (by simp)
  have hmul : HasLevel R (φ * ψ) := hasLevel_map₂ h1 h2 (fun a b => a * b) (by simp)
  have hconj : HasLevel R (fun x => conj (φ x)) :=
    hasLevel_map₂ h1 h2 (fun a _ => conj a) (by simp)
  obtain ⟨e1, f1⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R φ hR h1
  obtain ⟨e2, f2⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R ψ hR h2
  refine ⟨⟨R, hR, hadd⟩, fun c => ⟨R, hR, hsmul c⟩, ⟨R, hR, hmul⟩, ⟨R, hR, hconj⟩, ?_,
    fun c => ?_, ?_, fun b => ?_⟩
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hadd).1, e1, e2]
    unfold haarAt
    rw [← mul_add, ← finsum_add_distrib f1 f2]
    rfl
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR (hsmul c)).1, e1]
    unfold haarAt
    rw [mul_left_comm c]
    congr 1
    exact ((AddMonoidHom.mulLeft c).map_finsum f1).symm
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hconj).1, e1]
    unfold haarAt
    rw [map_mul, map_inv₀, map_pow, map_natCast]
    congr 1
    exact ((starRingEnd ℂ).toAddMonoidHom.map_finsum f1).symm
  · obtain ⟨N, hN, hb⟩ := exists_natCast_smul_intM b
    have hRN := Nat.mul_pos hR hN
    have ht := hasLevel_translate h1 hb
    refine ⟨⟨_, hRN, ht⟩, ?_⟩
    rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN ht).1, (GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN (hasLevel_mul h1 N)).1]
    unfold haarAt
    rw [finsum_translate (hasLevel_mul h1 N) b]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBounds
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.IpPos

open NumberField

variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub {R : ℕ} {x : Matrix κ ι K}
    (hx : x ∈ _root_.GlobalTheory.SW.perSub K κ ι R) :
    ∃ y : Matrix κ ι K, _root_.GlobalTheory.SW.IntM y ∧ x = (R : K) • y := by
  obtain ⟨y, rfl⟩ := (_root_.GlobalTheory.SW.HaarLevel.mem_perSub R x).mp hx
  exact ⟨_root_.GlobalTheory.SW.HaarLevel.incl K κ ι y,
    (_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mpr ⟨y, rfl⟩,
    (Nat.cast_smul_eq_nsmul K R _).symm⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ}
    (h : _root_.GlobalTheory.SW.HasLevel R φ) (x : Matrix κ ι K) :
    φ (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x).out = φ x := by
  have hmem := QuotientAddGroup.eq.mp
    (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x)).symm
  rw [← _root_.GlobalTheory.SW.HaarLevel.periodic h x _ hmem, add_neg_cancel_left]

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.intM_natCast_smul (n : ℕ) {x : Matrix κ ι K}
    (hx : _root_.GlobalTheory.SW.IntM x) : _root_.GlobalTheory.SW.IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_natCast n).mul (hx k i)

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : _root_.GlobalTheory.SW.HasLevel R φ)
    (S : ℕ) : _root_.GlobalTheory.SW.HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact _root_.GlobalTheory.SW.IpPos.intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (_root_.GlobalTheory.SW.IpPos.intM_natCast_smul S hy)

def classes (K κ ι : Type) [Field K] (R : ℕ) : Set (Matrix κ ι K ⧸ perSub K κ ι R) :=
  {q | IntM ((R : K) • q.out)}

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.classes_finite_card {R : ℕ} (hR : 0 < R) :
    (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).Finite ∧
      (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤
      (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
  set L := _root_.GlobalTheory.SW.perSub K κ ι 1
  set H := (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).addSubgroupOf L
  have hRK : (R : K) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have hidx : H.index = (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
    show (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).relIndex L = _
    rw [_root_.GlobalTheory.SW.HaarLevel.relIndex_perSub 1 (R * R) one_pos, mul_pow, ← sq]
  let g : L →+ Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R :=
    (QuotientAddGroup.mk' _).comp
      ((DistribSMul.toAddMonoidHom (Matrix κ ι K) ((R : K)⁻¹)).comp L.subtype)
  have hker : H ≤ g.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker]
    obtain ⟨y, hy, hzy⟩ :=
      _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub (AddSubgroup.mem_addSubgroupOf.mp hz)
    simp only [g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribSMul.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, hzy, smul_smul]
    rw [show ((R : K))⁻¹ * ((1 * (R * R) : ℕ) : K) = R by push_cast; field_simp]
    exact AddSubgroup.subset_closure ⟨y, hy, rfl⟩
  let F := QuotientAddGroup.lift H g hker
  have hsub : _root_.GlobalTheory.SW.IpPos.classes K κ ι R ⊆ Set.range F := by
    intro q hq
    have hL : (R : K) • q.out ∈ L :=
      AddSubgroup.subset_closure ⟨_, hq, by rw [Nat.cast_one, one_smul]⟩
    refine ⟨QuotientAddGroup.mk ⟨_, hL⟩, ?_⟩
    simp only [F, QuotientAddGroup.lift_mk, g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribSMul.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply, smul_smul,
      inv_mul_cancel₀ hRK, one_smul]
    exact QuotientAddGroup.out_eq' q
  have hfin : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero (by
    rw [← AddSubgroup.index, hidx]; positivity)
  refine ⟨(Set.finite_range F).subset hsub, ?_⟩
  calc (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range F)
    _ = Nat.card (Set.range F) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (L ⧸ H) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = _ := hidx

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.ip_eq_sum {R : ℕ} (hR : 0 < R) {φ ψ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) (hψ : _root_.GlobalTheory.SW.HasLevel R ψ) :
    _root_.GlobalTheory.SW.ip φ ψ =
      ((R : ℂ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        φ q.out * conj (ψ q.out) := by
  have hlev : _root_.GlobalTheory.SW.HasLevel R (fun x => φ x * conj (ψ x)) := by
    refine ⟨fun x hx => hφ.1 x (left_ne_zero_of_mul hx), fun x y hy => ?_⟩
    simp only [hφ.2 x y hy, hψ.2 x y hy]
  unfold _root_.GlobalTheory.SW.ip
  rw [(_root_.GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hlev).1]
  unfold _root_.GlobalTheory.SW.haarAt
  congr 1
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  rw [Set.Finite.coe_toFinset]
  exact hφ.1 _ (left_ne_zero_of_mul hq)

end GlobalTheory.SW.IpPos

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
private lemma schwartzBruhatInnerProduct_self_eq_lemma {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) :
    _root_.GlobalTheory.SW.ip φ φ =
      (((R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        ‖φ q.out‖ ^ 2 : ℝ) := by
  rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hR hφ hφ]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.ip_self_nonneg_and_bounds : ∀ (K κ ι : Type) [Field K] [NumberField K]
    [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    (_root_.GlobalTheory.SW.ip φ φ).im = 0 ∧ 0 ≤ (_root_.GlobalTheory.SW.ip φ φ).re ∧
    (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
      (_root_.GlobalTheory.SW.ip φ φ).re) ∧
    (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (_root_.GlobalTheory.SW.ip φ φ).re ≤
      (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧
    (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
      ‖_root_.GlobalTheory.SW.ip φ ψ‖ ^ 2 ≤
        (_root_.GlobalTheory.SW.ip φ φ).re * (_root_.GlobalTheory.SW.ip ψ ψ).re := by
  intro K κ ι _ _ _ _ R φ hR hφ
  set N := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)
  have hfc := _root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR
  set s := hfc.1.toFinset with hs
  set Sφ := ∑ q ∈ s, ‖φ q.out‖ ^ 2 with hSφ
  have hc : (0 : ℝ) < (R : ℝ) ^ N := by positivity
  have hip : _root_.GlobalTheory.SW.ip φ φ = (((R : ℝ) ^ N)⁻¹ * Sφ : ℝ) :=
    schwartzBruhatInnerProduct_self_eq_lemma hR hφ
  have hre : (_root_.GlobalTheory.SW.ip φ φ).re = ((R : ℝ) ^ N)⁻¹ * Sφ := by
    rw [hip, Complex.ofReal_re]
  have hS0 : 0 ≤ Sφ := Finset.sum_nonneg fun _ _ => by positivity
  have hpt : ∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re := by
    intro x
    rw [hre, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    by_cases hx : φ x = 0
    · simpa [hx] using hS0
    · have hq : (QuotientAddGroup.mk x : Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R) ∈ s := by
        rw [hs, Set.Finite.mem_toFinset]
        show _root_.GlobalTheory.SW.IntM _
        exact hφ.1 _ (by rwa [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ])
      have h := Finset.single_le_sum (f := fun q => ‖φ q.out‖ ^ 2) (fun _ _ => by positivity) hq
      simpa only [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ] using h
  refine ⟨by rw [hip, Complex.ofReal_im], by rw [hre]; positivity, hpt, fun B hB => ?_,
    ⟨√((R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re), fun x => by
      simpa using Real.abs_le_sqrt (hpt x)⟩, fun ψ hψ => ?_⟩
  · have h1 : Sφ ≤ s.card • B ^ 2 :=
      Finset.sum_le_card_nsmul _ _ _ (fun q _ => pow_le_pow_left₀ (norm_nonneg _) (hB _) 2)
    have hcard : (s.card : ℝ) ≤ ((R : ℝ) ^ N) ^ 2 := by
      rw [hs, ← Set.ncard_eq_toFinset_card _ hfc.1]
      exact_mod_cast hfc.2
    rw [nsmul_eq_mul] at h1
    rw [hre]
    calc ((R : ℝ) ^ N)⁻¹ * Sφ ≤ ((R : ℝ) ^ N)⁻¹ * (((R : ℝ) ^ N) ^ 2 * B ^ 2) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg B))
      _ = (R : ℝ) ^ N * B ^ 2 := by field_simp
  · obtain ⟨S, hS, hψS⟩ := hψ
    have hRS : 0 < R * S := Nat.mul_pos hR hS
    have hφ' := _root_.GlobalTheory.SW.IpPos.hasLevel_mul hφ S
    have hψ' : _root_.GlobalTheory.SW.HasLevel (R * S) ψ := by
      rw [mul_comm]; exact _root_.GlobalTheory.SW.IpPos.hasLevel_mul hψS R
    rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hRS hφ' hψ',
      schwartzBruhatInnerProduct_self_eq_lemma hRS hφ', schwartzBruhatInnerProduct_self_eq_lemma hRS hψ',
      Complex.ofReal_re, Complex.ofReal_re, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    set t := (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hRS).1.toFinset
    set d : ℝ := ((R * S : ℕ) : ℝ) ^ N
    have hcs : ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 ≤
        (∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2 := by
      calc _ ≤ (∑ q ∈ t, ‖φ q.out‖ * ‖ψ q.out‖) ^ 2 := by
            gcongr
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp [Complex.norm_conj]
        _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    calc (d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖) ^ 2
        = d⁻¹ * d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 := by ring
      _ ≤ d⁻¹ * d⁻¹ * ((∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = _ := by ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralEqSumResidueRepresentative
section
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem exists_rep_add_smul_zm_of_intM_smul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ}
    (hR : 0 < R) (x : Matrix κ ι ℚ) (hx : _root_.GlobalTheory.SW.IntM (R • x)) :
    ∃ (n : κ → ι → Fin (R * R)) (m : κ → ι → ℤ),
      x = _root_.GlobalTheory.SW.FourierJ.rep R n + R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  obtain ⟨M, hM⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp hx
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  have hRq : (R : ℚ) ≠ 0 := by positivity
  refine ⟨fun k i => ⟨(M k i % ((R : ℤ) * R)).toNat, ?_⟩, fun k i => M k i / ((R : ℤ) * R), ?_⟩
  · have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have h2 := Int.emod_lt_of_pos (M k i) hRR
    have h3 : ((M k i % ((R : ℤ) * R)).toNat : ℤ) < (R : ℤ) * R := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  · ext k i
    have hk := congrFun (congrFun hM k) i
    simp only [Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply, nsmul_eq_mul] at hk
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul]
    have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have hn : (((M k i % ((R : ℤ) * R)).toNat : ℕ) : ℚ) = ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
    have hq : ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) + (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ)
        = (M k i : ℚ) := by
      have := Int.mul_ediv_add_emod (M k i) ((R : ℤ) * R)
      have h' : (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) +
          ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ) := by
        exact_mod_cast this
      linear_combination h'
    have hx' : x k i = (M k i : ℚ) / R := by
      rw [eq_div_iff hRq]
      linear_combination hk
    rw [hx', hn, ← hq, add_div]
    congr 1
    rw [mul_assoc, mul_div_cancel_left₀ _ hRq]

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem mem_perSub_iff_exists_eq_smul_zm {κ ι : Type} [Fintype κ] [Fintype ι] (R : ℕ)
    (y : Matrix κ ι ℚ) : y ∈ _root_.GlobalTheory.SW.perSub ℚ κ ι R ↔
      ∃ m : κ → ι → ℤ, y = R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  rw [_root_.GlobalTheory.SW.HaarLevel.mem_perSub]
  constructor
  · rintro ⟨y', rfl⟩
    obtain ⟨m, hm⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp
      ((_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mpr ⟨y', rfl⟩)
    exact ⟨m, by rw [hm]⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨y', hy'⟩ := (_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mp
      ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)
    exact ⟨y', by rw [hy']⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem rep_injective_of_neg_add_eq_smul_zm {κ ι : Type} {R : ℕ} (hR : 0 < R)
    {n n' : κ → ι → Fin (R * R)} (m : κ → ι → ℤ)
    (hm : -_root_.GlobalTheory.SW.FourierJ.rep R n + _root_.GlobalTheory.SW.FourierJ.rep R n' =
      R • _root_.GlobalTheory.SW.FourierJ.zm m) : n = n' := by
    funext k i
    have hk := congrFun (congrFun hm k) i
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul] at hk
    have hRq : (R : ℚ) ≠ 0 := by positivity
    rw [neg_add_eq_sub, ← sub_div, div_eq_iff hRq] at hk
    have hzq : ((n' k i : ℕ) : ℚ) - (n k i : ℕ) = (R : ℚ) * R * m k i := by
      linear_combination hk
    have hz : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = (R : ℤ) * R * m k i := by
      exact_mod_cast hzq
    have hb : ((n' k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n' k i).isLt
    have ha : ((n k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n k i).isLt
    have h0 : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd ⟨m k i, hz⟩
      rw [abs_lt]
      constructor <;>
        linarith [Int.natCast_nonneg (n k i : ℕ), Int.natCast_nonneg (n' k i : ℕ)]
    exact Fin.ext (by omega)


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.FourierJ.haar_eq_sum_rep : ∀ (κ ι : Type) [Fintype κ]
    [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ : Matrix κ ι ℚ → ℂ), 0 < R →
    _root_.GlobalTheory.SW.HasLevel R φ → _root_.GlobalTheory.SW.haar φ =
      ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ *
        ∑ n : κ → ι → Fin (R * R), φ (_root_.GlobalTheory.SW.FourierJ.rep R n) := by
  intro κ ι _ _ _ _ R φ hR hφ
  classical
  obtain ⟨h1, -⟩ := _root_.GlobalTheory.SW.haar_eq_haarAt ℚ κ ι R φ hR hφ
  rw [h1]
  unfold _root_.GlobalTheory.SW.haarAt
  rw [Module.finrank_self, one_mul]
  congr 1
  have hper : ∀ x : Matrix κ ι ℚ, φ (Quotient.out
      (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R)) = φ x := by
    intro x
    have hmem : -x + Quotient.out
        (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R) ∈
        _root_.GlobalTheory.SW.perSub ℚ κ ι R :=
      QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have h := _root_.GlobalTheory.SW.HaarLevel.periodic hφ x _ hmem
    rwa [add_neg_cancel_left] at h
  have hsupp : (Function.support fun q : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R =>
      φ (Quotient.out q)) ⊆ ↑(Finset.univ.image fun n : κ → ι → Fin (R * R) =>
        (QuotientAddGroup.mk (_root_.GlobalTheory.SW.FourierJ.rep R n) :
          Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R)) := by
    intro q hq
    obtain ⟨n, m, hnm⟩ := exists_rep_add_smul_zm_of_intM_smul hR _ (hφ.1 _ (Function.mem_support.mp hq))
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    refine ⟨n, ?_⟩
    rw [← QuotientAddGroup.out_eq' q, hnm, QuotientAddGroup.eq, neg_add_cancel_left]
    exact (mem_perSub_iff_exists_eq_smul_zm R _).mpr ⟨m, rfl⟩
  have hinj : Function.Injective fun n : κ → ι → Fin (R * R) =>
      (QuotientAddGroup.mk (_root_.GlobalTheory.SW.FourierJ.rep R n) :
        Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R) := by
    intro n n' h
    obtain ⟨m, hm⟩ := (mem_perSub_iff_exists_eq_smul_zm R _).mp (QuotientAddGroup.eq.mp h)
    exact rep_injective_of_neg_add_eq_smul_zm hR m hm
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun n _ n' _ h => hinj h)]
  exact Finset.sum_congr rfl fun n _ => hper _

end GlobalTheory.SW.FourierJ
end

