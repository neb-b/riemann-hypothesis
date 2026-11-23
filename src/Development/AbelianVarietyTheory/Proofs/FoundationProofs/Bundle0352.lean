module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisibleOrdinarySelmerChainExistsIntegralRepres
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.DivChain

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem l_ne_zero : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

theorem norm_l_le_one (c : Coef l) : ‖((l : ℕ) : Qbar l)‖ ≤ 1 :=
  CupCob.norm_le_one_of_mem c (c.O.natCast_mem l)

theorem mem_of_memE (c : Coef l) {x : Qbar l} (hx : MemE c x) (h1 : ‖x‖ ≤ 1) : x ∈ c.O := by
  obtain ⟨k, hk⟩ := hx
  by_cases hx0 : x = 0
  · rw [hx0]; exact c.O.zero_mem
  set b : c.O := ⟨(l : Qbar l) ^ k * x, hk⟩ with hb
  set L : c.O := (l : c.O) ^ k with hL
  have hLv : (L : Qbar l) = (l : Qbar l) ^ k := by simp [hL]
  have hbv : (b : Qbar l) = (l : Qbar l) ^ k * x := rfl
  have hb0 : b ≠ 0 := by
    intro h
    have : (b : Qbar l) = 0 := by rw [h]; rfl
    rw [hbv] at this
    exact hx0 ((mul_eq_zero.1 this).resolve_left (pow_ne_zero _ l_ne_zero))
  have hL0 : L ≠ 0 := by
    intro h
    have : (L : Qbar l) = 0 := by rw [h]; rfl
    rw [hLv] at this
    exact pow_ne_zero _ l_ne_zero this
  have hnorm : ‖(b : Qbar l)‖ ≤ ‖(L : Qbar l)‖ := by
    rw [hLv, hbv, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) h1
  have e1 := UpperTheory.V.Base.normO l c.O b hb0
  have e2 := UpperTheory.V.Base.normO l c.O L hL0
  have hl1 : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : 0 < ((l : ℝ)⁻¹) := inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
  have h2 : ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O b).toNat ≤
      ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O L).toNat := by
    rw [← e1, ← e2]; exact pow_le_pow_left₀ (norm_nonneg _) hnorm _
  rw [pow_le_pow_iff_right_of_lt_one₀ hl0 hl1] at h2
  have hv : IsDiscreteValuationRing.addVal c.O L ≤ IsDiscreteValuationRing.addVal c.O b := by
    have t1 : IsDiscreteValuationRing.addVal c.O L ≠ ⊤ := by
      rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    have t2 : IsDiscreteValuationRing.addVal c.O b ≠ ⊤ := by
      rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    rw [← ENat.coe_toNat t1, ← ENat.coe_toNat t2]
    exact_mod_cast h2
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 hv
  have h3 : (b : Qbar l) = (L : Qbar l) * (w : Qbar l) := by rw [hw]; rfl
  rw [hLv, hbv] at h3
  have hx' : x = (w : Qbar l) := mul_left_cancel₀ (pow_ne_zero k l_ne_zero) h3
  rw [hx']; exact w.2

def cob (W : R2 Ω l) (y : Fin 2 → Qbar l) : G ℚ Ω → Fin 2 → Qbar l := fun s => mat W s *ᵥ y - y

theorem cob_smul (W : R2 Ω l) (a : Qbar l) (y : Fin 2 → Qbar l) (s : G ℚ Ω) (i : Fin 2) :
    cob W (a • y) s i = a * cob W y s i := by
  simp only [cob, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem cob_pow_mem (c : Coef l) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) {y : Fin 2 → Qbar l} {k : ℕ}
    (hk : ∀ i, (l : Qbar l) ^ k * y i ∈ c.O) (s : G ℚ Ω) (i : Fin 2) : (l : Qbar l) ^ k * cob W y s i ∈ c.O := by
  rw [← cob_smul]
  have hk' : ∀ j, ((l : Qbar l) ^ k • y) j ∈ c.O := fun j => by rw [Pi.smul_apply, smul_eq_mul]; exact hk j
  simp only [cob, Pi.sub_apply]
  exact sub_mem (CupCob.mulVec_mem c _ _ (hint s) hk' i) (hk' i)

theorem cob_loc (c : Coef l) (W : R2 Ω l) (hW : Continuous W) (hint : ∀ s i j, mat W s i j ∈ c.O)
    {y : Fin 2 → Qbar l} (hy : VecE c y) (s : G ℚ Ω) : ∀ᶠ t in nhds s, ∀ i, cob W y t i - cob W y s i ∈ c.O := by
  obtain ⟨k, hk⟩ := hy
  have hr : 0 < ‖(l : Qbar l) ^ k‖ := norm_pos_iff.2 (pow_ne_zero _ l_ne_zero)
  have hc : ∀ i j, Continuous fun t : G ℚ Ω => mat W t i j := fun i j =>
    (Units.continuous_val.comp hW).matrix_elem i j
  have ev : ∀ i j, ∀ᶠ t in nhds s, dist (mat W t i j) (mat W s i j) < ‖(l : Qbar l) ^ k‖ :=
    fun i j => Metric.tendsto_nhds.1 ((hc i j).tendsto s) _ hr
  have ev' : ∀ᶠ t in nhds s, ∀ i j, dist (mat W t i j) (mat W s i j) < ‖(l : Qbar l) ^ k‖ :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev i j
  have term : ∀ i j t, dist (mat W t i j) (mat W s i j) < ‖(l : Qbar l) ^ k‖ →
      (mat W t i j - mat W s i j) * y j ∈ c.O := by
    intro i j t ht
    apply mem_of_memE c
    · exact ⟨k, by rw [mul_left_comm]; exact mul_mem (sub_mem (hint t i j) (hint s i j)) (hk j)⟩
    · rw [dist_eq_norm] at ht
      rw [norm_mul]
      have h1 : ‖(l : Qbar l) ^ k * y j‖ ≤ 1 := CupCob.norm_le_one_of_mem c (hk j)
      rw [norm_mul] at h1
      calc ‖mat W t i j - mat W s i j‖ * ‖y j‖ ≤ ‖(l : Qbar l) ^ k‖ * ‖y j‖ :=
            mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)
        _ ≤ 1 := h1
  filter_upwards [ev'] with t ht i
  have e : cob W y t i - cob W y s i = (mat W t i 0 - mat W s i 0) * y 0 + (mat W t i 1 - mat W s i 1) * y 1 := by
    simp only [cob, Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [e]; exact add_mem (term i 0 t (ht i 0)) (term i 1 t (ht i 1))

theorem cob_mem (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) (hW : Continuous W)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (hker : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    (hup : ∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0) {y : Fin 2 → Qbar l} (hy : VecE c y) :
    cob W y ∈ divSelCoc c W S A := by
  obtain ⟨k, hk⟩ := hy
  refine ⟨⟨k, fun s i => cob_pow_mem c W hint hk s i⟩, fun s t i => ?_, fun s => cob_loc c W hW hint ⟨k, hk⟩ s,
    fun a ha i => ?_, fun q _ _ B _ => ⟨y, ⟨k, hk⟩, fun s _ i => by simp [cob]⟩, ⟨y 1, ⟨k, hk 1⟩, fun s hs => ?_⟩⟩
  · have e : cob W y (s * t) i - cob W y s i - (mat W s *ᵥ cob W y t) i = 0 := by
      simp only [cob, mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Pi.sub_apply]; ring
    rw [e]; exact c.O.zero_mem
  · simp [cob, mat, hker a ha]
  · have e : cob W y s 1 - (mat W s 1 1 * y 1 - y 1) = 0 := by
      simp only [cob, Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup s hs]; ring
    rw [e]; exact c.O.zero_mem

theorem cg_of (c : Coef l) {n E : ℕ} (h : n ≤ E) {a b w : Qbar l} (hw : w ∈ c.O)
    (e : a - b = (l : Qbar l) ^ E * w) : Cg n a b := by
  unfold Cg
  rw [e, norm_mul, norm_pow, norm_pow]
  calc ‖(l : Qbar l)‖ ^ E * ‖w‖ ≤ ‖(l : Qbar l)‖ ^ E * 1 :=
        mul_le_mul_of_nonneg_left (CupCob.norm_le_one_of_mem c hw) (by positivity)
    _ = ‖(l : Qbar l)‖ ^ E := mul_one _
    _ ≤ ‖(l : Qbar l)‖ ^ n := pow_le_pow_of_le_one (norm_nonneg _) (norm_l_le_one c) h

theorem representatives : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → (∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0) → ∀ x : ℕ → DivSel c W S A, x 0 ≠ 0 → (∀ n, l • x (n + 1) = x n) → ∃ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) ∧ (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) ∧ (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) ∧ (∀ n s, Cv n (a (n + 1) s) (a n s)) ∧ (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) ∧ (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) ∧ (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) ∧ ¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y) := by
  intro l _ Ω _ _ S A W c hW hint hker hup x hx0 hx
  have step : ∀ (n : ℕ) (z : divSelCoc c W S A), ∃ z' : divSelCoc c W S A,
      ((QuotientAddGroup.mk z : DivSel c W S A) = x n →
        (QuotientAddGroup.mk z' : DivSel c W S A) = x (n + 1) ∧
          ∀ s i, (l : Qbar l) * z'.1 s i - z.1 s i ∈ c.O) := by
    intro n z
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (x (n + 1))
    by_cases hz : (QuotientAddGroup.mk z : DivSel c W S A) = x n
    swap
    · exact ⟨w, fun h => absurd h hz⟩
    have h1 : (QuotientAddGroup.mk (l • w) : DivSel c W S A) = QuotientAddGroup.mk z := by
      rw [QuotientAddGroup.mk_nsmul, hw, hx, hz]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    obtain ⟨t, ht, hts⟩ := h1
    have hty : VecE c ((l : Qbar l)⁻¹ • t) := by
      obtain ⟨k, hk⟩ := ht
      refine ⟨k + 1, fun i => ?_⟩
      rw [Pi.smul_apply, smul_eq_mul, pow_succ, mul_assoc, ← mul_assoc (l : Qbar l), mul_inv_cancel₀ l_ne_zero, one_mul]
      exact hk i
    have hmem : cob W ((l : Qbar l)⁻¹ • t) ∈ divCob c W := ⟨_, hty, fun s i => by simp [cob]⟩
    refine ⟨⟨w.1 + cob W ((l : Qbar l)⁻¹ • t), add_mem w.2 (cob_mem c W S A hW hint hker hup hty)⟩,
      fun _ => ⟨?_, fun s i => ?_⟩⟩
    · rw [← hw, eq_comm, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      convert hmem using 1
      simp
    · have hu : cob W ((l : Qbar l)⁻¹ • t) s i = (l : Qbar l)⁻¹ * cob W t s i := cob_smul W _ t s i
      have h3 := hts s i
      have hl : (l : Qbar l) * (l : Qbar l)⁻¹ = 1 := mul_inv_cancel₀ l_ne_zero
      have e : (l : Qbar l) * (w.1 + cob W ((l : Qbar l)⁻¹ • t)) s i - z.1 s i =
          -((((-(l • w) + z : divSelCoc c W S A) : G ℚ Ω → Fin 2 → Qbar l) s i) - (mat W s *ᵥ t - t) i) := by
        have hc : (mat W s *ᵥ t - t) i = cob W t s i := rfl
        rw [hc]
        simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_nsmul, Pi.add_apply, Pi.neg_apply,
          Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, hu]
        linear_combination (cob W t s i) * hl
      rw [e]; exact c.O.neg_mem h3
  choose f hf using step
  obtain ⟨z0, hz0⟩ := QuotientAddGroup.mk_surjective (x 0)
  let zs : ℕ → divSelCoc c W S A := fun n => Nat.rec z0 (fun m z => f m z) n
  have hzs : ∀ n, zs (n + 1) = f n (zs n) := fun n => rfl
  have hcls : ∀ n, (QuotientAddGroup.mk (zs n) : DivSel c W S A) = x n := by
    intro n
    induction n with
    | zero => exact hz0
    | succ n ih => rw [hzs]; exact (hf n (zs n) ih).1
  have hrel : ∀ n s i, (l : Qbar l) * (zs (n + 1)).1 s i - (zs n).1 s i ∈ c.O := fun n =>
    (hf n (zs n) (hcls n)).2
  obtain ⟨k, hk⟩ := (zs 0).2.1
  have hint_n : ∀ n s i, (l : Qbar l) ^ (n + k) * (zs n).1 s i ∈ c.O := by
    intro n
    induction n with
    | zero => simpa using hk
    | succ n ih =>
      intro s i
      have e : (l : Qbar l) ^ (n + 1 + k) * (zs (n + 1)).1 s i = (l : Qbar l) ^ (n + k) *
          ((l : Qbar l) * (zs (n + 1)).1 s i - (zs n).1 s i) + (l : Qbar l) ^ (n + k) * (zs n).1 s i := by ring
      rw [e]; exact add_mem (mul_mem (natPow_mem c _) (hrel n s i)) (ih s i)
  let a : ℕ → G ℚ Ω → Fin 2 → Qbar l := fun j s => ((l : Qbar l) ^ (j - k + k)) • (zs (j - k)).1 s
  have ha : ∀ j s i, a j s i = (l : Qbar l) ^ (j - k + k) * (zs (j - k)).1 s i := fun _ _ _ => rfl
  refine ⟨a, k, fun j s i => ?_, fun j s t i => ?_, fun j s => ?_, fun j s i => ?_, fun j b hb i => ?_,
    fun j q hq hl B hB => ?_, fun j => ?_, ?_⟩
  · rw [ha]; exact hint_n (j - k) s i
  · refine cg_of c (E := j - k + k) (by omega) ((zs (j - k)).2.2.1 s t i) ?_
    simp only [a, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · filter_upwards [(zs (j - k)).2.2.2.1 s] with t ht i
    refine cg_of c (E := j - k + k) (by omega) (ht i) ?_
    rw [ha, ha]; ring
  · by_cases hjk : j < k
    · have e1 : j + 1 - k = 0 := by omega
      have e2 : j - k = 0 := by omega
      have : a (j + 1) s i = a j s i := by rw [ha, ha, e1, e2]
      rw [this]; unfold Cg; rw [sub_self, norm_zero]; exact norm_nonneg _
    · have e1 : j + 1 - k = j - k + 1 := by omega
      refine cg_of c (E := j - k + k) (by omega) (hrel (j - k) s i) ?_
      rw [ha, ha, e1]; ring
  · refine cg_of c (E := j - k + k) (by omega) ((zs (j - k)).2.2.2.2.1 b hb i) ?_
    rw [ha]; simp
  · obtain ⟨y, ⟨k', hk'⟩, hys⟩ := (zs (j - k)).2.2.2.2.2.1 q hq hl B hB
    refine ⟨(l : Qbar l) ^ (j - k + k) • y, ⟨k', fun i => ?_⟩, fun s hs i => ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]; exact mul_mem (natPow_mem c _) (hk' i)
    · refine cg_of c (E := j - k + k) (by omega) (hys s hs i) ?_
      simp only [a, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  · obtain ⟨y, ⟨k', hk'⟩, hys⟩ := (zs (j - k)).2.2.2.2.2.2
    refine ⟨(l : Qbar l) ^ (j - k + k) * y, ⟨k', ?_⟩, fun s hs => ?_⟩
    · rw [mul_left_comm]; exact mul_mem (natPow_mem c _) hk'
    · refine cg_of c (E := j - k + k) (by omega) (hys s hs) ?_
      rw [ha]; ring
  · rintro ⟨y, ⟨k', hk'⟩, hys⟩
    apply hx0
    rw [← hcls 0, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    have hL0 : (l : Qbar l) ^ k ≠ 0 := pow_ne_zero _ l_ne_zero
    have hL : (l : Qbar l) ^ k * ((l : Qbar l) ^ k)⁻¹ = 1 := mul_inv_cancel₀ hL0
    refine ⟨((l : Qbar l) ^ k)⁻¹ • y, ⟨k' + k, fun i => ?_⟩, fun s i => ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, pow_add, mul_assoc, ← mul_assoc ((l : Qbar l) ^ k), hL, one_mul]
      exact hk' i
    · show (zs 0).1 s i - cob W (((l : Qbar l) ^ k)⁻¹ • y) s i ∈ c.O
      have hv := hys s i
      have hak : a k s i = (l : Qbar l) ^ k * (zs 0).1 s i := by rw [ha, Nat.sub_self, zero_add]
      rw [hak] at hv
      have hcu : cob W (((l : Qbar l) ^ k)⁻¹ • y) s i = ((l : Qbar l) ^ k)⁻¹ * cob W y s i := cob_smul W _ y s i
      have key : (l : Qbar l) ^ k * ((zs 0).1 s i - cob W (((l : Qbar l) ^ k)⁻¹ • y) s i) =
          (l : Qbar l) ^ k * (zs 0).1 s i - cob W y s i := by
        rw [hcu]; linear_combination (-cob W y s i) * hL
      apply mem_of_memE c
      · refine ⟨k + k', ?_⟩
        have e : (l : Qbar l) ^ (k + k') * ((zs 0).1 s i - cob W (((l : Qbar l) ^ k)⁻¹ • y) s i) =
            (l : Qbar l) ^ k' * ((l : Qbar l) ^ k * (zs 0).1 s i) - (l : Qbar l) ^ k' * cob W y s i := by
          rw [pow_add, mul_comm ((l : Qbar l) ^ k) _, mul_assoc, key]; ring
        rw [e]
        exact sub_mem (mul_mem (natPow_mem c _) (hk s i)) (cob_pow_mem c W hint hk' s i)
      · have hn : ‖(l : Qbar l) ^ k‖ * ‖(zs 0).1 s i - cob W (((l : Qbar l) ^ k)⁻¹ • y) s i‖ ≤
            ‖(l : Qbar l) ^ k‖ * 1 := by
          rw [← norm_mul, key, mul_one]; exact hv
        exact le_of_mul_le_mul_left hn (norm_pos_iff.2 hL0)

end GlobalTheory.Ord2.DivChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationCombinationEqIdTracelessIrredu
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Sl2Ad

theorem form_isSymm {K : Type} [Field K] : (form (K := K)).IsSymm := by
  first
  | exact ⟨fun v w => by simp only [RingHom.id_apply, form_apply]; ring⟩
  | exact fun v w => by simp only [RingHom.id_apply, form_apply]; ring
  | (intro v w; simp only [RingHom.id_apply, form_apply]; ring)

theorem form_ad {K : Type} [Field K] (A : GL (Fin 2) K) (v w : Fin 3 → K) :
    form (ad A *ᵥ v) (ad A *ᵥ w) = form v w := by
  rw [← coord_conj_ofCoord, ← coord_conj_ofCoord,
    form_coord (by rw [trace_conj, trace_ofCoord]) (by rw [trace_conj, trace_ofCoord])]
  conv_rhs => rw [← coord_ofCoord v, ← coord_ofCoord w, form_coord (trace_ofCoord v) (trace_ofCoord w)]
  have : ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord v * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord w * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = (A : Matrix (Fin 2) (Fin 2) K) * (ofCoord v * ofCoord w) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), h, Matrix.one_mul]
  rw [this, trace_conj]

theorem form_nondegenerate {K : Type} [Field K] [CharZero K] : (form (K := K)).Nondegenerate := by
  rw [form, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
  simp [Matrix.det_fin_three]

theorem coord_smul_scalar {F K : Type} [Field F] [Field K] [Algebra F K] (a : F) (X : Matrix (Fin 2) (Fin 2) K) :
    coord (a • X) = a • coord X := by
  ext i; fin_cases i <;> simp [coord]

theorem coord_sum {K : Type} [Field K] {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin 2) (Fin 2) K) :
    coord (∑ i ∈ s, f i) = ∑ i ∈ s, coord (f i) := by
  ext j; fin_cases j <;> simp [coord, Matrix.sum_apply]

end GlobalTheory.Sl2Ad


open GlobalTheory.Sl2Ad in
theorem GlobalTheory.Sl2Ad.augmentation_contains_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → IsIrr r → ∃ (n : ℕ) (γ : Fin n → Γ) (a : Fin n → ℚ_[l]), ∀ X : Matrix (Fin 2) (Fin 2) (Qbar l), X.trace = 0 → X = ∑ i, a i • ((r (γ i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) - X) := by
  intro l _ c Γ _ r _ hirr
  set S : Γ →* Matrix (Fin 3) (Fin 3) (Qbar l) := adHom.comp r with hS
  have hSg : ∀ g, S g = ad (r g) := fun g => rfl
  have h1 := _root_.GlobalTheory.augSpan_one_mem_of_orthogonal_three S form form_nondegenerate form_isSymm (fun g v w => form_ad _ v w)
    (fun v hv => GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr r hirr v (fun g => by rw [← hSg]; exact hv g))
    (fun y hy hy' => _root_.GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr r hirr y hy (fun g => by rw [← hSg]; exact hy' g))
  obtain ⟨n, b, g, hg⟩ := Submodule.mem_span_set'.mp h1
  choose γ hγ using fun i => (g i).2
  have hdet : (∑ i, b i • (S (γ i) - 1)).det ≠ 0 := by
    have : ∑ i, b i • (S (γ i) - 1) = 1 :=
      (Finset.sum_congr rfl fun i _ => by rw [← hγ i]).trans hg
    rw [this, Matrix.det_one]; exact one_ne_zero
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.exists_nat_coeffs_det_ne_zero (fun i => S (γ i) - 1) b hdet
  set J : Submodule ℚ_[l] (Matrix (Fin 3) (Fin 3) (Qbar l)) := Submodule.span ℚ_[l] (Set.range fun g => S g - 1) with hJ
  have hmul : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h, rfl⟩ := hy
        have : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
          rw [map_mul]; noncomm_ring
        rw [this]
        exact J.sub_mem (J.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
      | zero => rw [mul_zero]; exact J.zero_mem
      | add y z _ _ hy hz => rw [mul_add]; exact J.add_mem hy hz
      | smul t y _ hy => rw [mul_smul_comm]; exact J.smul_mem t hy
    | zero => rw [zero_mul]; exact J.zero_mem
    | add x z _ _ hx hz => rw [add_mul]; exact J.add_mem hx hz
    | smul t x _ hx => rw [smul_mul_assoc]; exact J.smul_mem t hx
  have hT : (∑ i, (a i : Qbar l) • (S (γ i) - 1)) ∈ J := by
    refine J.sum_mem fun i _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact J.nsmul_mem (Submodule.subset_span ⟨_, rfl⟩) _
  have hone := _root_.GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero J hmul _ hT ha
  obtain ⟨n', a', g', hg'⟩ := Submodule.mem_span_set'.mp hone
  choose γ' hγ' using fun i => (g' i).2
  refine ⟨n', γ', a', fun X hX => ?_⟩
  have htr : (∑ i, a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) - X)).trace = 0 := by
    rw [Matrix.trace_sum]; refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.trace_smul, Matrix.trace_sub, trace_conj, hX, sub_zero, smul_zero]
  refine ((ofCoord_coord hX).symm.trans ?_).trans (ofCoord_coord htr)
  congr 1
  rw [coord_sum]
  have : ∀ i, coord (a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X))
      = (a' i • (S (γ' i) - 1)) *ᵥ coord X := by
    intro i
    rw [coord_smul_scalar, show ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X)
      = (r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) + (-1 : Qbar l) • X by
        rw [neg_one_smul, ← sub_eq_add_neg], coord_add, coord_conj _ hX, coord_smul, hSg, Matrix.smul_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, neg_one_smul, ← sub_eq_add_neg]
  simp_rw [this, ← Matrix.sum_mulVec]
  have e : ∑ i, a' i • (S (γ' i) - 1) = 1 :=
    (Finset.sum_congr rfl fun i _ => by rw [← hγ' i]).trans hg'
  rw [e, Matrix.one_mulVec]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDotProductEqOfPrimePowApproxQbarL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory

theorem exists_dotProduct_eq_of_approx_pow {K : Type*} [NormedField K] (r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (X : Type*) (m : ℕ) (M : X → Fin m → K) (z : X → K)
    (h : ∀ n : ℕ, ∃ y : Fin m → K, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ r ^ n) :
    ∃ y : Fin m → K, ∀ x, z x = M x ⬝ᵥ y := by
  classical
  let T : (X →₀ K) →ₗ[K] (Fin m → K) := Finsupp.linearCombination K M
  let φ : Module.Dual K (X →₀ K) := Finsupp.linearCombination K z
  have hker : φ ∈ (LinearMap.ker T).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro c hc
    have hc' : ∑ x ∈ c.support, c x • M x = 0 := by
      simpa [T, Finsupp.linearCombination_apply, Finsupp.sum] using hc
    have hφ : φ c = ∑ x ∈ c.support, c x * z x := by
      simp [φ, Finsupp.linearCombination_apply, Finsupp.sum]
    have hb : ∀ n : ℕ, ‖φ c‖ ≤ (∑ x ∈ c.support, ‖c x‖) * r ^ n := by
      intro n
      obtain ⟨y, hy⟩ := h n
      have h0 : ∑ x ∈ c.support, c x * (M x ⬝ᵥ y) = 0 := by
        have := congrArg (· ⬝ᵥ y) hc'
        simpa [sum_dotProduct, smul_dotProduct] using this
      have : φ c = ∑ x ∈ c.support, c x * (z x - M x ⬝ᵥ y) := by
        simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero, hφ]
      rw [this, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hy x) (norm_nonneg _)
    have hlim : Filter.Tendsto (fun n : ℕ => (∑ x ∈ c.support, ‖c x‖) * r ^ n) Filter.atTop
        (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
        (∑ x ∈ c.support, ‖c x‖)
    exact norm_le_zero_iff.mp (ge_of_tendsto' hlim hb)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hker
  obtain ⟨g, hg⟩ := hker
  refine ⟨fun i => g (fun j => if i = j then 1 else 0), fun x => ?_⟩
  have h1 := congrArg (fun f : Module.Dual K (X →₀ K) => f (Finsupp.single x 1)) hg
  simp only [LinearMap.dualMap_apply, T, φ, Finsupp.linearCombination_single, one_smul,
    smul_eq_mul, one_mul] at h1
  rw [← h1, LinearMap.pi_apply_eq_sum_univ g (M x)]
  simp [dotProduct]

theorem exists_dotProduct_eq_of_approx_prime_pow :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) (m : ℕ) (M : X → Fin m → Qbar l) (z : X → Qbar l), (∀ n : ℕ, ∃ y : Fin m → Qbar l, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ∃ y : Fin m → Qbar l, ∀ x, z x = M x ⬝ᵥ y := by
  intro l _ X m M z h
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine exists_dotProduct_eq_of_approx_pow _ (norm_nonneg _) hl X m M z fun n => ?_
  simpa only [norm_pow] using h n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActDiagNatOneComm
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem toGQ_diag_nat_one_ent (q : ℕ) (hq : 0 < q) :
    ent (toGQ !![(q : ℤ), 0; 0, 1]) 0 0 = (q : ℚ) ∧ ent (toGQ !![(q : ℤ), 0; 0, 1]) 0 1 = 0 ∧
    ent (toGQ !![(q : ℤ), 0; 0, 1]) 1 0 = 0 ∧ ent (toGQ !![(q : ℤ), 0; 0, 1]) 1 1 = 1 := by
  have h : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.det_fin_two_of]; omega
  unfold ent toGQ
  rw [dite_eq_left h]
  simp

theorem eOm_zero_of_injective_diag {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (hε : Function.Injective ε) : eOm ε 0 = 1 := by
  unfold eOm
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun hε 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.exp_sl_diag_coeff (X : Tower Ω ε) (hε : Function.Injective ε) (q : ℕ) (hq : 0 < q) (f : X.K) (r : ℚ) :
    (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f)).coeff r = (X.exp f).coeff (r / q) := by
  obtain ⟨h00, h01, h10, h11⟩ := toGQ_diag_nat_one_ent q hq
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have h := X.exp_upper _ h10 f (r / q)
  rw [h00, h01, h11, mul_zero, zero_div, eOm_zero_of_injective_diag ε hε, one_mul, div_one, div_mul_cancel₀ r hqQ] at h
  exact h

theorem Tower.gal_sl_diag (X : Tower Ω ε) (hε : Function.Injective ε) (q : ℕ) (hq : 0 < q)
    (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f) = X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (X.gal s f) := by
  apply RingHom.injective X.exp.toRingHom
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, X.exp_sl_diag_coeff hε q hq, X.exp_sl_diag_coeff hε q hq, X.gal_exp]

theorem mZl_diag_nat_one_mulVec (l : ℕ) [Fact l.Prime] (q : ℕ) (c : ℤ_[l]) (u : Fin 2 → ℤ_[l]) :
    mZl l !![(q : ℤ), 0; 0, 1] *ᵥ ![u 0, c * u 1] =
      ![(mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u) 0, c * (mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u) 1] := by
  funext i
  fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Tower.galB_act_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), 0 < q → ∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l),
      X.galB l s (X.act l !![(q : ℤ), 0; 0, 1] b) = X.act l !![(q : ℤ), 0; 0, 1] (X.galB l s b) := by
  intro Ω _ _ ε X hε l _ q hq s b
  funext u
  simp only [Tower.galB, Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap, Tower.kmap_kmap, mZl_diag_nat_one_mulVec]
  have hφ : (X.sl (toGQ !![(q : ℤ), 0; 0, 1])).toRingEquiv.trans (X.gal s) =
      (X.gal s).trans (X.sl (toGQ !![(q : ℤ), 0; 0, 1])).toRingEquiv :=
    RingEquiv.ext fun f => X.gal_sl_diag hε q hq s f
  rw [hφ]

end GlobalTheory.KZ
end
end

