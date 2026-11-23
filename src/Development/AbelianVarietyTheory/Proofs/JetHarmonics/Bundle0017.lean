module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLeadingMinorsGeOfLeRank
section
namespace GlobalTheory

theorem exists_mem_valuation_le_of_mem_span {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {M : Type} [AddCommGroup M]
    [Module O M] (A : Set M) (φ : M →ₗ[O] O) {x : M} (hx : x ∈ Submodule.span O A)
    (h0 : v (algebraMap O C (φ x)) ≠ 0) :
    ∃ a ∈ A, v (algebraMap O C (φ x)) ≤ v (algebraMap O C (φ a)) := by
  by_contra hne
  push Not at hne
  have key : ∀ y ∈ Submodule.span O A,
      v (algebraMap O C (φ y)) < v (algebraMap O C (φ x)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem a ha => exact hne a ha
    | zero => simpa using pos_iff_ne_zero.mpr h0
    | add a b _ _ ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact v.map_add_lt ha hb
    | smul o a _ ha =>
      rw [map_smul, smul_eq_mul, map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one o)) ha
  exact lt_irrefl _ (key x hx)

theorem exists_leading_minors_ge_of_le_rank {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {r : ℕ} (A : Set (Fin r → O))
    {c : O} (hc : c ≠ 0) (hA : ∀ x : Fin r → O, c • x ∈ Submodule.span O A) :
    ∀ n : ℕ, n ≤ r → ∃ t : ℕ → Fin r → O, (∀ i, i < n → t i ∈ A) ∧
      ∀ (m : ℕ) (hm : m ≤ r), m ≤ n → v (algebraMap O C c) ^ m ≤
        v (algebraMap O C (Matrix.of fun a i : Fin m => t i (Fin.castLE hm a)).det) := by
  have hvc : v (algebraMap O C c) ≠ 0 := by
    rw [Ne, v.zero_iff]
    intro h
    exact hc (hv.hom_inj (by rw [h, map_zero]))
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    intro m hm h0
    obtain rfl : m = 0 := Nat.le_zero.mp h0
    simp
  | succ n ih =>
    intro hn
    obtain ⟨t, htA, ht⟩ := ih (Nat.le_of_succ_le hn)
    let coef : Fin (n + 1) → O := fun a => (-1) ^ ((a : ℕ) + n) *
      (Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b))).det
    let φ : (Fin r → O) →ₗ[O] O :=
      ∑ a : Fin (n + 1), coef a • LinearMap.proj (Fin.castLE hn a)
    have hφ : ∀ x, φ x = ∑ a : Fin (n + 1), coef a * x (Fin.castLE hn a) := by
      intro x
      simp [φ, LinearMap.sum_apply]
    have hdet : ∀ x, (Matrix.of fun a i : Fin (n + 1) =>
        Function.update t n x i (Fin.castLE hn a)).det = φ x := by
      intro x
      rw [hφ, Matrix.det_succ_column _ (Fin.last n)]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : (Matrix.of fun a i : Fin (n + 1) =>
          Function.update t n x i (Fin.castLE hn a)).submatrix a.succAbove
          (Fin.last n).succAbove =
          Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b)) := by
        ext b i
        simp [Function.update_of_ne (Nat.ne_of_lt i.isLt)]
      rw [this]
      simp only [coef, Matrix.of_apply, Fin.val_last, Function.update_self]
      ring
    have hval : φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1) =
        c * (Matrix.of fun a i : Fin n => t i (Fin.castLE (Nat.le_of_succ_le hn) a)).det := by
      rw [map_smul, smul_eq_mul, hφ, Finset.sum_eq_single (Fin.last n)]
      · congr 1
        simp only [coef, Pi.single_eq_same, mul_one, Fin.val_last, Fin.succAbove_last]
        rw [← two_mul, pow_mul]
        simp only [even_two, Even.neg_pow, one_pow, one_mul]
        rfl
      · intro b _ hb
        rw [Pi.single_eq_of_ne (fun h => hb (Fin.castLE_injective hn h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hlow : v (algebraMap O C c) ^ (n + 1) ≤
        v (algebraMap O C (φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1))) := by
      rw [hval, map_mul, map_mul, pow_succ']
      exact mul_le_mul_right (ht n _ le_rfl) _
    obtain ⟨a, haA, ha⟩ := exists_mem_valuation_le_of_mem_span v hv A φ (hA _)
      (ne_of_gt (lt_of_lt_of_le (pow_pos (pos_iff_ne_zero.mpr hvc) _) hlow))
    refine ⟨Function.update t n a, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt h)]
        exact htA i h
      · rw [Function.update_self]
        exact haA
    · intro m hm hmn
      rcases Nat.lt_or_eq_of_le hmn with h | rfl
      · have h' : m ≤ n := Nat.lt_succ_iff.mp h
        have : (Matrix.of fun b i : Fin m => Function.update t n a i (Fin.castLE hm b)) =
            Matrix.of fun b i : Fin m => t i (Fin.castLE hm b) := by
          ext b i
          simp [Function.update_of_ne (Nat.ne_of_lt (lt_of_lt_of_le i.isLt h'))]
        rw [this]
        exact ht m hm h'
      · rw [hdet]
        exact hlow.trans ha

theorem exists_leading_minors_ge :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
      v.Integers O → ∀ (r : ℕ) (A : Set (Fin r → O)) (c : O), c ≠ 0 →
      (∀ x : Fin r → O, c • x ∈ Submodule.span O A) →
      ∃ t : Fin r → Fin r → O, (∀ i, t i ∈ A) ∧ ∀ s : Fin r,
        v (algebraMap O C c) ^ (s.val + 1) ≤
          v (algebraMap O C (Matrix.of fun a i : Fin (s.val + 1) =>
            t (Fin.castLE s.isLt i) (Fin.castLE s.isLt a)).det) := by
  intro C _ v O _ _ hv r A c hc hA
  obtain ⟨t, htA, ht⟩ := exists_leading_minors_ge_of_le_rank v hv A hc hA r le_rfl
  exact ⟨fun i => t i, fun i => htA i i.isLt, fun s => ht (s.val + 1) s.isLt s.isLt⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPadicIntFrameChangeEtaleBasis
section
noncomputable section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder

namespace GlobalTheory.MomOne.FrameChange

variable {g : ℕ}

theorem beta_sum_left {κ : Type} [Fintype κ] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (c : κ → ℂ)
    (v : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    beta d Hm (∑ k, c k • v k) w = ∑ k, c k * beta d Hm (v k) w := by
  simp only [beta, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun _ => Finset.univ) (h := by simp)]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin g))) (t := (Finset.univ : Finset κ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem beta_conj (d : ℕ) {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z w : Fin g → ℂ) :
    conj (beta d Hm z w) = beta d Hm w z := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [beta, hf, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : conj (Hm j i) = Hm i j := h.apply i j
  rw [this]; ring

theorem eq_sum_frame (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ)
    (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (ha : ∀ i, (a i : ℂ) ≠ 0)
    (v : Fin g → ℂ) : v = ∑ i, (beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have key : ∀ (z : Fin g → ℂ) k, beta d Hm (∑ i, z i • x i) (x k) = z k * a k := by
    intro z k
    rw [beta_sum_left]
    simp [hx]
  have hli : LinearIndependent ℂ x := by
    refine Fintype.linearIndependent_iff.2 fun z hz k => ?_
    have h := key z k
    rw [hz] at h
    have h0 : beta d Hm 0 (x k) = 0 := by simp [beta, hf]
    rw [h0] at h
    exact (mul_eq_zero.1 h.symm).resolve_right (ha k)
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℂ (Set.range x) := by rw [hsp]; trivial
  obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key, mul_div_cancel_right₀ _ (ha i)]

def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zcHom_injective (q : ℕ) [Fact q.Prime] : Function.Injective (zcHom q) :=
  (algebraMap ℚ_[q] ℂ_[q]).injective.comp Subtype.val_injective

end GlobalTheory.MomOne.FrameChange

namespace GlobalTheory.MomOne
open FrameChange

theorem frameChange : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → Split S.d q → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → S.NNBasis q b → ∃ T : (Fin r → ℤ_[q]) ≃ₜ (Fin g → ℤ_[q]), ∀ A i, GlobalTheory.MomOne.zc (T A i) = ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j)) := by
  intro q _ ι g S x a r b hS hsp hxL hx ha hb
  obtain ⟨hd, hd7, hpos, -, -, -, hβ, -⟩ := hS
  obtain ⟨hbL, hgen, hind⟩ := hb
  have hq : q.Prime := Fact.out
  have hH : S.Hm.IsHermitian := hpos.isHermitian
  obtain ⟨⟨h1, -, hR⟩, hZ, -⟩ := okArith S.d q ι hd hd7 hsp
  let O : Subring ℂ :=
    { carrier := {z | InOK S.d z}
      one_mem' := h1
      zero_mem' := ⟨0, 0, by simp⟩
      mul_mem' := fun {u v} hu hv => (hR u v hu hv).2.1
      add_mem' := fun {u v} hu hv => (hR u v hu hv).1
      neg_mem' := fun {u} hu => (hR u u hu hu).2.2.1 }
  have hconj : ∀ u, InOK S.d u → InOK S.d (conj u) := fun u hu => (hR u u hu hu).2.2.2
  choose s hs c hc hsc using fun i => hgen (x i) (hxL i)
  have hs0 : ∀ i, (s i : ℂ) ≠ 0 := fun i h => by
    have h' : s i = 0 := by exact_mod_cast h
    have := hs i
    rw [h', Nat.coprime_zero_left] at this
    exact hq.one_lt.ne' this
  have ha0 : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).1.ne'

  have hMN : ∀ i k, ∑ j, beta S.d S.Hm (x i) (b j) * (conj (c k j) / (s k * a k)) = if i = k then 1 else 0 := by
    intro i k
    have e := beta_sum_left S.d S.Hm (c k) b (x i)
    have e2 := beta_sum_left S.d S.Hm (fun _ : Unit => (s k : ℂ)) (fun _ => x k) (x i)
    simp only [Finset.univ_unique, Finset.sum_singleton] at e2
    rw [← hsc k, e2] at e
    have e3 := congrArg conj e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, beta_conj S.d hH, map_natCast] at e3
    simp_rw [← mul_div_assoc, mul_comm (beta _ _ _ _)]
    rw [← Finset.sum_div, ← e3, hx]
    split_ifs with h
    · subst h; exact div_self (mul_ne_zero (hs0 i) (ha0 i))
    · simp
  have hNM : ∀ j l, ∑ i, (conj (c i j) / (s i * a i)) * beta S.d S.Hm (x i) (b l) = if j = l then 1 else 0 := by
    intro j l
    set P : ℂ := ∏ i, ((s i : ℂ) * a i) with hP
    have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hs0 i) (ha0 i)
    let e : Fin r → ℂ := fun j => ∑ i, c i j / (s i * a i) * beta S.d S.Hm (b l) (x i)
    have hmem : ∀ j, P * (e j - if j = l then 1 else 0) ∈ O := by
      intro j
      have hPO : P ∈ O := O.prod_mem fun i _ => O.mul_mem (natCast_mem O _) (natCast_mem O _)
      rw [mul_sub, Finset.mul_sum]
      refine O.sub_mem (O.sum_mem fun i _ => ?_) (O.mul_mem hPO (by split_ifs; exacts [O.one_mem, O.zero_mem]))
      have : P * (c i j / (s i * a i) * beta S.d S.Hm (b l) (x i)) =
          (∏ k ∈ Finset.univ.erase i, ((s k : ℂ) * a k)) * c i j * beta S.d S.Hm (b l) (x i) := by
        rw [hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        have := hs0 i
        have := ha0 i
        field_simp
      rw [this]
      exact O.mul_mem (O.mul_mem (O.prod_mem fun i _ => O.mul_mem (natCast_mem O _) (natCast_mem O _)) (hc i j))
        (hβ _ (hbL l) _ (hxL i))
    have hsum : ∑ j, e j • b j = b l := by
      conv_rhs => rw [eq_sum_frame S.d S.Hm x a hx ha0 (b l)]
      simp only [e, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hxi : x i = (s i : ℂ)⁻¹ • ∑ j, c i j • b j := by
        rw [← hsc i, smul_smul, inv_mul_cancel₀ (hs0 i), one_smul]
      generalize beta S.d S.Hm (b l) (x i) = t
      rw [hxi, smul_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      have := hs0 i
      have := ha0 i
      field_simp
    have h0 := hind _ hmem (by
      simp only [mul_smul, sub_smul, ← Finset.smul_sum, Finset.sum_sub_distrib, hsum]
      simp [ite_smul]) j
    have h2 : e j = if j = l then 1 else 0 := sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hP0)
    have h3 := congrArg conj h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_sum, map_mul, map_div₀, beta_conj S.d hH, map_natCast] at h3
    rw [h3]
    split_ifs <;> simp

  choose m hm using fun i j => (hZ _ (hβ _ (hxL i) _ (hbL j))).1
  choose n hn using fun i j => (hZ _ (hconj _ (hc i j))).1
  have hu : ∀ i, ∃ u : ℤ_[q], ι ((s i * a i : ℂ)⁻¹) = zcHom q u := by
    intro i
    have hun : IsUnit ((s i * a i : ℕ) : ℤ_[q]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Coprime.mul_left (hs i) (ha i).2).symm
    obtain ⟨u, hu⟩ := hun.exists_left_inv
    refine ⟨u, ?_⟩
    have := congrArg (zcHom q) hu
    rw [map_mul, map_natCast, map_one] at this
    rw [map_inv₀, eq_inv_of_mul_eq_one_left this]
    simp
  choose u hu using hu
  let M : Matrix (Fin g) (Fin r) ℤ_[q] := Matrix.of m
  let N : Matrix (Fin r) (Fin g) ℤ_[q] := Matrix.of fun j i => n i j * u i
  have hM : ∀ i j, zcHom q (M i j) = ι (beta S.d S.Hm (x i) (b j)) := fun i j => (hm i j).symm
  have hN : ∀ j i, zcHom q (N j i) = ι (conj (c i j) / (s i * a i)) := fun j i => by
    rw [div_eq_mul_inv, map_mul, hu, hn]
    exact map_mul (zcHom q) _ _
  have e1 : M * N = 1 := by
    apply Matrix.ext
    intro i k
    apply zcHom_injective q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp_rw [map_mul, hM, hN, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hMN, Matrix.one_apply]
    split_ifs <;> simp
  have e2 : N * M = 1 := by
    apply Matrix.ext
    intro i k
    apply zcHom_injective q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp_rw [map_mul, hM, hN, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hNM, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨{ toFun := M.mulVec
            invFun := N.mulVec
            left_inv := fun A => by rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
            right_inv := fun A => by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
            continuous_toFun := continuous_const.matrix_mulVec continuous_id
            continuous_invFun := continuous_const.matrix_mulVec continuous_id }, fun A i => ?_⟩
  show zcHom q (∑ j, M i j * A j) = ∑ j, zcHom q (A j) * _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hM, mul_comm]

end GlobalTheory.MomOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSmallInPrimePow
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem thue_normSq (d e : ℕ) (he : d + 1 = 4 * e) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + e * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have he' : (d : ℝ) + 1 = 4 * e := by exact_mod_cast he
  have h1 : ((u : ℂ) + (v : ℂ) * wK d).re = u + v / 2 := by
    simp [wK]; ring
  have h2 : ((u : ℂ) + (v : ℂ) * wK d).im = v * Real.sqrt d / 2 := by
    simp [wK]; ring
  rw [Complex.normSq_apply, h1, h2]
  push_cast
  linear_combination ((v : ℝ) ^ 2 / 4) * hs + ((v : ℝ) ^ 2 / 4) * he'

theorem thue_norm_zc {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]

theorem thue_pigeon {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) (k : ℕ) :
    ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧ u ^ 2 ≤ (q : ℤ) ^ k ∧ v ^ 2 ≤ (q : ℤ) ^ k ∧
      ‖(u : ℤ_[q]) + (v : ℤ_[q]) * a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
  have hq : q.Prime := Fact.out
  haveI : NeZero (q ^ k) := ⟨pow_ne_zero _ hq.ne_zero⟩
  set m := Nat.sqrt (q ^ k) with hm
  let f : Fin (m + 1) × Fin (m + 1) → ZMod (q ^ k) := fun p =>
    PadicInt.toZModPow k (((p.1 : ℕ) : ℤ_[q]) + ((p.2 : ℕ) : ℤ_[q]) * a)
  have hcard : Fintype.card (ZMod (q ^ k)) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact Nat.lt_succ_sqrt _
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hm2 : ((m : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    have := Nat.sqrt_le' (q ^ k)
    exact_mod_cast this
  have hb : ∀ i j : Fin (m + 1), (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    intro i j
    have hi := i.2
    have hj := j.2
    refine le_trans ?_ hm2
    apply sq_le_sq' <;> omega
  refine ⟨((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ), ?_, hb _ _, hb _ _, ?_⟩
  · by_contra h
    push_neg at h
    apply hxy
    ext
    · have := h.1; omega
    · have := h.2; omega
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have : PadicInt.toZModPow k ((((x.1 : ℕ) : ℤ_[q]) + ((x.2 : ℕ) : ℤ_[q]) * a) -
        (((y.1 : ℕ) : ℤ_[q]) + ((y.2 : ℕ) : ℤ_[q]) * a)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hf
    rw [← this]
    congr 1
    push_cast
    ring

theorem exists_small_in_prime_pow : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → ∀ k : ℕ, ∃ (β : ℂ) (N : ℕ), InOK d β ∧ β ≠ 0 ∧ ‖ι β‖ ≤ (q : ℝ) ^ (-(k : ℤ)) ∧ (N : ℂ) = β * conj β ∧ N ≤ (d + 3) * q ^ k := by
  intro d q _ ι hd h16 hs k
  obtain ⟨⟨-, hw, -⟩, h2, -⟩ := _root_.GlobalTheory.MomOne.okArith d q ι hd h16 hs
  obtain ⟨⟨a, ha⟩, -⟩ := h2 _ hw
  obtain ⟨u, v, huv, hu, hv, hn⟩ := thue_pigeon a k
  obtain ⟨e, he⟩ : ∃ e : ℕ, d + 1 = 4 * e := ⟨(d + 1) / 4, by omega⟩
  have he1 : (1 : ℤ) ≤ e := by omega
  have hed : (e : ℤ) ≤ d := by omega
  have hpos : 0 < u ^ 2 + u * v + e * v ^ 2 := by
    have h3 : v ^ 2 ≤ e * v ^ 2 := by nlinarith [sq_nonneg v]
    have h4 : 0 < u ^ 2 + v ^ 2 := by
      rcases huv with h | h
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg v]
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg u]
    nlinarith [sq_nonneg (u + v)]
  have hN := thue_normSq d e he u v
  obtain ⟨N, hNe⟩ := Int.eq_ofNat_of_zero_le hpos.le
  refine ⟨(u : ℂ) + (v : ℂ) * wK d, N, ⟨u, v, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, map_zero] at hN
    have : u ^ 2 + u * v + e * v ^ 2 = 0 := by exact_mod_cast hN.symm
    omega
  · have : ι ((u : ℂ) + (v : ℂ) * wK d) = zc ((u : ℤ_[q]) + (v : ℤ_[q]) * a) := by
      rw [map_add (f := _), map_mul, ha]
      simp [zc]
    rw [this, thue_norm_zc]
    exact hn
  · rw [Complex.mul_conj, hN, hNe]
    simp
  · have h5 : (e : ℤ) * v ^ 2 ≤ d * (q : ℤ) ^ k :=
      mul_le_mul hed hv (sq_nonneg v) (by positivity)
    have h6 : (N : ℤ) ≤ (d + 3) * (q : ℤ) ^ k := by
      rw [← hNe]
      nlinarith [sq_nonneg (u - v), sq_nonneg u, sq_nonneg v]
    exact_mod_cast h6

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.InvDerMap

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv i f) = pderiv i (MvPowerSeries.map φ f) := by
  ext m
  simp [coeff_map, coeff_pderiv]

theorem map_ev_axis {d : ℕ} (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := 1) ![pt R d 0, 0] g) =
      ev (n := 1) ![pt S d 0, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  have h : HasSubst (fun p : Fin 2 × Fin d => (![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    rintro ⟨j, i⟩
    fin_cases j <;> simp [pt]
  rw [MvPowerSeries.map_subst h]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> simp [pt]

theorem map_Dof {d : ℕ} (F : Fin d → PS R 2 d) (u : Fin d → R) (f : PS R 1 d) :
    MvPowerSeries.map φ (Dof F u f) =
      Dof (fun i => MvPowerSeries.map φ (F i)) (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dof, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]

theorem map_Dof_iterate {d : ℕ} (F : Fin d → PS R 2 d) (u : Fin d → R) (n : ℕ) (f : PS R 1 d) :
    MvPowerSeries.map φ ((Dof F u)^[n] f) =
      (Dof (fun i => MvPowerSeries.map φ (F i)) (fun i => φ (u i)))^[n] (MvPowerSeries.map φ f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_Dof, ih]

end GlobalTheory.InvDerMap

namespace GlobalTheory

theorem map_dmonOf (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (F : Fin d → PS R 2 d)
    (ι : Type) [Fintype ι] (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R 1 d) :
    MvPowerSeries.map φ (DmonOf F u m f) =
      DmonOf (fun i => MvPowerSeries.map φ (F i)) (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, InvDerMap.map_Dof_iterate, ih]

end GlobalTheory
end
end

