module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrix
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.LocalComponent

theorem exists_idem_away (D : D7) {q : ℕ} (hq : q.Prime) :
    ∃ f ∈ OhE D, f * f = f ∧ sgA D f = f ∧ (∀ k : ℕ, ∃ w ∈ OhE D, f = (q : AE D) ^ k * w) ∧
      ∀ n : ℕ, n.Coprime q → ∃ w ∈ OhE D, 1 - f = (n : AE D) * w := by
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := GlobalTheory.IdealIdele.exists_idem (OhE D) hsep hcpl q hq.pos
  have h2 : ∀ k : ℕ, ∃ w ∈ OhE D, f = (q : AE D) ^ k * w := by
    intro k
    induction k with
    | zero => exact ⟨f, hf, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, h⟩ := ih
      refine ⟨v * w, mul_mem hv hw, ?_⟩
      calc f = f * f := hff.symm
        _ = ((q : AE D) ^ k * v) * ((q : AE D) * w) := by rw [← h, ← hfw]
        _ = _ := by ring
  have h4 : ∀ n : ℕ, n.Coprime q → ∃ w ∈ OhE D, 1 - f = (n : AE D) * w := fun n hn =>
    h3 n (Nat.pos_of_ne_zero (by rintro rfl; exact hq.ne_one (by simpa using hn))) hn.symm
  refine ⟨f, hf, hff, ?_, h2, h4⟩
  have key : f * (1 - sgA D f) = 0 := by
    refine hsep _ fun N hN => ?_
    obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.ne_one
    obtain ⟨u, hu, e1⟩ := h2 a
    obtain ⟨v, hv, e2⟩ := h4 n' ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm
    have e3 := congrArg (sgA D) e2
    rw [map_sub, map_one, map_mul, map_natCast] at e3
    refine ⟨u * sgA D v, mul_mem hu (VacMove.sgA_mem D hv), ?_⟩
    rw [e3]
    push_cast
    linear_combination ((n' : AE D) * sgA D v) * e1
  have key' := congrArg (sgA D) key
  rw [map_mul, map_sub, map_one, VacMove.sgA_sgA, map_zero] at key'
  linear_combination key' - key

theorem exists_common_denom (D : D7) {q : ℕ} (hq : q.Prime) {n : ℕ} (y : Fin n → AE D) :
    ∃ a m : ℕ, m.Coprime q ∧ ∀ i, (q : AE D) ^ a * (m : AE D) * y i ∈ OhE D := by
  choose N hN hy using fun i => VacMove.exists_nat_denom D (y i)
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hN i).ne'
  obtain ⟨a, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hP q hq.ne_one
  refine ⟨a, m, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm, fun i => ?_⟩
  obtain ⟨c, hc⟩ : N i ∣ ∏ i, N i := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have e' : (q : AE D) ^ a * (m : AE D) = (c : AE D) * (N i : AE D) := by
    have := congrArg (Nat.cast : ℕ → AE D) (e.symm.trans hc)
    push_cast at this
    rw [this, mul_comm]
  rw [e', mul_assoc]
  exact mul_mem (natCast_mem _ c) (hy i)

theorem glue_mul {A : Type} [CommRing A] {n : ℕ} {f : A} (hf : f * f = f) {σ τ : Matrix (Fin n) (Fin n) A}
    (h : σ * τ = 1) : ((1 - f) • σ + f • (1 : Matrix (Fin n) (Fin n) A)) * ((1 - f) • τ + f • 1) = 1 := by
  have h1 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : f * (1 - f) = 0 := by linear_combination -hf
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, h1, h2, h3, hf, zero_smul,
    Matrix.mul_one, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem mulVec_inc_smul (D : D7) {n : ℕ} (H : Matrix (Fin n) (Fin n) (AE D)) (c : ℕ) (x : Fin n → D.host.E)
    (i : Fin n) : H.mulVec (fun j => inc D (((c : D.host.E) • x) j)) i =
      (c : AE D) * H.mulVec (fun j => inc D (x j)) i := by
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring


set_option maxHeartbeats 1000000 in
theorem exists_local_component : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 → ∃ g : GA D n, (∀ p : ℕ, p.Prime → p ≠ q → TrivAt D p (g : GL (Fin n) (AE D))) ∧ ∀ (h : GA D n) (B C : Lat D n), Moves D (h : GL (Fin n) (AE D)) B → EqAway D q B C → SAt D q s B C → Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) C := by
  intro D n q hq s hs
  obtain ⟨f, hf, hff, hsg, h2, h3⟩ := exists_idem_away D hq
  have hs' : cT D s * s = 1 := mul_eq_one_comm.1 hs
  have a : s.map (inc D) * (cT D s).map (inc D) = 1 := by
    rw [← Matrix.map_mul, hs, Matrix.map_one _ (map_zero _) (map_one _)]
  have b : (cT D s).map (inc D) * s.map (inc D) = 1 := by
    rw [← Matrix.map_mul, hs', Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin n) (AE D) := ⟨_, _, glue_mul hff a, glue_mul hff b⟩
  have hg : g ∈ GA D n := by
    rw [PtsMem.mem_GA]
    have e : ((g : Matrix (Fin n) (Fin n) (AE D)).map (sgA D)).transpose =
        (1 - f) • (cT D s).map (inc D) + f • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
      ext i j
      change sgA D ((1 - f) * inc D (s j i) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) j i) =
        (1 - f) * inc D (D.host.conj (s j i)) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) i j
      rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, hsg, PtsMem.sgA_inc]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
    rw [e]
    exact glue_mul hff b
  refine ⟨⟨g, hg⟩, fun p hp hpq i j => ?_, ?_⟩
  · have hz : ZeroAt D p (1 - f) := fun k => by
      obtain ⟨w, hw, e⟩ := h3 (p ^ k) (Nat.Coprime.pow_left k ((Nat.coprime_primes hp hq).2 hpq))
      exact ⟨1, one_pos, by simp, w, hw, by rw [e]; push_cast; ring⟩
    have := VacMove.zeroAt_mul D hp hz (inc D (s i j) - (1 : Matrix (Fin n) (Fin n) (AE D)) i j)
    convert this using 1
    change (1 - f) * inc D (s i j) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) i j - _ = _
    ring
  · rintro h B C hB ⟨k, hBC, hCB⟩ ⟨m, hm, hsB, hsC⟩ x
    set H : Matrix (Fin n) (Fin n) (AE D) :=
      (((h : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) with hH
    have hB' : ∀ (c : ℕ) (y : Fin n → D.host.E), (c : D.host.E) • y ∈ B ↔
        ∀ i, (c : AE D) * H.mulVec (fun j => inc D (y j)) i ∈ OhE D := fun c y => by
      rw [hB]
      exact forall_congr' fun i => by rw [mulVec_inc_smul]
    have e : ∀ i, ((((((⟨g, hg⟩ : GA D n) * h : GA D n) : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) :
        Matrix (Fin n) (Fin n) (AE D)).mulVec (fun j => inc D (x j))) i =
        (1 - f) * H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i + f * H.mulVec (fun j => inc D (x j)) i := by
      intro i
      rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      change H.mulVec (((1 - f) • (cT D s).map (inc D) + f • (1 : Matrix (Fin n) (Fin n) (AE D))).mulVec _) i = _
      have e1 : ((cT D s).map (inc D)).mulVec (fun j => inc D (x j)) = fun j => inc D ((cT D s).mulVec x j) :=
        funext fun j => (RingHom.map_mulVec (inc D) (cT D s) x j).symm
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, e1, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul]
      rfl
    simp only [e]
    constructor
    · intro hx i
      obtain ⟨w, hw, e1⟩ := h3 m hm
      obtain ⟨v, hv, e2⟩ := h2 k
      have m1 := (hB' m _).1 (hsC x hx) i
      have m2 := (hB' (q ^ k) x).1 (by simpa using hCB x hx) i
      have := add_mem (mul_mem hw m1) (mul_mem hv m2)
      convert this using 1
      push_cast
      rw [e1]
      linear_combination H.mulVec (fun j => inc D (x j)) i * e2
    · intro hx
      obtain ⟨a1, n1, hn1, d1⟩ := exists_common_denom D hq (H.mulVec (fun j => inc D ((cT D s).mulVec x j)))
      obtain ⟨a2, n2, hn2, d2⟩ := exists_common_denom D hq (H.mulVec (fun j => inc D (x j)))
      have m1 : (n1 : D.host.E) • (cT D s).mulVec x ∈ B := (hB' n1 _).2 fun i => by
        obtain ⟨v, hv, e2⟩ := h2 a1
        have := add_mem (mul_mem (mul_mem (natCast_mem _ n1) (sub_mem (one_mem _) hf)) (hx i)) (mul_mem hv (d1 i))
        convert this using 1
        linear_combination ((n1 : AE D) * H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i) * e2 -
          (n1 : AE D) * (H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i - H.mulVec (fun j => inc D (x j)) i) * hff
      have m2 : ((q ^ a2 : ℕ) : D.host.E) • x ∈ B := (hB' (q ^ a2) _).2 fun i => by
        obtain ⟨w, hw, e1⟩ := h3 n2 hn2
        have := add_mem (mul_mem (mul_mem (pow_mem (natCast_mem _ q) a2) hf) (hx i)) (mul_mem hw (d2 i))
        convert this using 1
        push_cast
        linear_combination ((q : AE D) ^ a2 * H.mulVec (fun j => inc D (x j)) i) * e1 +
          (q : AE D) ^ a2 * (H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i - H.mulVec (fun j => inc D (x j)) i) * hff
      have c1 := hsB _ m1
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hs, Matrix.one_mulVec, smul_smul] at c1
      have c2 := hBC _ m2
      rw [smul_smul] at c2
      have hcop : IsCoprime ((m * n1 : ℕ) : ℤ) ((q ^ (k + a2) : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ (Nat.Coprime.mul_left hm hn1))
      obtain ⟨u, v, huv⟩ := hcop
      have huv' := congrArg (Int.cast : ℤ → D.host.E) huv
      push_cast at huv' c2
      have := add_mem (zsmul_mem c1 u) (zsmul_mem c2 v)
      convert this using 1
      ext j
      simp only [← Int.cast_smul_eq_zsmul D.host.E, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-x j) * huv'

end GlobalTheory.LocalComponent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecomposition
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

open Filter
open scoped Topology

noncomputable section

namespace GlobalTheory.ThetaTranslDecomp

variable {Λ : AddSubgroup ℂ}

private lemma u1_apply_eq_mul_u1_one (ω : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω G z = G (z + ω) * U1 Λ ω (fun _ => (1 : ℂ)) z := by
  simp only [U1, one_mul]

private lemma u1_one_ne_zero (ω z : ℂ) : U1 Λ ω (fun _ => (1 : ℂ)) z ≠ 0 := by
  simp only [U1, one_mul]
  exact Complex.exp_ne_zero _

private lemma u1_one_add_mul_comm_cexp (a b z : ℂ) :
    U1 Λ a (fun _ => (1 : ℂ)) (z + b) * U1 Λ b (fun _ => (1 : ℂ)) z =
      U1 Λ a (fun _ => (1 : ℂ)) z * U1 Λ b (fun _ => (1 : ℂ)) (z + a) *
        Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ)) := by
  simp only [U1, one_mul, ← Complex.exp_add]
  congr 1
  ring

private lemma u1_one_add_mul_eq_u1_one_add_mul_cexp (a b z : ℂ) :
    U1 Λ a (fun _ => (1 : ℂ)) (z + b) * U1 Λ b (fun _ => (1 : ℂ)) z =
      U1 Λ (a + b) (fun _ => (1 : ℂ)) z *
        Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) := by
  simp only [U1, one_mul, ← Complex.exp_add, map_add (f := _)]
  congr 1
  ring

private lemma cexp_pi_mul_conj_sub_div_area_eq_one_of_mem (hΛ : IsLat Λ) {a b : ℂ} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ)) = 1 := by
  obtain ⟨z0, hz0⟩ := hΛ.dense_compl.nonempty
  have hs0 : sgStar Λ z0 ≠ 0 := fun h0 => hz0 ((hΛ.sg_eq_zero z0).1 h0)
  have hsq : ∀ c : ℂ, (if c / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 = 1 := by
    intro c
    split_ifs <;> norm_num
  have l1 := hΛ.sg_law (add_mem ha hb) z0
  have l2 := hΛ.sg_law ha (z0 + b)
  have l3 := hΛ.sg_law hb z0
  rw [u1_apply_eq_mul_u1_one] at l1 l2 l3
  have key : (if (a + b) / 2 ∈ Λ then (1 : ℂ) else -1) *
      Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) =
      (if a / 2 ∈ Λ then (1 : ℂ) else -1) * (if b / 2 ∈ Λ then (1 : ℂ) else -1) := by
    apply mul_right_cancel₀ hs0
    calc _ = sgStar Λ (z0 + (a + b)) * U1 Λ (a + b) (fun _ => (1 : ℂ)) z0 *
          Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) := by
          rw [l1]; ring
      _ = sgStar Λ (z0 + b + a) * (U1 Λ a (fun _ => (1 : ℂ)) (z0 + b) * U1 Λ b (fun _ => (1 : ℂ)) z0) := by
          rw [u1_one_add_mul_eq_u1_one_add_mul_cexp, show z0 + b + a = z0 + (a + b) by ring]; ring
      _ = _ := by rw [← mul_assoc, l2, mul_assoc, l3]; ring
  have h2 : Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) /
      (2 * (area Λ : ℂ))) ^ 2 = 1 := by
    have := congrArg (· ^ 2) key
    simp only [mul_pow, hsq, one_mul] at this
    exact this
  rw [show (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ) =
      (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) +
      (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) by ring,
    Complex.exp_add, ← sq, h2]

theorem ratio_pow_add (hΛ : IsLat Λ) {t : ℂ} {N : ℕ} (hN : 0 < N) (ht : (N : ℂ) * t ∈ Λ)
    (z : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    (U1 Λ t (sgStar Λ) (z + l) / sgStar Λ (z + l)) ^ N = (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N := by
  by_cases hz : z ∈ Λ
  · have h1 : sgStar Λ z = 0 := (hΛ.sg_eq_zero z).2 hz
    have h2 : sgStar Λ (z + l) = 0 := (hΛ.sg_eq_zero _).2 (add_mem hz hl)
    rw [h1, h2, div_zero, div_zero]
  · have hs : sgStar Λ z ≠ 0 := fun h0 => hz ((hΛ.sg_eq_zero z).1 h0)
    have hzl : z + l ∉ Λ := fun h' => hz (by simpa using sub_mem h' hl)
    have hsl : sgStar Λ (z + l) ≠ 0 := fun h0 => hzl ((hΛ.sg_eq_zero _).1 h0)
    have hsn : (if l / 2 ∈ Λ then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
    have la := hΛ.sg_law hl (z + t)
    have lb := hΛ.sg_law hl z
    rw [u1_apply_eq_mul_u1_one] at la lb
    have hK := u1_one_add_mul_comm_cexp (Λ := Λ) t l z
    have e3 := u1_one_ne_zero (Λ := Λ) l z
    have e4 := u1_one_ne_zero (Λ := Λ) l (z + t)
    have hA : sgStar Λ (z + l + t) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ (z + t) /
        U1 Λ l (fun _ => (1 : ℂ)) (z + t) := by
      rw [eq_div_iff e4, show z + l + t = z + t + l by ring]
      exact la
    have hB : sgStar Λ (z + l) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ z /
        U1 Λ l (fun _ => (1 : ℂ)) z := by
      rw [eq_div_iff e3]
      exact lb
    have hF : U1 Λ t (fun _ => (1 : ℂ)) (z + l) = U1 Λ t (fun _ => (1 : ℂ)) z *
        U1 Λ l (fun _ => (1 : ℂ)) (z + t) *
        Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) /
        U1 Λ l (fun _ => (1 : ℂ)) z := by
      rw [eq_div_iff e3]
      exact hK
    have hbase : U1 Λ t (sgStar Λ) (z + l) / sgStar Λ (z + l) = U1 Λ t (sgStar Λ) z / sgStar Λ z *
        Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) := by
      rw [u1_apply_eq_mul_u1_one, u1_apply_eq_mul_u1_one t (sgStar Λ) z, hA, hF, hB]
      field_simp
    rw [hbase, mul_pow, ← Complex.exp_nat_mul,
      show (N : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) =
        (Real.pi : ℂ) * ((N : ℂ) * t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) ((N : ℂ) * t)) / (area Λ : ℂ) by
        rw [map_mul, map_natCast]; ring,
      cexp_pi_mul_conj_sub_div_area_eq_one_of_mem hΛ ht hl, mul_one]

theorem sqThD_eq (hΛ : IsLat Λ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {v z : ℂ}
    (hv : v ∉ Λ) (hz : z ∉ Λ) : sqThD Λ v z = sgStar Λ z ^ 3 * L.derivWeierstrassP z := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hzL : z ∉ L.lattice := fun hz' => hz ((h z).2 hz')
  have hev : sqTh Λ v =ᶠ[𝓝 z] fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v) := by
    filter_upwards [hU.mem_nhds hzL] with w hw
    have hwΛ : w ∉ Λ := fun h' => hw ((h w).1 h')
    rw [hΛ.sqTh_eq hv hwΛ, GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]
  have hsg : HasDerivAt (sgStar Λ) (deriv (sgStar Λ) z) z := (hΛ.differentiable z).hasDerivAt
  have hwp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    have hd : DifferentiableAt ℂ L.weierstrassP z :=
      (L.analyticOnNhd_weierstrassP z hzL).differentiableAt
    have := hd.hasDerivAt
    rwa [L.deriv_weierstrassP] at this
  have hD : HasDerivAt (fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v)) _ z :=
    (hsg.pow 2).mul (hwp.sub_const (L.weierstrassP v))
  unfold sqThD
  rw [hev.deriv_eq, hD.deriv, hΛ.sqTh_eq hv hz,
    GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]
  norm_num
  ring

theorem exists_decomp : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (t : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ Λ →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), N ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  intro Λ hΛ t N hN ht v hv
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hσ : Differentiable ℂ (sgStar Λ) := hΛ.differentiable
  have hσ0 : ∀ w, sgStar Λ w = 0 ↔ w ∈ Λ := hΛ.sg_eq_zero
  have hU : Differentiable ℂ (U1 Λ t (sgStar Λ)) := by
    unfold U1
    fun_prop
  have hmer : Meromorphic (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) := fun x =>
    ((hU.analyticAt x).meromorphicAt.div (hσ.analyticAt x).meromorphicAt).pow N
  have hcont : ∀ a, a ∉ Λ → ContinuousAt (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) a :=
    fun a ha => ((hU a).continuousAt.div (hσ a).continuousAt (fun h0 => ha ((hσ0 a).1 h0))).pow N
  have hd : ∀ a ∉ L.lattice, ∃ c, Tendsto (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (𝓝[≠] a) (𝓝 c) :=
    fun a ha => ⟨_, (hcont a (fun h' => ha ((hL a).1 h'))).tendsto.mono_left nhdsWithin_le_nhds⟩
  have hp : ∀ z, ∀ l ∈ L.lattice, (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (z + l) =
      (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) z :=
    fun z l hl => ratio_pow_add hΛ hN ht z ((hL l).2 hl)
  obtain ⟨A, B, hAB⟩ := GlobalTheory.EllipticPoles.no_pole_case L hmer hd hp
  have hpt : ∀ z, z ∉ Λ → (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N =
      A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    intro z hzΛ
    have hz : z ∉ L.lattice := fun h' => hzΛ ((hL z).2 h')
    have t1 := (hcont z hzΛ).tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    have hc2 : ContinuousAt (fun w => A.eval (L.weierstrassP w) + B.eval (L.weierstrassP w) * L.derivWeierstrassP w) z :=
      (A.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).add
        ((B.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).mul
          (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt)
    exact tendsto_nhds_unique (t1.congr' (hAB z)) (hc2.tendsto.mono_left nhdsWithin_le_nhds)
  have hS : Differentiable ℂ (sqTh Λ v) := hΛ.differentiable_sqTh v
  have hdS : Continuous (deriv (sqTh Λ v)) := (hS.contDiff (n := 1)).continuous_deriv le_rfl
  have hdσ : Continuous (deriv (sgStar Λ)) := (hσ.contDiff (n := 1)).continuous_deriv le_rfl
  have hT : Continuous (sqThD Λ v) := by
    unfold sqThD
    exact (hσ.continuous.mul hdS).sub ((continuous_const.mul hdσ).mul hS.continuous)
  set P := A.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hP
  set Q := B.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hQ
  refine ⟨max (max P.natDegree Q.natDegree) N, fun i => P.coeff i, fun j => Q.coeff j, ?_, ?_⟩
  · have := le_max_right (max P.natDegree Q.natDegree) N
    omega
  have hIP : P.natDegree < max (max P.natDegree Q.natDegree) N + 1 := by
    have := le_max_left (max P.natDegree Q.natDegree) N
    have := le_max_left P.natDegree Q.natDegree
    omega
  have hIQ : Q.natDegree < max (max P.natDegree Q.natDegree) N + 1 := by
    have := le_max_left (max P.natDegree Q.natDegree) N
    have := le_max_right P.natDegree Q.natDegree
    omega
  have hNI : N ≤ 2 * max (max P.natDegree Q.natDegree) N + 3 := by
    have := le_max_right (max P.natDegree Q.natDegree) N
    omega
  generalize max (max P.natDegree Q.natDegree) N = I at hIP hIQ hNI ⊢
  have heq : (fun z => sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N) =
      fun z => ∑ i ∈ Finset.range (I + 1), P.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), Q.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
    refine Continuous.ext_on hΛ.dense_compl ((hσ.continuous.pow _).mul (hU.continuous.pow _))
      ((continuous_finsetSum _ fun i _ => continuous_const.mul ((hσ.continuous.pow _).mul (hS.continuous.pow _))).add
        (continuous_finsetSum _ fun j _ =>
          continuous_const.mul (((hσ.continuous.pow _).mul (hS.continuous.pow _)).mul hT))) ?_
    intro z hz
    have hzΛ : z ∉ Λ := hz
    have hs : sgStar Λ z ≠ 0 := fun h0 => hzΛ ((hσ0 z).1 h0)
    have hz' : z ∉ L.lattice := fun h' => hzΛ ((hL z).2 h')
    have hq := hpt z hzΛ
    have hApt : A.eval (L.weierstrassP z) = P.eval (L.weierstrassP z - L.weierstrassP v) := by
      rw [hP, Polynomial.eval_comp]; simp
    have hBpt : B.eval (L.weierstrassP z) = Q.eval (L.weierstrassP z - L.weierstrassP v) := by
      rw [hQ, Polynomial.eval_comp]; simp
    rw [hApt, hBpt, Polynomial.eval_eq_sum_range' hIP, Polynomial.eval_eq_sum_range' hIQ] at hq
    have hUN : U1 Λ t (sgStar Λ) z ^ N = sgStar Λ z ^ N * (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hs)]
    simp only
    rw [hUN, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hNI, hq,
      sqThD_eq hΛ L hL hv hzΛ, hΛ.sqTh_eq hv hzΛ, GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL,
      mul_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_pow, ← pow_mul, show 2 * I + 3 = (2 * (I - i) + 3) + 2 * i by omega]
      ring
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_pow, ← pow_mul, show 2 * I + 3 = 2 * (I - j) + 2 * j + 3 by omega]
      ring
  intro z
  exact congrFun heq z

end GlobalTheory.ThetaTranslDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexCompletedStandardNeZero
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem relIndex_ne_zero_of_denom {A ι κ : Type} [CommRing A] [Finite ι] [Finite κ] (S : Subring A) (I : AddSubgroup A) (k n : ℕ)
    (hk : IsUnit (k : A)) (hfin : Finite (S ⧸ Ideal.span {((k * n : ℕ) : S)})) (hn : ∀ s ∈ S, (n : A) * s ∈ I)
    (L T : AddSubgroup (Matrix ι κ A)) (hL : ∀ ζ : Matrix ι κ A, (∀ i j, ζ i j ∈ I) → ζ ∈ L)
    (hT : ∀ ζ ∈ T, ∀ i j, (k : A) * ζ i j ∈ S) : L.relIndex T ≠ 0 := by
  let φ : T →+ (ι → κ → S ⧸ Ideal.span {((k * n : ℕ) : S)}) :=
    AddMonoidHom.mk' (fun ζ i j => Ideal.Quotient.mk _ ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩) (fun x y => by
      funext i j
      rw [Pi.add_apply, Pi.add_apply, ← map_add (f := _)]
      congr 1
      exact Subtype.ext (mul_add _ _ _))
  have hle : φ.ker ≤ L.addSubgroupOf T := by
    intro ζ hζ
    rw [AddSubgroup.mem_addSubgroupOf]
    refine hL _ fun i j => ?_
    have h0 : Ideal.Quotient.mk (Ideal.span {((k * n : ℕ) : S)}) ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩ = 0 :=
      congrFun (congrFun ((AddMonoidHom.mem_ker).1 hζ) i) j
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : (s : A) * (((k * n : ℕ) : S) : A) = (k : A) * ζ.1 i j := congrArg Subtype.val hs
    have h2 : ζ.1 i j = (n : A) * s := by
      apply hk.mul_left_cancel
      rw [← h1]
      push_cast
      ring
    rw [h2]
    exact hn _ s.2
  have : φ.ker.FiniteIndex := AddSubgroup.finiteIndex_ker φ
  exact (AddSubgroup.finiteIndex_of_le hle).index_ne_zero

theorem idx_latA_ne_zero : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m : ℕ), 0 < m → ∀ T : Submodule (𝓞 D.host.E) (XA D N N'), (∀ ζ ∈ T, m • ζ ∈ latA D cc N N') → idx (latA D cc N N') T ≠ 0 := by
  intro D hD cc δ hc N N' m hm T hT
  obtain ⟨-, -, -, -, ⟨m₁, hm₁, h₁⟩, m₂, hm₂, h₂⟩ := _root_.GlobalTheory.CompletedLattice.completed_lattice D hD cc δ hc N N'
  have hk : 0 < m₁ * m := Nat.mul_pos hm₁ hm
  have hu : IsUnit ((m₁ * m : ℕ) : AE D) := by
    have := (IsUnit.mk0 ((m₁ * m : ℕ) : D.host.E) (Nat.cast_ne_zero.2 hk.ne')).map (inc D)
    rwa [map_natCast] at this
  refine relIndex_ne_zero_of_denom (OhE D) (IhE D cc) (m₁ * m) m₂ hu
    (GlobalTheory.HeckeVal.finite_quot D _ (Nat.mul_pos hk hm₂)) h₂ _ _ (fun ζ h => mem_latA.2 h) fun ζ hζ i j => ?_
  have h := h₁ _ (mem_latA.1 (hT ζ hζ) i j)
  rw [Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc] at h
  rwa [Nat.cast_mul]

end GlobalTheory.FinWeil
end

