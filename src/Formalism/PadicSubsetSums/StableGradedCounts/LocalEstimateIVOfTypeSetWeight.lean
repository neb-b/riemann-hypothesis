module

public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Formalism.GaloisIrreducibility.NoSolvableTransitive
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0003
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0007
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0004
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0008

@[expose] public section

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem type_weight_upper_unit : TypeWeightU := by
  intro g D Nd n hg hD hN
  rw [one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod₀
  · intro d hd
    have hgd : (1 : ℝ) ≤ (g : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ g))
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
  · intro d hd
    have hd1 := hD d hd
    have hgd : (1 : ℝ) < (g : ℝ) ^ d := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < g)) (by omega)
    have hNd : (d : ℝ) * (Nd d : ℝ) ≤ (g : ℝ) ^ d - 1 := by
      have h := hN d hd
      have h1 : 1 ≤ g ^ d := Nat.one_le_pow _ _ (by omega)
      have h2 : ((d * Nd d : ℕ) : ℝ) ≤ ((g ^ d - 1 : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub h1] at h2
      push_cast at h2
      linarith
    have hpos : (0 : ℝ) < (g : ℝ) ^ d - 1 := by linarith
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hfact : (0 : ℝ) < ((n d).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc ((Nd d).choose (n d) : ℝ) / ((g : ℝ) ^ d - 1) ^ (n d)
        ≤ ((Nd d : ℝ) ^ (n d) / ((n d).factorial : ℝ)) / ((g : ℝ) ^ d - 1) ^ (n d) :=
          div_le_div_of_nonneg_right (Nat.choose_le_pow_div _ _) (pow_nonneg hpos.le _)
      _ ≤ ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))⁻¹ := by
          rw [div_div, inv_eq_one_div, div_le_div_iff₀ (mul_pos hfact (pow_pos hpos _))
            (mul_pos (pow_pos hdpos _) hfact), one_mul]
          have hp : ((d : ℝ) * Nd d) ^ (n d) ≤ ((g : ℝ) ^ d - 1) ^ (n d) :=
            pow_le_pow_left₀ (by positivity) hNd _
          calc (Nd d : ℝ) ^ (n d) * ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))
              = ((d : ℝ) * Nd d) ^ (n d) * ((n d).factorial : ℝ) := by ring
            _ ≤ ((g : ℝ) ^ d - 1) ^ (n d) * ((n d).factorial : ℝ) :=
                mul_le_mul_of_nonneg_right hp hfact.le
            _ = ((n d).factorial : ℝ) * ((g : ℝ) ^ d - 1) ^ (n d) := by ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem comparison_transfer_holds : ComparisonTransfer := by
  intro ι _ _ T _ wU wJ g A hg hU0 hU1 hJ1 hJU
  classical
  have hg0 : 0 < g := by linarith
  have hgi : 1 / g ≤ 1 := (div_le_one hg0).2 hg
  have hgi0 : 0 ≤ 1 / g := by positivity
  set a : ℝ := 1 - 1 / g with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have htot : ∀ w : ∀ v, T v → ℝ, (∀ v, ∑ t, w v t = 1) →
      ∑ x : (∀ v, T v), ∏ v, w v (x v) = 1 := by
    intro w hw
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    simp [hw]
  have hprod : ∀ x : (∀ v, T v), a ^ Fintype.card ι * ∏ v, wU v (x v) ≤ ∏ v, wJ v (x v) := by
    intro x
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun v _ => mul_nonneg ha0 (hU0 v _)) (fun v _ => hJU v _)
  have hsJ := Finset.sum_sdiff (f := fun x => ∏ v, wJ v (x v)) (Finset.subset_univ A)
  have hsU := Finset.sum_sdiff (f := fun x => ∏ v, wU v (x v)) (Finset.subset_univ A)
  rw [htot wJ hJ1] at hsJ
  rw [htot wU hU1] at hsU
  have hcomp : a ^ Fintype.card ι * ∑ x ∈ Finset.univ \ A, ∏ v, wU v (x v) ≤
      ∑ x ∈ Finset.univ \ A, ∏ v, wJ v (x v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => hprod x)
  have hA0 : 0 ≤ ∑ x ∈ A, ∏ v, wU v (x v) :=
    Finset.sum_nonneg (fun x _ => Finset.prod_nonneg (fun v _ => hU0 v _))
  have hbern : 1 - (Fintype.card ι : ℝ) / g ≤ a ^ Fintype.card ι := by
    have h := one_add_mul_le_pow (a := -(1 / g)) (by linarith) (Fintype.card ι)
    have e1 : 1 + (Fintype.card ι : ℝ) * -(1 / g) = 1 - (Fintype.card ι : ℝ) / g := by ring
    have e2 : 1 + -(1 / g) = a := by rw [ha]; ring
    rw [e1, e2] at h
    exact h
  have hpow1 : a ^ Fintype.card ι ≤ 1 := pow_le_one₀ ha0 ha1
  have hc : ∑ x ∈ Finset.univ \ A, ∏ v, wU v (x v) = 1 - ∑ x ∈ A, ∏ v, wU v (x v) := by linarith
  rw [hc] at hcomp
  have hm := mul_le_mul_of_nonneg_right hpow1 hA0
  nlinarith

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem share_from_count : ShareFromCount := by
  intro ε W₁ W₂ PP₁ PP₂ D₁ D₂ Dall Dstar bad hε0 hε1 hD hP1 hPW1 hP2 hPW2 hall h1 h2 hbad
  have hall' : (1 - ε) * Dstar ≤ Dall := by
    have := (abs_le.mp hall).1
    linarith
  have h1e : 0 < 1 - ε := by linarith
  have hDall : 0 < Dall := lt_of_lt_of_le (mul_pos h1e hD) hall'
  have hd1 : D₁ ≤ (1 + ε) * W₁ * Dstar := by
    have := (abs_le.mp h1).2
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hD.le) (sub_nonneg.mpr hPW1)]
  have hd2 : D₂ ≤ (1 + ε) * W₂ * Dstar := by
    have := (abs_le.mp h2).2
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hD.le) (sub_nonneg.mpr hPW2)]
  have hW : 0 ≤ W₁ + W₂ := by linarith
  have hne : 1 - ε ≠ 0 := h1e.ne'
  have hc : 0 ≤ (1 + ε) / (1 - ε) * (W₁ + W₂) :=
    mul_nonneg (div_nonneg (by linarith) h1e.le) hW
  rw [div_le_iff₀ hDall]
  calc bad ≤ (1 + ε) * (W₁ + W₂) * Dstar := by linarith
    _ = (1 + ε) / (1 - ε) * (W₁ + W₂) * ((1 - ε) * Dstar) := by
        rw [show (1 + ε) / (1 - ε) * (W₁ + W₂) * ((1 - ε) * Dstar)
            = (1 + ε) * (W₁ + W₂) * Dstar * ((1 - ε) / (1 - ε)) by ring, div_self hne, mul_one]
    _ ≤ (1 + ε) / (1 - ε) * (W₁ + W₂) * Dall := mul_le_mul_of_nonneg_left hall' hc

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem primeToPart_unique {M : Type} [Monoid M] {l : ℕ} (hl : l.Prime) {x z : M}
    (hx : IsOfFinOrder x) (hz : IsOfFinOrder z) (hc : Nat.Coprime l (orderOf z)) {a : ℕ}
    (h : x ^ (l ^ a) = z ^ (l ^ a)) : primeToPart l x = z := by
  unfold primeToPart
  set m := orderOf x with hm
  have hm0 : m ≠ 0 := hx.orderOf_pos.ne'
  have hmpos : 0 < m := hx.orderOf_pos
  set v := m.factorization l with hv
  set m' := m / l ^ v with hm'
  have hcl : Nat.Coprime l m' := Nat.coprime_ordCompl hl hm0
  have hcop' : Nat.Coprime (l ^ v) m' := Nat.Coprime.pow_left v hcl
  have hm'pos : 0 < m' := Nat.ordCompl_pos l hm0
  have hsplit : l ^ v * m' = m := Nat.ordProj_mul_ordCompl_eq_self m l
  set N := (l ^ v) ^ Nat.totient m' with hN
  set oz := orderOf z with hoz
  have hoz0 : 0 < oz := hz.orderOf_pos
  have hcz : Nat.Coprime (l ^ a) oz := Nat.Coprime.pow_left a hc
  have hφz : 0 < Nat.totient oz := by
    first
    | exact Nat.totient_pos.2 hoz0
    | exact Nat.totient_pos hoz0
  have hφm : 0 < Nat.totient m' := by
    first
    | exact Nat.totient_pos.2 hm'pos
    | exact Nat.totient_pos hm'pos
  set j := (l ^ a) ^ Nat.totient oz with hj
  have hjz : j % oz = 1 % oz := Nat.ModEq.pow_totient hcz
  have hzj : z ^ j = z := by
    rw [← pow_mod_orderOf z j, ← hoz, hjz, pow_mod_orderOf, pow_one]
  have hjr : j = l ^ a * (l ^ a) ^ (Nat.totient oz - 1) := by
    rw [hj, ← pow_succ', Nat.sub_add_cancel hφz]
  have hzx : z = x ^ j := by
    calc z = z ^ j := hzj.symm
      _ = x ^ j := by rw [hjr, pow_mul z, ← h, ← pow_mul]
  have hxj1 : x ^ (j * oz) = 1 := by rw [pow_mul, ← hzx, hoz, pow_orderOf_eq_one]
  have hmj : m ∣ j * oz := orderOf_dvd_of_pow_eq_one hxj1
  have hlvj : l ^ v ∣ j :=
    (Nat.Coprime.pow_left v hc).dvd_of_dvd_mul_right (dvd_trans ⟨m', hsplit.symm⟩ hmj)
  have hlvN : l ^ v ∣ N := dvd_pow_self _ hφm.ne'
  have hj1 : 1 ≤ j := Nat.one_le_pow _ _ (pow_pos hl.pos a)
  obtain ⟨j0, hj0⟩ : ∃ j0, j = j0 + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m0, hm0'⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
  have hA : x ^ (j * l ^ a) = x ^ (l ^ a) := by rw [pow_mul, ← hzx, ← h]
  have hB : x ^ (l ^ a) * x ^ (m0 * l ^ a) = 1 := by
    rw [← pow_add, show l ^ a + m0 * l ^ a = m * l ^ a by rw [hm0']; ring, pow_mul, hm,
      pow_orderOf_eq_one, one_pow]
  have hx1 : x ^ (j0 * l ^ a) = 1 := by
    calc x ^ (j0 * l ^ a) = x ^ (j0 * l ^ a) * (x ^ (l ^ a) * x ^ (m0 * l ^ a)) := by
          rw [hB, mul_one]
      _ = x ^ (j * l ^ a) * x ^ (m0 * l ^ a) := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          rw [hj0]
          ring
      _ = 1 := by rw [hA, hB]
  have hmdvd1 : m ∣ j0 * l ^ a := orderOf_dvd_of_pow_eq_one hx1
  have hm'dvd : m' ∣ j0 :=
    (Nat.Coprime.pow_right a hcl.symm).dvd_of_dvd_mul_right
      (dvd_trans ⟨l ^ v, by rw [mul_comm]; exact hsplit.symm⟩ hmdvd1)
  have hN1 : N ≡ 1 [MOD m'] := Nat.ModEq.pow_totient hcop'
  have hj1' : j ≡ 1 [MOD m'] := by
    rw [hj0]
    have := (Nat.modEq_zero_iff_dvd.2 hm'dvd).add_right 1
    simpa using this
  have hNj1 : N ≡ j [MOD m'] := hN1.trans hj1'.symm
  have hNj2 : N ≡ j [MOD l ^ v] :=
    (Nat.modEq_zero_iff_dvd.2 hlvN).trans (Nat.modEq_zero_iff_dvd.2 hlvj).symm
  have hNj : N ≡ j [MOD m] := by
    rw [← hsplit]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop').1 ⟨hNj2, hNj1⟩
  rw [hzx, ← pow_mod_orderOf x N, ← pow_mod_orderOf x j, ← hm]
  rw [show N % m = j % m from hNj]

private theorem ptp_lemma {M : Type} [Monoid M] {l : ℕ} (hl : l.Prime) {x : M}
    (hx : IsOfFinOrder x) :
    (primeToPart l x) ^ (l ^ (orderOf x).factorization l) = x ^ (l ^ (orderOf x).factorization l) ∧
    Nat.Coprime l (orderOf (primeToPart l x)) ∧ IsOfFinOrder (primeToPart l x) ∧
    ∀ b, (orderOf x).factorization l ≤ b → (primeToPart l x) ^ (l ^ b) = x ^ (l ^ b) := by
  have hmpos : 0 < orderOf x := hx.orderOf_pos
  have hm0 : orderOf x ≠ 0 := hmpos.ne'
  have hcl : Nat.Coprime l (orderOf x / l ^ (orderOf x).factorization l) :=
    Nat.coprime_ordCompl hl hm0
  have hcop' := Nat.Coprime.pow_left ((orderOf x).factorization l) hcl
  have hm'pos : 0 < orderOf x / l ^ (orderOf x).factorization l := Nat.ordCompl_pos l hm0
  have hsplit : l ^ (orderOf x).factorization l * (orderOf x / l ^ (orderOf x).factorization l) =
      orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ l
  have hφm : 0 < Nat.totient (orderOf x / l ^ (orderOf x).factorization l) := by
    first
    | exact Nat.totient_pos.2 hm'pos
    | exact Nat.totient_pos hm'pos
  have hP : primeToPart l x = x ^ ((l ^ (orderOf x).factorization l) ^
      Nat.totient (orderOf x / l ^ (orderOf x).factorization l)) := rfl
  set v := (orderOf x).factorization l with hv
  set m' := orderOf x / l ^ v with hm'
  set N := (l ^ v) ^ Nat.totient m' with hN
  have hlvN : l ^ v ∣ N := dvd_pow_self _ hφm.ne'
  have ha : (primeToPart l x) ^ (l ^ v) = x ^ (l ^ v) := by
    rw [hP, ← pow_mul, ← pow_mod_orderOf x (N * l ^ v), ← pow_mod_orderOf x (l ^ v)]
    congr 1
    have h1 : N * l ^ v ≡ 1 * l ^ v [MOD m'] := (Nat.ModEq.pow_totient hcop').mul_right _
    rw [one_mul] at h1
    have h2 : N * l ^ v ≡ l ^ v [MOD l ^ v] :=
      (Nat.modEq_zero_iff_dvd.2 (dvd_mul_left _ _)).trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl).symm
    have h3 := (Nat.modEq_and_modEq_iff_modEq_mul hcop').1 ⟨h2, h1⟩
    rw [hsplit] at h3
    exact h3
  have hb : Nat.Coprime l (orderOf (primeToPart l x)) := by
    have h4 : (primeToPart l x) ^ m' = 1 := by
      rw [hP, ← pow_mul]
      obtain ⟨c, hc⟩ := hlvN
      have h5 : N * m' = c * orderOf x := by rw [hc, ← hsplit]; ring
      rw [h5, pow_mul', pow_orderOf_eq_one, one_pow]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h4) hcl
  have hc : IsOfFinOrder (primeToPart l x) := by
    rw [hP]
    exact hx.pow
  refine ⟨ha, hb, hc, fun b hvb => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvb
  rw [pow_add, pow_mul, pow_mul, ha]

theorem prime_to_part_endomorphism : PrimeToPartEndo := by
  intro M M' _ _ l x y φ hl hx hy
  obtain ⟨hxa, hxc, hxf, hxd⟩ := ptp_lemma hl hx
  obtain ⟨hya, hyc, hyf, hyd⟩ := ptp_lemma hl hy
  have hmap : ∀ w : M, IsOfFinOrder w → IsOfFinOrder (φ w) := fun w hw => by
    obtain ⟨n, hn, hwn⟩ := isOfFinOrder_iff_pow_eq_one.1 hw
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← map_pow, hwn, map_one]⟩
  constructor
  · have hxy : IsOfFinOrder (x * y) := (Commute.all x y).isOfFinOrder_mul hx hy
    refine primeToPart_unique (a := max ((orderOf x).factorization l) ((orderOf y).factorization l))
      hl hxy ((Commute.all _ _).isOfFinOrder_mul hxf hyf) ?_ ?_
    · exact Nat.Coprime.coprime_dvd_right ((Commute.all _ _).orderOf_mul_dvd_mul_orderOf)
        (Nat.Coprime.mul_right hxc hyc)
    · rw [mul_pow, mul_pow, hxd _ (le_max_left _ _), hyd _ (le_max_right _ _)]
  · refine (primeToPart_unique (a := (orderOf x).factorization l) hl (hmap x hx) (hmap _ hxf) ?_ ?_).symm
    · exact Nat.Coprime.coprime_dvd_right (orderOf_map_dvd φ _) hxc
    · rw [← map_pow, ← map_pow, hxa]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem mem_BB_iff (g N l : ℕ) : l ∈ BB g N ↔ l = g ∨ (l < g ^ N + 1 ∧ l.Prime ∧
    ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) := by
  unfold BB
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem subsum_bound : LemmaPSubSum := by
  intro N a h0 hN
  classical
  refine le_trans ?_ (prodMaxInvLeSq N a h0 hN)
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  obtain ⟨A, hA, hc⟩ := Formalism.GaloisIrreducibility.permSubSumInv (Fin N) σ a hσ
  exact ⟨A, hc, hA⟩

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Classical in
theorem twistedIdem_def {G : Type} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ) :
    twistedIdem J χ =
      ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) • MonoidAlgebra.of ℂ G (u : G) := rfl

open Classical in
theorem of_mul_twistedIdem {G : Type} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ)
    (v : J) : MonoidAlgebra.of ℂ G (v : G) * twistedIdem J χ
      = ((χ v : ℂˣ) : ℂ) • twistedIdem J χ := by
  classical
  unfold twistedIdem
  rw [Finset.mul_sum, Finset.smul_sum]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft v)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [mul_smul_comm, ← map_mul, smul_smul]
  congr 1
  have h1 := (χ v).ne_zero
  have h2 := (χ u).ne_zero
  simp only [Equiv.coe_mulLeft, map_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp <;> ring





end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem irreducible_count_upper_unit : IrredCountUpperUnit := by
  classical
  intro K _ _ d hd
  set F := (Finset.univ : Finset (Fin d → K)).filter
    (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hF
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hpos : 0 < (Nat.card K) ^ d - 1 := by
    have : 1 < (Nat.card K) ^ d := Nat.one_lt_pow (by omega) hq
    omega
  have hdvd : ∏ c ∈ F, monicOf c ∣ (X ^ (Nat.card K) ^ d - X : K[X]) := by
    apply Finset.prod_dvd_of_coprime
    · intro a ha b hb hab
      have hia : Irreducible (monicOf a) := (Finset.mem_filter.mp ha).2.1
      have hib : Irreducible (monicOf b) := (Finset.mem_filter.mp hb).2.1
      rw [Function.onFun, hia.coprime_iff_not_dvd]
      intro h
      exact hab (monicOf_injective (eq_of_monic_of_associated (monicOf_monic a) (monicOf_monic b)
        (hia.associated_of_dvd hib h)))
    · intro c hc
      exact ((Finset.mem_filter.mp hc).2.1.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).mp
        (by rw [monicOf_natDegree])
  have hsplit : (X ^ (Nat.card K) ^ d - X : K[X]) = X * (X ^ ((Nat.card K) ^ d - 1) - C 1) := by
    rw [mul_sub, ← pow_succ', Nat.sub_add_cancel (by omega), C_1, mul_one]
  have hcop : IsCoprime (∏ c ∈ F, monicOf c) (X : K[X]) := by
    apply IsCoprime.prod_left
    intro c hc
    have hic : Irreducible (monicOf c) := (Finset.mem_filter.mp hc).2.1
    rw [hic.coprime_iff_not_dvd]
    intro h
    have h1 : (X : K[X]) ∣ monicOf c := (hic.associated_of_dvd irreducible_X h).symm.dvd
    exact (Finset.mem_filter.mp hc).2.2 (X_dvd_iff.mp h1)
  rw [hsplit] at hdvd
  have hdvd2 := hcop.dvd_of_dvd_mul_left hdvd
  have hdeg := natDegree_le_of_dvd hdvd2 (X_pow_sub_C_ne_zero hpos 1)
  rw [natDegree_prod_of_monic _ _ (fun c _ => monicOf_monic c), natDegree_X_pow_sub_C _] at hdeg
  simp only [monicOf_natDegree, Finset.sum_const, smul_eq_mul, Nat.card_eq_fintype_card] at hdeg
  rw [mul_comm]
  exact hdeg

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open UniqueFactorizationMonoid in
theorem sum_degType {K : Type} [Field K] (f : K[X]) (hf : f ≠ 0) :
    (degType f).sum = f.natDegree := by
  classical
  unfold degType
  have h0 : (0 : K[X]) ∉ UniqueFactorizationMonoid.normalizedFactors f := fun h =>
    (UniqueFactorizationMonoid.prime_of_normalized_factor 0 h).ne_zero rfl
  rw [← Polynomial.natDegree_multiset_prod _ h0]
  exact Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors hf))

theorem sqWeight_eq {K : Type} [Field K] [Fintype K] (f : K[X]) :
    sqWeight f = ((degType f).map (fun d => ((Fintype.card K : ℝ) ^ d - 1)⁻¹)).prod := by
  unfold sqWeight degType
  rw [Multiset.map_map]
  rfl

theorem one_le_of_mem_degType {K : Type} [Field K] (f : K[X]) (d : ℕ) (hd : d ∈ degType f) :
    1 ≤ d := by
  classical
  unfold degType at hd
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hd
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr)

theorem inv_pow_sum_le (q : ℝ) (hq : 1 < q) (s : Multiset ℕ) (hs : ∀ d ∈ s, 1 ≤ d) :
    (q ^ s.sum)⁻¹ ≤ (s.map (fun d => (q ^ d - 1)⁻¹)).prod := by
  have hq0 : 0 < q := by linarith
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 1 ≤ a := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun d hd => hs d (Multiset.mem_cons_of_mem hd))
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, pow_add, mul_inv]
    have hqa : 1 < q ^ a := one_lt_pow₀ hq (by omega)
    have h1 : (q ^ a)⁻¹ ≤ (q ^ a - 1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    have h2 : 0 ≤ (q ^ s.sum)⁻¹ := (inv_pos.mpr (pow_pos hq0 _)).le
    have h3 : 0 ≤ (q ^ a - 1)⁻¹ := (inv_pos.mpr (by linarith)).le
    exact mul_le_mul h1 ih' h2 h3

theorem square_mass_lower_bound : SqMassLower := by
  intro K _ _ N hN
  have hq : (1 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hw : ∀ c ∈ sqSet K N, ((Fintype.card K : ℝ) ^ N)⁻¹ ≤ sqWeight (monicOf c) := by
    intro c _
    rw [sqWeight_eq]
    have h := inv_pow_sum_le _ hq (degType (monicOf c)) (one_le_of_mem_degType _)
    rwa [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree] at h
  have h1 : ((sqSet K N).card : ℝ) * ((Fintype.card K : ℝ) ^ N)⁻¹ ≤
      ∑ c ∈ sqSet K N, sqWeight (monicOf c) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hw
  have h2 : Fintype.card K ^ N ≤ (sqSet K N).card + 2 * Fintype.card K ^ (N - 1) :=
    squarefree_count K N hN
  have h3 : (Fintype.card K : ℝ) ^ N ≤ ((sqSet K N).card : ℝ) + 2 * (Fintype.card K : ℝ) ^ (N - 1) := by
    exact_mod_cast h2
  refine le_trans ?_ h1
  have hpos : (0 : ℝ) < (Fintype.card K : ℝ) ^ N := by positivity
  have h5 : (Fintype.card K : ℝ) ^ N = (Fintype.card K : ℝ) ^ (N - 1) * (Fintype.card K : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have h6 : (2 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ N
      = 2 * (Fintype.card K : ℝ) ^ (N - 1) := by
    rw [h5]; field_simp
  nlinarith [h3, h6]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem mem_sqSet {K : Type} [Field K] [Fintype K] {N : ℕ} (c : Fin N → K) :
    c ∈ sqSet K N ↔ Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 := by
  simp [sqSet]

theorem type_weight_exact : TypeWeightExact := by
  intro K _ _ N n hn
  set q : ℝ := (Fintype.card K : ℝ) with hq
  have hconst : ∀ c : Fin N → K,
      (∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d) →
      sqWeight (monicOf c) = ∏ d ∈ Finset.Icc 1 N, ((q ^ d - 1)⁻¹) ^ (n d) := by
    intro c hcount
    rw [sqWeight_eq, Finset.prod_multiset_map_count]
    have hsub : (degType (monicOf c)).toFinset ⊆ Finset.Icc 1 N := by
      intro d hd
      have hd' := Multiset.mem_toFinset.mp hd
      refine Finset.mem_Icc.mpr ⟨one_le_of_mem_degType _ d hd', ?_⟩
      have h1 := Multiset.le_sum_of_mem hd'
      rwa [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree] at h1
    rw [Finset.prod_subset hsub]
    · exact Finset.prod_congr rfl fun d hd => by rw [hcount d hd]
    · intro d _ hd
      rw [Multiset.count_eq_zero_of_notMem (fun h => hd (Multiset.mem_toFinset.mpr h)), pow_zero]
  refine (Finset.sum_congr rfl (fun c hc => by
    simp only [Finset.mem_filter] at hc
    exact hconst c hc.2)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := type_count_exact K N n hn
  have key : ∀ a : ℕ → ℕ, (∏ d ∈ Finset.Icc 1 N, ((a d : ℕ) : ℝ) / (q ^ d - 1) ^ (n d)) =
      ((∏ d ∈ Finset.Icc 1 N, a d : ℕ) : ℝ) * ∏ d ∈ Finset.Icc 1 N, ((q ^ d - 1)⁻¹) ^ (n d) := by
    intro a
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun d _ => by rw [inv_pow, div_eq_mul_inv]
  rw [key, ← hcard]
  congr 3
  ext c
  simp only [Finset.mem_filter, mem_sqSet, Finset.mem_univ, true_and, and_assoc]
  rfl

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Polynomial Formalism.GaloisIrreducibility

theorem monicOf_monic' {K : Type} [Field K] {N : ℕ} (c : Fin N → K) : (monicOf c).Monic := by
  exact Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c)

theorem sqMassLeOne_of (h : TypeSetWeight) : SqMassLeOne := by
  intro K _ _ M
  simpa [Fintype.card_perm, Nat.factorial_ne_zero] using h K M (fun _ => True)

theorem localEstimateIV_of (h : TypeSetWeight) (hP : LemmaPSubSum) (hD : DivisorDegreeSubSum) :
    LocalEstimateIV := by
  intro K _ _ N a ha haN
  classical
  have hfilt : (sqSet K N).filter (fun c => ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a) =
      (sqSet K N).filter (fun c => IsSubSum (degType (monicOf c)) a) := by
    apply Finset.filter_congr
    intro c _
    exact hD K (monicOf c) a (monicOf_monic' c).ne_zero
  rw [hfilt]
  refine le_trans (h K N (fun m => IsSubSum m a)) ?_
  have hP' := hP N a ha haN
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hf]
  have h8 : (8 : ℝ) * (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => IsSubSum σ.partition.parts a)).card : ℝ) ≤ 7 * N.factorial := by
    exact_mod_cast hP'
  linarith

theorem localEstimateV_of (h : TypeSetWeight) (hC : CycleProbSum) (hS : PrimeRecipSum) :
    LocalEstimateV := by
  intro K _ _ N hN
  classical
  have hiff : ∀ f : K[X], f ≠ 0 → ((∃ P : K[X], Irreducible P ∧ P ∣ f ∧ P.natDegree.Prime ∧
      N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N) ↔
      ∃ p ∈ degType f, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    intro f hf
    constructor
    · rintro ⟨P, hPi, hPd, hp⟩
      obtain ⟨q, hq, hPq⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf hPi hPd
      have hdeg : P.natDegree = q.natDegree :=
        Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hPq)
      refine ⟨q.natDegree, Multiset.mem_map.2 ⟨q, hq, rfl⟩, ?_⟩
      rw [← hdeg]
      exact hp
    · rintro ⟨p, hp, hpp⟩
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
      exact ⟨q, UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq, hpp⟩
  have hfilt : (sqSet K N).filter (fun c => ¬ ∃ P : K[X], Irreducible P ∧ P ∣ monicOf c ∧
      P.natDegree.Prime ∧ N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N) =
      (sqSet K N).filter (fun c => ¬ ∃ p ∈ degType (monicOf c), p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    apply Finset.filter_congr
    intro c _
    rw [hiff _ (monicOf_monic' c).ne_zero]
  rw [hfilt]
  have hT := h K N (fun m => ¬ ∃ p ∈ m, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)
  have hparts : ∀ σ : Equiv.Perm (Fin N), (∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) ↔
      (∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    intro σ
    rw [Equiv.Perm.parts_partition]
    constructor
    · rintro ⟨p, hp, hpp⟩
      rcases Multiset.mem_add.1 hp with h1 | h1
      · exact ⟨p, h1, hpp⟩
      · rw [Multiset.eq_of_mem_replicate h1] at hpp
        exact absurd hpp.1 Nat.not_prime_one
    · rintro ⟨p, hp, hpp⟩
      exact ⟨p, Multiset.mem_add.2 (Or.inl hp), hpp⟩
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hgoal : (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun σ =>
      ¬ ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)).card : ℝ) / N.factorial ≤
      1 - 1 / (5 * Real.log N) := by
    rw [div_le_iff₀ hf]
    have hadd := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Equiv.Perm (Fin N))))
      (fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)
    simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hadd
    beta_reduce at hadd
    have hQ : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) =
        Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
          ∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N :=
      Finset.filter_congr (fun σ _ => hparts σ)
    rw [hQ] at hadd
    have hadd' := congrArg (fun n : ℕ => (n : ℝ)) hadd
    simp only [Nat.cast_add] at hadd'
    rw [hC N] at hadd'
    have hsum := hS N hN
    have hsum' : ∑ p ∈ Finset.range (N + 1) with Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N,
        (N.factorial : ℝ) / p =
        N.factorial * ∑ p ∈ Finset.range (N + 1) with Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N,
          1 / (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      ring
    rw [hsum'] at hadd'
    nlinarith [mul_le_mul_of_nonneg_left hsum hf.le]
  exact le_trans (le_of_eq (by congr)) (le_trans hT (le_trans (le_of_eq (by congr)) hgoal))

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Polynomial

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem sum_mul_count_eq (s : Multiset ℕ) (N : ℕ) (h : ∀ d ∈ s, 1 ≤ d) (hs : s.sum = N) :
    ∑ d ∈ Finset.Icc 1 N, d * s.count d = N := by
  have hsub : s.toFinset ⊆ Finset.Icc 1 N := by
    intro d hd
    rw [Multiset.mem_toFinset] at hd
    have h2 := Multiset.le_sum_of_mem hd
    rw [hs] at h2
    exact Finset.mem_Icc.mpr ⟨h d hd, h2⟩
  rw [← Finset.sum_subset hsub]
  · conv_rhs => rw [← hs]
    rw [Finset.sum_multiset_count]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [smul_eq_mul, mul_comm]
  · intro d _ hd
    rw [Multiset.mem_toFinset] at hd
    rw [Multiset.count_eq_zero.mpr hd, mul_zero]

theorem multiset_eq_of_count (s m : Multiset ℕ) (N : ℕ) (hs1 : ∀ d ∈ s, 1 ≤ d) (hs : s.sum = N)
    (hm1 : ∀ d ∈ m, 1 ≤ d) (hm : m.sum = N)
    (h : ∀ d ∈ Finset.Icc 2 N, s.count d = m.count d) : s = m := by
  ext d
  by_cases h2 : d ∈ Finset.Icc 2 N
  · exact h d h2
  by_cases h3 : d = 1 ∧ 1 ≤ N
  · obtain ⟨rfl, hN⟩ := h3
    have h1mem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
    have e1 := Finset.add_sum_erase (Finset.Icc 1 N) (fun d => d * s.count d) h1mem
    have e2 := Finset.add_sum_erase (Finset.Icc 1 N) (fun d => d * m.count d) h1mem
    have e3 : ∑ x ∈ (Finset.Icc 1 N).erase 1, x * s.count x =
        ∑ x ∈ (Finset.Icc 1 N).erase 1, x * m.count x := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      obtain ⟨hne, hx'⟩ := Finset.mem_erase.mp hx
      rw [Finset.mem_Icc] at hx'
      rw [h x (Finset.mem_Icc.mpr ⟨by omega, hx'.2⟩)]
    beta_reduce at e1 e2
    rw [sum_mul_count_eq s N hs1 hs] at e1
    rw [sum_mul_count_eq m N hm1 hm] at e2
    simp only [one_mul] at e1 e2
    omega
  · have hout : ∀ t : Multiset ℕ, (∀ x ∈ t, 1 ≤ x) → t.sum = N → t.count d = 0 := by
      intro t ht1 hts
      rw [Multiset.count_eq_zero]
      intro hd
      have ha := ht1 d hd
      have hb := Multiset.le_sum_of_mem hd
      rw [hts] at hb
      rw [Finset.mem_Icc] at h2
      omega
    rw [hout s hs1 hs, hout m hm1 hm]

theorem sqWeight_nonneg {K : Type} [Field K] [Fintype K] (f : K[X]) : 0 ≤ sqWeight f := by
  unfold sqWeight
  apply Multiset.prod_nonneg
  intro x hx
  obtain ⟨P, -, rfl⟩ := Multiset.mem_map.mp hx
  have : (1 : ℝ) ≤ (Fintype.card K : ℝ) ^ P.natDegree :=
    one_le_pow₀ (by exact_mod_cast Fintype.card_pos)
  exact inv_nonneg.mpr (by linarith)

theorem type_weight_le (K : Type) [Field K] [Fintype K] (N : ℕ) (m : Multiset ℕ)
    (hm1 : ∀ d ∈ m, 1 ≤ d) (hm : m.sum = N) :
    ∑ c ∈ (sqSet K N).filter (fun c => degType (monicOf c) = m), sqWeight (monicOf c) ≤
      (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun σ => σ.partition.parts = m)).card : ℝ) / (N.factorial : ℝ) := by
  classical
  set n : ℕ → ℕ := fun d => m.count d with hn
  have hsum : ∑ d ∈ Finset.Icc 1 N, d * n d = N := sum_mul_count_eq m N hm1 hm
  obtain ⟨S, hS, hSsum⟩ : ∃ S : Finset (Fin N → K),
      (∀ c ∈ sqSet K N, (∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d) → c ∈ S) ∧
      ∑ c ∈ S, sqWeight (monicOf c) = _ :=
    ⟨_, fun c hc h => by simp only [Finset.mem_filter]; exact ⟨hc, h⟩,
      type_weight_exact K N n hsum⟩
  obtain ⟨S', hS', hc⟩ : ∃ S' : Finset (Equiv.Perm (Fin N)),
      (∀ σ ∈ S', ∀ d ∈ Finset.Icc 2 N, σ.cycleType.count d = n d) ∧
      S'.card * ∏ d ∈ Finset.Icc 1 N, (d ^ n d * (n d).factorial) = N.factorial :=
    ⟨_, fun σ hσ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ; exact hσ,
      cycle_type_probability N n hsum⟩
  have step1 : ∑ c ∈ (sqSet K N).filter (fun c => degType (monicOf c) = m),
      sqWeight (monicOf c) ≤ ∑ c ∈ S, sqWeight (monicOf c) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro c hc
      have hc' := Finset.mem_filter.mp hc
      exact hS c hc'.1 (fun d _ => by rw [hc'.2])
    · intro c _ _
      exact sqWeight_nonneg _
  have step2 := type_weight_upper_unit (Fintype.card K) (Finset.Icc 1 N)
    (fun d => ((Finset.univ : Finset (Fin d → K)).filter
      (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card) n
    Fintype.one_lt_card (fun d hd => (Finset.mem_Icc.mp hd).1)
    (fun d hd => irreducible_count_upper_unit K d (Finset.mem_Icc.mp hd).1)
  have hZpos : (0 : ℝ) < ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) := by
    apply Finset.prod_pos
    intro d hd
    have : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    positivity
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  have hc' : (S'.card : ℝ) * ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) =
      (N.factorial : ℝ) := by exact_mod_cast hc
  have step3 : 1 / ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) =
      (S'.card : ℝ) / (N.factorial : ℝ) := by
    rw [div_eq_div_iff hZpos.ne' hfac.ne', one_mul, hc']
  have step4 : S'.card ≤ ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun σ => σ.partition.parts = m)).card := by
    apply Finset.card_le_card
    intro σ hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply multiset_eq_of_count _ _ N (fun d hd => σ.partition.parts_pos hd)
      (by rw [σ.partition.parts_sum, Fintype.card_fin]) hm1 hm
    intro d hd
    rw [Equiv.Perm.parts_partition, Multiset.count_add, hS' σ hσ d hd,
      Multiset.count_replicate, if_neg (by have := (Finset.mem_Icc.mp hd).1; omega), add_zero]
  calc _ ≤ ∑ c ∈ S, sqWeight (monicOf c) := step1
    _ = _ := hSsum
    _ ≤ _ := step2
    _ = (S'.card : ℝ) / (N.factorial : ℝ) := step3
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hfac.le
      exact_mod_cast step4

theorem type_set_weight_bound : TypeSetWeight := by
  classical
  intro K _ _ N A
  set T : Finset (Multiset ℕ) := (Finset.univ : Finset N.Partition).image (fun p => p.parts)
    with hT
  have hTmem : ∀ m : Multiset ℕ, (∀ d ∈ m, 1 ≤ d) → m.sum = N → m ∈ T := by
    intro m h1 h2
    exact Finset.mem_image.mpr ⟨⟨m, fun {i} hi => h1 i hi, h2⟩, Finset.mem_univ _, rfl⟩
  have hTprop : ∀ m ∈ T, (∀ d ∈ m, 1 ≤ d) ∧ m.sum = N := by
    intro m hm
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨fun d hd => p.parts_pos hd, p.parts_sum⟩
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  rw [← Finset.sum_fiberwise_of_maps_to (t := T) (g := fun c => degType (monicOf c))
    (fun c _ => hTmem _ (one_le_of_mem_degType _)
      (by rw [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree]))]
  rw [Finset.card_eq_sum_card_fiberwise (t := T) (f := fun σ : Equiv.Perm (Fin N) => σ.partition.parts)
    (fun σ _ => hTmem _ (fun d hd => σ.partition.parts_pos hd)
      (by rw [σ.partition.parts_sum, Fintype.card_fin]))]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro m hm
  obtain ⟨hm1, hm2⟩ := hTprop m hm
  by_cases hA : A m
  · refine le_trans ?_ (le_trans (type_weight_le K N m hm1 hm2) ?_)
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro c hc
        simp only [Finset.mem_filter] at hc ⊢
        exact ⟨hc.1.1, hc.2⟩
      · intro c _ _
        exact sqWeight_nonneg _
    · apply div_le_div_of_nonneg_right _ hfac.le
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      exact ⟨hσ ▸ hA, hσ⟩
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro c hc
      simp only [Finset.mem_filter] at hc
      exact absurd (hc.2 ▸ hc.1.2) hA

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem sqWeight_mul {K : Type} [Field K] [Fintype K] (f g : K[X]) (hf : f ≠ 0) (hg : g ≠ 0) :
    sqWeight (f * g) = sqWeight f * sqWeight g := by
  classical
  unfold sqWeight
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hf hg, Multiset.map_add (f := _), Multiset.prod_add]

theorem divisor_square_weight_sum_le (hM : SqMassLeOne) (K : Type) [Field K] [Fintype K] (N : ℕ) (h : K[X])
    (hmon : h.Monic) (hdeg : h.natDegree ≤ N) (S : Finset (Fin N → K))
    (hS : ∀ c ∈ S, c ∈ sqSet K N ∧ h ∣ monicOf c) :
    ∑ c ∈ S, sqWeight (monicOf c) ≤ sqWeight h := by
  classical
  set M := N - h.natDegree with hMdef
  let φ : (Fin N → K) → (Fin M → K) := fun c i => (monicOf c / h).coeff i
  have hmul : ∀ c ∈ S, h * (monicOf c / h) = monicOf c := fun c hc =>
    EuclideanDomain.mul_div_cancel' hmon.ne_zero (hS c hc).2
  have hqmon : ∀ c ∈ S, (monicOf c / h).Monic := fun c hc =>
    hmon.of_mul_monic_left (by rw [hmul c hc]; exact monicOf_monic c)
  have hqdeg : ∀ c ∈ S, (monicOf c / h).natDegree = M := by
    intro c hc
    have h1 := hmon.natDegree_mul (hqmon c hc)
    rw [hmul c hc, monicOf_natDegree] at h1
    omega
  have hφ : ∀ c ∈ S, monicOf (φ c) = monicOf c / h := fun c hc =>
    monicOf_coeffs (hqmon c hc) (hqdeg c hc)
  have hφmem : ∀ c ∈ S, φ c ∈ sqSet K M := by
    intro c hc
    have hc' := (mem_sqSet c).mp (hS c hc).1
    rw [mem_sqSet, hφ c hc]
    refine ⟨hc'.1.squarefree_of_dvd ⟨h, by rw [mul_comm, hmul c hc]⟩, ?_⟩
    intro h0
    apply hc'.2
    rw [← hmul c hc, Polynomial.mul_coeff_zero, h0, mul_zero]
  have hinj : Set.InjOn φ (S : Set (Fin N → K)) := by
    intro c1 h1 c2 h2 he
    apply monicOf_injective
    rw [← hmul c1 h1, ← hmul c2 h2, ← hφ c1 h1, ← hφ c2 h2, he]
  have hw : ∀ c ∈ S, sqWeight (monicOf c) = sqWeight h * sqWeight (monicOf (φ c)) := by
    intro c hc
    rw [hφ c hc, ← sqWeight_mul _ _ hmon.ne_zero (hqmon c hc).ne_zero, hmul c hc]
  rw [Finset.sum_congr rfl hw, ← Finset.mul_sum]
  have h1 : ∑ c ∈ S, sqWeight (monicOf (φ c)) ≤ 1 := by
    rw [← Finset.sum_image (f := fun c' => sqWeight (monicOf c')) hinj]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hM K M)
    · intro c' hc'
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
      exact hφmem c hc
    · intro c' _ _
      exact sqWeight_nonneg _
  calc sqWeight h * ∑ c ∈ S, sqWeight (monicOf (φ c)) ≤ sqWeight h * 1 :=
        mul_le_mul_of_nonneg_left h1 (sqWeight_nonneg h)
    _ = sqWeight h := mul_one _

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Polynomial

noncomputable def wtOf {α : Type} [Fintype α] (μ : α → ℝ) (S : Set α) : ℝ := ∑ x, S.indicator μ x

section aux
variable {α β : Type} [Fintype α]

theorem wtOf_eq_filter (μ : α → ℝ) (p : α → Prop) [DecidablePred p] :
    wtOf μ {x | p x} = ∑ x ∈ Finset.univ.filter p, μ x := by
  unfold wtOf
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : p x <;> simp [Set.indicator, h]

theorem wtOf_eq_filter' (μ : α → ℝ) (s : Finset α) (p : α → Prop) [DecidablePred p] :
    wtOf μ {x | x ∈ s ∧ p x} = ∑ x ∈ s.filter p, μ x := by
  unfold wtOf
  rw [Finset.sum_filter, ← Finset.sum_subset (Finset.subset_univ s)]
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    by_cases h : p x <;> simp [Set.indicator, h, hx]
  · intro x _ hx
    simp [Set.indicator, hx]

theorem wtOf_mono (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) {S T : Set α} (h : S ⊆ T) :
    wtOf μ S ≤ wtOf μ T := by
  unfold wtOf
  exact Finset.sum_le_sum (fun x _ => Set.indicator_le_indicator_of_subset h hμ x)

theorem wtOf_nonneg (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (S : Set α) : 0 ≤ wtOf μ S := by
  unfold wtOf
  exact Finset.sum_nonneg (fun x _ => Set.indicator_nonneg (fun y _ => hμ y) x)

theorem wtOf_union_le (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (S T : Set α) :
    wtOf μ (S ∪ T) ≤ wtOf μ S + wtOf μ T := by
  unfold wtOf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have := hμ x
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [Set.indicator, hS, hT] <;> linarith

theorem wtOf_biUnion_le (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (t : Finset β) (S : β → Set α) :
    wtOf μ (⋃ b ∈ t, S b) ≤ ∑ b ∈ t, wtOf μ (S b) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [wtOf]
  | insert b t hb ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hb]
    exact (wtOf_union_le μ hμ _ _).trans (by linarith)

theorem wtOf_compl (μ : α → ℝ) (S : Set α) : wtOf μ Sᶜ = wtOf μ Set.univ - wtOf μ S := by
  simp only [wtOf, Set.indicator_compl, Set.indicator_univ, Pi.sub_apply, Finset.sum_sub_distrib]

theorem wtOf_univ (μ : α → ℝ) : wtOf μ Set.univ = ∑ x, μ x := by
  simp [wtOf]

end aux

section prod
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

theorem wtOf_pi (P : Ω → ℝ) (S : ι → Set Ω) :
    wtOf (fun x : ι → Ω => ∏ v, P (x v)) {x | ∀ v, x v ∈ S v} = ∏ v, wtOf P (S v) := by
  classical
  unfold wtOf
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : ∀ v, x v ∈ S v
  · rw [Set.indicator_of_mem (show x ∈ {x : ι → Ω | ∀ v, x v ∈ S v} from h)]
    exact Finset.prod_congr rfl (fun v _ => (Set.indicator_of_mem (h v) P).symm)
  · push_neg at h
    obtain ⟨v, hv⟩ := h
    have h0 : x ∉ {x : ι → Ω | ∀ v, x v ∈ S v} := fun hx => hv (hx v)
    have h1 : Set.indicator (S v) P (x v) = 0 := by simp [Set.indicator, hv]
    rw [Set.indicator_apply, if_neg h0, Finset.prod_eq_zero (Finset.mem_univ v) h1]

theorem wtOf_one_place (P : Ω → ℝ) (hP : ∑ c, P c = 1) (S : Set Ω) (v₀ : ι) :
    wtOf (fun x : ι → Ω => ∏ v, P (x v)) {x | x v₀ ∈ S} = wtOf P S := by
  have hset : {x : ι → Ω | x v₀ ∈ S} =
      {x : ι → Ω | ∀ v, x v ∈ (if v = v₀ then S else Set.univ)} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h v
      split_ifs with hv
      · subst hv
        exact h
      · exact Set.mem_univ _
    · intro h
      simpa using h v₀
  rw [hset, wtOf_pi, Finset.prod_eq_single v₀]
  · simp
  · intro v _ hv
    simp [hv, wtOf_univ, hP]
  · intro h
    exact absurd (Finset.mem_univ v₀) h

end prod

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Polynomial

theorem propW_of (h1 : SqMassLower) (h3 : LocalEstimateII) (h4 : LocalEstimateIII)
    (h5 : LocalEstimateIV) (h6 : LocalEstimateV) : PropW := by
  classical
  intro K L ι J _ _ _ _ _ _ _ N q₁ d χ P hN hq hq1 hd hne hq2 hd2 hmax h16 hq1d hdd hP0 hP1 hPsq
  have hμ : ∀ x : ι → Fin N → K, 0 ≤ ∏ v, P (x v) :=
    fun x => Finset.prod_nonneg fun v _ => hP0 _
  have hconv : ∀ (p : (Fin N → K) → Prop), wtOf P {c | c ∈ sqSet K N ∧ p c} =
      ∑ c ∈ (sqSet K N).filter p, sqWeight (monicOf c) := by
    intro p
    rw [wtOf_eq_filter']
    exact Finset.sum_congr rfl fun c hc => hPsq c (Finset.mem_filter.1 hc).1
  set q : ℝ := (Fintype.card K : ℝ) with hqdef
  set f : ℝ := (Fintype.card ι : ℝ) with hfdef

  set S1 : Set (Fin N → K) := {c | c ∈ sqSet K N}ᶜ with hS1
  set S3 : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
    l ∉ BB (Fintype.card K) N ∧ ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)} with hS3
  set S4 : Kˣ → Set (Fin N → K) := fun c₀ => {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
    l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
      primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} with hS4
  set S5 : ℕ → Set (Fin N → K) := fun a => {c | c ∈ sqSet K N ∧
    ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a} with hS5
  set S6 : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ ¬ ∃ Q : K[X], Irreducible Q ∧ Q ∣ monicOf c ∧
    Q.natDegree.Prime ∧ N < 2 * Q.natDegree ∧ Q.natDegree + 3 ≤ N} with hS6

  have b1 : wtOf P S1 ≤ 2 / q := by
    rw [hS1, wtOf_compl, wtOf_univ, hP1]
    have e : wtOf P {c | c ∈ sqSet K N} = ∑ c ∈ sqSet K N, sqWeight (monicOf c) := by
      have := hconv (fun _ => True)
      simpa using this
    rw [e]
    have := h1 K N (by omega)
    linarith
  have b3 : wtOf P S3 ≤ 23 * Real.log q / Real.sqrt q := by
    refine (hconv _).trans_le ?_
    convert h3 K L N hq
  have b4 : ∀ c₀ : Kˣ, wtOf P (S4 c₀) ≤
      1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / (q - 1) := by
    intro c₀
    refine (hconv _).trans_le ?_
    convert h4 K L N q₁ d c₀ (by omega) hq1 hd hne hq2 hd2 hmax h16 hq1d hdd
  have b5 : ∀ a ∈ Finset.Icc 1 (N / 2), wtOf P (S5 a) ≤ 7 / 8 := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    refine (hconv _).trans_le ?_
    convert h5 K N a (by omega) (by omega)
  have b6 : wtOf P S6 ≤ 1 - 1 / (5 * Real.log N) := by
    refine (hconv _).trans_le ?_
    convert h6 K N hN

  have hcover : {x : ι → Fin N → K | ¬ GoodAt K L N (fun v => monicOf (x v)) χ} ⊆
      (((((⋃ v ∈ (Finset.univ : Finset ι), {x : ι → Fin N → K | x v ∈ S1}) ∪
        (⋃ v ∈ (Finset.univ : Finset ι), {x : ι → Fin N → K | x v ∈ S3})) ∪
        (⋃ w ∈ (Finset.univ : Finset (ι × J)), ({x : ι → Fin N → K | x w.1 ∈ S4 (χ w.1 w.2)} ∪
          {x : ι → Fin N → K | x w.1 ∈ S4 (χ w.1 w.2)⁻¹}))) ∪
        (⋃ a ∈ Finset.Icc 1 (N / 2), {x : ι → Fin N → K | ∀ v, x v ∈ S5 a})) ∪
        {x : ι → Fin N → K | ∀ v, x v ∈ S6}) := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_setOf_eq,
      Finset.mem_univ, true_implies, forall_true_left] at hcon
    obtain ⟨⟨⟨⟨c1, c3⟩, c4⟩, c5⟩, c6⟩ := hcon
    have hsq : ∀ v, x v ∈ sqSet K N := by
      intro v
      have := c1 v
      simpa [hS1] using this
    have hsq' : ∀ v, Squarefree (monicOf (x v)) ∧ (monicOf (x v)).coeff 0 ≠ 0 := by
      intro v
      have := hsq v
      simpa [sqSet] using this
    apply hx
    refine ⟨fun v => ⟨monicOf_monic _, monicOf_natDegree _, (hsq' v).2⟩, fun v => (hsq' v).1,
      ?_, ?_, ?_, ?_⟩
    · intro l hl hlB v
      by_contra hinj
      exact c3 v ⟨hsq v, l, hl, hlB, hinj⟩
    · intro l hl hlq v j y hy
      refine ⟨fun he => ?_, fun he => ?_⟩
      · exact (c4 (v, j)).1 ⟨hsq v, l, hl, hlq, y, hy, he⟩
      · exact (c4 (v, j)).2 ⟨hsq v, l, hl, hlq, y, hy, he⟩
    · intro a ha1 ha2
      by_contra hall
      push Not at hall
      exact c5 a (Finset.mem_Icc.2 ⟨ha1, by omega⟩) fun v => ⟨hsq v, hall v⟩
    · by_contra hno
      push Not at hno
      apply c6
      intro v
      refine ⟨hsq v, ?_⟩
      rintro ⟨Q, hQ1, hQ2, hQ3, hQ4, hQ5⟩
      exact absurd hQ5 (not_le.2 (hno v Q hQ1 hQ2 hQ3 hQ4))
  rw [← wtOf_eq_filter (fun x : ι → Fin N → K => ∏ v, P (x v))
    (fun x => ¬ GoodAt K L N (fun v => monicOf (x v)) χ)]
  refine (wtOf_mono _ hμ hcover).trans ?_
  refine (wtOf_union_le _ hμ _ _).trans (add_le_add ((wtOf_union_le _ hμ _ _).trans
    (add_le_add ((wtOf_union_le _ hμ _ _).trans (add_le_add ((wtOf_union_le _ hμ _ _).trans
      (add_le_add ?_ ?_)) ?_)) ?_)) ?_)
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc ∑ v : ι, wtOf (fun x : ι → Fin N → K => ∏ v, P (x v)) {x | x v ∈ S1}
        = ∑ _v : ι, wtOf P S1 := Finset.sum_congr rfl fun v _ => wtOf_one_place P hP1 S1 v
      _ = f * wtOf P S1 := by simp [hfdef]
      _ ≤ f * (2 / q) := mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg _)
      _ = 2 * f / q := by ring
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc ∑ v : ι, wtOf (fun x : ι → Fin N → K => ∏ v, P (x v)) {x | x v ∈ S3}
        = ∑ _v : ι, wtOf P S3 := Finset.sum_congr rfl fun v _ => wtOf_one_place P hP1 S3 v
      _ = f * wtOf P S3 := by simp [hfdef]
      _ ≤ f * (23 * Real.log q / Real.sqrt q) :=
          mul_le_mul_of_nonneg_left b3 (Nat.cast_nonneg _)
      _ = 23 * f * Real.log q / Real.sqrt q := by ring
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    set B : ℝ := 1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / (q - 1) with hB
    calc ∑ w : ι × J, wtOf (fun x : ι → Fin N → K => ∏ v, P (x v))
          ({x | x w.1 ∈ S4 (χ w.1 w.2)} ∪ {x | x w.1 ∈ S4 (χ w.1 w.2)⁻¹})
        ≤ ∑ _w : ι × J, (B + B) := by
          refine Finset.sum_le_sum fun w _ => (wtOf_union_le _ hμ _ _).trans (add_le_add ?_ ?_)
          · rw [wtOf_one_place P hP1]; exact b4 _
          · rw [wtOf_one_place P hP1]; exact b4 _
      _ = 2 * f * (Fintype.card J : ℝ) * B := by
          simp [hfdef, Fintype.card_prod]; ring
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc ∑ a ∈ Finset.Icc 1 (N / 2), wtOf (fun x : ι → Fin N → K => ∏ v, P (x v))
          {x | ∀ v, x v ∈ S5 a}
        ≤ ∑ _a ∈ Finset.Icc 1 (N / 2), (7 / 8 : ℝ) ^ Fintype.card ι := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [wtOf_pi P (fun _ => S5 a), Finset.prod_const, Finset.card_univ]
          exact pow_le_pow_left₀ (wtOf_nonneg P hP0 _) (b5 a ha) _
      _ = ((N / 2 : ℕ) : ℝ) * (7 / 8 : ℝ) ^ Fintype.card ι := by simp
      _ ≤ (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Nat.cast_div_le
  · rw [wtOf_pi P (fun _ => S6), Finset.prod_const, Finset.card_univ]
    calc wtOf P S6 ^ Fintype.card ι ≤ (Real.exp (-(1 / (5 * Real.log N)))) ^ Fintype.card ι := by
          refine pow_le_pow_left₀ (wtOf_nonneg P hP0 _) (b6.trans ?_) _
          exact Real.one_sub_le_exp_neg _
      _ = Real.exp (-f / (5 * Real.log N)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          rw [hfdef]; ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem localEstimateIV_of_typeSetWeight (h : TypeSetWeight) : LocalEstimateIV := by
  exact localEstimateIV_of h subsum_bound divisor_degree_subsum

theorem localEstimateV_of_typeSetWeight (h : TypeSetWeight) : LocalEstimateV := by
  exact localEstimateV_of h prime_cycle_probability_sum prime_reciprocal_sum_bound

theorem square_mass_le_one : SqMassLeOne := by
  exact sqMassLeOne_of type_set_weight_bound

theorem local_estimate_fourth : LocalEstimateIV := by
  exact localEstimateIV_of_typeSetWeight type_set_weight_bound

theorem local_estimate_fifth : LocalEstimateV := by
  exact localEstimateV_of_typeSetWeight type_set_weight_bound

theorem propW_of_localEstimates (h3 : LocalEstimateII) (h4 : LocalEstimateIII) : PropW := by
  exact propW_of square_mass_lower_bound h3 h4 local_estimate_fourth local_estimate_fifth

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
