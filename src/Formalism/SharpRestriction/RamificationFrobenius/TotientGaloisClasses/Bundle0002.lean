module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

@[expose] public section

-- bundled from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.DvdCondNIffCls
section
namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem dvd_condN_iff_cls {p : ℕ} (hp : p.Prime) :
    p ∣ H.condN ↔ H.cls p = .ram2 ∨ H.cls p = .ramQ ∨ H.cls p = .ramD := by
  have key : H.cls p = .ram2 ∨ H.cls p = .ramQ ∨ H.cls p = .ramD ↔ p ∈ H.small ∨ p = H.q ∨ p = H.d := by
    unfold Host.cls primeClass
    split_ifs <;> simp_all
  obtain ⟨hqp, hdp, -, -, -⟩ := H.hyp
  have hQS : H.QS ≠ 0 := H.QS_pos.ne'
  have hs : p ∣ H.QS ↔ p ∈ H.small := by
    show p ∣ H.QS ↔ p ∈ H.QS.primeFactors
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => ⟨hp, h, hQS⟩, fun h => h.2.1⟩
  rw [key, show H.condN = H.QS * H.q * H.d from rfl, hp.dvd_mul, hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp hqp,
    Nat.prime_dvd_prime_iff_eq hp hdp, hs, or_assoc]

theorem not_inert_of_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ H.condN) :
    ¬ (H.cls p = .inertClass ∨ H.cls p = .signal) := by
  rcases (dvd_condN_iff_cls H hp).mp h with h1 | h1 | h1 <;> rw [h1] <;> simp

end Formalism.BasicNotions.Host
end

-- bundled from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostRam
section
open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

theorem exists_unit_val {N : ℕ} [NeZero N] {x : ℕ} (hx : Nat.Coprime x N) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD N] :=
  ⟨ZMod.unitOfCoprime x hx, by rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]; exact Nat.mod_modEq x N⟩

theorem exists_unit_crt {N a b : ℕ} [NeZero N] (hN : N = a * b) (hab : Nat.Coprime a b) {x y : ℕ}
    (hx : Nat.Coprime x a) (hy : Nat.Coprime y b) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD a] ∧ (u : ZMod N).val ≡ y [MOD b] := by
  obtain ⟨z, hza, hzb⟩ := Nat.chineseRemainder hab x y
  have hza' : Nat.Coprime z a :=
    Nat.coprime_iff_gcd_eq_one.mpr ((Nat.ModEq.gcd_eq hza).trans (Nat.coprime_iff_gcd_eq_one.mp hx))
  have hzb' : Nat.Coprime z b :=
    Nat.coprime_iff_gcd_eq_one.mpr ((Nat.ModEq.gcd_eq hzb).trans (Nat.coprime_iff_gcd_eq_one.mp hy))
  have hz : Nat.Coprime z N := by
    rw [hN]
    exact Nat.Coprime.mul_right hza' hzb'
  obtain ⟨u, hu⟩ := exists_unit_val hz
  exact ⟨u, (Nat.ModEq.of_dvd ⟨b, hN⟩ hu).trans hza, (Nat.ModEq.of_dvd ⟨a, hN.trans (Nat.mul_comm a b)⟩ hu).trans hzb⟩

theorem jacobi_pred {p : ℕ} (hp4 : p % 4 = 3) : Nat.Coprime (p - 1) p ∧ jacobiSym ((p - 1 : ℕ) : ℤ) p = -1 := by
  constructor
  · have h2 : Nat.gcd (p - 1) p ∣ p - 1 + 1 := by
      rw [show p - 1 + 1 = p by omega]
      exact Nat.gcd_dvd_right _ _
    exact Nat.dvd_one.mp ((Nat.dvd_add_right (Nat.gcd_dvd_left _ _)).mp h2)
  · have hodd : Odd p := Nat.odd_iff.mpr (by omega)
    have hmod : ((p - 1 : ℕ) : ℤ) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      simp
    rw [jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hp4]

theorem ordCompl_mul_prime {m l : ℕ} (hl : l.Prime) (hm : Nat.Coprime m l) : ordCompl[l] (m * l) = m := by
  have hnd : ¬ l ∣ m := (Nat.Prime.coprime_iff_not_dvd hl).mp (Nat.Coprime.symm hm)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hnd (dvd_zero l)
  have hf : (m * l).factorization l = 1 := by
    rw [Nat.factorization_mul hm0 hl.ne_zero, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd,
      hl.factorization_self, zero_add]
  rw [hf, pow_one, Nat.mul_div_cancel _ hl.pos]

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

theorem condN_eq_q : H.condN = H.QS * H.d * H.q := by
  rw [HostRaw.condN]
  ring

theorem condN_div_q : H.condN / H.q = H.QS * H.d := by
  obtain ⟨hq, -, -, -, -⟩ := H.hyp
  rw [condN_eq_q, Nat.mul_div_cancel _ hq.pos]

theorem condN_div_d : H.condN / H.d = H.QS * H.q := by
  obtain ⟨-, hd, -, -, -⟩ := H.hyp
  rw [HostRaw.condN, Nat.mul_div_cancel _ hd.pos]

theorem ordCompl_q : ordCompl[H.q] H.condN = H.QS * H.d := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  rw [condN_eq_q]
  apply ordCompl_mul_prime hq
  have hqd : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).mpr (by omega)
  exact Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd

variable {H}

theorem PsQ.exists_q (hP : H.PsQ) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] ∧ (H.art u).1.1 = -1 := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hq4 : H.q % 4 = 3 := by omega
  obtain ⟨hcop, hj⟩ := jacobi_pred hq4
  have hqd : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).mpr (by omega)
  have hc : Nat.Coprime (H.QS * H.d) H.q :=
    Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.condN) (condN_eq_q H) hc (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hu2' : (u : ZMod H.condN).val % H.q = (H.q - 1) % H.q := hu2
  have h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.q : ℤ) = ((H.q - 1 : ℕ) : ℤ) % (H.q : ℤ) := by
    exact_mod_cast hu2'
  have h3 : (((H.art u).1.1 : ℤˣ) : ℤ) = -1 := by
    rw [hP u, jacobiSym.mod_left' h2, hj]
  exact Units.ext (by simpa using h3)

end HostRaw

namespace HostAx

variable {φ : Frame} (H : HostAx φ)

theorem exists_d : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] ∧ H.art u = φ.iod := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hd4 : H.d % 4 = 3 := by omega
  obtain ⟨hcop, hj⟩ := jacobi_pred hd4
  have hqd : Nat.Coprime H.q H.d := (Nat.coprime_primes hq hd).mpr (by omega)
  have hc : Nat.Coprime (H.QS * H.q) H.d :=
    Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left H.d H.q) H.QS_coprime) hqd
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.condN) (a := H.QS * H.q) (b := H.d) rfl hc
    (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hu2' : (u : ZMod H.condN).val % H.d = (H.d - 1) % H.d := hu2
  have h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.d : ℤ) = ((H.d - 1 : ℕ) : ℤ) % (H.d : ℤ) := by
    exact_mod_cast hu2'
  have h3 := H.der.art_ch u
  rw [jacobiSym.mod_left' h2, hj] at h3
  rcases H.art_d u hu1 with h | h
  · exfalso
    rw [h] at h3
    simp at h3
  · exact h

theorem exact_all (hP : H.PsQ) (hE : H.Exact) (l : ℕ) (hl : l.Prime) (h : l ∣ H.condN) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1 := by
  obtain ⟨hq, hd, -, -, -⟩ := H.hyp
  rcases (Nat.Prime.dvd_mul hl).mp h with h' | h'
  · rcases (Nat.Prime.dvd_mul hl).mp h' with h'' | h''
    · exact hE l hl h''
    · rw [(Nat.prime_dvd_prime_iff_eq hl hq).mp h'', HostRaw.condN_div_q]
      obtain ⟨u, hu1, hu2⟩ := hP.exists_q
      refine ⟨u, hu1, fun h1 => ?_⟩
      have h3 := congrArg (fun x : ℤˣ => (x : ℤ)) hu2
      rw [h1] at h3
      simp at h3
  · rw [(Nat.prime_dvd_prime_iff_eq hl hd).mp h', HostRaw.condN_div_d]
    obtain ⟨u, hu1, hu2⟩ := exists_d H
    refine ⟨u, hu1, fun h1 => ?_⟩
    have h3 := congrArg (fun g : φ.GG => ((g.1.2 : ℤˣ) : ℤ)) (hu2.symm.trans h1)
    simp [Frame.iod] at h3

end HostAx

end Formalism.HC

end
end

