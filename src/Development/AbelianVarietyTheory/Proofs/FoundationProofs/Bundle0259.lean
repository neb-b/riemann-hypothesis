module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussPowFourHom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSign
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertResidue

theorem card_of_involution {k : Type} [Field k] [Finite k] {q : ℕ} [Fact q.Prime] [CharP k q] (s : k →+* k)
    (hs : ∀ x, s (s x) = x) {r : k} {m : ℤ} (hr : r ^ 2 = m) (hsr : s r = -r) (hne : -r ≠ r) :
    (∃ f, Odd f ∧ Nat.card k = q ^ (2 * f)) ∧ ¬ IsSquare (m : ZMod q) := by
  letI : Algebra (ZMod q) k := ZMod.algebra k q
  haveI := Fintype.ofFinite k
  let σ : k ≃ₐ[ZMod q] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs, map_mul' := map_mul s, map_add' := map_add s,
      commutes' := fun c => RingHom.congr_fun (Subsingleton.elim (s.comp (algebraMap (ZMod q) k)) _) c }
  have hσ : ∀ x, σ x = s x := fun _ => rfl
  constructor
  · obtain ⟨⟨j, hj⟩, e⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod q) k).2 σ
    set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod q) k with hφ
    change φ ^ j = σ at e
    have ho : orderOf φ = Module.finrank (ZMod q) k := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod q) k
    have h2 : φ ^ (2 * j) = 1 := by
      rw [two_mul, pow_add, e]; ext x; exact hs x
    have hsq : (φ r) ^ 2 = r ^ 2 := by rw [← map_pow, hr, map_intCast]
    have hev : ∀ i, (φ ^ (2 * i)) r = r := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [mul_add, pow_add, AlgEquiv.mul_apply, mul_one, sq, AlgEquiv.mul_apply]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
        · rw [h, h, ih]
        · rw [h, map_neg, h, neg_neg, ih]
    have hodd : Odd j := by
      rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
      · exact absurd (by rw [← hsr, ← hσ, ← e, hev]) hne
      · exact ⟨i, rfl⟩
    refine ⟨j, hodd, ?_⟩
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [ho] at hd
    have hn : Module.finrank (ZMod q) k = 2 * j := by
      obtain ⟨c, hc⟩ := hd
      have hj0 := hodd.pos
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith [Nat.zero_le (Module.finrank (ZMod q) k * c)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), hn, Nat.card_zmod]
  · rintro ⟨c, hc⟩
    have h1 : r ^ 2 = (algebraMap (ZMod q) k c) ^ 2 := by rw [hr, sq, ← map_mul, ← hc, map_intCast]
    apply hne
    rw [← hsr, ← hσ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;> simp

theorem exists_root (D : D7) (n : ℕ) (b : D.host.E) (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ r : 𝓞 D.host.E, r ^ 2 = ((-(n : ℤ) : ℤ) : 𝓞 D.host.E) ∧ D.host.conj • r = -r := by
  have hint : IsIntegral ℤ b := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hb]
    exact (isIntegral_natCast n).neg
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  refine ⟨⟨b, hint⟩, RingOfIntegers.ext ?_, RingOfIntegers.ext hconj⟩
  have : (((-(n : ℤ) : ℤ) : 𝓞 D.host.E) : D.host.E) = ((-(n : ℤ) : ℤ) : D.host.E) :=
    map_intCast (algebraMap (𝓞 D.host.E) D.host.E) _
  rw [this]
  push_cast
  exact hb

theorem two_not_mem (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsPrime) (hsP : ∀ x ∈ P, D.host.conj • x ∈ P) :
    (2 : 𝓞 D.host.E) ∉ P := by
  intro h2
  have hw : D.host.conj • (Formalism.L2.Pj.w0E D) = 1 - Formalism.L2.Pj.w0E D := by
    rw [← Formalism.L2.Pj.conj_w0E D]
    exact RingOfIntegers.ext (Formalism.L2.Pj.barE_eq_conj D (Formalism.L2.Pj.w0E D)).symm
  have hsq := Formalism.L2.Pj.w0E_sq D
  obtain ⟨k, hk⟩ : ∃ k, Formalism.L2.Pj.mE D = 2 * k := by
    have h1 := D.host.hyp.2.2.2.1
    have h3 := Formalism.L2.Pj.mE_spec D
    exact ⟨Formalism.L2.Pj.mE D / 2, by omega⟩
  rw [hk] at hsq
  push_cast at hsq
  set w := Formalism.L2.Pj.w0E D
  have hm : w * (1 - w) ∈ P := by
    have : w * (1 - w) = k * 2 := by linear_combination -hsq
    rw [this]; exact P.mul_mem_left _ h2
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hP.mem_or_mem hm with h | h
  · have h' := hsP _ h
    rw [hw] at h'
    simpa using P.add_mem h h'
  · have h' := hsP _ h
    rw [smul_sub, smul_one, hw] at h'
    simpa using P.add_mem h h'

theorem card_of_root (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) (hfix : D.host.conj • P = P) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 D.host.E) ∈ P) (n : ℕ) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    (∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f)) ∧ ¬ IsSquare (-(n : ZMod q)) := by
  have hsP : ∀ x ∈ P, D.host.conj • x ∈ P := fun x hx => by
    rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx
  obtain ⟨r, hr, hsr⟩ := exists_root D n b hb
  haveI := Fact.mk hq
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI : CharP (𝓞 D.host.E ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hqP)
  let c := MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj
  let s : 𝓞 D.host.E ⧸ P →+* 𝓞 D.host.E ⧸ P := Ideal.quotientMap P c hsP
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (D.host.conj • x) := fun _ => rfl
  have h := card_of_involution (q := q) s (r := Ideal.Quotient.mk P r) (m := -(n : ℤ))
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, smul_smul, VacInt.conj_mul_self, one_smul])
    (by rw [← map_pow, hr, map_intCast]) (by rw [hs, hsr, map_neg])
    (fun h => by
      rw [← map_neg, Ideal.Quotient.eq] at h
      have h2 : 2 * r ∈ P := by
        have := P.neg_mem h
        convert this using 1
        ring
      have h3 := (hP.isPrime.mem_or_mem h2).resolve_left (two_not_mem D hP.isPrime hsP)
      have hnP : (n : 𝓞 D.host.E) ∈ P := by
        have := P.neg_mem (hr ▸ P.pow_mem_of_mem h3 2 two_pos)
        simpa using this
      obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
      exact hP.ne_top ((Ideal.eq_top_iff_one P).2
        (huv ▸ P.add_mem (P.mul_mem_left u hqP) (P.mul_mem_left v hnP))))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  push_cast at h
  exact h

theorem exists_prime (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) :
    ∃ q n : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ Ideal.absNorm P = q ^ n := by
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI := Fintype.ofFinite (𝓞 D.host.E ⧸ P)
  obtain ⟨q, hc, n, hq, hn⟩ := FiniteField.card' (𝓞 D.host.E ⧸ P)
  refine ⟨q, n, hq, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]

theorem norm_prime : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → Ev D (Ideal.absNorm P) ∧ (D.host.conj • P = P → sgn D (Ideal.absNorm P) = -1 ∧ ∃ q f : ℕ, q.Prime ∧ InertQ D q ∧ q ≠ 2 ∧ (q : 𝓞 D.host.E) ∈ P ∧ Odd f ∧ Ideal.absNorm P = q ^ (2 * f) ∧ (q ≠ D.host.d → ¬ IsSquare (-(D.host.d : ZMod q)))) ∧ (D.host.conj • P ≠ P → sgn D (Ideal.absNorm P) = 1 ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P → ¬ InertQ D q) := by
  intro D P hP
  obtain ⟨q, n, hq, hqP, hn⟩ := exists_prime D hP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  by_cases hfix : D.host.conj • P = P
  · have hin : InertQ D q := by
      by_contra h
      exact VacInt.conj_smul_ne D hq h P hP.isPrime hqP hfix
    obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
    have hd' : q ≠ D.host.d → _ := fun h => card_of_root D hP hfix hq hqP D.host.d
      ((Nat.coprime_primes hq hd).2 h) (D.host.sqd)
      (D.host.sqd_sq)
    obtain ⟨f, hf, hN⟩ : ∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f) := by
      by_cases h : q = D.host.d
      · exfalso
        haveI := hP.isPrime
        haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := by
          refine ⟨Ideal.IsMaximal.eq_of_le
            (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible)
            (Ideal.IsPrime.ne_top inferInstance) ?_⟩
          rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
          exact hqP
        exact D.host.der.decompConj q hq (h ▸ Dvd.intro_left _ rfl) P (MulAction.mem_stabilizer_iff.2 hfix)
      · exact (hd' h).1
    refine ⟨?_, fun _ => ⟨?_, q, f, hq, hin, ?_, hqP, hf, hN, fun h => (hd' h).2⟩, fun h => absurd hfix h⟩
    · intro p _ _
      rw [hN, Nat.factorization_pow]
      simp [Nat.even_mul]
    · have hf0 : 2 * f ≠ 0 := by have := hf.pos; omega
      rw [hN, sgn, hlf, Nat.primeFactors_prime_pow hf0 hq, Finset.filter_singleton, if_pos hin,
        Finset.sum_singleton, Nat.factorization_pow_self hq, Nat.mul_div_cancel_left _ two_pos, hf.neg_one_pow]
    · rintro rfl
      exact two_not_mem D hP.isPrime
        (fun x hx => by rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx) (by exact_mod_cast hqP)
  · have hall : ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ P → ¬ InertQ D p := fun p hp h => hfix (h P hP.isPrime hP0 hp)
    have h0 : ∀ p : ℕ, InertQ D p → (Ideal.absNorm P).factorization p = 0 := fun p hp => by
      rw [hn, hq.factorization_pow, Finsupp.single_eq_of_ne]
      rintro rfl
      exact hall _ hqP hp
    refine ⟨fun p _ hp => by rw [h0 p hp]; exact Even.zero, fun h => absurd h hfix, fun _ => ⟨?_, fun p _ hp => hall p hp⟩⟩
    rw [← sgn_one (D := D)]
    exact sgn_congr fun p _ hp => by rw [h0 p hp]; simp

end GlobalTheory.InertResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TripleIntertwiner

variable (D : D7) (T : Tor D) {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  unfold Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  unfold Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hf_conj (x y : VC D N N') : Hf D T x y = (starRingEnd ℂ) (Hf D T y x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

def wLin (x : VC D N N') : (VC D N N' → ℂ) →ₗ[ℂ] (VC D N N' → ℂ) where
  toFun := Wd D T x
  map_add' F G := by funext z; simp only [Wd, U, Pi.add_apply]; ring
  map_smul' a F := by funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def cocExp (x y : VC D N N') : ℂ :=
  (Real.pi : ℂ) * (Hf D T y x - Hf D T x y) / 2 -
    (Real.pi : ℂ) * Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ) / 2 *
      (((Hf D T x y).re : ℂ) + ((Hf D T y x).re : ℂ))

theorem wLin_heis :
    (∀ (x y : VC D N N') f, wLin D T x (wLin D T y f) = Complex.exp (cocExp D T x y) • wLin D T (x + y) f) ∧
    (∀ x x' y : VC D N N', Complex.exp (cocExp D T (x + x') y) =
      Complex.exp (cocExp D T x y) * Complex.exp (cocExp D T x' y)) ∧
    (∀ x y y' : VC D N N', Complex.exp (cocExp D T x (y + y')) =
      Complex.exp (cocExp D T x y) * Complex.exp (cocExp D T x y')) ∧
    ∀ x y : VC D N N', Complex.exp (cocExp D T x y) ≠ 0 := by
  refine ⟨fun x y f => ?_, fun x x' y => ?_, fun x y y' => ?_, fun _ _ => Complex.exp_ne_zero _⟩
  · funext z
    show Wd D T x (Wd D T y f) z = Complex.exp (cocExp D T x y) * Wd D T (x + y) f z
    simp only [Wd, U, wdPh, ee, qH, add_assoc]
    have : ∀ a b c d e g h u : ℂ, a + b + c + d = e + g + h →
        Complex.exp a * (Complex.exp b * (u * Complex.exp c) * Complex.exp d) =
          Complex.exp e * (Complex.exp g * (u * Complex.exp h)) := by
      intro a b c d e g h u hh
      calc _ = u * Complex.exp (a + b + c + d) := by simp only [Complex.exp_add]; ring
        _ = _ := by rw [hh]; simp only [Complex.exp_add]; ring
    apply this
    simp only [cocExp, hf_add_left, hf_add_right, Complex.add_re]
    push_cast
    ring
  · rw [← Complex.exp_add]; congr 1
    simp only [cocExp, hf_add_left, hf_add_right, Complex.add_re]
    push_cast
    ring
  · rw [← Complex.exp_add]; congr 1
    simp only [cocExp, hf_add_left, hf_add_right, Complex.add_re]
    push_cast
    ring

theorem im_int_of_comm (x v : VC D N N')
    (h : Complex.exp (cocExp D T x v) = Complex.exp (cocExp D T v x)) : ∃ m : ℤ, (Hf D T v x).im = m := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨m, ?_⟩
  have h1 : Hf D T v x - Hf D T x v = 2 * ((Hf D T v x).im : ℂ) * Complex.I := by
    rw [hf_conj D T x v, Complex.sub_conj]; push_cast; ring
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D T v x).im : ℂ) = (2 * (Real.pi : ℂ) * Complex.I) * m := by
    simp only [cocExp] at hm
    linear_combination hm - (Real.pi : ℂ) * h1
  have h3 := mul_left_cancel₀ Complex.two_pi_I_ne_zero h2
  exact_mod_cast h3

theorem iop_eq_itw (A B : AddSubgroup (VC D N N'))
    (hB : ∀ x ∈ B, ∀ F, Wd D T x F = fun z => al D T x * U D T x F z) (G : VC D N N' → ℂ) :
    Iop D T A B G = itw (wLin D T) A B G := by
  funext z
  simp only [Iop, itw, Pi.smul_apply, smul_eq_mul]
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (congrFun (hB _ (rep_mem q) G) z).symm

theorem itw_smul {V F : Type} [AddCommGroup V] [AddCommGroup F] [Module ℂ F] (W : V → F →ₗ[ℂ] F)
    (A B : AddSubgroup V) (a : ℂ) (f : F) : itw W A B (a • f) = a • itw W A B f := by
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [itw, h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    simp only [itw, finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum]
    rw [smul_comm]

theorem triple_constant : ∀ D : D7, GaussSumTripleConstant D := by
  intro D cc δ hc N N' A B C kA kB kC th hth
  by_cases h0 : th = 0
  · refine ⟨1, one_pow _, ?_⟩
    subst h0
    have e : ∀ X Y : AddSubgroup (VC D N N'), Iop D (tor0 D cc δ) X Y 0 = 0 := by
      intro X Y; funext z; simp [Iop, U]
    rw [e, e, e]; funext z; simp
  set T := tor0 D cc δ with hT
  have line := fun X (k : KLat D T X) => _root_.GlobalTheory.ThetaLine.theta_line D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' X k
  have eqI : ∀ X Y : AddSubgroup (VC D N N'), KLat D T Y → ∀ G, Iop D T X Y G = itw (wLin D T) X Y G :=
    fun X Y k G => iop_eq_itw D T X Y (line Y k).2.1 G
  have fix : ∀ X : AddSubgroup (VC D N N'), KLat D T X → ∀ G ∈ ThSp D T X, ∀ x ∈ X, wLin D T x G = G := by
    intro X k G hG x hx
    show Wd D T x G = G
    rw [(line X k).2.1 x hx]
    funext z
    exact hG.2 x hx z
  have uni : ∀ X Y : AddSubgroup (VC D N N'), KLat D T X → KLat D T Y → ∀ G ∈ ThSp D T X,
      itw (wLin D T) X Y G ∈ ThSp D T Y ∧ itw (wLin D T) Y X (itw (wLin D T) X Y G) = G := by
    intro X Y kX kY G hG
    have := _root_.GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' X Y kX kY G hG
    rw [← eqI X Y kY, ← eqI Y X kX]
    exact ⟨this.2.1, this.2.2.2⟩
  have nz : ∀ X Y : AddSubgroup (VC D N N'), KLat D T X → KLat D T Y → ∀ G ∈ ThSp D T X, G ≠ 0 →
      itw (wLin D T) X Y G ≠ 0 := by
    intro X Y kX kY G hG hG0 h
    have := (uni X Y kX kY G hG).2
    rw [h, ← zero_smul ℂ (0 : VC D N N' → ℂ), itw_smul, zero_smul] at this
    exact hG0 this.symm
  have ex : ∀ X : AddSubgroup (VC D N N'), KLat D T X → ∃ G ∈ ThSp D T X, G ≠ 0 :=
    fun X k => ⟨_, (uni A X kA k th hth).1, nz A X kA k th hth h0⟩
  have fin : ∀ X Y : AddSubgroup (VC D N N'), KLat D T X → KLat D T Y → X.relIndex Y ≠ 0 := by
    intro X Y kX kY h
    obtain ⟨G, hG, hG0⟩ := ex X kX
    apply nz X Y kX kY G hG hG0
    have h' : (X.addSubgroupOf Y).index = 0 := h
    simp [itw, h']
  have fin3 : ∀ Y : AddSubgroup (VC D N N'), KLat D T Y → (A ⊓ B ⊓ C).relIndex Y ≠ 0 := fun Y k =>
    AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero (fin A Y kA k) (fin B Y kB k))
      (fin C Y kC k)
  have H := wLin_heis D T (N := N) (N' := N')
  have coc : ∀ X : AddSubgroup (VC D N N'), KLat D T X → ∀ x ∈ X, ∀ y ∈ X,
      Complex.exp (cocExp D T x y) = 1 := by
    intro X k x hx y hy
    obtain ⟨G, hG, hG0⟩ := ex X k
    have := H.1 x y G
    rw [fix X k G hG y hy, fix X k G hG x hx, fix X k G hG _ (X.add_mem hx hy)] at this
    exact smul_left_injective ℂ hG0 (this.symm.trans (one_smul ℂ G).symm)
  have m1 := (uni A B kA kB th hth).1
  have m2 := (uni B C kB kC _ m1).1
  have m3 := (uni A C kA kC th hth).1
  have m4 := (uni C B kC kB _ m3).1
  obtain ⟨μ, μ', h4, e1, e2⟩ := itw_triple (c := fun x y => Complex.exp (cocExp D T x y)) H
    (fin3 A kA) (fin3 B kB) (fin3 C kC) (coc A kA) (coc B kB) (coc C kC)
    (fun v hv => (line A kA).2.2.2.1 v fun y hy => im_int_of_comm D T y v (hv y hy))
    th (fix A kA th hth) (fix B kB _ m1) (fix C kC _ m2) (fix C kC _ m3) (fix B kB _ m4)
  have e3 := (uni C A kC kA _ m2).2
  rw [e1, itw_smul] at e3
  have e4 := (uni B C kB kC _ m1).2
  have e5 := (uni A B kA kB th hth).2
  rw [← e4, ← e3, itw_smul, itw_smul, e2, smul_smul] at e5
  have e6 : μ * μ' = 1 := smul_left_injective ℂ h0 (e5.trans (one_smul ℂ th).symm)
  refine ⟨μ, ?_, ?_⟩
  · calc μ ^ 8 = μ ^ 4 * μ ^ 4 := by ring
      _ = (μ * μ') ^ 4 := by rw [mul_pow, ← h4]
      _ = 1 := by rw [e6, one_pow]
  · rw [eqI B C kC, eqI A B kB, eqI A C kC, ← e3]
    rfl

end GlobalTheory.TripleIntertwiner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenThetaStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  first | exact @GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | exact GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | (intros; apply GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSpaceUpqTZeroRight
section
open Formalism.BasicNotions MeasureTheory Filter Topology

namespace GlobalTheory

theorem compactSpace_UpqT_zero_right : ∀ N : ℕ, CompactSpace (UpqT N 0) :=
  fun N => (GlobalTheory.compactSpace_UpqT_definite N).1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjInvolutiveAndExistsHalfIdempotent
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.HalfIdempotent

theorem conj_involutive_and_exists_half_idempotent : ∀ (D : D7), (∀ y : AE D, sgA D (sgA D y) = y) ∧ ∃ ε ∈ OhE D, ε * ε = ε ∧ ε * sgA D ε = 0 ∧ ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q (ε + sgA D ε)) ∧ (¬ InertQ D q → ZeroAt D q (1 - (ε + sgA D ε))) :=
  fun D => ⟨GlobalTheory.NormSum.VacMove.sgA_sgA D, GlobalTheory.NormSum.VacMove.exists_half_idem D⟩

end GlobalTheory.NormSum.HalfIdempotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicPropertiesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (GL3Theta.th0 Λ t₀) ∧ GL3Theta.th0 Λ t₀ 0 = 1 ∧ (∀ z, GL3Theta.th0 Λ t₀ (-z) = GL3Theta.th0 Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z ^ 2 = sqTh Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧ ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, U1 Λ ω (GL3Theta.th0 Λ t₀) z = GL3Theta.th0 Λ t₀ z := by
  first | exact @GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | exact GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | (intros; apply GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties <;> assumption)
end

