module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero

@[expose] public section

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

namespace Tilt

variable (p R) in
def seqEquiv : Perfection R p ≃* Tilt p R := Perfection.quotientMulEquiv p (span {(p : R)})

def seq (n : ℕ) : Tilt p R →* R :=
  (Perfection.coeffMonoidHom R p n).comp (seqEquiv p R).symm.toMonoidHom

def ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) : Tilt p R := seqEquiv p R ⟨x, h⟩

@[simp] theorem seq_ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) (n : ℕ) :
    seq n (ofSeq x h : Tilt p R) = x n := by
  exact congrArg (Perfection.coeffMonoidHom R p n) ((seqEquiv p R).symm_apply_apply ⟨x, h⟩)

theorem seq_zero (y : Tilt p R) : seq 0 y = PreTilt.untilt y :=
  Perfection.coeff_zero_symm_quotientMulEquiv y

@[simp] theorem untilt_ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) :
    PreTilt.untilt (ofSeq x h : Tilt p R) = x 0 := by
  rw [← seq_zero, seq_ofSeq]

theorem seq_succ_pow (y : Tilt p R) (n : ℕ) : seq (n + 1) y ^ p = seq n y :=
  Perfection.coeffMonoidHom_pow_p' ((seqEquiv p R).symm y) n

theorem seq_add_pow (y : Tilt p R) (m n : ℕ) : seq (m + n) y ^ p ^ n = seq m y :=
  Perfection.coeffMonoidHom_pow_p_pow' ((seqEquiv p R).symm y) m n

theorem seq_pow_self (y : Tilt p R) (n : ℕ) : seq n y ^ p ^ n = PreTilt.untilt y := by
  rw [← seq_zero, ← seq_add_pow y 0 n, zero_add]

theorem ext_seq {x y : Tilt p R} (h : ∀ n, seq n x = seq n y) : x = y :=
  (seqEquiv p R).symm.injective (Perfection.extMonoid h)

theorem seq_frobeniusEquiv_symm (y : Tilt p R) (n : ℕ) :
    seq n ((frobeniusEquiv (Tilt p R) p).symm y) = seq (n + 1) y := by
  conv_rhs => rw [← frobeniusEquiv_symm_pow_p (Tilt p R) p y, map_pow, seq_succ_pow]

end Tilt

namespace tateModule

open Tilt

theorem untilt_eq_one (η : tateModule p R) : PreTilt.untilt η.1 = 1 := η.2

theorem seq_pow_eq_one (η : tateModule p R) (n : ℕ) : seq n η.1 ^ p ^ n = 1 := by
  rw [seq_pow_self, untilt_eq_one]

theorem ext_seq {x y : tateModule p R} (h : ∀ n, seq n x.1 = seq n y.1) : x = y :=
  Subtype.ext (Tilt.ext_seq h)

theorem seq_pow_congr (η : tateModule p R) {n a b : ℕ} (h : (a : ZMod (p ^ n)) = b) :
    seq n η.1 ^ a = seq n η.1 ^ b :=
  pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h) (seq_pow_eq_one η n)

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
theorem cast_val_toZModPow (a : ℤ_[p]) (n : ℕ) :
    (((PadicInt.toZModPow n a).val : ℕ) : ZMod (p ^ n)) = PadicInt.toZModPow n a :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  ZMod.natCast_zmod_val _

def padicPow (η : tateModule p R) (a : ℤ_[p]) : tateModule p R :=
  ⟨ofSeq (fun n => seq n η.1 ^ (PadicInt.toZModPow n a).val) (fun n => by
    rw [← pow_mul, mul_comm, pow_mul, seq_succ_pow]
    apply seq_pow_congr
    haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    rw [cast_val_toZModPow, ZMod.natCast_val, PadicInt.cast_toZModPow _ _ n.le_succ]), by
    change PreTilt.untilt _ = 1
    rw [untilt_ofSeq, seq_zero, untilt_eq_one, one_pow]⟩

theorem seq_padicPow (η : tateModule p R) (a : ℤ_[p]) (n : ℕ) :
    seq n (padicPow η a).1 = seq n η.1 ^ (PadicInt.toZModPow n a).val := seq_ofSeq _ _ n

theorem seq_padicPow_of_eq (η : tateModule p R) {a : ℤ_[p]} {n m : ℕ}
    (h : PadicInt.toZModPow n a = m) : seq n (padicPow η a).1 = seq n η.1 ^ m := by
  rw [seq_padicPow]
  exact seq_pow_congr η (by rw [cast_val_toZModPow, h])

@[simp] theorem padicPow_natCast (η : tateModule p R) (m : ℕ) : padicPow η m = η ^ m :=
  ext_seq fun n => by
    rw [seq_padicPow_of_eq η (map_natCast _ m), SubmonoidClass.coe_pow, map_pow]

@[simp] theorem padicPow_zero (η : tateModule p R) : padicPow η 0 = 1 := by
  simpa using padicPow_natCast η 0

theorem padicPow_add (η : tateModule p R) (a b : ℤ_[p]) :
    padicPow η (a + b) = padicPow η a * padicPow η b :=
  ext_seq fun n => by
    rw [Submonoid.coe_mul, map_mul, seq_padicPow η a, seq_padicPow η b, ← pow_add]
    apply seq_padicPow_of_eq
    rw [Nat.cast_add, cast_val_toZModPow, cast_val_toZModPow, map_add (f := _)]

theorem padicPow_mul (η : tateModule p R) (a b : ℤ_[p]) :
    padicPow η (a * b) = padicPow (padicPow η a) b :=
  ext_seq fun n => by
    rw [seq_padicPow _ b, seq_padicPow η a, ← pow_mul]
    apply seq_padicPow_of_eq
    rw [Nat.cast_mul, cast_val_toZModPow, cast_val_toZModPow, map_mul]

theorem exists_padicPow_eq (η : tateModule p R) {a : ℤ_[p]} {m k : ℕ}
    (h : (p : ℤ_[p]) ^ k ∣ a - m) : ∃ η' : tateModule p R, padicPow η a = η ^ m * η' ^ p ^ k := by
  obtain ⟨b, hb⟩ := h
  refine ⟨padicPow η b, ?_⟩
  rw [← padicPow_natCast, ← padicPow_natCast, ← padicPow_mul, ← padicPow_add]
  congr 1
  push_cast
  linear_combination hb

end tateModule

open Tilt tateModule

theorem isPrimitive_iff (ε : tateModule p R) : IsPrimitive ε ↔ seq 1 ε.1 ≠ 1 := by
  rw [IsPrimitive, ← seq_zero, seq_frobeniusEquiv_symm]

theorem IsPrimitive.isPrimitiveRoot {ε : tateModule p R} (hε : IsPrimitive ε) (n : ℕ) :
    IsPrimitiveRoot (seq n ε.1) (p ^ n) := by
  rcases n with _ | n
  · rw [seq_zero, untilt_eq_one, pow_zero]; exact IsPrimitiveRoot.one
  · rw [← orderOf_eq_prime_pow (x := seq (n + 1) ε.1) _ (seq_pow_eq_one ε _)]
    · exact IsPrimitiveRoot.orderOf _
    · rw [add_comm, seq_add_pow]; exact (isPrimitive_iff ε).1 hε

theorem IsPrimitive.padicPow_iff {ε : tateModule p R} (hε : IsPrimitive ε) (a : ℤ_[p]) :
    IsPrimitive (padicPow ε a) ↔ IsUnit a := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [isPrimitive_iff, seq_padicPow, Ne, (hε.isPrimitiveRoot 1).pow_eq_one_iff_dvd,
    ← ZMod.natCast_eq_zero_iff, cast_val_toZModPow, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    pow_one, ← PadicInt.maximalIdeal_eq_span_p, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]

section Domain

variable [IsDomain R]

theorem IsPrimitive.padicPow_surjective {ε : tateModule p R} (hε : IsPrimitive ε) :
    Function.Surjective (padicPow ε) := by
  intro η
  have h : ∀ n, ∃ i : ℕ, seq n ε.1 ^ i = seq n η.1 := fun n => by
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨i, -, hi⟩ := (hε.isPrimitiveRoot n).eq_pow_of_pow_eq_one (seq_pow_eq_one η n)
    exact ⟨i, hi⟩
  choose i hi using h
  have hd : ∀ n, (p : ℤ) ^ n ∣ (i (n + 1) : ℤ) - i n := fun n => by
    have h1 : seq n ε.1 ^ i n = seq n ε.1 ^ i (n + 1) := by
      rw [hi, ← seq_succ_pow η.1, ← hi, ← seq_succ_pow ε.1 n, ← pow_mul, ← pow_mul, mul_comm]
    have hf : IsOfFinOrder (seq n ε.1) :=
      (hε.isPrimitiveRoot n).isOfFinOrder (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    rw [hf.pow_eq_pow_iff_modEq, ← (hε.isPrimitiveRoot n).eq_orderOf] at h1
    exact_mod_cast h1.dvd
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
    (fun n => (i n : ℤ)) p hd), tateModule.ext_seq fun n => ?_⟩
  rw [← hi]
  apply seq_padicPow_of_eq
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ hd]
  simp

theorem IsPrimitive.exists_unit {ε ε' : tateModule p R} (hε : IsPrimitive ε)
    (hε' : IsPrimitive ε') : ∃ a : ℤ_[p]ˣ, ε' = padicPow ε a := by
  obtain ⟨a, rfl⟩ := hε.padicPow_surjective ε'
  obtain ⟨a, rfl⟩ := (hε.padicPow_iff a).1 hε'
  exact ⟨a, rfl⟩

end Domain

section Good

variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)]

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
theorem exists_pow_eq (x : R) {n : ℕ} (hn : 0 < n) : ∃ y : R, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R (FractionRing R) x) hn
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) hn
    (x := z) (by rw [hz]; exact isIntegral_algebraMap)
  exact ⟨y, IsFractionRing.injective R (FractionRing R) (by rw [map_pow, hz])⟩

theorem Tilt.seq_surjective (n : ℕ) : Function.Surjective (seq n : Tilt p R → R) := by
  have h0 : ∀ x : R, ∃ y : Tilt p R, seq 0 y = x := fun x => by
    choose r hr using fun z : R => exists_pow_eq z (Fact.out : p.Prime).pos
    exact ⟨ofSeq (fun n => r^[n] x) (fun n => by rw [Function.iterate_succ_apply', hr]),
      seq_ofSeq _ _ 0⟩
  intro x
  obtain ⟨y, hy⟩ := h0 x
  exact ⟨y ^ p ^ n, by rw [map_pow, ← hy, ← seq_add_pow y 0 n, zero_add]⟩

theorem Tilt.untilt_surjective_of_isAlgClosed : Function.Surjective (PreTilt.untilt : Tilt p R → R) := fun x => by
  obtain ⟨y, hy⟩ := Tilt.seq_surjective (p := p) 0 x
  exact ⟨y, by rw [← seq_zero, hy]⟩

instance : Nonempty (PFlat p R) :=
  let ⟨y, hy⟩ := Tilt.untilt_surjective_of_isAlgClosed (p := p) (p : R)
  ⟨⟨y, hy⟩⟩


variable (p R) in
def pflat : PFlat p R := Classical.arbitrary _

variable [CharZero R]

variable (p R) in
theorem exists_isPrimitive : ∃ ε : tateModule p R, IsPrimitive ε := by
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  haveI : NeZero (p : FractionRing R) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (FractionRing R) p
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R)
    (Fact.out : p.Prime).pos (x := ζ) (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  have hz := hζ.of_map_of_injective (IsFractionRing.injective R (FractionRing R))
  obtain ⟨y, hy⟩ := Tilt.seq_surjective (p := p) 1 z
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change PreTilt.untilt y = 1
    rw [← seq_zero, ← seq_succ_pow, zero_add, hy, hz.pow_eq_one]
  · rw [isPrimitive_iff]
    change seq 1 y ≠ 1
    rw [hy]
    exact hz.ne_one (Fact.out : p.Prime).one_lt

variable (p R) in
def eps : tateModule p R := (exists_isPrimitive p R).choose

variable (p R) in
theorem isPrimitive_eps : IsPrimitive (eps p R) := (exists_isPrimitive p R).choose_spec

end Good

namespace PFlat

variable [IsDomain R] [CharZero R]

variable [ValuationRing R]

end PFlat

end Reformulated.AutPerF
