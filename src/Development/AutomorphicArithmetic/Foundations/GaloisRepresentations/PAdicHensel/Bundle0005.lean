module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
section
noncomputable section

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo GlobalTheory.CongL

namespace UpperTheory.Gal.G1

def CjMem : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (w : HeightOneSpectrum (𝓞 E)) (y : 𝓞 E),
  y ∈ (CertificateRingHomMap.cj w).asIdeal ↔ A.bar y ∈ w.asIdeal

def DiscInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (y : 𝓞 E),
  (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} →
  ∃ a b : ℤ, ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y = (a : 𝓞 E) + (b : 𝓞 E) * A.ω

def BarAdj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (y : 𝓞 E),
  (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} → ((A.bar y : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)}

def KeyK : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (q : ℕ), q.Prime →
  ¬ (q : ℤ) ∣ A.tr ^ 2 - 4 * A.nm → ∀ (r : ℤ) (u w : HeightOneSpectrum (𝓞 E)), (q : 𝓞 E) ∈ u.asIdeal → (q : 𝓞 E) ∈ w.asIdeal →
  A.ω - (r : 𝓞 E) ∈ u.asIdeal → A.ω - (r : 𝓞 E) ∈ w.asIdeal →
  ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} → (y ∈ u.asIdeal ↔ y ∈ w.asIdeal)

theorem gen_of {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (x : E) (f : ℚ) (hf : f ≠ 0)
    (h : 2 * (A.ω : E) - (A.tr : E) = (f : E) * x) : Pl.Gen A x := by
  have hf' : (f : E) ≠ 0 := by exact_mod_cast hf
  constructor
  · have e : (A.ω : E) = ((A.tr : E) + (f : E) * x) / 2 := by rw [← h]; ring
    rw [e]
    exact div_mem (add_mem (intCast_mem _ _) (mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ x)))
      (ofNat_mem _ 2)
  · have e : x = (2 * (A.ω : E) - (A.tr : E)) / (f : E) := by rw [h]; field_simp
    rw [e]
    exact div_mem (sub_mem (mul_mem (ofNat_mem _ 2) (IntermediateField.mem_adjoin_simple_self ℚ _)) (intCast_mem _ _))
      (SubfieldClass.ratCast_mem _ _)

theorem datEx_of (h1 : AuxiliaryInertOddPrime) (h2 : ArithK) (h3 : SetupEx) (h4 : ScOf) (h5 : PerfCof) : Pl.DatEx := by
  intro E _ _ _ l _ n d hn hd x hx Q hQ
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨A, -, ⟨f, hf, hfx⟩, hs, hg⟩ := h2 E d hd.1.1 x hx τ₀ Q hQ
  obtain ⟨e, he, hc⟩ := h5 E A
  have hgood : ∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → ¬ q ∣ e → A.Good q := fun q hq' hq hqe =>
    ⟨hs q hq, hc q ((Nat.Prime.coprime_iff_not_dvd hq'.out).2 hqe).symm⟩
  refine ⟨A, hd.1.1, gen_of A x f hf hfx, hg, ⟨e, he, hgood⟩, fun X => ?_⟩
  obtain ⟨p, hp, hb, hsq⟩ := h1 d hd.1.1 (max e (X.sup id))
  have hpX : p ∉ X := fun h => by
    have : p ≤ X.sup id := Finset.le_sup (f := id) h
    omega
  obtain ⟨S⟩ := h3 E A n p hn.pos (hgood p hsq fun h => by have := Nat.le_of_dvd he h; omega)
  exact ⟨p, hp, S, hpX, h4 E hd.2.2.1 A n p S hn⟩

end UpperTheory.Gal.G1
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PArithK
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

private lemma conj_sqrt_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (d : ℕ) (x : E)
    (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : IsCMField.complexConj E x = -x :=
  _root_.UpperTheory.Reformulated.B.ConjugateSqrtNeg.conj_sqrt_neg d x hd hx

private lemma omega_at {E : Type} [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) (d : ℕ) (x : E)
    (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (tr nm : ℤ) (f : ℚ)
    (hdisc : ((tr ^ 2 - 4 * nm : ℤ) : ℚ) = f ^ 2 * (-(d : ℚ))) :
    ∃ ω : 𝓞 E, ω + bar ω = (tr : 𝓞 E) ∧ ω * bar ω = (nm : 𝓞 E) ∧
      2 * (ω : E) - (tr : E) = (f : E) * x := by
  have hcx := conj_sqrt_neg d x hd hx
  have hdiscE : ((tr : E) ^ 2 - 4 * (nm : E)) = (f : E) ^ 2 * (-(d : E)) := by
    have := congrArg (algebraMap ℚ E) hdisc
    simpa using this
  obtain ⟨w, hw⟩ : ∃ w : E, w = ((tr : E) + (f : E) * x) / 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : E, v = ((tr : E) - (f : E) * x) / 2 := ⟨_, rfl⟩
  have hcw : IsCMField.complexConj E w = v := by
    simp only [hw, hv, map_div₀, map_add (f := _), map_mul, map_intCast, map_ratCast, hcx, map_ofNat]
    ring
  have hsum : w + v = (tr : E) := by
    rw [hw, hv]; ring
  have hprod : w * v = (nm : E) := by
    have h : w * v = ((tr : E) ^ 2 - (f : E) ^ 2 * x ^ 2) / 4 := by
      rw [hw, hv]; ring
    rw [h, hx]
    linear_combination (1 / 4 : E) * hdiscE
  have hroot : w ^ 2 - (tr : E) * w + (nm : E) = 0 := by
    rw [← hsum, ← hprod]; ring
  have hint : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + (Polynomial.C (-tr) * Polynomial.X + Polynomial.C nm), ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      exact lt_of_le_of_lt (Polynomial.degree_linear_le) (by norm_num)
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      simp only [eq_intCast, Int.cast_neg]
      linear_combination hroot
  obtain ⟨ω, hω⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hint
  have hω' : (ω : E) = w := hω
  have hbω : ((bar ω : 𝓞 E) : E) = v := by rw [hbar, hω', hcw]
  refine ⟨ω, ?_, ?_, ?_⟩
  · apply RingOfIntegers.ext
    simp only [map_add (f := _), map_intCast, hω', hbω, hsum]
  · apply RingOfIntegers.ext
    simp only [map_mul, map_intCast, hω', hbω, hprod]
  · rw [hω', hw]; ring

theorem UpperTheory.Gal.G1.pArithK :
    BarEx → QuadEx → CEx → UnitMod → CodiffGen → CodiffUnit → IdemEx → RealGen → PosGen → DeltaEx → PerfOf → ArithK := by
  intro hBar hQuad hC hUnit _ _ hIdem hReal hPos hDelta hPerf E _ _ _ d hd x hx τ₀ Q hQ
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ∏ q ∈ Q, q := ⟨_, rfl⟩
  have hprime : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1.out
  have hM : 0 < M := by
    rw [hMdef]
    exact Finset.prod_pos fun q hq => (hprime q hq).pos
  have hmem : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ Q := by
    intro q hq hqM
    rw [hMdef] at hqM
    obtain ⟨a, ha, hqa⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 hqM
    rwa [(Nat.prime_dvd_prime_iff_eq hq (hprime a ha)).1 hqa]
  obtain ⟨bar, hbar⟩ := hBar E
  obtain ⟨tr, nm, f, hneg, hdisc, hsplit⟩ := hQuad d hd
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h0 : ((tr ^ 2 - 4 * nm : ℤ) : ℚ) = 0 := by rw [hdisc]; ring
    have h1 : tr ^ 2 - 4 * nm = 0 := by exact_mod_cast h0
    omega
  obtain ⟨ω, htr, hnm, hωx⟩ := omega_at bar hbar d x hd hx tr nm f hdisc
  obtain ⟨c, hc1, hc2, hc3, b, hb⟩ := hC E τ₀ M hM
  have hbb : ∀ y, bar (bar y) = y := by
    intro y
    apply Subtype.ext
    show ((bar (bar y) : 𝓞 E) : E) = (y : E)
    rw [hbar, hbar, IsCMField.complexConj_apply_apply]
  have hsp : ∀ q ∈ Q, ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm := by
    intro q hq
    obtain ⟨hF, hs⟩ := hQ q hq
    exact hsplit q hs
  obtain ⟨ε, hε⟩ := hIdem E bar ω tr nm hbb htr hnm M hM
    (fun q hq hqM => hsp q (hmem q hq hqM))
  obtain ⟨t, ht1, ht2⟩ := hReal E bar hbar M hM ε hε
  obtain ⟨t', ht1', ht2', ht3'⟩ := hPos E M hM t ht1 ht2
  have hcop : IsCoprime (tr ^ 2 - 4 * nm) (M : ℤ) := by
    rw [hMdef, Nat.cast_prod]
    refine IsCoprime.prod_right fun q hq => ?_
    exact ((Nat.prime_iff_prime_int.1 (hprime q hq)).coprime_iff_not_dvd.2 (hsp q hq).1).symm
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := hDelta E bar hbar ω tr nm htr hnm hneg M hcop t' ht1' ht2' ht3' τ₀
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc2
  let A : Arith E :=
    { bar := bar, bar_eq := hbar, ω := ω, tr := tr, nm := nm, tr_eq := htr, nm_eq := hnm, disc_neg := hneg,
      τ₀ := τ₀, c := c, c_real := Subtype.ext ((hbar c).trans hc1), c_neg := hc2, c_pos := hc3,
      δ := δ, δ_im := hδ1, δ_int := hδ2.1, δ_sign := hδ3 }
  refine ⟨A, rfl, ⟨f, hf0, hωx⟩, fun q _ hq => hsplit q hq, fun q hq => ⟨hsp q hq, ?_⟩⟩
  have hdvd : q ∣ M := by
    rw [hMdef]
    exact Finset.dvd_prod_of_mem _ hq
  exact hPerf E A M hδ2 (hUnit E M c b hc0 hb) q hdvd
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAuxPrime
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

private theorem sq_of_dvd (p : ℕ) [Fact p.Prime] (d m : ℕ) (h1 : p ∣ m ^ 2 + d) (h2 : ¬ p ∣ 2 * m) :
    IsSquare (-(d : ℚ_[p])) := by
  have hp : (p : ℤ) ∣ ((m ^ 2 + d : ℕ) : ℤ) := by exact_mod_cast h1
  have hq : ¬ (p : ℤ) ∣ ((2 * m : ℕ) : ℤ) := by exact_mod_cast h2
  set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[p]) with hF
  set a : ℤ_[p] := ((m : ℤ) : ℤ_[p]) with ha
  have e1 : Polynomial.aeval a F = (((m ^ 2 + d : ℕ) : ℤ) : ℤ_[p]) := by
    simp [hF, ha]
  have e2 : Polynomial.aeval a (Polynomial.derivative F) = (((2 * m : ℕ) : ℤ) : ℤ_[p]) := by
    simp [hF, ha]
    left
    norm_num
  have n1 : ‖Polynomial.aeval a F‖ < 1 := by
    rw [e1]; exact (PadicInt.norm_int_lt_one_iff_dvd _).2 hp
  have n2 : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    rw [e2]
    exact le_antisymm (PadicInt.norm_le_one _)
      (not_lt.1 fun h => hq ((PadicInt.norm_int_lt_one_iff_dvd _).1 h))
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [n2]; simpa using n1)
  have hz' : z ^ 2 + (d : ℤ_[p]) = 0 := by simpa [hF] using hz
  have hz'' : ((z : ℚ_[p])) ^ 2 + (d : ℚ_[p]) = 0 := by
    have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz'
    simpa using this
  refine ⟨(z : ℚ_[p]), ?_⟩
  linear_combination -hz''

theorem UpperTheory.Gal.G1.exists_auxiliary_prime_cmDatum :
    AuxiliaryInertOddPrime := by
  intro d hd b
  set c := (max b (2 * d)).factorial with hc
  have hcpos : 0 < c := Nat.factorial_pos _
  have hN : d * c ^ 2 + 1 ≠ 1 := by
    have : 0 < d * c ^ 2 := by positivity
    omega
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hN
  have hpc : ¬ p ∣ c := fun h => by
    have h2 : p ∣ d * c ^ 2 := Dvd.dvd.mul_left (dvd_pow h (by norm_num)) d
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 hdvd))
  have hgt : max b (2 * d) < p := by
    by_contra h
    exact hpc ((hp.dvd_factorial).2 (not_lt.1 h))
  have hb : b < p := lt_of_le_of_lt (le_max_left _ _) hgt
  have h2d : 2 * d < p := lt_of_le_of_lt (le_max_right _ _) hgt
  have hpd : ¬ p ∣ d := fun h => by
    have := Nat.le_of_dvd hd h
    omega
  have hp2 : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, inferInstance, hb, sq_of_dvd p d (d * c) ?_ ?_⟩
  · have : (d * c) ^ 2 + d = d * (d * c ^ 2 + 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_left hdvd d
  · intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hpd h
      · exact hpc h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRootAt
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pRootAt :
    RootAt := by
  intro E _ _ _ A q _ hs w hw
  obtain ⟨_, r, k, hk⟩ := hs
  have hkE : (r : 𝓞 E) ^ 2 - (A.tr : 𝓞 E) * (r : 𝓞 E) + (A.nm : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hk
  have hprod : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) = (q : 𝓞 E) * (-(k : 𝓞 E)) := by
    have htr := A.tr_eq
    have hnm := A.nm_eq
    have h0 : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
      rw [← htr, ← hnm]; ring
    push_cast
    linear_combination h0 - hkE
  have hmem : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) ∈ w.asIdeal := by
    rw [hprod]; exact w.asIdeal.mul_mem_right _ hw
  rcases w.isPrime.mem_or_mem hmem with h | h
  · exact ⟨r, ⟨k, hk⟩, h⟩
  · refine ⟨A.tr - r, ⟨k, ?_⟩, h⟩
    rw [← hk]; ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScOf
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pScOf :
    SetupBasic → ScOf := by
  intro hB E _ _ _ hev A n p _ S hn
  obtain ⟨hga, -, hc⟩ := hB E A n p S
  have hmul : Module.finrank ℚ (maximalRealSubfield E) * Module.finrank (maximalRealSubfield E) E =
      Module.finrank ℚ E := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hpos : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
  have hlt : 2 < Module.finrank ℚ E := by
    obtain ⟨k, hk⟩ := hev
    rw [← hmul, h2]
    omega
  exact ⟨rfl, rfl, hga, hn, (hc hlt).2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PStdForm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

private lemma c_re_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (τ : E →+* ℂ)
    (h : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀) : (τ (A.c : E)).re < 0 := by
  rcases InfinitePlace.mk_eq_iff.mp h with h | h
  · rw [h]; exact A.c_neg
  · have h1 := A.c_neg
    rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h1
    exact h1

private lemma dg_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.dg n i : 𝓞 E) : E) ≠ 0 := by
  have := A.c_ne
  unfold Arith.dg
  split_ifs <;> simp [this]

private lemma dg_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.dg n i : 𝓞 E) : E) = ((A.dg n i : 𝓞 E) : E) := by
  have h : A.bar (A.dg n i) = A.dg n i := by
    unfold Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

private lemma hd_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.hd n i : 𝓞 E) : E) = ((A.hd n i : 𝓞 E) : E) := by
  have h : A.bar (A.hd n i) = A.hd n i := by
    unfold Arith.hd Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

private lemma hd_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.hd n i : 𝓞 E) : E) = -(A.c : E) * ((A.dg n i : 𝓞 E) : E) := by
  simp [Arith.hd]

private lemma re_form {n : ℕ} (a : ℂ) (x : Fin n → ℂ) :
    (star x ⬝ᵥ ((Matrix.diagonal fun _ => a) *ᵥ x)).re = a.re * ∑ i, Complex.normSq (x i) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (x i) * (a * x i) = a * ((Complex.normSq (x i) : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h, Complex.re_mul_ofReal]

private lemma sum_pos' {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < ∑ i, Complex.normSq (x i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

private lemma form_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (e : E →+* ℂ) :
    ((A.H n).map e)ᵀ * (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)⁻¹).map e =
      Matrix.diagonal fun _ => -e (A.c : E) := by
  unfold Arith.H
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [hd_eq, map_mul, map_neg, map_inv₀, mul_assoc, mul_inv_cancel₀ ((map_ne_zero e).2 (dg_ne A n i)), mul_one]

private lemma sym_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    ((A.H n).map (cj E))⁻¹ * ((Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)).map (cj E))ᵀ * (A.H n).map (cj E) =
      Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E) := by
  have hH : (A.H n).map (cj E) = A.H n := by
    unfold Arith.H
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact hd_cj A n i
  have hD : (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)).map (cj E) =
      Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact dg_cj A n i
  have hu : IsUnit (A.H n).det := (A.det_ne n).isUnit
  have hc : (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)) * A.H n =
      A.H n * Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E) := by
    unfold Arith.H
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [hH, hD, Matrix.diagonal_transpose, Matrix.mul_assoc, hc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNormHolds
section
namespace UpperTheory.Gal.G1

theorem LocFour_holds : LocFour := pLocFour
theorem HenselV_holds : HenselV := pHenselV
theorem SplitRep_holds : SplitRep := pSplitRep
theorem BlockMat_holds : BlockMat := pBlockMat
theorem PadMap_holds : PadMap := pPadMap
theorem Scale_holds : Scale := pScale
theorem PadicUnitNorm_holds : PadicUnitNorm := pPadicUnitNorm
theorem PadicSqFin_holds : PadicSqFin := pPadicSqFin
theorem TrivMat_holds : TrivMat := pTrivMat
theorem CongrScale_holds : CongrScale := pCongrScale
theorem SplitCongr_holds : SplitCongr := pSplitCongr
theorem InfCongr_holds : InfCongr := pInfCongr
theorem DefSign_holds : DefSign := pDefSign
theorem RelOf_holds : RelOf := pRelOf
theorem LocUnit_holds : LocUnit := pLocUnit HenselV_holds
theorem LocRoot_holds : LocRoot := pLocRoot HenselV_holds
theorem ZUnitNorm_holds : ZUnitNorm := pZUnitNorm PadicUnitNorm_holds
theorem ZSqFin_holds : ZSqFin := pZSqFin PadicSqFin_holds
theorem AdFour_holds : AdFour := pAdFour LocFour_holds LocUnit_holds LocRoot_holds SplitRep_holds
theorem UnitCls_holds : UnitCls := pUnitCls Scale_holds ZUnitNorm_holds ZSqFin_holds
theorem FinCongr_holds : FinCongr := pFinCongr PadMap_holds LocRoot_holds TrivMat_holds CongrScale_holds SplitCongr_holds DefSign_holds
theorem NormTwo_holds : NormTwo := pNormTwo AdFour_holds
theorem FinCls_holds : FinCls := pFinCls UnitCls_holds FinCongr_holds InfCongr_holds DefSign_holds RelOf_holds
theorem IsoEx_holds : IsoEx := pIsoEx NormTwo_holds BlockMat_holds

end UpperTheory.Gal.G1
end

