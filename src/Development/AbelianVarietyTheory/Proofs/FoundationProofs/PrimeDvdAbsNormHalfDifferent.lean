module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224

@[expose] public section

noncomputable section

namespace GlobalTheory.HalfCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level Coeff Moduli)

variable {D : D7}

abbrev badInt (D : D7) : ℕ := D.host.QS * D.host.q * Ideal.absNorm D.host.ccK

theorem exists_prime_under {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ∀ N : ℕ, (N : 𝓞 K) ∈ P.asIdeal ↔ p ∣ N := by
  haveI := P.isPrime
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨ringChar (𝓞 K ⧸ P.asIdeal), CharP.char_is_prime (𝓞 K ⧸ P.asIdeal) _, fun N => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]

theorem mem_of_dvd {R : Type} [CommRing R] {J : Ideal R} {p N : ℕ} (hp : (p : R) ∈ J) (h : p ∣ N) : (N : R) ∈ J := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  exact J.mul_mem_right _ hp

theorem not_mem_of_coprime {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {a b : ℕ}
    (h : Nat.Coprime a b) (hb : (b : 𝓞 K) ∈ P.asIdeal) : (a : 𝓞 K) ∉ P.asIdeal := by
  intro ha
  obtain ⟨p, hp, hP⟩ := exists_prime_under P
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h ((hP a).1 ha) ((hP b).1 hb))

theorem exists_place_of_dvd_absNorm {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (J : Ideal (𝓞 K))
    (h : p ∣ Ideal.absNorm J) : ∃ P : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ P.asIdeal ∧ P.asIdeal ∣ J := by
  obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp J h
  have hm : (p : 𝓞 K) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [hu]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨P, hP.isPrime, ?_⟩, hm, hd⟩
  rintro rfl
  exact hp.ne_zero (by simpa using hm)

theorem prime_dvd_absNorm_halfDifferent (D : D7) {p : ℕ} (hp : p.Prime) :
    p ∣ Ideal.absNorm D.host.𝔟 ↔ p ∣ D.host.QS * D.host.q :=
  D.host.prime_dvd_absNorm_half_iff hp

theorem coprime_ccK (D : D7) : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.QS * D.host.q) :=
  Nat.Coprime.mul_right D.host.ccK_coprimeS (D.host.ccK_coprime _ (by simp))

theorem ccE_ne_bot (D : D7) : D.host.ccE ≠ ⊥ := fun h =>
  D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)

theorem absNorm_ccK_mem {P : Place D} (h : P.asIdeal ∣ D.host.ccE) :
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
  rw [map_natCast] at this
  exact Ideal.le_of_dvd h this

theorem two_q_mem {P : Place D} (h : P.asIdeal ∣ D.host.𝔟) : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  obtain ⟨p, hp, hP⟩ := exists_prime_under P
  exact (hP _).2 ((prime_dvd_absNorm_halfDifferent D hp).1 ((hP _).1 (Ideal.le_of_dvd h (Ideal.absNorm_mem _))))

theorem primeToAA_iff (P : Place D) : PrimeToAA D P ↔ ¬ P.asIdeal ∣ D.host.ccE ∧ ¬ P.asIdeal ∣ D.host.𝔟 := by
  classical
  have hb := D.host.half_ne_bot
  have hc := ccE_ne_bot D
  have hnot : ¬ (P.asIdeal ∣ D.host.ccE ∧ P.asIdeal ∣ D.host.𝔟) := fun h =>
    not_mem_of_coprime P (coprime_ccK D) (two_q_mem h.2) (absNorm_ccK_mem h.1)
  unfold PrimeToAA Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [FractionalIdeal.count_mul _ _ (FractionalIdeal.coeIdeal_ne_zero.2 hc)
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)), FractionalIdeal.count_inv,
    FractionalIdeal.count_coe _ _ hc, FractionalIdeal.count_coe _ _ hb]
  rw [← Associates.count_ne_zero_iff_dvd hc P.irreducible, ← Associates.count_ne_zero_iff_dvd hb P.irreducible] at hnot ⊢
  omega

theorem primeToAA_of_not_mem {P : Place D} (h : ((badInt D : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : PrimeToAA D P :=
  (primeToAA_iff P).2 ⟨fun hc => h (mem_of_dvd (absNorm_ccK_mem hc) (Dvd.intro_left _ rfl)),
    fun hb => h (mem_of_dvd (two_q_mem hb) (Dvd.intro _ rfl))⟩

section Lev

variable {H : ModHost D}

end Lev

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Rec

end GlobalTheory.HalfCompare
