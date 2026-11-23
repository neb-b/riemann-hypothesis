module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0003
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.FiniteDimensionalRoots
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial

namespace UpperTheory.KStar.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_roots {M : ℕ} (hM : M ≠ 0) :
    FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}) := by
  have hfin : ({x : Om l | x ^ M = 1} : Set (Om l)).Finite := by
    apply (Polynomial.nthRootsFinset M (1 : Om l)).finite_toSet.subset
    intro x hx
    simpa [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hM)] using hx
  haveI : Finite ({x : Om l | x ^ M = 1} : Set (Om l)) := hfin.to_subtype
  apply IntermediateField.finiteDimensional_adjoin
  intro x hx
  refine ⟨Polynomial.X ^ M - 1, Polynomial.monic_X_pow_sub_C 1 hM, ?_⟩
  simp [Set.mem_setOf_eq.mp hx]

def rootsExt (l : ℕ) [Fact l.Prime] (M : ℕ) (hM : M ≠ 0) : FinExt l :=
  ⟨IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}, finiteDimensional_roots hM⟩

theorem mem_of_rootsExt_le {M : ℕ} (hM : M ≠ 0) {LL : FinExt l} (h : (rootsExt l M hM).1 ≤ LL.1) (x : Om l)
    (hx : x ^ M = 1) : x ∈ LL.1 :=
  h (IntermediateField.subset_adjoin _ _ hx)

theorem le_roots_of_dense {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (J : H.E →+* Om l) (K : FinExt l) {M : ℕ} (hM : M ≠ 0)
    (hN : H.condN ∣ M) (hdense : (K.1 : Set (Om l)) ⊆ closure (Set.range J)) :
    K.1 ≤ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1} := by
  set A := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1} with hA
  haveI : FiniteDimensional ℚ_[l] A := finiteDimensional_roots hM
  have hrange : Set.range J ⊆ (A : Set (Om l)) := by
    rintro _ ⟨y, rfl⟩
    apply H.image_mem_of_roots J A.toSubfield
    intro z hz
    apply IntermediateField.subset_adjoin
    obtain ⟨k, hk⟩ := hN
    show z ^ M = 1
    rw [hk, pow_mul, hz, one_pow]
  have hclosed : IsClosed (A : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule A.toSubalgebra)
  intro x hx
  exact closure_minimal hrange hclosed (hdense hx)

theorem lcm_ne_zero {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : Nat.lcm l H.condN ≠ 0 :=
  Nat.lcm_ne_zero (Fact.out : l.Prime).ne_zero H.condN_ne_zero

theorem kw_le_roots {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) {Ω : Type} [Field Ω] [Algebra H.E Ω]
    {Gw : Subgroup (Ω ≃ₐ[H.E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l H.E Ω Gw O) :
    B.Kw.1 ≤ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ Nat.lcm l H.condN = 1} :=
  le_roots_of_dense H (B.j.comp (algebraMap H.E Ω)) B.Kw (lcm_ne_zero H) (Nat.dvd_lcm_right _ _) B.j_dense

end UpperTheory.KStar.Cyc

end
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
section
namespace UpperTheory.Small

open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain

variable {R : Ranks} (H : Host R)

theorem not_dvd_QS {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) : ¬ l ∣ H.QS := fun h =>
  hs (Nat.mem_primeFactors.2 ⟨hl, h, H.QS_pos.ne'⟩)

theorem not_dvd_condN {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) (hq : l ≠ H.q) (hd : l ≠ H.d) : ¬ l ∣ H.condN := by
  intro h
  rcases (Nat.Prime.dvd_mul hl).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hl).1 h1 with h2 | h2
    · exact not_dvd_QS H hl hs h2
    · exact hq ((Nat.prime_dvd_prime_iff_eq hl H.hyp.1).1 h2)
  · exact hd ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).1 h1)

theorem factorization_condN_le {l : ℕ} (hl : l.Prime) :
    H.condN.factorization l ≤ max 1 (H.QS.factorization l) ∧ (l = 2 → H.condN.factorization l ≤ H.QS.factorization l) := by
  have hq := H.hyp.1
  have hd := H.hyp.2.1
  have h8 := H.hyp.2.2.1
  have h16 := H.hyp.2.2.2.1
  have e : H.condN.factorization l = H.QS.factorization l + H.q.factorization l + H.d.factorization l := by
    show (H.QS * H.q * H.d).factorization l = _
    rw [Nat.factorization_mul (mul_ne_zero H.QS_pos.ne' hq.ne_zero) hd.ne_zero,
      Nat.factorization_mul H.QS_pos.ne' hq.ne_zero]
    rfl
  rw [e, hq.factorization, hd.factorization, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h1 : H.q = l
  · have hs := factorization_eq_zero H (h1 ▸ q_not_mem H)
    have h2 : H.d ≠ l := by omega
    rw [if_pos h1, if_neg h2, hs]
    exact ⟨by simp, fun h => by omega⟩
  · by_cases h2 : H.d = l
    · have hs := factorization_eq_zero H (h2 ▸ d_not_mem H)
      rw [if_neg h1, if_pos h2, hs]
      exact ⟨by simp, fun h => by omega⟩
    · rw [if_neg h1, if_neg h2]
      exact ⟨by simp, fun _ => by simp⟩

theorem image_mem_Kur_sup {l : ℕ} [Fact l.Prime] (J : H.E →+* Om l) {s : ℕ} (hs : H.condN.factorization l ≤ s) (x : H.E) :
    J x ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} := by
  have hl : l.Prime := Fact.out
  have hN := H.toHostRaw.condN_ne_zero
  refine H.toHostRaw.image_mem_of_roots J
    (MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}).toSubfield (fun y hy => ?_) x
  set a := l ^ H.condN.factorization l with ha
  set b := H.condN / a with hb
  have hab : a * b = H.condN := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hco : Nat.Coprime a b := (Nat.coprime_ordCompl hl hN).pow_left _
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hy
    exact zero_ne_one hy
  have hbez := Nat.gcd_eq_gcd_ab a b
  rw [hco.gcd_eq_one] at hbez
  have e : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hy0, ← hbez]
    simp
  have h1 : y ^ a ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _
    ⟨b, Nat.ordCompl_pos l hN, Nat.not_dvd_ordCompl hl hN, by rw [← pow_mul, hab, hy]⟩
  have h2 : y ^ b ∈ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} := by
    refine IntermediateField.subset_adjoin _ _ ?_
    obtain ⟨c, hc⟩ := pow_dvd_pow l hs
    show (y ^ b) ^ (l ^ s) = 1
    rw [hc, ← ha, ← pow_mul, ← mul_assoc, mul_comm b a, hab, pow_mul, hy, one_pow]
  show y ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}
  rw [e]
  exact mul_mem (zpow_mem ((le_sup_left : MaximalUnramifiedExtension l ≤ _) h1) _)
    (zpow_mem ((le_sup_right : IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} ≤ _) h2) _)

theorem not_mem_of_ramIdx_one {l : ℕ} (hl : l.Prime) (P : HeightOneSpectrum (𝓞 H.E)) (hP : (l : 𝓞 H.E) ∈ P.asIdeal)
    (he : P.asIdeal.ramificationIdx ℤ = 1) : l ∉ H.small := by
  intro hs
  obtain ⟨P, hPp, hP0⟩ := P
  have h2 := H.toHostAx.mem_sq_of_dvd_QS H.QS_exact hl (Nat.dvd_of_mem_primeFactors hs) P hP
  have he' : P.ramificationIdx ℤ = 1 := he
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 H.E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hP
  have : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hPp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) P hb] at he'
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he'
  rw [hmap, Ideal.span_le]
  simpa using h2

end UpperTheory.Small
end

