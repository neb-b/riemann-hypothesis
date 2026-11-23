module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

abbrev FM (P : Pair G) : Type := AdjoinRoot P.pol

def jM (P : Pair G) : FM P →ₐ[G.F] G.C :=
  Ideal.Quotient.liftₐ _ (aeval (P.γ : G.C)) fun f hf => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.1 hf
    rw [map_mul, Pair.pol, minpoly.aeval, zero_mul]

theorem jM_mk (P : Pair G) (f : G.F[X]) : jM P (AdjoinRoot.mk P.pol f) = aeval (P.γ : G.C) f := rfl

theorem jM_root (P : Pair G) : jM P (AdjoinRoot.root P.pol) = P.γ := by
  rw [← AdjoinRoot.mk_X, jM_mk, aeval_X]

theorem jM_injective (P : Pair G) : Function.Injective (jM P) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [jM_mk] at ha
  exact AdjoinRoot.mk_eq_zero.2 (minpoly.dvd G.F _ ha)

theorem jM_algQ (P : Pair G) (q : ℚ) : jM P (algebraMap ℚ (FM P) q) = algebraMap ℚ G.C q := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F (FM P), AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem jM_comm (P : Pair G) (a : FM P) : jM P a * P.γ = P.γ * jM P a := by
  rw [← jM_root, ← map_mul, ← map_mul, mul_comm]

theorem exists_jM (P : Pair G) (u : G.C) (hu : u * P.γ = P.γ * u) : ∃ a, jM P a = u := by
  have hc : u ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact hu.symm
  rw [GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC _ P.reg.2 P.reg.1,
    Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨f, rfl⟩ := hc
  exact ⟨AdjoinRoot.mk _ f, rfl⟩

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp [sh, map_mul]

theorem sh_one : sh G (1 : G.C) = 1 := by simp [sh]

theorem sh_add (x y : G.C) : sh G (x + y) = sh G x + sh G y := by simp [sh, map_add (f := _)]

theorem sh_zero : sh G (0 : G.C) = 0 := by simp [sh]

theorem sh_sh (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_algF (a : G.F) : sh G (algebraMap G.F G.C a) = algebraMap G.F G.C (IsCMField.complexConj G.F a) :=
  G.star_F a

def iC (P : Pair G) (x : G.C) : G.C := (P.β : G.C) * sh G x * ((P.β⁻¹ : G.Cˣ) : G.C)

theorem iC_mul (P : Pair G) (x y : G.C) : iC P (x * y) = iC P y * iC P x := by
  simp only [iC, sh_mul, mul_assoc, Units.inv_mul_cancel_left]

theorem iC_one (P : Pair G) : iC P 1 = 1 := by simp [iC, sh_one]

theorem iC_add (P : Pair G) (x y : G.C) : iC P (x + y) = iC P x + iC P y := by
  simp [iC, sh_add, mul_add, add_mul]

theorem iC_zero (P : Pair G) : iC P 0 = 0 := by simp [iC, sh_zero]

theorem iC_algF (P : Pair G) (a : G.F) :
    iC P (algebraMap G.F G.C a) = algebraMap G.F G.C (IsCMField.complexConj G.F a) := by
  rw [iC, sh_algF, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem iC_algQ (P : Pair G) (q : ℚ) : iC P (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, iC_algF]
  congr 1
  simp

theorem iC_gamma_mul (P : Pair G) : iC P P.γ * P.γ = algebraMap ℚ G.C P.c := by
  have h := P.sim
  have h2 : (P.β : G.C) * sh G P.γ = ((P.γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C P.c * P.β) := by
    rw [← h]; simp only [← mul_assoc, Units.inv_mul, one_mul]
  calc iC P P.γ * P.γ = ((P.β : G.C) * sh G P.γ) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := rfl
    _ = ((P.γ⁻¹ : G.Cˣ) : G.C) * algebraMap ℚ G.C P.c * P.γ := by
        rw [h2]; simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [mul_assoc, Algebra.commutes, ← mul_assoc, Units.inv_mul, one_mul]

theorem iC_comm (P : Pair G) (u : G.C) (hu : u * P.γ = P.γ * u) : iC P u * P.γ = P.γ * iC P u := by
  have h1 : iC P u * iC P P.γ = iC P P.γ * iC P u := by rw [← iC_mul, ← iC_mul, hu]
  have hg : iC P P.γ = algebraMap ℚ G.C P.c * ((P.γ⁻¹ : G.Cˣ) : G.C) := by
    rw [← iC_gamma_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [hg, ← mul_assoc, ← Algebra.commutes, mul_assoc, mul_assoc] at h1
  have hc : IsUnit (algebraMap ℚ G.C P.c) := (P.c.isUnit).map _
  have h2 := hc.mul_left_cancel h1
  calc iC P u * P.γ = P.γ * (((P.γ⁻¹ : G.Cˣ) : G.C) * iC P u) * P.γ := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = P.γ * (iC P u * ((P.γ⁻¹ : G.Cˣ) : G.C)) * P.γ := by rw [h2]
    _ = _ := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

theorem iC_iC (P : Pair G) (x : G.C) : iC P (iC P x) = x := by
  have hb : sh G (P.β : G.C) = P.β := P.sym
  have hbi : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) := by
    have e : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * P.β = 1 := by
      rw [← hb, ← sh_mul, Units.mul_inv, sh_one]
    calc sh G ((P.β⁻¹ : G.Cˣ) : G.C) = sh G ((P.β⁻¹ : G.Cˣ) : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [e, one_mul]
  simp only [iC, sh_mul, hb, hbi, sh_sh, mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

def iMf (P : Pair G) (a : FM P) : FM P := (exists_jM P (iC P (jM P a)) (iC_comm P _ (jM_comm P a))).choose

theorem jM_iMf (P : Pair G) (a : FM P) : jM P (iMf P a) = iC P (jM P a) :=
  (exists_jM P (iC P (jM P a)) (iC_comm P _ (jM_comm P a))).choose_spec

def iM (P : Pair G) : FM P →ₐ[ℚ] FM P where
  toFun := iMf P
  map_one' := jM_injective P (by rw [jM_iMf, map_one, iC_one])
  map_mul' a b := jM_injective P (by
    rw [mul_comm (iMf P a), jM_iMf, map_mul, map_mul, jM_iMf, jM_iMf, iC_mul])
  map_zero' := jM_injective P (by rw [jM_iMf, map_zero, iC_zero])
  map_add' a b := jM_injective P (by rw [jM_iMf, map_add (f := _), map_add (f := _), jM_iMf, jM_iMf, iC_add])
  commutes' q := jM_injective P (by rw [jM_iMf, jM_algQ, iC_algQ])

theorem jM_iM (P : Pair G) (a : FM P) : jM P (iM P a) = iC P (jM P a) := jM_iMf P a

theorem iM_algF (P : Pair G) (a : G.F) :
    iM P (algebraMap G.F (FM P) a) = algebraMap G.F (FM P) (IsCMField.complexConj G.F a) :=
  jM_injective P (by rw [jM_iM, AlgHom.commutes, AlgHom.commutes, iC_algF])

theorem iM_root_mul (P : Pair G) :
    iM P (AdjoinRoot.root P.pol) * AdjoinRoot.root P.pol = algebraMap ℚ (FM P) P.c :=
  jM_injective P (by rw [map_mul, jM_iM, jM_root, jM_algQ, iC_gamma_mul])

theorem iM_iM (P : Pair G) (a : FM P) : iM P (iM P a) = a :=
  jM_injective P (by rw [jM_iM, jM_iM, iC_iC])

theorem mul_iM_of_cent (P : Pair G) (w : P.cent) (a : FM P) (ha : jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C)) :
    a * iM P a = algebraMap ℚ (FM P) ((w : G.Cˣ × ℚˣ).2 : ℚ) :=
  jM_injective P (by
    rw [map_mul, jM_iM, jM_algQ, ha, iC, ← mul_assoc, ← mul_assoc, w.2.2, mul_assoc, Units.mul_inv, mul_one])

theorem exists_pow_mem_conj {H : Type} [Group H] (K K₀ : Subgroup H) (g y : H) (hK : K.Commensurable K₀)
    (hy : y ∈ K.map (MulAut.conj g).toMonoidHom) :
    ∃ m : ℕ, 0 < m ∧ y ^ m ∈ K₀.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨k, hk, rfl⟩ := hy
  obtain ⟨m, hm0, -, hm⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (H := K₀.subgroupOf K) hK.2.relIndex_ne_zero (⟨k, hk⟩ : K)
  refine ⟨m, hm0, k ^ m, ?_, by simp [map_pow]⟩
  simpa [Subgroup.mem_subgroupOf] using hm

end GlobalTheory.StabFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAway
section
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.RatDenAwayP

theorem val_le_one (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) (v : AwayP p) :
    v.1.valuation ℚ q ≤ 1 := by
  have h1 : (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) v.1 ∈ v.1.adicCompletionIntegers ℚ := h v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  exact h1

def primeHOS (l : ℕ) (hl : l.Prime) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(l : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl)
  ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero

theorem prime_dvd_den (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) {l : ℕ} (hl : l.Prime)
    (hd : l ∣ q.den) : l = p := by
  by_contra hne
  have hv : (primeHOS l hl).asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro e
    have e' : Ideal.span {(l : ℤ)} = Ideal.span {(p : ℤ)} := e
    rw [Ideal.span_singleton_eq_span_singleton] at e'
    have h1 : l ∣ p := Int.natCast_dvd_natCast.1 e'.dvd
    have h2 : p ∣ l := Int.natCast_dvd_natCast.1 e'.symm.dvd
    exact hne (Nat.dvd_antisymm h1 h2)
  let v : AwayP p := ⟨primeHOS l hl, hv⟩
  have hq := val_le_one p q h v
  have hden : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) < 1 := by
    rw [valuation_lt_one_iff_mem]
    show ((q.den : ℤ)) ∈ Ideal.span {(l : ℤ)}
    rw [Ideal.mem_span_singleton]; exact_mod_cast hd
  have hnum : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ q.num) < 1 := by
    have e : algebraMap ℤ ℚ q.num = q * algebraMap ℤ ℚ (q.den : ℤ) := by
      rw [algebraMap_int_eq, eq_intCast, eq_intCast, Int.cast_natCast, Rat.mul_den_eq_num]
    rw [e, map_mul]
    calc (primeHOS l hl).valuation ℚ q * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ))
        ≤ 1 * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) := by gcongr
      _ < 1 := by rw [one_mul]; exact hden
  rw [valuation_lt_one_iff_mem] at hnum
  change q.num ∈ Ideal.span {(l : ℤ)} at hnum
  rw [Ideal.mem_span_singleton, Int.natCast_dvd] at hnum
  have hc : Nat.Coprime l q.den := Nat.Coprime.coprime_dvd_left hnum q.reduced
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 hc hd

end GlobalTheory.RatDenAwayP

namespace GlobalTheory

theorem ratDen_pow_of_intAfP : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p →
    ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  intro p _ q h
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hd => RatDenAwayP.prime_dvd_den p q h hl hd)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  rw [← hden]
  exact Rat.den_mul_eq_num q

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepTrivialAbove
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TrivAbove

variable {E : Type} [Field E] [NumberField E]

theorem one_coord' (w : HeightOneSpectrum (𝓞 E)) : (1 : Af E) w = 1 := rfl

theorem mul_coord' (x y : Af E) (w : HeightOneSpectrum (𝓞 E)) : (x * y) w = x w * y w := rfl

theorem inv_coord' (z : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : (↑z⁻¹ : Af E) w = ((z : Af E) w)⁻¹ := by
  show (((coord w z)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
  rw [Units.val_inv_eq_inv_val, coe_coord]


open Classical in
theorem prod_single_coord (S : Finset (HeightOneSpectrum (𝓞 E)))
    (x : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w' : HeightOneSpectrum (𝓞 E)) :
    ((∏ w ∈ S, single w (x w) : (Af E)ˣ) : Af E) w' = if w' ∈ S then (x w' : w'.adicCompletion E) else 1 := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Units.val_one, one_coord']; simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul, mul_coord', ih]
    by_cases h : w' = a
    · subst h; simp [ha, single_self]
    · rw [suppAt_single a (x a) w' h]; simp [h]

theorem mem_hatOUnits [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) (z : (Af E)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((z : Af E) w - 1) <
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) :
    z ∈ hatOUnits c := by
  have key : ∀ z : Af E, (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w - 1) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) → z ∈ hatO c :=
    fun z h => (GlobalTheory.T.mem_completedOrder_iff_placewise E c hc z).2 ⟨1, one_mem _, fun w => by rw [one_coord', map_one], h⟩
  refine ⟨key _ fun w => (hz w).le, key _ fun w => ?_⟩
  have h1 : Valued.v ((z : Af E) w - 1) < Valued.v (1 : w.adicCompletion E) := by
    rw [map_one]
    exact (hz w).trans_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hv : Valued.v ((z : Af E) w) = 1 := by
    have := Valuation.map_eq_of_sub_lt _ h1
    rwa [map_one] at this
  have hz0 : (z : Af E) w ≠ 0 := by rw [← coe_coord]; exact (coord w z).ne_zero
  show Valued.v ((↑z⁻¹ : Af E) w - 1) ≤ _
  rw [inv_coord']
  have he : ((z : Af E) w)⁻¹ - 1 = -(((z : Af E) w - 1) * ((z : Af E) w)⁻¹) := by
    field_simp; ring
  rw [he, Valuation.map_neg, map_mul, map_inv₀, hv, inv_one, mul_one]
  exact (hz w).le

theorem exists_rep_trivial_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (l : ℕ),
    c ≠ ⊥ → l.Prime → ∀ q : PicO c, ∃ y : (Af E)ˣ, (QuotientGroup.mk y : PicO c) = q ∧
      ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → (y : Af E) w = 1 := by
  intro E _ _ _ c l hc hl q
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite := by
    have hl0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero
    exact (Ideal.finite_factors hl0).subset fun w hw => Ideal.dvd_span_singleton.2 hw
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, -⟩ := PI.FinOrdValD.WA.weakApprox_units hfin.toFinset (fun w => (coord w y0)⁻¹)
    (fun w => (multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))
  set A : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom a with hAdef
  set y1 : (Af E)ˣ := A * y0 with hy1
  set u : (Af E)ˣ := ∏ w ∈ hfin.toFinset, single w (coord w y1) with hudef
  have hA : A ∈ princ ⊔ hatOUnits c := Subgroup.mem_sup_left ⟨a, rfl⟩
  have hu : u ∈ princ ⊔ hatOUnits c := by
    refine Subgroup.mem_sup_right (mem_hatOUnits hc u fun w => ?_)
    rw [hudef, prod_single_coord]
    split_ifs with hw
    · rw [coe_coord, hy1, Units.val_mul, mul_coord']
      have hAw : (A : Af E) w = algebraMap E (w.adicCompletion E) (a : E) := rfl
      have := ha w hw
      rw [hAw]
      simpa [Units.val_inv_eq_inv_val, coe_coord] using this
    · rw [sub_self, map_zero]; exact WithZero.exp_pos.bot_lt
  refine ⟨y1 * u⁻¹, ?_, fun w hw => ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy1, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff A).2 hA, (QuotientGroup.eq_one_iff u).2 hu, one_mul, inv_one, mul_one]
  · have hwT : w ∈ hfin.toFinset := hfin.mem_toFinset.2 hw
    rw [Units.val_mul, mul_coord', inv_coord', hudef, prod_single_coord, if_pos hwT, coe_coord]
    exact mul_inv_cancel₀ (by rw [← coe_coord]; exact (coord w y1).ne_zero)

end GlobalTheory.CMVal.TrivAbove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryLiftDetOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParahoricLiftDet

open GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta Formalism.MainNotions.S Formalism.IndefR.Mult MeasureTheory

variable {D : D7} {n : ℕ}

theorem finite_maximalSpectrum_kP (P : Pl D.host.E) : Finite (MaximalSpectrum (kP P)) := by
  have hP : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  exact Finite.of_subsingleton

theorem exists_detOne_lift (P : Pl D.host.E) (k : GL (Fin n) (kP P)) (hk : Matrix.GeneralLinearGroup.det k = 1) :
    ∃ Y : Matrix (Fin n) (Fin n) (𝓞 D.host.E), Y.map (Ideal.Quotient.mk P.asIdeal) = k.1 ∧ Y.det = 1 := by
  haveI := finite_maximalSpectrum_kP P
  have hk' : k.1.det = 1 := by
    have := congrArg Units.val hk
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  obtain ⟨Y, hY⟩ := GlobalTheory.specialLinearGroup_map_surjective (n := Fin n) (f := Ideal.Quotient.mk P.asIdeal)
    Ideal.Quotient.mk_surjective ⟨k.1, hk'⟩
  exact ⟨Y.1, congrArg Subtype.val hY, Y.2⟩

theorem idem_mul_pow {A : Type} [CommRing A] {p : A} (hp : p * p = p) (m : ℕ) : p * p ^ m = p := by
  induction m with
  | zero => rw [pow_zero, mul_one]
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, hp]

theorem idem_mul_det {A : Type} [CommRing A] {m : ℕ} {p : A} (hp : p * p = p) {a b : Matrix (Fin m) (Fin m) A}
    (h : p • a = p • b) : p * a.det = p * b.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin] at h1
  have hpow : p * p ^ m = p := idem_mul_pow hp m
  calc p * a.det = p * p ^ m * a.det := by rw [hpow]
    _ = p * p ^ m * b.det := by rw [mul_assoc, h1, ← mul_assoc]
    _ = p * b.det := by rw [hpow]


set_option maxHeartbeats 1000000 in
theorem exists_local_lift_det : ∀ {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}, IsBaseFrame V β Λ N → ∀ {P : Pl D.host.E} {e : AE D},
    Formalism.L2.NTheta.IsIdemAt e P → ∀ (k : GL (Fin V.rank) (kP P)), Matrix.GeneralLinearGroup.det k = 1 →
    ∃ κ : GA D V, SuppAt e V κ ∧ κ ∈ GfC V ∧ finE V κ ∈ St β ∧ redFn β P (finE V κ) = k ∧
      (∀ P', P' ≠ P → ¬ Lev.IsConjPl P P' → redFn β P' (finE V κ) = 1) ∧ IsDetAt e V κ 1 := by
  intro D V β Λ N hB P e he k hk
  have := P.isPrime
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  obtain ⟨Y₀, hY₀, hdet1⟩ := exists_detOne_lift P k hk
  have hdet : Ideal.Quotient.mk P.asIdeal Y₀.det ≠ 0 := by
    rw [hdet1, map_one]; exact one_ne_zero
  obtain ⟨u, hu⟩ := finSw_div_int he (d := Y₀.det) fun h => hdet (Ideal.Quotient.eq_zero_iff_mem.2 h)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Y₀.map (oToS D.host.F D.host.E) := ⟨_, rfl⟩
  have hYdet : Y.det = 1 := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet1, map_one]
  have hu' : u * Y.det = p := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Subtype.ext (hu.trans hp.symm)
  have hmm := conj_inv_part β p u Y hu' hpp
  rw [hp] at hmm
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin V he.1 _ _ hmm
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  have hκd := hκ
  rw [← hp] at hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add (f := _), finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ

  have hD : e * (mt V κ).det = e := by
    have he2 : finSw D e * finSw D e = finSw D e := by rw [← RingHom.map_mul, he.1.1]
    have h1 := idem_mul_det he2 hκd
    have e1 : (finE V κ).1 = (mt V κ).map (finSw D) := rfl
    have e2 : (β.1 * Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).1).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one,
        one_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hYdet, map_one]
    rw [e1, e2, ← RingHom.mapMatrix_apply, ← RingHom.map_det, mul_one, ← RingHom.map_mul] at h1
    have h2 : finPart D (e * (mt V κ).det) = finPart D e := (swp_bij (F := D.host.F) (E := D.host.E)).1 h1
    refine GlobalTheory.SplitScalar.adele_ext ?_ h2
    rw [RingHom.map_mul, GlobalTheory.PlaceModelSum.infPart_split he.1, zero_mul]
  refine ⟨κ, hs, (T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_, fun P' h1 h2 => ?_, ?_⟩
  · rw [redFn_of_smul_eq β P _ hSt p hres Y hκ, hY, ← hY₀]
    exact Matrix.ext fun i j => resS_oToS P _
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one β P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf
  · show ((1 : (AE D)ˣ) : AE D) = e * (mt V κ).det + (1 - e)
    rw [hD, Units.val_one]
    ring

end GlobalTheory.ParahoricLiftDet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDetRoot
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitDetRoot

theorem infPart_sigR_one (D : D7) (x : AE D) (hx : infPart D x = 1) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = 1 := by
  have h := GlobalTheory.DetRootCong.map_sigR (F := D.host.F) (E := D.host.E)
    (AlgHom.fst D.host.F (InfiniteAdeleRing D.host.F) (Af D.host.F)) D.sp.cm.sig x
  refine h.trans ?_
  exact (congrArg _ hx).trans (map_one _)

end GlobalTheory.UnitDetRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  first | exact @GlobalTheory.SplitDetCharacter.exists_character | exact GlobalTheory.SplitDetCharacter.exists_character | (intros; apply GlobalTheory.SplitDetCharacter.exists_character <;> assumption)
end

