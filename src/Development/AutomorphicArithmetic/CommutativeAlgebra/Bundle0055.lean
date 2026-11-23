module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
section
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.ActionSupremumCommute

variable {A O M : Type} [CommRing A] [Ring O] [Algebra A O] [AddCommGroup M] [Module O M]

private lemma nat_act (N : ℕ) (y : M) : algebraMap A O (N : A) • y = N • y := by
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

private lemma act_comm (c d : A) (y : M) :
    algebraMap A O c • algebraMap A O d • y = algebraMap A O d • algebraMap A O c • y := by
  rw [smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm c d]

private lemma exists_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) :
    ∃ r s : A, b = r * a + s * (N : A) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hv
  exact ⟨r, s, rfl⟩

private lemma act_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) (w : M) :
    ∃ y z : M, algebraMap A O b • w = algebraMap A O a • y + N • z := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • w, algebraMap A O s • w, ?_⟩
  rw [map_add (f := _), add_smul, map_mul, map_mul, mul_smul, mul_smul, act_comm r a, act_comm s (N : A), nat_act]

private lemma act_sup_of {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)})
    {y z : M} (hy : algebraMap A O a • y = N • z) :
    ∃ z' : M, algebraMap A O b • y = N • z' := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • z + algebraMap A O s • y, ?_⟩
  rw [map_add (f := _), add_smul, map_mul, map_mul, mul_smul, mul_smul, hy, nat_act, smul_add,
    smul_comm N (algebraMap A O r) z, smul_comm N (algebraMap A O s) y]

private lemma fwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) (W : Submodule O M)
    (hW : ∀ c ∈ 𝔞, ∀ z : M, algebraMap A O c • z ∈ W) {y z : M}
    (hy : algebraMap A O a • y = N • z) : y ∈ W := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ u ∈ W, algebraMap A O t • y = N • u := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z', hz'⟩ := act_sup_of hb hy
      refine ⟨algebraMap A O c • z', hW c hc z', ?_⟩
      rw [mul_comm b c, map_mul, mul_smul, hz']
      exact smul_comm _ _ _
    · rintro t t' ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
      exact ⟨u + v, W.add_mem hu hv, by rw [map_add (f := _), add_smul, hu', hv', smul_add]⟩
  obtain ⟨u, hu, hu'⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hu'
  rwa [inj y u hu']

private lemma bwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)}) {y : M}
    (hy : y ∈ Submodule.span O {z : M | ∃ c ∈ 𝔞 ^ 1, ∃ z' : M, z = algebraMap A O c • z'}) :
    ∃ z : M, algebraMap A O a • y = N • z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    rw [pow_one] at hc
    have hac : a * c ∈ Ideal.span {(N : A)} :=
      h ▸ Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) hc
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hac
    refine ⟨algebraMap A O t • z', ?_⟩
    rw [← mul_smul, ← map_mul, ← ht, map_mul, mul_smul, act_comm t (N : A), nat_act]
  | zero => exact ⟨0, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hx'
    exact ⟨u + v, by rw [smul_add, hu, hv, smul_add]⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o • u, ?_⟩
    rw [← mul_smul, Algebra.commutes, mul_smul, hu]
    exact smul_comm _ _ _

private lemma part2 {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) {x : M}
    (hx : ∀ c ∈ 𝔞, ∃ z : M, algebraMap A O c • x = N • z) :
    ∃ y z : M, x = algebraMap A O a • y + N • z := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ y z : M, algebraMap A O t • x = N • (algebraMap A O a • y + N • z) := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z0, hz0⟩ := hx c hc
      obtain ⟨y, z, hyz⟩ := act_sup (O := O) hb z0
      refine ⟨y, z, ?_⟩
      rw [map_mul, mul_smul, hz0, ← hyz]
      exact smul_comm _ _ _
    · rintro t t' ⟨y, z, h1⟩ ⟨y', z', h2⟩
      refine ⟨y + y', z + z', ?_⟩
      rw [map_add (f := _), add_smul, h1, h2]
      simp only [smul_add]
      abel
  obtain ⟨y, z, hyz⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hyz
  exact ⟨y, z, inj _ _ hyz⟩

end UpperTheory.ActionSupremumCommute

theorem UpperTheory.lattice_generation :
    LatGen := by
  intro q _ D a N 𝔞 hN hG
  haveI := D.freeLa
  have inj : ∀ u v : D.La, N • u = N • v → u = v := by
    intro u v huv
    have h0 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, huv, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact absurd (Int.natCast_eq_zero.mp h1) hN.ne'
    · exact sub_eq_zero.mp h1
  refine ⟨fun y => ⟨fun ⟨z, hz⟩ => UpperTheory.ActionSupremumCommute.fwd hG inj _ ?_ hz,
    fun hy => UpperTheory.ActionSupremumCommute.bwd hG hy⟩, fun x hx => UpperTheory.ActionSupremumCommute.part2 hG inj hx⟩
  intro c hc z
  exact Submodule.subset_span ⟨c, by rwa [pow_one], z, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplierIsUnit
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes GlobalTheory.LKGeo.MultScale
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

namespace UpperTheory.MultiplicativeUnitDivisibility

variable {p : ℕ} [Fact p.Prime]

private theorem exists_dvd_EFA (D : Datum p) (d : ℤ) (hd : ∀ x y : D.La, d ∣ D.EF x y)
    {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    ∃ c : AfP p, IsIntAf c ∧ EFA D v w = (d : AfP p) * c := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, x, ha, rfl⟩ := hv
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a', x', ha', rfl⟩ := hw
      obtain ⟨k, hk⟩ := hd x x'
      refine ⟨a * a' * (k : AfP p), isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast k), ?_⟩
      rw [EFA_tmul, hk]
      push_cast
      ring
    | zero => exact ⟨0, isIntAf_zero, by simp⟩
    | add u u' _ _ h h' =>
      obtain ⟨c, hc, e⟩ := h
      obtain ⟨c', hc', e'⟩ := h'
      exact ⟨c + c', isIntAf_add hc hc', by rw [map_add (f := _), e, e', mul_add]⟩
    | neg u _ h =>
      obtain ⟨c, hc, e⟩ := h
      exact ⟨-c, isIntAf_neg hc, by rw [map_neg, e, mul_neg]⟩
  | zero => exact ⟨0, isIntAf_zero, by simp⟩
  | add u u' _ _ h h' =>
    obtain ⟨c, hc, e⟩ := h
    obtain ⟨c', hc', e'⟩ := h'
    exact ⟨c + c', isIntAf_add hc hc', by rw [map_add (f := _), LinearMap.add_apply, e, e', mul_add]⟩
  | neg u _ h =>
    obtain ⟨c, hc, e⟩ := h
    exact ⟨-c, isIntAf_neg hc, by rw [map_neg, LinearMap.neg_apply, e, mul_neg]⟩

private theorem exists_ne (D : Datum p) : ∃ x y : D.La, D.EF x y ≠ 0 := by
  have hF : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  have hr : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) hF
  haveI := Module.nontrivial_of_finrank_pos hr
  obtain ⟨x, hx⟩ := _root_.exists_ne (0 : D.La)
  have hne : D.EF x ≠ 0 := by
    intro h
    apply hx
    apply D.nondeg
    rw [h, map_zero]
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hne
  exact ⟨x, y, by simpa using hy⟩

private theorem isUnit_intCast {d : ℤ} (hd : d ≠ 0) : IsUnit (d : AfP p) := by
  have h : IsUnit (d : ℚ) := (Int.cast_ne_zero.mpr hd).isUnit
  simpa using h.map (algebraMap ℚ (AfP p))

private theorem isIntAf_sim {D : Datum p} {G : HTGroup p} (L : Link D G) (g : G.GAf)
    (hg : ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D) : IsIntAf ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) := by
  let S : Set ℤ := {z | ∃ x y : D.La, D.EF x y = z}
  obtain ⟨d, hdI⟩ := (IsPrincipalIdealRing.principal (Ideal.span S)).principal
  have hdvd : ∀ x y : D.La, d ∣ D.EF x y := by
    intro x y
    have hm : D.EF x y ∈ Ideal.span S := Ideal.subset_span ⟨x, y, rfl⟩
    rw [hdI] at hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨a, by rw [← ha, smul_eq_mul, mul_comm]⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, hxy⟩ := exists_ne D
    apply hxy
    obtain ⟨k, hk⟩ := hdvd x y
    rw [hk, zero_mul]
  have key : ∀ z ∈ Ideal.span S, ∃ c : AfP p, IsIntAf c ∧
      ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) * (z : AfP p) = (d : AfP p) * c := by
    intro z hz
    change z ∈ Submodule.span ℤ S at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, y, rfl⟩ := hz
      have h1 := EFA_actG L g (inAf D x) (inAf D y)
      rw [EFA_inAf] at h1
      rw [← h1]
      exact exists_dvd_EFA D d hdvd (hg _ (inAf_mem D x)) (hg _ (inAf_mem D y))
    | zero => exact ⟨0, isIntAf_zero, by simp⟩
    | add a b _ _ h1 h2 =>
      obtain ⟨c1, h1i, h1e⟩ := h1
      obtain ⟨c2, h2i, h2e⟩ := h2
      refine ⟨c1 + c2, isIntAf_add h1i h2i, ?_⟩
      rw [Int.cast_add, mul_add, h1e, h2e, mul_add]
    | smul a b _ h =>
      obtain ⟨c, hi, he⟩ := h
      refine ⟨a * c, isIntAf_mul (isIntAf_intCast a) hi, ?_⟩
      rw [smul_eq_mul, Int.cast_mul, mul_left_comm, he]
      ring
  obtain ⟨c, hc, hce⟩ := key d (by rw [hdI]; exact Submodule.mem_span_singleton_self d)
  have hsc : ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) = c :=
    (isUnit_intCast (p := p) hd0).mul_left_cancel (by rw [mul_comm]; exact hce)
  rw [hsc]
  exact hc

private theorem pow_dvd_of_isIntAf {q k c c' : ℕ} (hq : q.Prime) (hqp : q ≠ p) {t : AfP p} (ht : IsIntAf t)
    (h : (c : AfP p) = c' * t) (hd : q ^ k ∣ c') : q ^ k ∣ c := by
  obtain ⟨m, rfl⟩ := hd
  have hm : IsIntAf ((m : AfP p) * t) := by
    have hmi := isIntAf_intCast (p := p) (m : ℤ)
    rw [Int.cast_natCast] at hmi
    exact isIntAf_mul hmi ht
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  let v0 : HeightOneSpectrum ℤ :=
    ⟨Ideal.span {(q : ℤ)}, (Ideal.span_singleton_prime hq0).mpr hqz,
      by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0⟩
  have hv0p : v0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro heq
    have hmem : (q : ℤ) ∈ Ideal.span {(p : ℤ)} := heq ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hmem
    have hpq : p ∣ q := Int.natCast_dvd_natCast.mp hmem
    exact hqp ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp hpq).symm
  let v : AwayP p := ⟨v0, hv0p⟩
  have hev : (AfP.eval v) (c : AfP p) =
      (q : HeightOneSpectrum.adicCompletion ℚ v0) ^ k * (AfP.eval v) ((m : AfP p) * t) := by
    rw [h, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, map_natCast]
  have hval : ∀ n : ℕ, Valued.v (n : HeightOneSpectrum.adicCompletion ℚ v0) = v0.intValuation (n : ℤ) := by
    intro n
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v0 (n : ℤ)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
    rw [← h1]
    congr 1
    simp
  have hs : Valued.v ((AfP.eval v) ((m : AfP p) * t)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers ℤ ℚ v0).mp (hm v)
  have hle : v0.intValuation (c : ℤ) ≤ WithZero.exp (-(k : ℤ)) := by
    have hc := hval c
    rw [map_natCast] at hev
    rw [← hc, hev, map_mul, map_pow, hval q, HeightOneSpectrum.intValuation_singleton v0 hq0 rfl]
    refine (mul_le_of_le_one_right' hs).trans (le_of_eq ?_)
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd] at hle
  change Ideal.span {(q : ℤ)} ^ k ∣ Ideal.span {(c : ℤ)} at hle
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] at hle
  exact_mod_cast hle

private theorem dvd_of_isIntAf {c c' : ℕ} (hc' : c'.Coprime p) {t : AfP p} (ht : IsIntAf t)
    (h : (c : AfP p) = c' * t) : c' ∣ c := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd c c']
  intro q k hq hqk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hqp : q ≠ p := by
      rintro rfl
      have hqc : q ∣ c' := (dvd_pow_self q hk.ne').trans hqk
      exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqc hc') dvd_rfl)
    exact pow_dvd_of_isIntAf hq hqp ht h hqk

private theorem main : MultUnit := by
  intro p _ D G L
  refine ⟨?_, ?_⟩
  · intro u hu
    have hst : ∀ g ∈ L.KN 1, ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D := by
      intro g hg v hv
      obtain ⟨w, hw, e⟩ := hg.1 v hv
      rw [e, one_smul]
      exact add_mem hv hw
    have h1 := isIntAf_sim L u (hst u hu)
    have h2 := isIntAf_sim L u⁻¹ (hst _ (inv_mem hu))
    refine ⟨((uSimR (AfP p) u⁻¹ : (AfP p)ˣ) : AfP p), h1, h2, ?_⟩
    have h3 : (uSimR (AfP p) u⁻¹ : (AfP p)ˣ) = ((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ := rfl
    rw [h3]
    exact Units.mul_inv _
  · intro c c' t t' hc hc' ht ht' htt h
    refine Nat.dvd_antisymm ?_ (dvd_of_isIntAf hc' ht h)
    refine dvd_of_isIntAf hc ht' ?_
    rw [h, mul_assoc, htt, mul_one]

end UpperTheory.MultiplicativeUnitDivisibility

theorem UpperTheory.multiplier_is_unit : MultUnit := UpperTheory.MultiplicativeUnitDivisibility.main
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientInvariantOfTraceUnitCrt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private theorem isIntAf_one' {p : ℕ} [Fact p.Prime] : IsIntAf (1 : AfP p) := fun v => by
  rw [map_one]; exact one_mem _

private theorem inAf_mem' {p : ℕ} [Fact p.Prime] {D : Datum p} (y : D.La) : inAf D y ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, y, isIntAf_one', rfl⟩

set_option maxHeartbeats 200000 in
theorem UpperTheory.quotient_invariant_of_trace_unit_crt :
    NumEx → QComp → QIso → ClsEx → TrEta → TrUnit → CongCRT → BaseInv := by
  intro hNumEx hQComp hQIso hClsEx hTrEta hTrUnit hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N' N t c a hN't hNum C' C u hu W
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have hNum' := (hNumEx p D E gb w q r 𝔴 𝔫 S (N : ℕ) hNpos).2 c a t hNum
  obtain ⟨hNc, hGen⟩ := hNum
  obtain ⟨-, hGen'⟩ := hNum'
  rw [← hN't] at hGen'
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hu1 := ((hLev u).mp hu).1
  have hIu : Integ L u := integ_of_mem hu1
  have hCRTu := hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu
  have hC := hCRTu.1.mp (by have h1 := ((hLev u).mp hu).2; rwa [S.lev] at h1)
  have hEta : ∀ y : D.La, (T.M N').univ.eta ((c * t) • y) ≫ W.ψ = W.o.eta (c • y) := by
    intro y
    obtain ⟨v, hv, ev⟩ := hC.1 _ (inAf_mem' y)
    exact hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans S.N₀ (c * t) c hN'c hNc y y ⟨v, hv, ev⟩
  obtain ⟨hIso, hLB⟩ := hTrUnit p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans hu1
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨n', hn'⟩ := hQIso q _ _ _ _ _ _ _ _ c (c * t) _ _ _ _ (T.M N').univ W.o S.Y.univ _ W.ψ hIso W.trans.1
    W.trans.2.1 hLB hEta qC
  have hov : (W.π ≫ C.j) ≫ S.Y.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, C.ov, reassoc_of% W.ov]
  have hlv : ∀ y : D.La, ((T.M N').univ.eta ((algebraMap (𝓞 D.F) D.O) (↑t * a) • y)).left ≫ n'.φ =
      (W.π ≫ C.j) ≫ (S.Y.lv y).left := by
    intro y
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y = t • ((algebraMap (𝓞 D.F) D.O) a • y) := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    obtain ⟨v₂, hv₂, e₂⟩ := (hCRTu.2 a N hNpos N.2.2 hGen).mp hC.2 y
    have hTE := hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ ⟨v₂, hv₂, e₂⟩
    rw [one_smul] at hTE
    rw [hsm, hn', hqC, ← Category.assoc, ← Over.comp_left, hTE, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]
  obtain ⟨-, huq⟩ := hClsEx q _ _ _ S.b gb _ S.mat _ _ _ _ _ hN'c hN'pos h3 hcq hGen' S.Y _ _ (T.M N').univ
  obtain ⟨hj, hm⟩ := huq ⟨W.π ≫ C.j, hov, n', hlv⟩ C'
  refine ⟨hj, ?_⟩
  calc Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = n'.φ := by rw [hn', hqC]
    _ = C'.m.φ := hm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliIso
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem UpperTheory.quotient_moduli_iso : UpperTheory.Gal.Int.Geo.QIso := by
  intro q _ D R R' _ _ _ b gb N N' N₀ c c' X X₁ s s₁ o' o u f ψ hiso hmon hact hpol heta n
  obtain ⟨hP⟩ := hpol
  have hrefl : ∀ {Y : Scheme} (L : LB Y), L.IsLB → LBIso L L :=
    fun L hL => (GlobalTheory.CechPic.cls_eq_iff hL hL).mp rfl
  have h1 : (Hecke.lbPow o'.P 1).IsLB := DVR.linComb_isLB _ o'.isLB _ _
  have e1 : LBIso o'.P (Hecke.lbPow o'.P 1) :=
    (GlobalTheory.CechPic.cls_eq_iff o'.isLB h1).mp (by simpa only [one_smul] using (GlobalTheory.LocTrivDescent.cls_lbPow_eq o'.isLB 1 h1).symm)
  have e3 : LBIso (o.P.pull (Hecke.sq2 ψ)) ((u.P.pull n.φ₂).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) n.pol
  have e4 : LBIso ((u.P.pull n.φ₂).pull (Hecke.sq2 ψ)) (u.P.pull (Hecke.sq2 ψ ≫ n.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn u.P (fun _ => n.φ₂) (fun _ => (1 : ℤ)) (Hecke.sq2 ψ))
      (hrefl _ (pull_isLB (pull_isLB u.isLB _) _))
  have pol : LBIso o'.P (u.P.pull (Hecke.sq2 ψ ≫ n.φ₂)) :=
    LBIso.trans o'.isLB (pull_isLB o.isLB _) (pull_isLB u.isLB _)
      (LBIso.trans o'.isLB h1 (pull_isLB o.isLB _) e1 hP)
      (LBIso.trans (pull_isLB o.isLB _) (pull_isLB (pull_isLB u.isLB _) _) (pull_isLB u.isLB _) e3 e4)
  refine ⟨⟨Over.Hom.left ψ ≫ n.φ, Hecke.sq2 ψ ≫ n.φ₂, ?_, ?_, ?_, pol, ?_⟩, rfl⟩
  · have hc := (GlobalTheory.FibreAct.isGrpPullback_of_iso ψ).comp n.cart
    simpa using hc
  · constructor
    · rw [Category.assoc, n.sq.1, ← Category.assoc, ← Category.assoc, Hecke.sq2, ← Over.comp_left,
        lift_fst, Over.comp_left]
    · rw [Category.assoc, n.sq.2, ← Category.assoc, ← Category.assoc, Hecke.sq2, ← Over.comp_left,
        lift_snd, Over.comp_left]
  · intro x
    rw [← Category.assoc, ← Over.comp_left, hact x, Over.comp_left, Category.assoc, n.act x,
      Category.assoc]
  · intro y
    rw [← Category.assoc, ← Over.comp_left, heta y, n.eta y]
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
section
open CategoryTheory UpperTheory.Gal.Int.Geo

theorem UpperTheory.quotient_unique_of_comp :
    QComp → QUniq := by
  intro hQ q _ D R R' _ _ _ b gb N N₀ c h3 hc X X₁ s s₁ o u f n n'
  obtain ⟨u', ⟨m⟩⟩ := _root_.GlobalTheory.HTPullEvery.exists_objMap q D R b N₀ X₁ X s₁ (f ≫ s₁) f rfl u

  have down : ∀ k : QMap o u f c, ∃ k₁ : QMap o u' (𝟙 X) c, k.φ = k₁.φ ≫ m.φ := by
    intro k
    obtain ⟨k₀, hk⟩ : ∃ k₀ : QMap o u (𝟙 X ≫ f) c, k₀.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨k₁, h₁⟩ := (hQ q D R R' b gb N N₀ c X X X₁ s (f ≫ s₁) s₁ o u' u (𝟙 X) f).2.1 k₀ m
    exact ⟨k₁, hk ▸ h₁⟩
  obtain ⟨n₁, h₁⟩ := down n
  obtain ⟨n₂, h₂⟩ := down n'

  have self : ∀ k : QMap o u' (𝟙 X) c, ∃ a : GlobalTheory.UPel.HT.ObjMap u' u' (𝟙 X), k.φ = n₁.φ ≫ a.φ := by
    intro k
    obtain ⟨k₀, hk⟩ : ∃ k₀ : QMap o u' (𝟙 X ≫ 𝟙 X) c, k₀.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨a₀, ha₀⟩ : ∃ a : GlobalTheory.UPel.HT.ObjMap u' u' (𝟙 X), k₀.φ = n₁.φ ≫ a.φ :=
      (hQ q D R R' b gb N N₀ c X X X s (f ≫ s₁) (f ≫ s₁) o u' u' (𝟙 X) (𝟙 X)).2.2.1
        inferInstance n₁ k₀
    exact ⟨a₀, hk ▸ ha₀⟩
  obtain ⟨a, ha⟩ := self n₁
  obtain ⟨a', ha'⟩ := self n₂
  have hr : a.φ = a'.φ := GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique q D R b N₀ h3 hc X X (f ≫ s₁) (f ≫ s₁) u' u' (𝟙 X) a a'
  rw [h₁, h₂, ha', ← hr, ← ha]
end

