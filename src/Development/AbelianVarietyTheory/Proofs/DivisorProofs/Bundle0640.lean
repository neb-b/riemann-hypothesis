module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsZeroPtEpsScalePt
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalModuleActionLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.TanKill

theorem exists_mem_pow_forall_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (k : Type) [Field k] (β : R →+* k), ∃ c ∈ w0 ^ r, ∀ i, β (b.t i c) ≠ 0 := by
  intro p _ D R _ b w0 r hw k _ β
  classical
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos D.a with ha | ha
  · obtain ⟨i, -⟩ := hcon 0 (zero_mem _)
    exact (Fin.elim0 (ha ▸ i))
  let i0 : Fin D.a := ⟨0, ha⟩
  have hsub : ((w0 ^ r : Ideal (𝓞 D.F)) : Set (𝓞 D.F)) ⊆
      ⋃ i ∈ ((Finset.univ : Finset (Fin D.a)) : Set (Fin D.a)), (RingHom.ker (β.comp (b.t i)) : Set (𝓞 D.F)) := by
    intro c hc
    obtain ⟨i, hi⟩ := hcon c hc
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) (RingHom.mem_ker.mpr hi)
  obtain ⟨i, -, hi⟩ := (Ideal.subset_union_prime i0 i0 (fun i _ _ _ => RingHom.ker_isPrime _)).mp hsub
  have hi' : w0 ≤ RingHom.ker (β.comp (b.t i)) := (RingHom.ker_isPrime _).le_of_pow_le hi
  have hle : Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) ≤ RingHom.ker β := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact RingHom.mem_ker.mpr (RingHom.mem_ker.mp (hi' hy))
  rw [hw.2.2.1 i, top_le_iff] at hle
  exact RingHom.ker_ne_top β hle

theorem exists_mem_pow_add_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (β : R →+* k) (r2 : ℤ), (r2 : k) = (D.tr : k) - β b.ρ → ∃ c ∈ w0 ^ r, ∃ e f : 𝓞 D.F, c + e * (D.ω - (r2 : 𝓞 D.F)) + f * (p : 𝓞 D.F) = 1 := by
  intro p _ D R _ b w0 r hw k _ _ _ β r2 hr2
  haveI : w0.IsMaximal := hw.1
  letI : Field (𝓞 D.F ⧸ w0) := Ideal.Quotient.field w0

  have hpQ : ((p : 𝓞 D.F ⧸ w0)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w0), Ideal.Quotient.eq_zero_iff_mem]; exact hw.2.1
  haveI : CharP (𝓞 D.F ⧸ w0) p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hpQ
  have hne : w0 ≠ ⊥ := by
    intro h
    have h1 := hw.2.1
    rw [h, Ideal.mem_bot] at h1
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1
  haveI : Finite (𝓞 D.F ⧸ w0) := Ideal.finiteQuotientOfFreeOfNeBot w0 hne
  letI : Algebra (ZMod p) (𝓞 D.F ⧸ w0) := ZMod.algebra _ p
  letI : Algebra (ZMod p) k := ZMod.algebra _ p
  haveI : Algebra.IsAlgebraic (ZMod p) (𝓞 D.F ⧸ w0) := inferInstance
  let φ0 := IsAlgClosed.lift (M := k) (R := ZMod p) (S := 𝓞 D.F ⧸ w0)
  let φ : 𝓞 D.F →+* k := φ0.toRingHom.comp (Ideal.Quotient.mk w0)
  have hker : RingHom.ker φ = w0 := by
    ext y
    rw [RingHom.mem_ker]
    change φ0 (Ideal.Quotient.mk w0 y) = 0 ↔ y ∈ w0
    rw [map_eq_zero_iff φ0 φ0.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hφ := hw.2.2.2 k β φ hker

  let J : Ideal (𝓞 D.F) := Ideal.span {D.ω - (r2 : 𝓞 D.F), (p : 𝓞 D.F)}
  have hJ : w0 ⊔ J = ⊤ := by
    by_contra hsup
    have hle : J ≤ w0 := by
      have := hw.1.eq_of_le hsup le_sup_left
      exact this ▸ le_sup_right
    have hmem : D.ω - (r2 : 𝓞 D.F) ∈ w0 := hle (Ideal.subset_span (Set.mem_insert _ _))
    rw [← hker, RingHom.mem_ker, map_sub, map_intCast, hφ, hr2] at hmem
    have hρ : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
      have h := congrArg β b.ρ_root
      simpa using h
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (-((D.tr : k) - 2 * β b.ρ)) * hmem - 4 * hρ
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).mp hd)
  have hJr : w0 ^ r ⊔ J = ⊤ := by
    have h := Ideal.isCoprime_iff_sup_eq.mpr hJ
    exact Ideal.isCoprime_iff_sup_eq.mp h.pow_left
  obtain ⟨c, hc, j, hj, hcj⟩ := Submodule.mem_sup.mp (hJr ▸ Submodule.mem_top : (1 : 𝓞 D.F) ∈ w0 ^ r ⊔ J)
  obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp hj
  exact ⟨c, hc, e, f, by rw [add_assoc, hef, hcj]⟩

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

theorem sum_eq_zero_of_eigen (T : Module.End k V) {I : Type} [DecidableEq I] (s : Finset I) :
    ∀ (w : I → V) (l : I → k), (∀ i ∈ s, T (w i) = l i • w i) → (∀ i ∈ s, l i ≠ 0) →
      T (∑ i ∈ s, w i) = 0 → ∑ i ∈ s, w i = 0 := by
  induction s using Finset.induction_on with
  | empty => intros; simp
  | insert j s hj ih =>
    intro w l hw hl hT
    rw [Finset.sum_insert hj] at hT ⊢
    have e : ∑ i ∈ s, (l i - l j) • w i = T (w j + ∑ i ∈ s, w i) - l j • (w j + ∑ i ∈ s, w i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, hw j (Finset.mem_insert_self j s), smul_add, Finset.smul_sum,
        Finset.sum_congr rfl (fun i hi => hw i (Finset.mem_insert_of_mem hi))]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    have key := ih (fun i => (l i - l j) • w i) l
      (fun i hi => by rw [map_smul, hw i (Finset.mem_insert_of_mem hi), smul_comm])
      (fun i hi => hl i (Finset.mem_insert_of_mem hi))
      (by rw [e, map_sub, map_smul, hT, map_zero, smul_zero, sub_zero])
    rw [key, hT, zero_sub, eq_comm, neg_eq_zero] at e
    exact (smul_eq_zero.mp e).resolve_left (hl j (Finset.mem_insert_self j s))

end GlobalTheory.UPel.HT.EtLev.TanKill

namespace GlobalTheory.UPel.HT.EtLev.TanKill

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

lemma L_int {O : Type} [Ring O] (L : O →+* Module.End k V) (n : ℤ) (u : V) : L (n : O) u = (n : k) • u := by
  rw [map_intCast, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

lemma L_nat {O : Type} [Ring O] (L : O →+* Module.End k V) (n : ℕ) (u : V) : L (n : O) u = (n : k) • u := by
  rw [map_natCast, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]

theorem core {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ)
    (hw : IsEtPlace b w0) [IsAlgClosed k] (β : R →+* k) (L : 𝓞 D.F →+* Module.End k V)
    (hlie : ∀ v, L D.ω v = β b.ρ • v → ∃ w : Fin D.a → V, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ v = ∑ i, w i)
    (v : V) (hv : ∀ c ∈ w0 ^ r, L c v = 0) : v = 0 := by
  by_cases hp : (p : k) = 0
  swap
  · have h := hv _ (Ideal.pow_mem_pow hw.2.1 r)
    rw [← Nat.cast_pow, L_nat] at h
    exact (smul_eq_zero.mp h).resolve_left (by rw [Nat.cast_pow]; exact pow_ne_zero _ hp)
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hp
  set Tω := L D.ω with hTω
  set ρ1 := β b.ρ with hρ1
  set ρ2 := (D.tr : k) - ρ1 with hρ2
  have hquad : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    have hb : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
    have h := D.nm_eq
    rw [hb] at h
    linear_combination (-1 : 𝓞 D.F) * h
  have hq : ∀ u, Tω (Tω u) = (D.tr : k) • Tω u - (D.nm : k) • u := by
    intro u
    have h := congrArg (fun f => f u) (congrArg L hquad)
    simp only [map_add (f := _), map_sub, map_mul, map_zero, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, L_int] at h
    rw [← hTω] at h
    rw [← sub_eq_zero, ← h]
    abel
  have hρ : ρ1 ^ 2 - (D.tr : k) * ρ1 + (D.nm : k) = 0 := by
    have h := congrArg β b.ρ_root
    simpa using h
  have hsum : ρ1 + ρ2 = D.tr := by rw [hρ2]; ring
  have hprod : ρ1 * ρ2 = D.nm := by rw [hρ2]; linear_combination (-1 : k) * hρ
  clear_value Tω ρ1 ρ2
  have hδ : ρ1 - ρ2 ≠ 0 := by
    intro h0
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      have : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = (ρ1 - ρ2) ^ 2 := by
        push_cast
        rw [← hsum, ← hprod]; ring
      rw [this, h0]; ring
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).mp hd)
  have hcomm : ∀ c u, L c (Tω u) = Tω (L c u) := by
    intro c u
    rw [hTω, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  set v1 := (ρ1 - ρ2)⁻¹ • (Tω v - ρ2 • v) with hv1
  set v2 := (ρ1 - ρ2)⁻¹ • (ρ1 • v - Tω v) with hv2
  have hv12 : v = v1 + v2 := by
    rw [hv1, hv2, ← smul_add]
    have : Tω v - ρ2 • v + (ρ1 • v - Tω v) = (ρ1 - ρ2) • v := by rw [sub_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have e1 : Tω v1 = ρ1 • v1 := by
    rw [hv1, map_smul, map_sub, map_smul, hq, smul_comm ρ1]
    congr 1
    rw [← hsum, ← hprod]
    module
  have e2 : Tω v2 = ρ2 • v2 := by
    rw [hv2, map_smul, map_sub, map_smul, hq, smul_comm ρ2]
    congr 1
    rw [← hsum, ← hprod]
    module
  have k1 : ∀ c ∈ w0 ^ r, L c v1 = 0 := by
    intro c hc
    rw [hv1, map_smul, map_sub, map_smul, hcomm, hv c hc, map_zero, smul_zero, sub_zero, smul_zero]
  have k2 : ∀ c ∈ w0 ^ r, L c v2 = 0 := by
    intro c hc
    rw [hv2, map_smul, map_sub, map_smul, hcomm, hv c hc, map_zero, smul_zero, sub_zero, smul_zero]
  have z1 : v1 = 0 := by
    obtain ⟨c, hc, hne⟩ := exists_mem_pow_forall_ne_zero p D R b w0 r hw k β
    obtain ⟨w, hwe, hweq⟩ := hlie v1 e1
    rw [hweq]
    refine sum_eq_zero_of_eigen (L c) Finset.univ w (fun i => β (b.t i c)) (fun i _ => hwe i c)
      (fun i _ => hne i) ?_
    rw [← hweq]; exact k1 c hc
  have z2 : v2 = 0 := by
    obtain ⟨r0, hr0⟩ := D.split
    have hr0k : ((r0 : k) - ρ1) * ((r0 : k) - ρ2) = 0 := by
      have : ((r0 ^ 2 - D.tr * r0 + D.nm : ℤ) : k) = 0 := (CharP.intCast_eq_zero_iff k p _).mpr hr0
      push_cast at this
      linear_combination this - (r0 : k) * hsum + hprod
    obtain ⟨r2, hr2⟩ : ∃ r2 : ℤ, (r2 : k) = ρ2 := by
      rcases mul_eq_zero.mp hr0k with h | h
      · exact ⟨D.tr - r0, by push_cast; rw [hρ2]; linear_combination -h⟩
      · exact ⟨r0, by linear_combination h⟩
    obtain ⟨c, hc, e, f, hcef⟩ := exists_mem_pow_add_eq_one p D R b w0 r hw k β r2 (by rw [hr2, hρ2, hρ1])
    have h := congrArg (fun g => g v2) (congrArg L hcef)
    simp only [map_add (f := _), map_mul, map_sub, map_one, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, L_int, L_nat, k2 c hc] at h
    simp only [zero_add, add_zero] at h
    rw [← hTω, e2, hr2, map_smul, sub_self, hp, zero_smul, map_zero, add_zero] at h
    exact h.symm
  rw [hv12, z1, z2, add_zero]

end GlobalTheory.UPel.HT.EtLev.TanKill

namespace GlobalTheory.UPel.HT.EtLev.TanKill

open GlobalTheory.TanPtMod

theorem tan_eq_one_of_etPlace : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1 := by
  intro p _ D R _ b N w0 r hw S s o k _ _ x v hv0 hv
  set β : R →+* k := (Spec.preimage (x ≫ s)).hom with hβ
  have hx : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let L : 𝓞 D.F →+* Module.End k (Tan x o.A) := (actEnd o.act).comp (algebraMap (𝓞 D.F) D.O)
  have hL : ∀ c (u : Tan x o.A), (L c u).hom = u.hom ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := fun _ _ => rfl
  have hlie : ∀ u : Tan x o.A, L D.ω u = β b.ρ • u →
      ∃ w : Fin D.a → Tan x o.A, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ u = ∑ i, w i := by
    intro u hu
    obtain ⟨w, hw1, hw2⟩ := o.lie k β x hx u.hom
      ⟨(mem_tanSub_iff x o.A _).mp u.hom_mem, by
        have := congrArg (fun t : Tan x o.A => t.hom.left) hu
        simpa [hL, GrpTangentPt.epsScalePt_left] using this⟩
    have hmem : ∀ i, w i ∈ tanSub x o.A := fun i => (mem_tanSub_iff x o.A _).mpr (hw1 i 0).1
    refine ⟨fun i => Tan.mk (w i) (hmem i), fun i c => Tan.ext (Over.OverMorphism.ext ((hw1 i c).2)), ?_⟩
    refine Tan.ext ?_
    rw [Tan.hom_sum, hw2, List.prod_ofFn]
    rfl
  have hmv : v ∈ tanSub x o.A := (mem_tanSub_iff x o.A _).mpr hv0
  have := core D b w0 r hw β L hlie (Tan.mk v hmv) (fun c hc => Tan.ext (by rw [hL]; exact hv c hc))
  exact congrArg Tan.hom this

end GlobalTheory.UPel.HT.EtLev.TanKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusFormalLogSubSmulIntegral
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem in_frob_formalLog_sub_smul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B)
    (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) →
    (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 →
    In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) -
      (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  intro p _ B O Q _ _ _ _ _ θ hF σB s hs hσ d g hg
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hXB : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) := HasSubst.X_pow hp
  have hXQ : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hX0 : ∀ i : Fin d, constantCoeff ((X i : MvPowerSeries (Fin d) B) ^ p) = 0 := fun i => by
    simp [hp]
  set v := subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) with hv
  have hv1 : constantCoeff v = 1 := by
    rw [hv, constantCoeff_subst_of_zero hXB hX0]
    simp [hg]
  have hgp1 : constantCoeff (g ^ p) = 1 := by simp [hg]
  obtain ⟨u, hu⟩ := isUnit_iff_constantCoeff.mpr (hgp1 ▸ isUnit_one : IsUnit (constantCoeff (g ^ p)))
  set k : MvPowerSeries (Fin d) B := ↑u⁻¹ with hk
  have hgk : g ^ p * k = 1 := by rw [hk, ← hu, Units.mul_inv]
  have hk1 : constantCoeff k = 1 := by
    have := congrArg constantCoeff hgk
    rwa [map_mul, hgp1, one_mul, map_one] at this

  have hc := fun α => GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p p B σB hσ d g α
  choose r hr using hc
  set R : MvPowerSeries (Fin d) B := fun α => r α with hR
  have hvR : v - g ^ p = C (p : B) * R := by
    ext α
    rw [coeff_C_mul, hr α]
    rfl
  set h := v * k with hh
  have hh1 : constantCoeff h = 1 := by rw [hh, map_mul, hv1, hk1, one_mul]
  have hhv : h * g ^ p = v := by rw [hh, mul_assoc, mul_comm k, hgk, mul_one]
  have hhJ : ∀ α, coeff α (h - 1) ∈ Ideal.span {(p : B)} := by
    intro α
    have : h - 1 = C (p : B) * (R * k) := by
      rw [hh, ← hgk, ← sub_mul, hvR, mul_assoc]
    rw [this, coeff_C_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hJ : ∀ x ∈ Ideal.span {(p : B)}, ∃ y ∈ Ideal.span {(p : B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨(p : B) ^ (p - 1) * a ^ p,
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (by omega)), ?_⟩
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), mul_comm]
  have hlog := _root_.GlobalTheory.DPLog.formalLog_in_of_sub_one_mem p B O Q θ hF _ hJ (Fin d) h hh1 hhJ

  set ι := algebraMap B Q with hι
  have hG1 : constantCoeff (map ι g) = 1 := by simp [hg]
  have hmapG : map s (map ι g) = map ι (map σB g) := by
    ext α
    simp [coeff_map, hs]
  have hmapv : map ι v = subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p)
      (map ι (map σB g)) := by
    rw [hv, map_subst hXB]
    congr 1
    funext i
    simp
  have hσG1 : constantCoeff (map ι (map σB g)) = 1 := by simp [hg]
  have key : frob p s (formalLog (map ι g)) - (p : Q) • formalLog (map ι g) =
      formalLog (map ι h) := by
    rw [frob, map_formalLog s hG1, hmapG, subst_formalLog hXQ hσG1, ← hmapv, ← hhv, map_mul,
      map_pow, formalLog_mul (by simp [hh1]) (by simp [hg]), formalLog_pow p hG1,
      Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
  rw [key]
  intro α
  obtain ⟨b, -, hb⟩ := hlog α
  exact ⟨b, trivial, hb⟩

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCuspidalFactorAtBlockLeviPiTensor
section
noncomputable section

namespace GlobalTheory.HcIrr.Factor

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr Representation

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem tprod_update_injective (v : ∀ i, M i) (hv : ∀ i, v i ≠ 0) (i : ι) :
    Function.Injective ((PiTensorProduct.tprod ℂ).toLinearMap v i) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  by_contra hx0
  have hw : ∀ j, Function.update v i x j ≠ 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hx0
    · rw [Function.update_of_ne hj]; exact hv j
  have hφ : ∀ j, ∃ φ : Module.Dual ℂ (M j), φ (Function.update v i x j) ≠ 0 := by
    intro j
    by_contra hc
    push_neg at hc
    exact hw j ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  choose φ hφ using hφ
  have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) hx
  rw [MultilinearMap.toLinearMap_apply, PiTensorProduct.lift.tprod, map_zero,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
  exact (Finset.prod_ne_zero_iff.2 fun j _ => hφ j) h1

end Tensor

section Blocks

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def blockIdx (b : Fin r → Fin s) (c : Fin s) : {i // b i = c} ≃ Block (natBlocks b) (c : ℕ) :=
  Equiv.subtypeEquivRight fun i => by simp [natBlocks, Fin.val_inj]

def blockNum (b : Fin r → Fin s) (c : Fin s) {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) :
    {i // b i = c} ≃ Fin d :=
  (blockIdx b c).trans (monoEquivOfFin _ h).toEquiv.symm

theorem monoEquivOfFin_blockNum (b : Fin r → Fin s) (c : Fin s) {d : ℕ}
    (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) (x : {i // b i = c}) :
    ((monoEquivOfFin (Block (natBlocks b) (c : ℕ)) h (blockNum b c h x) : Block (natBlocks b) (c : ℕ)) : Fin r) = x.1 := by
  simp [blockNum, blockIdx]

theorem blockEmb_eq (b : Fin r → Fin s) (c : Fin s) {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d)
    (g : GL (Fin d) K) :
    blockEmb (natBlocks b) (c : ℕ) h g = blockExt b c ((glEquiv K (blockNum b c h)).symm g) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : b i = c ∧ b j = c
  · have h1 := blockEmb_in (natBlocks b) (c : ℕ) h g (blockNum b c h ⟨i, hij.1⟩) (blockNum b c h ⟨j, hij.2⟩)
    rw [monoEquivOfFin_blockNum, monoEquivOfFin_blockNum] at h1
    have h2 := blockExt_in b c ((glEquiv K (blockNum b c h)).symm g) ⟨i, hij.1⟩ ⟨j, hij.2⟩
    rw [h1, h2]
    rfl
  · have hn : ¬ (natBlocks b i = (c : ℕ) ∧ natBlocks b j = (c : ℕ)) := by
      simpa [natBlocks, Fin.val_inj] using hij
    rw [blockEmb_out (natBlocks b) (c : ℕ) h g i j hn, blockExt_out b c _ i j hij]

end Blocks

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem blockRes_leviTensor (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s)
    {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) (g : GL (Fin d) K) :
    blockRes (natBlocks b) (leviTensor b lam) (c : ℕ) h g = PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c
        ((lam c).ρ ((glEquiv K (blockNum b c h)).symm g))) := by
  show leviTensor b lam (blockEmb (natBlocks b) (c : ℕ) h g) = _
  rw [blockEmb_eq, leviTensor_blockExt]

theorem map_update_tprod {s : ℕ} {M : Fin s → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (c : Fin s) (A : M c →ₗ[ℂ] M c) (v : ∀ i, M i) (x : M c) :
    PiTensorProduct.map (Function.update (fun c' => (LinearMap.id : M c' →ₗ[ℂ] M c')) c A)
      (PiTensorProduct.tprod ℂ (Function.update v c x)) = PiTensorProduct.tprod ℂ (Function.update v c (A x)) := by
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext c'
  by_cases hc : c' = c
  · subst hc; simp
  · simp [Function.update_of_ne hc]

theorem factor_iso : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, Simple (lam c)) → ∀ (c : Fin s) (d : ℕ)
    (h : Fintype.card (GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.Block (natBlocks b) (c : ℕ)) = d) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin d) K) W), GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.HasFactor (natBlocks b) (leviTensor b lam) (c : ℕ) h ρ →
    ∃ (e : {i // b i = c} ≃ Fin d) (L : W ≃ₗ[ℂ] (lam c : Type)),
      ∀ g v, L (ρ g v) = (lam c).ρ ((glEquiv K e).symm g) (L v) := by
  intro K _ _ _ r s b lam hsimp c d h W _ _ ρ hF
  refine ⟨blockNum b c h, ?_⟩
  set e := blockNum b c h
  let ρ' : Representation ℂ (GL (Fin d) K) (lam c) := (Formalism.IrreducibleCountingLemmas.TYPES.transp e (lam c)).ρ
  have hirr : ρ'.IsIrreducible := GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple _ (Formalism.L2.PT.simple_transp e (hsimp c))
  have hnt : ∀ c', Nontrivial (lam c') := fun c' =>
    PI.GreenLabelSurjWork.nontrivial_of_simple _ (hsimp c')
  choose v hv using fun c' => exists_ne (0 : (lam c' : Type))
  let f : IntertwiningMap ρ' (blockRes (natBlocks b) (leviTensor b lam) (c : ℕ) h) :=
    ((PiTensorProduct.tprod ℂ).toLinearMap v c).intertwiningMap_of_isIntertwiningMap _ _ (fun g x => by
      rw [blockRes_leviTensor, MultilinearMap.toLinearMap_apply, MultilinearMap.toLinearMap_apply,
        map_update_tprod]
      rfl)
  have hinj : Function.Injective (IntertwiningMap.equivLinearMapAsModule ρ' _ f) :=
    tprod_update_injective v hv c
  have hiso := hF.2.of_injective _ hinj
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL (Fin d) K)) ρ'.asModule :=
    (irreducible_iff_isSimpleModule_asModule ρ').1 hirr
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL (Fin d) K)) (⊤ : Submodule (MonoidAlgebra ℂ (GL (Fin d) K)) ρ'.asModule) :=
    IsSimpleModule.congr (Submodule.topEquiv)
  let E : ρ.asModule ≃ₗ[MonoidAlgebra ℂ (GL (Fin d) K)] ρ'.asModule := ((hiso ⊤).some.symm.trans Submodule.topEquiv)
  let F : IntertwiningMap ρ ρ' := (IntertwiningMap.equivLinearMapAsModule ρ ρ').symm E.toLinearMap
  refine ⟨LinearEquiv.ofBijective F.toLinearMap E.bijective, fun g x => ?_⟩
  exact IntertwiningMap.isIntertwining ρ ρ' F g x

end Main

end GlobalTheory.HcIrr.Factor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomialStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictHenselisation_etale_over_polynomial_alt : ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S) (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  first | (exact @GlobalTheory.strictHenselisation_etale_over_polynomial) | (exact GlobalTheory.strictHenselisation_etale_over_polynomial) | (intros; apply GlobalTheory.strictHenselisation_etale_over_polynomial  <;> assumption)
end

