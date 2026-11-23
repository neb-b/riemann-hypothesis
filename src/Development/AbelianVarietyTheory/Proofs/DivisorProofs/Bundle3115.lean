module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTangentInjectiveAwayFromEtalePlace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.TanInj

open GlobalTheory.UPel.HT.EtLev.TanKill

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

theorem core_inj {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F))
    (hw : IsEtPlace b w0) [IsAlgClosed k] (β : R →+* k) (L : 𝓞 D.F →+* Module.End k V)
    (hlie : ∀ v, L D.ω v = β b.ρ • v → ∃ w : Fin D.a → V, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ v = ∑ i, w i)
    (c : 𝓞 D.F) (hc0 : c ≠ 0)
    (hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w)
    (v : V) (hv : L c v = 0) : v = 0 := by
  have hpr : p.Prime := Fact.out
  by_cases hp : (p : k) = 0
  swap
  ·
    set N := Ideal.absNorm (Ideal.span {c}) with hNdef
    have hNmem : ((N : ℕ) : 𝓞 D.F) ∈ Ideal.span {c} := Ideal.absNorm_mem _
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hNmem
    have hN0 : N ≠ 0 := by
      rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hc0
    obtain ⟨e, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hpr.one_lt.ne'
    have hN'u : IsUnit ((N' : ℕ) : R) := b.unit N' ((Nat.Prime.coprime_iff_not_dvd hpr).mpr hN').symm
    have hN'k : ((N' : ℕ) : k) ≠ 0 := by
      have := hN'u.map β
      rw [map_natCast] at this
      exact this.ne_zero
    have hNk : ((N : ℕ) : k) ≠ 0 := by
      rw [hNe, Nat.cast_mul, Nat.cast_pow]
      exact mul_ne_zero (pow_ne_zero _ hp) hN'k
    have h : L ((N : ℕ) : 𝓞 D.F) v = 0 := by
      rw [← hd, map_mul, Module.End.mul_apply, hv, map_zero]
    rw [L_nat] at h
    exact (smul_eq_zero.mp h).resolve_left hNk
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hpr).mpr hp
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
  have k1 : L c v1 = 0 := by
    rw [hv1, map_smul, map_sub, map_smul, hcomm, hv, map_zero, smul_zero, sub_zero, smul_zero]
  have k2 : L c v2 = 0 := by
    rw [hv2, map_smul, map_sub, map_smul, hcomm, hv, map_zero, smul_zero, sub_zero, smul_zero]
  have hp0 : ((p : ℕ) : 𝓞 D.F) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have z1 : v1 = 0 := by
    have hne : ∀ i, β (b.t i c) ≠ 0 := by
      intro i h0
      have hprime : (RingHom.ker (β.comp (b.t i))).IsPrime := RingHom.ker_isPrime _
      have hpP : ((p : ℕ) : 𝓞 D.F) ∈ RingHom.ker (β.comp (b.t i)) := by
        rw [RingHom.mem_ker, RingHom.comp_apply, map_natCast, map_natCast, hp]
      have hbot : RingHom.ker (β.comp (b.t i)) ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hpP
        exact hp0 hpP
      have hmax : (RingHom.ker (β.comp (b.t i))).IsMaximal := hprime.isMaximal hbot
      have hnw : RingHom.ker (β.comp (b.t i)) ≠ w0 := by
        intro hP
        have hle : Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) ≤ RingHom.ker β := by
          refine Ideal.span_le.mpr ?_
          rintro _ ⟨y, hy, rfl⟩
          have : y ∈ RingHom.ker (β.comp (b.t i)) := hP ▸ hy
          exact RingHom.mem_ker.mpr (RingHom.mem_ker.mp this)
        rw [hw.2.2.1 i, top_le_iff] at hle
        exact RingHom.ker_ne_top β hle
      exact hcw _ hmax hpP hnw (RingHom.mem_ker.mpr h0)
    obtain ⟨w, hwe, hweq⟩ := hlie v1 e1
    rw [hweq]
    refine sum_eq_zero_of_eigen (L c) Finset.univ w (fun i => β (b.t i c)) (fun i _ => hwe i c)
      (fun i _ => hne i) ?_
    rw [← hweq]; exact k1
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
    obtain ⟨c', hc', e', f', hcef'⟩ := exists_mem_pow_add_eq_one p D R b w0 1 hw k β r2 (by rw [hr2, hρ2, hρ1])
    rw [pow_one] at hc'
    let J : Ideal (𝓞 D.F) := Ideal.span {D.ω - (r2 : 𝓞 D.F), ((p : ℕ) : 𝓞 D.F)}
    have hJ : Ideal.span {c} ⊔ J = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      have hJm : J ≤ m := le_trans le_sup_right hle
      have hωm : D.ω - (r2 : 𝓞 D.F) ∈ m := hJm (Ideal.subset_span (Set.mem_insert _ _))
      have hpm : ((p : ℕ) : 𝓞 D.F) ∈ m := hJm (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      have hcm : c ∈ m := le_trans le_sup_left hle (Ideal.mem_span_singleton_self c)
      have hmw : m ≠ w0 := by
        intro hmw
        subst hmw
        have h1 : (1 : 𝓞 D.F) ∈ m := by
          rw [← hcef']
          exact m.add_mem (m.add_mem hc' (m.mul_mem_left _ hωm)) (m.mul_mem_left _ hpm)
        exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      exact hcw m hm hpm hmw hcm
    obtain ⟨a, ha, j, hj, haj⟩ := Submodule.mem_sup.mp (hJ ▸ Submodule.mem_top : (1 : 𝓞 D.F) ∈ Ideal.span {c} ⊔ J)
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp hj
    have h := congrArg (fun g => g v2) (congrArg L haj)
    rw [← hef] at h
    simp only [map_add (f := _), map_mul, map_sub, map_one, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, L_int, L_nat, k2] at h
    rw [← hTω, e2, hr2, sub_self] at h
    simp only [hp, zero_smul, map_zero, zero_add, add_zero] at h
    exact h.symm
  rw [hv12, z1, z2, add_zero]

end GlobalTheory.UPel.HT.EtLev.TanInj

namespace GlobalTheory.UPel.HT.EtLev.TanInj

open GlobalTheory.TanPtMod

theorem tan_eq_one_of_notMem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (c : 𝓞 D.F), c ≠ 0 → (∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w) → ∀ v : epsPtR x ⟶ o.A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 → v = 1 := by
  intro p _ D R _ b N w0 hw S s o k _ _ x c hc0 hcw v hv0 hv
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
  have := core_inj D b w0 hw β L hlie c hc0 hcw (Tan.mk v hmv) (Tan.ext (by rw [hL]; exact hv))
  exact congrArg Tan.hom this

end GlobalTheory.UPel.HT.EtLev.TanInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFinrankEqNormPowStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_and_finrank_act_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  first | (exact @GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow) | (exact GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow) | (intros; apply GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjects
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ESPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem hom_ext_of_cart {A : Over S} {A₁ : Over S'} [GrpObj A] [GrpObj A₁] {φ : A₁.left ⟶ A.left}
    (h : IsGrpPullback A₁ A f φ) {T : Over S'} {u v : T ⟶ A₁} (e : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w u, Over.w v]))

theorem exists_baseChange {A B : Over S} {A₁ B₁ : Over S'} [GrpObj A] [GrpObj B] [GrpObj A₁] [GrpObj B₁]
    {φ : A₁.left ⟶ A.left} {χ : B₁.left ⟶ B.left} (hA : IsGrpPullback A₁ A f φ) (hB : IsGrpPullback B₁ B f χ)
    (ψ : A ⟶ B) : ∃ ψ₁ : A₁ ⟶ B₁, ψ₁.left ≫ χ = φ ≫ ψ.left :=
  ⟨Over.homMk (hB.1.lift (φ ≫ ψ.left) A₁.hom (by rw [Category.assoc, Over.w ψ, hA.1.w]))
    (hB.1.lift_snd _ _ _), hB.1.lift_fst _ _ _⟩

theorem grpSchemeSquareProductMap_comp_fst {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    Hecke.sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    Hecke.sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem isPIsog_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N s) (o₁ o₁' : Obj b N s') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := by
  intro p _ D R _ b N c S S' s s' f o o' o₁ o₁' m m' ψ hψ
  obtain ⟨hk, hm, hact, heta, ⟨hP⟩, ψ', hm', h₁, h₂⟩ := hψ
  obtain ⟨ψ₁, sq⟩ := exists_baseChange m.cart m'.cart ψ
  obtain ⟨ψ₁', sq'⟩ := exists_baseChange m'.cart m.cart ψ'
  haveI := hm
  haveI := hm'
  have hm₁ : IsMonHom ψ₁ := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback m.cart m'.cart ψ ψ₁ sq
  have hm₁' : IsMonHom ψ₁' := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback m'.cart m.cart ψ' ψ₁' sq'
  have hsq2 : Hecke.sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ Hecke.sq2 ψ := by
    apply Over.tensorObj_ext
    · change (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (fst o'.A o'.A).left
      have l : (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, m'.sq.1, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, Category.assoc, sq]
      have r : (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (fst o'.A o'.A).left = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, m.sq.1, Category.assoc]
      exact l.trans r.symm
    · change (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (snd o'.A o'.A).left
      have l : (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, m'.sq.2, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, Category.assoc, sq]
      have r : (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (snd o'.A o'.A).left = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, m.sq.2, Category.assoc]
      exact l.trans r.symm
  refine ⟨ψ₁, ⟨hk, hm₁, fun a => ?_, fun x => ?_, ⟨?_⟩, ψ₁', hm₁', ?_, ?_⟩, sq.symm⟩
  · apply hom_ext_of_cart m'.cart
    have e1 : (o₁.act.act a ≫ ψ₁).left ≫ m'.φ = m.φ ≫ (o.act.act a ≫ ψ).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, sq, ← Category.assoc, m.act, Category.assoc]
    have e2 : (ψ₁ ≫ o₁'.act.act a).left ≫ m'.φ = m.φ ≫ (ψ ≫ o'.act.act a).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, m'.act, ← Category.assoc, sq, Category.assoc]
    rw [e1, e2, hact a]
  · apply hom_ext_of_cart m'.cart
    have e1 : (o₁.eta x ≫ ψ₁).left ≫ m'.φ = f ≫ (o.eta x ≫ ψ).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, sq, ← Category.assoc, m.eta, Category.assoc]
    rw [e1, m'.eta, heta x]
  · have hL₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hL₁ (pull_isLB o₁'.isLB _)).1 ?_
    have e₁ := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol
    have e₂ := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol
    have e₃ := (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB o'.isLB (Hecke.sq2 ψ))).2 hP
    rw [GlobalTheory.BirigidPow.cls_lbPow o.isLB, GlobalTheory.CechPic.cls_pull o'.isLB] at e₃
    rw [GlobalTheory.CechPic.cls_pull o.isLB] at e₁
    rw [GlobalTheory.CechPic.cls_pull o'.isLB] at e₂
    rw [GlobalTheory.BirigidPow.cls_lbPow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB, e₂, ← GlobalTheory.CechPic.pull_comp, hsq2,
      GlobalTheory.CechPic.pull_comp, ← e₃, map_nsmul, ← e₁]
  · apply hom_ext_of_cart m.cart
    rw [ESDual.pow_left_comm m.cart c, Over.comp_left, Category.assoc, sq', ← Category.assoc, sq, Category.assoc,
      ← Over.comp_left, h₁]
  · apply hom_ext_of_cart m'.cart
    rw [ESDual.pow_left_comm m'.cart c, Over.comp_left, Category.assoc, sq, ← Category.assoc, sq', Category.assoc,
      ← Over.comp_left, h₂]

end GlobalTheory.UPel.HT.ESPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedNonKltDivisorOfPrincipalisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory

theorem isolatedNonKltDivisor_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.IsolatedNonKltDivisor := by
  intro hP X _ _ _ p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hnef hbig hx hc hvol hsum
  letI := algebraΓOfHom p
  have hLB : N₀.IsLB := hnef.isLB
  obtain ⟨A, hA, hj⟩ := GlobalTheory.T.exists_logCanonical_cut_angehrnSiu_induction hP X p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hLB hnef hbig hx hc hvol
  obtain ⟨j', lam, μ, m', D₀, hj', hm', hD₀, hμ, hlam, hnum, hcut⟩ := hj 0 (by omega)
  obtain rfl : j' = 0 := Nat.le_zero.mp hj'
  exact GlobalTheory.T.exists_isolated_lcCentre_of_zero_lcThreshold hP X p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hLB hnef hbig hx hc hvol hsum
    A lam μ m' D₀ hA hm' hD₀ hμ (by simpa using hlam) hnum hcut

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingInd
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace GlobalTheory.EtC.GmStep

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem cechC_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] {R : Type} [CommRing R] (F : Shv R) (s : ℤ)
    (k : ℕ) (j : Fin (k + 2)) (y : H R (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) F s) :
    pull R (disc.map ((cechC A A').app (op ⦋k + 1⦌))) F s (pull R (disc.map ((cech (baseHom A A')).δ j)) F s y) =
      pull R (disc.map ((cech (laurentHom A A')).δ j)) F s (pull R (disc.map ((cechC A A').app (op ⦋k⦌))) F s y) := by
  simp only [SimplicialObject.δ]
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, (cechC A A').naturality]

theorem aug_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ) (j : Fin (k + 2)) :
    disc.map ((cech (laurentHom A A')).δ j) ≫ augK A A' k = augK A A' (k + 1) := by
  have h := (cechAug (laurentHom A A')).naturality (SimplexCategory.δ j).op
  exact (disc.map_comp _ _).symm.trans (congrArg disc.map (h.trans (Category.comp_id _)))

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

theorem rowExact_base (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Finite A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A)
    (j : ℤ) (p : ℕ) : RowExact (ZMod q) (cech (baseHom A A')) (tw q j) 0 p := by
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI, hS⟩ := spec_integral_surj (algebraMap A A') hint hker
  have hB := @GlobalTheory.EtC.b4 q _ _ (baseHom A A') hI hS (isUnit_gamma q A hq) j
  refine GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic (ZMod q) (tw q j) _ (fun k s hs => GlobalTheory.T.cech_cohomology_vanishes_positive q A hA hq A' inferInstance k s j hs) (fun m hm => ?_) p
  haveI : Subsingleton (H (ZMod q) (sch.obj (Spec (CommRingCat.of A))) (tw q j) m) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) m hm
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := (hB m).2 a
    obtain ⟨b', rfl⟩ := (hB m).2 b
    rw [Subsingleton.elim a' b']⟩

theorem gm_vanishing_step : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  intro q _ n hn IH A _ _ hA hq i
  suffices h : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨A', _, _, hfin, hker, hx⟩ := GlobalTheory.T.laurent_cohomology_finite_killing q A hA hq n i hn x
  haveI := hfin
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI', hS'⟩ := spec_integral_surj _ (laurentMap_isIntegral _ hint) (laurentMap_ker _ hker)
  have hqL : IsUnit (q : LaurentPolynomial A) := by simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  have hB := @GlobalTheory.EtC.b4 q _ _ (laurentHom A A') hI' hS' (isUnit_gamma q _ hqL) i
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
  apply (hB N).1
  rw [map_zero]
  obtain ⟨Δ, hΔ0, hΔ⟩ := GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base (laurentHom A A')
  refine GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact (ZMod q) (tw q i) (cech (laurentHom A A')) (yoneda.obj _) Δ hΔ0 N _ ?_ ?_
  · exact (pull_comp (ZMod q) Δ (cechAug (laurentHom A A')) (tw q i) N x).symm.trans
      ((congrArg (fun g => pull (ZMod q) g (tw q i) N x) hΔ).trans hx)
  · intro p hp
    rcases (by omega : (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 0 ∨ (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 1 ∨
        2 ≤ (N : ℤ) - ((p + 1 : ℕ) : ℤ)) with h0 | h1 | h2
    · rw [h0]
      exact rowExact_transfer (fun k => pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0)
        (fun k => GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero q A hA hq A' hfin k i) (fun k j y => cechC_face A A' _ _ k j y) p
        (rowExact_base q A hA hq A' hker i p)
    · rw [h1]
      refine rowExact_transfer (fun k => rowOne A A' q i k) (fun k => GlobalTheory.T.cech_degree_zero_bijective q A hA hq A' hfin k i) (fun k j y => ?_) p
        (rowExact_base q A hA hq A' hker (i - 1) p)
      simp only [rowOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [pull_cast, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1, cechC_face,
        ← pull_comp (ZMod q) (disc.map ((cech (laurentHom A A')).δ j)) (augK A A' k), aug_face]
    · intro y _
      haveI := GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton q N IH A hA hq A' hfin (p + 1) _ i h2 (by omega)
      exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩

end GlobalTheory.EtC.GmStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfDualHomomorphismKernelKilledStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  first | (exact @GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (exact GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (intros; apply GlobalTheory.DualHomSurj.surjective_of_ker_killed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsDifferAffineTwoMembersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedSum_exponents_differ_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y2 → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  first | exact @GlobalTheory.GSep.twistSum_exp_affine | exact GlobalTheory.GSep.twistSum_exp_affine | (intros; apply GlobalTheory.GSep.twistSum_exp_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickPrincipalObjectsIsoUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTrick_principal_objects_iso_unique : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∀ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₁ act₁ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  first | (exact @GlobalTheory.ZarhinFam.actPB_of_zRel) | (exact GlobalTheory.ZarhinFam.actPB_of_zRel) | (intros; apply GlobalTheory.ZarhinFam.actPB_of_zRel  <;> assumption)
end

