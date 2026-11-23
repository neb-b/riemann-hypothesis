module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRatAddMulOfMemAdjoin
section
namespace GlobalTheory.RatCoordsAdjoin

theorem exists_rat_add_mul_of_mem_adjoin {E : Type} [Field E] [NumberField E] (d : ℕ) (s : E)
    (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s := by
  have halg : IsAlgebraic ℚ s := Algebra.IsAlgebraic.isAlgebraic s
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := ℚ) (S := ({s} : Set E))
      (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact halg)]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hy]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a * c - b * e * d, a * e + b * c, by
      push_cast; linear_combination ((b : E) * (e : E)) * hs⟩

end GlobalTheory.RatCoordsAdjoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootNormSubPowLe
section
universe u_1

namespace GlobalTheory.RootNormPowerBound

open Polynomial

theorem pow_card_le_norm_eval_prod {K : Type u_1} [NormedField K] (x : K) (c : ℝ) (hc : 0 ≤ c)
    (s : Multiset K) (hs : ∀ a ∈ s, c ≤ ‖a - x‖) :
    c ^ Multiset.card s ≤ ‖Polynomial.eval x (s.map fun a => X - C a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul, mul_comm]
    have ha : c ≤ ‖eval x (X - C a)‖ := by
      rw [eval_sub, eval_X, eval_C, norm_sub_rev]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hc _)
      (norm_nonneg _)

theorem exists_root_norm_sub_pow_le {K : Type u_1} [inst : NormedField K] [IsAlgClosed K]
    (p : Polynomial K) (hp : (0 : ℕ) < Polynomial.natDegree p) (x : K) :
    ∃ b ∈ Polynomial.roots p,
      ‖Polynomial.leadingCoeff p‖ * ‖b - x‖ ^ Polynomial.natDegree p ≤ ‖Polynomial.eval x p‖ := by
  have hsp : p.Splits := IsAlgClosed.splits p
  have hcard := hsp.natDegree_eq_card_roots
  have hne : p.roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  obtain ⟨b, hb, hmin⟩ := Multiset.exists_min_image (fun a => ‖a - x‖) hne
  refine ⟨b, hb, ?_⟩
  conv_rhs => rw [hsp.eq_prod_roots]
  rw [eval_mul, eval_C, norm_mul, hcard]
  exact mul_le_mul_of_nonneg_left (pow_card_le_norm_eval_prod x _ (norm_nonneg _) _ hmin) (norm_nonneg _)

end GlobalTheory.RootNormPowerBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSaturated
section
universe u_1

namespace GlobalTheory.SaturatedNotDvd

theorem exists_saturated {A : Type u_1} [CommRing A] [IsDomain A] {x a b : A} (hx : Prime x)
    (hb : ¬ x ∣ b) {I : Ideal A} (hI : I ≠ ⊥) (h : ∀ r ∈ I, ∃ s ∈ I, a * r = b * s) :
    ∃ K : Ideal A, K ≠ ⊥ ∧ (∀ u, x * u ∈ K → u ∈ K) ∧ ∀ r ∈ K, ∃ s ∈ K, a * r = b * s := by
  let K : Ideal A :=
    { carrier := {u | ∃ k : ℕ, x ^ k * u ∈ I}
      add_mem' := by
        rintro u v ⟨k, hk⟩ ⟨l, hl⟩
        refine ⟨k + l, ?_⟩
        have e : x ^ (k + l) * (u + v) = x ^ l * (x ^ k * u) + x ^ k * (x ^ l * v) := by ring
        rw [e]
        exact I.add_mem (I.mul_mem_left _ hk) (I.mul_mem_left _ hl)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have e : x ^ k * (c • u) = c * (x ^ k * u) := by rw [smul_eq_mul]; ring
        rw [e]
        exact I.mul_mem_left _ hk }
  refine ⟨K, ?_, ?_, ?_⟩
  · intro hK
    apply hI
    rw [eq_bot_iff] at hK ⊢
    intro r hr
    exact hK (show ∃ k : ℕ, x ^ k * r ∈ I from ⟨0, by simpa using hr⟩)
  · rintro u ⟨k, hk⟩
    exact ⟨k + 1, by rw [pow_succ, mul_assoc]; exact hk⟩
  · rintro r ⟨k, hk⟩
    obtain ⟨s, hs, hrs⟩ := h _ hk
    have hdvd : x ^ k ∣ b * s := ⟨a * r, by rw [← hrs]; ring⟩
    obtain ⟨s', hs'⟩ := hx.pow_dvd_of_dvd_mul_left k hb hdvd
    refine ⟨s', ⟨k, by rw [← hs']; exact hs⟩, ?_⟩
    have hxk : x ^ k ≠ 0 := pow_ne_zero _ hx.ne_zero
    apply mul_left_cancel₀ hxk
    calc x ^ k * (a * r) = a * (x ^ k * r) := by ring
      _ = b * s := hrs
      _ = b * (x ^ k * s') := by rw [hs']
      _ = x ^ k * (b * s') := by ring

theorem exists_not_dvd {A : Type u_1} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hx : ¬ IsUnit x) {K : Ideal A} (hK : K ≠ ⊥) (hs : ∀ u, x * u ∈ K → u ∈ K) :
    ∃ u ∈ K, ¬ x ∣ u := by
  by_contra hall
  push_neg at hall
  apply hK
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) K (IsNoetherian.noetherian K)
  · intro u hu
    obtain ⟨u', rfl⟩ := hall u hu
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) (hs u' hu)
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)

theorem main : (let d1 : (A : Type u_1) → [CommRing A] → Prop := @(fun (A : Type u_1) [CommRing A] ↦ ∀ (a b : A) (I : Ideal A), b ≠ (0 : A) → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a); ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}, Prime x → d1 (A ⧸ Ideal.span {x}) → ∀ {a b : A}, ¬x ∣ b → ∀ {I : Ideal A}, I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a) := by
  intro d1 A _ _ _ _ x hx hd a b hb I hI h
  have hd' : ∀ (a b : A ⧸ Ideal.span {x}) (I : Ideal (A ⧸ Ideal.span {x})), b ≠ 0 → I ≠ ⊥ →
      (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a := hd
  obtain ⟨K, hK, hsat, hKa⟩ := exists_saturated hx hb hI h
  obtain ⟨u₀, hu₀, hxu⟩ := exists_not_dvd hx.not_unit hK hsat
  have hz : ∀ y : A, Ideal.Quotient.mk (Ideal.span {x}) y = 0 ↔ x ∣ y := fun y => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have step : ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c d : A, a = b * c + x * d ∧ ∀ r ∈ K, ∃ s ∈ K, d * r = b * s := by
    intro a ha
    have hdiv : Ideal.Quotient.mk (Ideal.span {x}) b ∣ Ideal.Quotient.mk (Ideal.span {x}) a := by
      refine hd' _ _ (K.map (Ideal.Quotient.mk (Ideal.span {x}))) (fun h0 => hb ((hz b).1 h0)) ?_ ?_
      · intro hbot
        have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {x})) hu₀
        rw [hbot, Ideal.mem_bot] at hm
        exact hxu ((hz _).1 hm)
      · intro r hr
        obtain ⟨r', hr', rfl⟩ :=
          (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hr
        obtain ⟨s, hs, hrs⟩ := ha r' hr'
        exact ⟨_, Ideal.mem_map_of_mem _ hs, by rw [← map_mul, ← map_mul, hrs]⟩
    obtain ⟨c', hc'⟩ := hdiv
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
    have hxd : x ∣ a - b * c := (hz _).1 (by rw [map_sub, map_mul, hc', sub_self])
    obtain ⟨d, hdd⟩ := hxd
    refine ⟨c, d, by linear_combination hdd, ?_⟩
    intro r hr
    obtain ⟨s, hs, hrs⟩ := ha r hr
    have h1 : b * (s - c * r) = x * (d * r) := by linear_combination r * hdd - hrs
    have h2 : x ∣ s - c * r := (hx.dvd_or_dvd ⟨_, h1⟩).resolve_left hb
    obtain ⟨w, hw⟩ := h2
    have hwK : w ∈ K := hsat w (hw ▸ K.sub_mem hs (K.mul_mem_left c hr))
    refine ⟨w, hwK, ?_⟩
    apply mul_left_cancel₀ hx.ne_zero
    rw [← h1, hw]; ring
  have iter : ∀ n : ℕ, ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c y : A, a = b * c + x ^ n * y := by
    intro n
    induction n with
    | zero => intro a _; exact ⟨0, a, by simp⟩
    | succ n ih =>
      intro a ha
      obtain ⟨c, d, rfl, hd2⟩ := step a ha
      obtain ⟨c', y, rfl⟩ := ih d hd2
      exact ⟨c + x * c', y, by ring⟩
  have hne : Ideal.span {x} ≠ ⊤ := fun h => hx.not_unit (Ideal.span_singleton_eq_top.1 h)
  have hk := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ Ideal.span {b})
    (Ideal.span {x}) hne
  have hmem : Ideal.Quotient.mk (Ideal.span {b}) a ∈
      (⨅ i : ℕ, Ideal.span {x} ^ i • ⊤ : Submodule A (A ⧸ Ideal.span {b})) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨c, y, hcy⟩ := iter n a hKa
    have : Ideal.Quotient.mk (Ideal.span {b}) a
        = x ^ n • Ideal.Quotient.mk (Ideal.span {b}) y := by
      change _ = Ideal.Quotient.mk (Ideal.span {b}) (x ^ n * y)
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨c, by rw [hcy]; ring⟩
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) n)
      Submodule.mem_top
  rw [hk, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmem
  exact hmem

end GlobalTheory.SaturatedNotDvd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearDescentToBaseChangeOfForm
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_semilinear_descent_to_baseChange :
  ∀ {LL : Type} [Field LL] [Algebra ℚ LL] (L0 : IntermediateField ℚ LL) {Ks : Type} [Field Ks] [Algebra Ks LL]
    (kKs : Ks →+* L0), (∀ x, ((kKs x : L0) : LL) = algebraMap Ks LL x) →
    ∀ {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL) {n : ℕ} (bs : Fin n → WL), (∀ i, bs i ∈ WK) →
    Submodule.span Ks (Set.range bs) = WK → LinearIndependent LL bs → Submodule.span LL (Set.range bs) = ⊤ →
    ∀ {KT : Type} [Field KT] [Algebra Ks KT] (rd : L0 →+* KT), (∀ s, algebraMap Ks KT s = rd (kKs s)) →
    ∃ Φ : WL →+ KT ⊗[Ks] WK, (∀ (c : L0) (x : WL), Φ ((c : LL) • x) = rd c • Φ x) ∧
      (∀ (f : WL →ₗ[LL] WL) (fr : WK →ₗ[Ks] WK), (∀ w : WK, (fr w : WL) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange KT fr (Φ x)) ∧
      ∀ w : WK, Φ (w : WL) = (1 : KT) ⊗ₜ[Ks] w := by
  intro LL _ _ L0 Ks _ _ kKs hk WL _ _ _ _ WK n bs hb hKs hLi hLs KT _ _ rd hrd
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L0 LL)
    (LinearMap.ker_eq_bot.mpr (algebraMap L0 LL).injective)
  have hπ1 : π 1 = 1 := by
    have := LinearMap.congr_fun hπ 1
    simpa using this
  have hπx : ∀ (c : L0) (y : LL), π ((c : LL) * y) = c * π y := by
    intro c y
    have : ((c : LL) * y) = c • y := (Algebra.smul_def c y).symm
    rw [this, map_smul, smul_eq_mul]
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin n) LL WL, ∀ k, B k = bs k :=
    ⟨Module.Basis.mk hLi (by rw [hLs]), fun k => Module.Basis.mk_apply _ _ k⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : WL →+ KT ⊗[Ks] WK,
      ∀ x, Φ x = ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK)) :=
    ⟨{ toFun := fun x => ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK))
       map_zero' := by simp
       map_add' := by intro x y; simp [map_add (f := _), add_smul, Finset.sum_add_distrib] },
     fun _ => rfl⟩
  have key : ∀ (l : LL) (w : WK), Φ (l • (w : WL)) = rd (π l) • ((1 : KT) ⊗ₜ[Ks] w) := by
    intro l w
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).mp
      (show (w : WL) ∈ Submodule.span Ks (Set.range bs) by rw [hKs]; exact w.2)
    have hw : w = ∑ k, s k • (⟨bs k, hb k⟩ : WK) := by
      apply Subtype.ext; simp [hs]
    have hrep : ∀ k, B.repr (l • (w : WL)) k = l * algebraMap Ks LL (s k) := by
      have : l • (w : WL) = ∑ k, (l * algebraMap Ks LL (s k)) • B k := by
        rw [← hs, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hB, mul_smul, algebraMap_smul]
      intro k
      rw [this, B.repr_sum_self]
    rw [hΦ]
    conv_rhs => rw [hw, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrep, ← hk, mul_comm, hπx, map_mul, ← hrd, TensorProduct.tmul_smul, ← algebraMap_smul KT (s k),
      smul_smul, mul_comm]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro c x
    rw [hΦ, hΦ x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hπx, map_mul, mul_smul]
  · intro f fr hf x
    conv_lhs => rw [← B.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, hΦ x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hB, ← hf ⟨bs k, hb k⟩, key, map_smul, LinearMap.baseChange_tmul]
  · intro w
    have := key 1 w
    rw [one_smul, hπ1, map_one, one_smul] at this
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulEqZeroOfCrossed
section
set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.TransferCommutator

theorem exists_smul_eq_zero_of_crossed {G : Type} [Group G] [Finite G] {R : Type} [CommRing R] (ε : R →+* ℤ)
    (ρ : G → R) (hρ : ∀ g, ε (ρ g) = 1) {X : Type} [AddCommGroup X] [Module R X] (d : G → X)
    (hd : ∀ g h, d (g * h) = d g + ρ g • d h) :
    ∃ μ : R, (ε μ).natAbs = Nat.card (Abelianization G) ∧ ∀ g, μ • d g = 0 := by
  classical
  have := Fintype.ofFinite G
  let J : Submodule R X := (Submodule.pi Set.univ fun _ : G => RingHom.ker ε).map (Fintype.linearCombination R d)
  let ψ : G →* Multiplicative (X ⧸ J) := MonoidHom.mk' (fun g => Multiplicative.ofAdd (J.mkQ (d g))) fun g h => by
    rw [← ofAdd_add, ← map_add (f := _)]
    congr 1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hd]
    refine ⟨Pi.single h (ρ g - 1), fun i _ => ?_, ?_⟩
    · by_cases hi : i = h
      · subst hi; simp [RingHom.mem_ker, hρ]
      · simp [hi]
    · rw [Fintype.linearCombination_apply_single, sub_smul, one_smul]; abel
  let ψ' : Additive (Group.Abelianization G) →ₗ[ℤ] X ⧸ J :=
    (MonoidHom.toAdditiveLeft (Group.Abelianization.lift ψ)).toIntLinearMap
  have hψ' : ∀ g, ψ' (Additive.ofMul (Group.Abelianization.of g)) = J.mkQ (d g) := fun g => rfl
  let L : (G → ℤ) →ₗ[ℤ] Additive (Group.Abelianization G) :=
    Fintype.linearCombination ℤ fun g => Additive.ofMul (Group.Abelianization.of g)
  have hL : Function.Surjective L := fun q => by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (s := commutator G) q.toMul
    exact ⟨Pi.single g 1, by rw [Fintype.linearCombination_apply_single, one_smul]; exact congrArg Additive.ofMul hg⟩
  have eq := L.quotKerEquivOfSurjective hL
  have hfin : Finite (Group.Abelianization G) := inferInstanceAs (Finite (G ⧸ commutator G))
  have : Finite ((G → ℤ) ⧸ LinearMap.ker L) := Finite.of_equiv _ eq.symm.toEquiv
  let e : (G → ℤ) ≃ₗ[ℤ] LinearMap.ker L :=
    LinearEquiv.ofFinrankEq _ _ ((Submodule.finiteQuotient_iff _).1 this).symm
  have hdet := Submodule.natAbs_det_equiv (LinearMap.ker L) e
  have hrel : ∀ n : LinearMap.ker L, ∃ ν : G → R, (∀ i, ε (ν i) = n.1 i) ∧ ∑ i, ν i • d i = 0 := fun n => by
    have h0 : ∑ i, n.1 i • d i ∈ J := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      have := congrArg ψ' n.2
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, Fintype.linearCombination_apply, map_sum] at this
      simpa only [map_zsmul, hψ'] using this
    obtain ⟨ν, hν, hs⟩ := h0
    refine ⟨fun i => (n.1 i : R) - ν i, fun i => ?_, ?_⟩
    · rw [map_sub, (RingHom.mem_ker).1 (hν i trivial)]; simp
    · simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul]
      rw [← hs, Fintype.linearCombination_apply, sub_self]
  choose ν hν hs using hrel
  let M : Matrix G G R := Matrix.of fun j i => ν (e (Pi.single j 1)) i
  refine ⟨M.det, ?_, fun k => ?_⟩
  · change (ε M.det).natAbs = Nat.card (Group.Abelianization G)
    rw [RingHom.map_det, ← Matrix.det_transpose, ← Nat.card_congr (eq.toEquiv.trans Additive.toMul), ← hdet,
      ← LinearMap.det_toMatrix']
    congr 2
    ext i j
    simp [M, hν, LinearMap.toMatrix'_apply]
  · have h1 : M.det • d k = ∑ i, (M.adjugate * M) k i • d i := by
      rw [Matrix.adjugate_mul]
      simp [Matrix.one_apply]
    rw [h1]
    simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.smul_sum]
    exact (congrArg _ (hs _)).trans (smul_zero _)

theorem transfer_eq_one (G : Type) [Group G] [Finite G] (B : Type) [CommGroup B] (φ : commutator G →* B) :
    MonoidHom.transfer φ = 1 := by
  classical
  let Q := Group.Abelianization G
  have hfin : Finite Q := inferInstanceAs (Finite (G ⧸ commutator G))
  let : Fintype Q := (commutator G).fintypeQuotientOfFiniteIndex
  let R := MonoidAlgebra ℤ Q
  let T : (commutator G).LeftTransversal := default
  let α : Q → G := fun q => (T.2.leftQuotientEquiv q : G)
  have hα : ∀ q, Group.Abelianization.of (α q) = q := fun q => T.2.leftQuotientEquiv.symm_apply_apply q
  have hmem : ∀ g q, (α q)⁻¹ * g * α ((Group.Abelianization.of g)⁻¹ * q) ∈ commutator G := fun g q => by
    rw [← Group.Abelianization.ker_of, MonoidHom.mem_ker]
    simp [hα]
  let b : G → Q → Additive B := fun g q => Additive.ofMul (φ ⟨_, hmem g q⟩)
  have hb : ∀ g h q, b (g * h) q = b g q + b h ((Group.Abelianization.of g)⁻¹ * q) := fun g h q => by
    simp only [b]
    rw [← ofMul_mul, ← map_mul]
    congr 2
    ext
    simp [mul_assoc]
  let s : Q →* R := MonoidAlgebra.of ℤ Q
  let ε : R →ₐ[ℤ] ℤ := MonoidAlgebra.lift ℤ ℤ Q 1
  let d : G → (R ⊗[ℤ] Additive B) × R := fun g => (∑ q, s q ⊗ₜ b g q, s (Group.Abelianization.of g) - 1)
  obtain ⟨μ, hμ, h0⟩ := exists_smul_eq_zero_of_crossed (ε : R →+* ℤ) (fun g => s (Group.Abelianization.of g))
    (fun g => MonoidAlgebra.lift_of _ _) d fun g h => by
      refine Prod.ext ?_ ?_
      · simp only [d, Prod.fst_add, Prod.smul_fst, hb, TensorProduct.tmul_add, Finset.sum_add_distrib,
          Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]
        congr 1
        exact (Fintype.sum_equiv (Equiv.mulLeft (Group.Abelianization.of g)) _ _ fun q => by simp).symm
      · simp only [d, Prod.snd_add, Prod.smul_snd, map_mul, smul_eq_mul]; ring
  have hinv : ∀ q, μ * s q = μ := fun q => by
    have := congrArg Prod.snd (h0 (α q))
    simp only [d, Prod.smul_snd, hα, smul_eq_mul, mul_sub, mul_one, Prod.snd_zero] at this
    exact sub_eq_zero.1 this
  have hc : ∀ q, μ.coeff q = μ.coeff 1 := fun q => by
    have := MonoidAlgebra.coeff_mul_single_apply μ 1 q⁻¹ 1
    rw [show μ * MonoidAlgebra.single q⁻¹ 1 = μ from hinv q⁻¹] at this
    rw [inv_inv, one_mul, mul_one] at this
    exact this.symm
  have hε : ε μ = (Nat.card Q : ℤ) * μ.coeff 1 := by
    simp only [ε]
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [hc]
  have hu : (μ.coeff 1).natAbs = 1 := by
    rw [show (ε : R →+* ℤ) μ = _ from hε, Int.natAbs_mul, Int.natAbs_natCast] at hμ
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q)) (hμ.trans (mul_one _).symm)
  let c : R →ₗ[ℤ] ℤ := Finsupp.lapply (1 : Q) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℤ (S := ℤ) (M := Q)).toLinearMap
  ext g
  have h1 := congrArg Prod.fst (h0 g)
  simp only [d, Prod.smul_fst, Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, hinv, Prod.fst_zero,
    ← TensorProduct.tmul_sum] at h1
  have h2 := congrArg (fun x => TensorProduct.lid ℤ _ (c.rTensor _ x)) h1
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h2
  have h3 : ∑ q, b g q = 0 := by
    rcases Int.natAbs_eq_iff.1 hu with h | h
    · rw [show c μ = _ from h] at h2; simpa using h2
    · rw [show c μ = _ from h] at h2; simpa using h2
  rw [MonoidHom.transfer_def φ T, MonoidHom.one_apply]
  have h4 : ∏ q, (b g q).toMul = 1 := by rw [← toMul_sum, h3, toMul_zero]
  refine Eq.trans (Finset.prod_congr rfl fun q _ => congrArg φ (Subtype.ext ?_)) h4
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_assoc]
  rfl

end GlobalTheory.TransferCommutator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemSpanIntegers
section
namespace GlobalTheory.SmulMemSpanIntegers

theorem exists_smul_mem_span_integers {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type}
    [AddCommGroup WL] [Module Ks WL] [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {T : Set WL} {g : WL}
    (hg : g ∈ Submodule.span Ks T) :
    ∃ d : NumberField.RingOfIntegers Ks, d ≠ 0 ∧
      d • g ∈ Submodule.span (NumberField.RingOfIntegers Ks) T := by

  induction hg using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨d₁, hd₁, h₁⟩ := ihx
    obtain ⟨d₂, hd₂, h₂⟩ := ihy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm d₁ d₂ x]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul c x _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers Ks) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (NumberField.RingOfIntegers Ks) Ks b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ Ks)).2 hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have e : b • ((algebraMap (NumberField.RingOfIntegers Ks) Ks a /
        algebraMap (NumberField.RingOfIntegers Ks) Ks b) • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ hbK, algebraMap_smul]
    rw [mul_comm, mul_smul, e, smul_comm]
    exact Submodule.smul_mem _ _ h

end GlobalTheory.SmulMemSpanIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatible
section
open IsLocalRing

namespace GlobalTheory

theorem mem_ideal_smul_top_iff_mem {V : Type} [CommRing V] (I : Ideal V) (x : V) :
    x ∈ I • (⊤ : Submodule V V) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem localHom_map_mem_maximalIdeal_pow {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) {x : A}
    (hx : x ∈ maximalIdeal A ^ n) : α x ∈ maximalIdeal V ^ n := by
  have h1 : (maximalIdeal A).map α ≤ maximalIdeal V := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact map_nonunit α y hy
  have := Ideal.mem_map_of_mem α hx
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h1 n this

theorem eval_map_mem_maximalIdeal_pow_of_coeff_mem {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) (D : Polynomial A)
    (hD : ∀ i, D.coeff i ∈ maximalIdeal A ^ n) (η : V) :
    (D.map α).eval η ∈ maximalIdeal V ^ n := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (localHom_map_mem_maximalIdeal_pow α n (hD i))

end GlobalTheory
end

