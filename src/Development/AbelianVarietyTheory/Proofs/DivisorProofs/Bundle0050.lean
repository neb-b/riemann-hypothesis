module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAdjoin
section
open NumberField

noncomputable section

open Polynomial

namespace GlobalTheory.CycSpanFin

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem commute_aeval_left {x y : Module.End ℂ V} (h : Commute x y) (p : ℂ[X]) : Commute (aeval x p) y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial n a => rw [aeval_monomial]; exact (Algebra.commute_algebraMap_left a y).mul_left (h.pow_left n)

theorem coeff_mem_span_fin {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} {a : ℕ → M} {p : ℂ → M}
    (hp : ∀ u, p u = ∑ i ∈ Finset.range (n + 1), u ^ i • a i) {i : ℕ} (hi : i < n + 1) :
    a i ∈ Submodule.span ℂ (Set.range fun j : Fin (n + 1) => p ((j : ℕ) : ℂ)) := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  set Q : ℂ[X] := ∑ j ∈ Finset.range (n + 1), monomial j (φ (a j)) with hQdef
  have hev : ∀ u, Q.eval u = φ (p u) := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp, map_sum]
    simp only [Q, Polynomial.eval_finsetSum, eval_monomial]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hdeg : Q.natDegree ≤ n := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have h0 : Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
      (f := fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Nat.cast_injective.comp Fin.val_injective) ?_ ?_
    · intro j
      rw [hev]
      exact (Submodule.mem_dualAnnihilator φ).1 hφ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simpa using Nat.lt_succ_of_le hdeg
  have hcoeff : Q.coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
  rw [hQdef, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi), Polynomial.coeff_monomial_same] at hcoeff
  · exact hcoeff
  · intro j _ hji
    exact Polynomial.coeff_monomial_of_ne _ hji.symm

def stabAlg (N : Submodule ℂ V) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {T | ∀ v ∈ N, T v ∈ N}
  mul_mem' ha hb v hv := ha _ (hb v hv)
  add_mem' ha hb v hv := N.add_mem (ha v hv) (hb v hv)
  algebraMap_mem' r v hv := by
    rw [Module.algebraMap_end_apply]
    exact N.smul_mem r hv

def ext (T : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : Submodule ℂ V :=
  ⨆ k : Fin (d + 1), N.map (T ^ (k : ℕ))

theorem le_ext (T : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : N ≤ ext T d N := fun v hv =>
  Submodule.mem_iSup_of_mem (0 : Fin (d + 1)) ⟨v, hv, by simp⟩

theorem pow_mem_ext (T : Module.End ℂ V) {d k : ℕ} (hk : k ≤ d) {N : Submodule ℂ V} {v : V} (hv : v ∈ N) :
    (T ^ k) v ∈ ext T d N :=
  Submodule.mem_iSup_of_mem (⟨k, by omega⟩ : Fin (d + 1)) (Submodule.mem_map_of_mem hv)

theorem aeval_mem_ext (T : Module.End ℂ V) {Q : ℂ[X]} (hQ : Q ≠ 0) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, aeval T Q v = 0) (p : ℂ[X]) {v : V} (hv : v ∈ N) : aeval T p v ∈ ext T Q.natDegree N := by
  set Q' := Q * C Q.leadingCoeff⁻¹ with hQ'
  have hm : Q'.Monic := monic_mul_leadingCoeff_inv hQ
  have hdeg : Q'.natDegree = Q.natDegree := by
    rw [hQ', natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hQ))]
  have hQ'v : aeval T Q' v = 0 := by
    rw [hQ', mul_comm, map_mul, mul_apply_eq_comp, hN v hv, map_zero]
  have hsplit : p = p %ₘ Q' + (p /ₘ Q') * Q' := by
    rw [mul_comm]; exact (modByMonic_add_div p Q').symm
  rw [hsplit, map_add (f := _), LinearMap.add_apply, map_mul, mul_apply_eq_comp, hQ'v, map_zero, add_zero]
  have hlt : (p %ₘ Q').natDegree < Q.natDegree + 1 := by
    have := natDegree_modByMonic_le p hm
    omega
  rw [aeval_eq_sum_range' hlt, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (pow_mem_ext T (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hv)

theorem ext_stable (T : Module.End ℂ V) {Q : ℂ[X]} (hQ : Q ≠ 0) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, aeval T Q v = 0) : ∀ v ∈ ext T Q.natDegree N, T v ∈ ext T Q.natDegree N := by
  have : ext T Q.natDegree N ≤ (ext T Q.natDegree N).comap T := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap]
    change T ((T ^ (k : ℕ)) x) ∈ ext T Q.natDegree N
    have := aeval_mem_ext T hQ hN (X ^ ((k : ℕ) + 1)) hx
    rwa [map_pow, aeval_X, pow_succ', mul_apply_eq_comp] at this
  exact fun v hv => this hv

theorem ext_stable_comm (T S : Module.End ℂ V) (d : ℕ) (hST : Commute S T) {N : Submodule ℂ V}
    (hS : ∀ v ∈ N, S v ∈ N) : ∀ v ∈ ext T d N, S v ∈ ext T d N := by
  have : ext T d N ≤ (ext T d N).comap S := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap]
    change S ((T ^ (k : ℕ)) x) ∈ ext T d N
    have h := congrArg (fun F : Module.End ℂ V => F x) (hST.pow_right (k : ℕ)).eq
    simp only [mul_apply_eq_comp] at h
    rw [h]
    exact pow_mem_ext T (Nat.lt_succ_iff.1 k.2) (hS x hx)
  exact fun v hv => this hv

theorem ext_kill (T R : Module.End ℂ V) (d : ℕ) (hRT : Commute R T) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, R v = 0) : ∀ v ∈ ext T d N, R v = 0 := by
  have : ext T d N ≤ LinearMap.ker R := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [LinearMap.mem_ker]
    have h := congrArg (fun F : Module.End ℂ V => F x) (hRT.pow_right (k : ℕ)).eq
    simp only [mul_apply_eq_comp] at h
    rw [h, hN x hx, map_zero]
  exact fun v hv => this hv

theorem exists_stable (a : ℕ → Module.End ℂ V) (Q : ℕ → ℂ[X]) (hc : ∀ i j, Commute (a i) (a j))
    (hQ : ∀ j, Q j ≠ 0) (w : V) (hw : ∀ j, aeval (a j) (Q j) w = 0) : ∀ m : ℕ, ∃ N : Submodule ℂ V,
      FiniteDimensional ℂ N ∧ w ∈ N ∧ (∀ j < m, ∀ v ∈ N, a j v ∈ N) ∧ (∀ j, ∀ v ∈ N, aeval (a j) (Q j) v = 0) := by
  intro m
  induction m with
  | zero =>
    exact ⟨Submodule.span ℂ {w}, inferInstance, Submodule.mem_span_singleton_self w, by simp, fun j v hv => by
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hw, smul_zero]⟩
  | succ m ih =>
    obtain ⟨N, hf, hwN, hst, hk⟩ := ih
    refine ⟨ext (a m) (Q m).natDegree N, ?_, le_ext _ _ _ hwN, ?_, ?_⟩
    · unfold ext
      infer_instance
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact ext_stable_comm (a m) (a j) _ (hc j m) (hst j h)
      · subst j
        exact ext_stable (a m) (hQ m) (hk m)
    · intro j
      exact ext_kill (a m) _ _ (commute_aeval_left (hc j m) _) (hk j)

theorem finiteDimensional_span_adjoin : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V)
    (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) →
    ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) →
    FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := by
  intro V _ _ n c g hg hc w P hP hw
  obtain ⟨N, hf, hwN, hst, -⟩ := exists_stable (fun j : ℕ => g (j : ℂ)) (fun j => P (j : ℂ))
    (fun i j => hc _ _) (fun j => hP _) w (fun j => hw _) (n + 1)
  have hgS : ∀ u, g u ∈ stabAlg N := by
    intro u
    have hspan : Submodule.span ℂ (Set.range fun j : Fin (n + 1) => g ((j : ℕ) : ℂ)) ≤
        Subalgebra.toSubmodule (stabAlg N) :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact fun v hv => hst j j.2 v hv)
    apply hspan
    rw [hg u]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (coeff_mem_span_fin hg (Finset.mem_range.1 hi))
  have hA : Algebra.adjoin ℂ (Set.range g) ≤ stabAlg N :=
    Algebra.adjoin_le (by rintro _ ⟨u, rfl⟩; exact hgS u)
  have hle : Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w} ≤ N :=
    Submodule.span_le.2 (by rintro _ ⟨b, hb, rfl⟩; exact hA hb w hwN)
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CycSpanFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
section
namespace GlobalTheory.KilledFin

open Polynomial

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem span_adjoin_apply_le (s : Set (Module.End ℂ V)) (K : Submodule ℂ V)
    (hs : ∀ u ∈ s, ∀ v ∈ K, u v ∈ K) (ψ : V) (hψ : ψ ∈ K) :
    Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ s : Set (Module.End ℂ V)))
      ≤ K := by
  have key : ∀ z ∈ Algebra.adjoin ℂ s, ∀ v ∈ K, z v ∈ K := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap r =>
      intro v hv
      rw [Module.algebraMap_end_apply]
      exact K.smul_mem r hv
    | add x y _ _ hx hy =>
      intro v hv
      rw [LinearMap.add_apply]
      exact K.add_mem (hx v hv) (hy v hv)
    | mul x y _ _ hx hy =>
      intro v hv
      rw [Module.End.mul_apply]
      exact hx _ (hy v hv)
  rw [Submodule.span_le]
  rintro _ ⟨z, hz, rfl⟩
  exact key z hz ψ hψ

theorem span_adjoin_apply_stable (s : Set (Module.End ℂ V)) (ψ : V) (u : Module.End ℂ V)
    (hu : u ∈ Algebra.adjoin ℂ s) (v : V)
    (hv : v ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
      (Algebra.adjoin ℂ s : Set (Module.End ℂ V)))) :
    u v ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
      (Algebra.adjoin ℂ s : Set (Module.End ℂ V))) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨u * z, Subalgebra.mul_mem _ hu hz, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem commute_of_mem_adjoin (s : Set (Module.End ℂ V)) (t : Module.End ℂ V)
    (ht : ∀ u ∈ s, Commute u t) (z : Module.End ℂ V) (hz : z ∈ Algebra.adjoin ℂ s) (q : ℂ[X]) :
    Commute z (aeval t q) := by
  have h1 : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {t} := by
    rw [Algebra.adjoin_le_iff]
    intro u hu
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ((ht u hu).eq).symm
  have h2 : z ∈ Subalgebra.centralizer ℂ {t} := h1 hz
  have h3 : Algebra.adjoin ℂ {t} ≤ Subalgebra.centralizer ℂ {z} := by
    rw [Algebra.adjoin_le_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [Subalgebra.mem_centralizer_iff] at h2
    exact (h2 g rfl).symm
  have h4 := h3 (Polynomial.aeval_mem_adjoin_singleton ℂ (x := t) (p := q))
  rw [Subalgebra.mem_centralizer_iff] at h4
  exact h4 z rfl

def powSpan (t : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ i < d, ∃ n ∈ N, v = (t ^ i) n}

theorem pow_mem_powSpan (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) (n : V) (hn : n ∈ N) :
    (t ^ q.natDegree) n ∈ powSpan t q.natDegree N := by
  set d := q.natDegree with hd
  have hlc : q.coeff d ≠ 0 := by
    rw [hd, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hq
  have h0 := hkill n hn
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, LinearMap.add_apply,
    LinearMap.sum_apply] at h0
  have h1 := eq_neg_of_add_eq_zero_right h0
  have h2 : q.coeff d • (t ^ d) n ∈ powSpan t d N := by
    rw [← LinearMap.smul_apply, h1]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
    rw [LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨j, Finset.mem_range.mp hj, n, hn, rfl⟩
  exact (Submodule.smul_mem_iff _ hlc).mp h2

theorem powSpan_stable_self (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) (v : V) (hv : v ∈ powSpan t q.natDegree N) :
    t v ∈ powSpan t q.natDegree N := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, n, hn, rfl⟩ := hx
    have e : t ((t ^ i) n) = (t ^ (i + 1)) n := by rw [pow_succ', Module.End.mul_apply]
    rw [e]
    rcases Nat.lt_or_ge (i + 1) q.natDegree with h | h
    · exact Submodule.subset_span ⟨i + 1, h, n, hn, rfl⟩
    · have : i + 1 = q.natDegree := by omega
      rw [this]
      exact pow_mem_powSpan t q hq N hkill n hn
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem powSpan_stable (t u : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V)
    (hu : ∀ n ∈ N, u n ∈ N) (hc : Commute u t) (v : V) (hv : v ∈ powSpan t d N) :
    u v ∈ powSpan t d N := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, n, hn, rfl⟩ := hx
    have e : u ((t ^ i) n) = (t ^ i) (u n) := by
      rw [← Module.End.mul_apply, (hc.pow_right i).eq, Module.End.mul_apply]
    rw [e]
    exact Submodule.subset_span ⟨i, hi, u n, hu n hn, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem le_powSpan (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) : N ≤ powSpan t q.natDegree N := by
  intro n hn
  rcases Nat.eq_zero_or_pos q.natDegree with h | h
  · have hC := Polynomial.eq_C_of_natDegree_eq_zero h
    have h0 := hkill n hn
    rw [hC, Polynomial.aeval_C, Module.algebraMap_end_apply] at h0
    have hc0 : q.coeff 0 ≠ 0 := by
      intro hc; apply hq; rw [hC, hc, map_zero]
    rw [(smul_eq_zero.mp h0).resolve_left hc0]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨0, h, n, hn, by simp⟩

theorem powSpan_finite (t : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) [FiniteDimensional ℂ N] :
    FiniteDimensional ℂ (powSpan t d N) ∧
      Module.finrank ℂ (powSpan t d N) ≤ d * Module.finrank ℂ N := by
  let Φ : (Fin d → N) →ₗ[ℂ] V :=
    ∑ i : Fin d, (t ^ (i : ℕ)) ∘ₗ N.subtype ∘ₗ LinearMap.proj i
  have hle : powSpan t d N ≤ LinearMap.range Φ := by
    rw [powSpan, Submodule.span_le]
    rintro _ ⟨i, hi, n, hn, rfl⟩
    refine ⟨Pi.single ⟨i, hi⟩ ⟨n, hn⟩, ?_⟩
    simp [Φ, LinearMap.sum_apply, Pi.single_apply]
    rw [Finset.sum_eq_single ⟨i, hi⟩ (fun b _ hb => by simp [hb]) (by simp)]
    simp
  haveI : FiniteDimensional ℂ (LinearMap.range Φ) := inferInstance
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  calc Module.finrank ℂ (powSpan t d N) ≤ Module.finrank ℂ (LinearMap.range Φ) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ (Fin d → N) := LinearMap.finrank_range_le Φ
    _ = d * Module.finrank ℂ N := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]

end GlobalTheory.KilledFin


open Polynomial in
theorem GlobalTheory.killed_span_adjoin_finrank_le :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V))
      (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) →
      (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) →
      FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧
      Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤
        ∏ t ∈ T, (p t).natDegree := by
  intro V _ _ T p
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ _ ψ _
    have hle := GlobalTheory.KilledFin.span_adjoin_apply_le (V := V) ((∅ : Finset (Module.End ℂ V)) : Set _)
      (Submodule.span ℂ {ψ}) (by intro u hu; simp at hu) ψ (Submodule.mem_span_singleton_self ψ)
    refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
    rw [Finset.prod_empty]
    refine (Submodule.finrank_mono hle).trans ?_
    exact (finrank_span_le_card ({ψ} : Set V)).trans (by simp)
  | insert t T htT ih =>
    intro hcomm hne ψ hkillψ
    have hcommT : ∀ s ∈ T, ∀ u ∈ T, Commute s u := fun s hs u hu =>
      hcomm s (Finset.mem_insert_of_mem hs) u (Finset.mem_insert_of_mem hu)
    obtain ⟨hfd, hrk⟩ := ih hcommT (fun u hu => hne u (Finset.mem_insert_of_mem hu)) ψ
      (fun u hu => hkillψ u (Finset.mem_insert_of_mem hu))
    set N := Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) with hN
    have htcomm : ∀ u ∈ (T : Set (Module.End ℂ V)), Commute u t := fun u hu =>
      hcomm u (Finset.mem_insert_of_mem hu) t (Finset.mem_insert_self t T)
    have hkill : ∀ n ∈ N, aeval t (p t) n = 0 := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        have hc := GlobalTheory.KilledFin.commute_of_mem_adjoin _ t htcomm z hz (p t)
        show aeval t (p t) (z ψ) = 0
        rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply,
          hkillψ t (Finset.mem_insert_self t T), map_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
    have hq := hne t (Finset.mem_insert_self t T)
    have hK := GlobalTheory.KilledFin.powSpan_finite t (p t).natDegree N
    have hψK : ψ ∈ GlobalTheory.KilledFin.powSpan t (p t).natDegree N :=
      GlobalTheory.KilledFin.le_powSpan t (p t) hq N hkill
        (Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩)
    have hle := GlobalTheory.KilledFin.span_adjoin_apply_le
      ((insert t T : Finset (Module.End ℂ V)) : Set (Module.End ℂ V))
      (GlobalTheory.KilledFin.powSpan t (p t).natDegree N) (by
        intro u hu v hv
        rw [Finset.coe_insert, Set.mem_insert_iff] at hu
        rcases hu with hut | hu
        · subst hut
          exact GlobalTheory.KilledFin.powSpan_stable_self u (p u) hq N hkill v hv
        · exact GlobalTheory.KilledFin.powSpan_stable t u _ N
            (fun n hn => GlobalTheory.KilledFin.span_adjoin_apply_stable _ ψ u
              (Algebra.subset_adjoin hu) n hn) (htcomm u hu) v hv) ψ hψK
    haveI := hK.1
    refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
    rw [Finset.prod_insert htT]
    calc _ ≤ Module.finrank ℂ (GlobalTheory.KilledFin.powSpan t (p t).natDegree N) :=
          Submodule.finrank_mono hle
      _ ≤ (p t).natDegree * Module.finrank ℂ N := hK.2
      _ ≤ _ := Nat.mul_le_mul_left _ hrk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj
section
open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlobalTheory.Et.TrivTors

def sigmaFinSuccIso (V : Scheme.{0}) (k : ℕ) :
    (∐ fun _ : Fin (k + 1) => V) ≅ V ⨿ (∐ fun _ : Fin k => V) where
  hom := Sigma.desc (Fin.cases coprod.inl fun i => Sigma.ι (fun _ : Fin k => V) i ≫ coprod.inr)
  inv := coprod.desc (Sigma.ι (fun _ : Fin (k + 1) => V) 0)
    (Sigma.desc fun i => Sigma.ι (fun _ : Fin (k + 1) => V) i.succ)
  hom_inv_id := by
    ext i
    induction i using Fin.cases
    · simp only [Fin.cases_zero, Sigma.ι_comp_desc_assoc]
      exact coprod.inl_desc _ _
    · simp only [Fin.cases_succ, Sigma.ι_comp_desc_assoc, Category.assoc, Category.comp_id]
      erw [coprod.inr_desc, Sigma.ι_comp_desc]
  inv_hom_id := by
    apply coprod.hom_ext
    · erw [coprod.inl_desc_assoc, Sigma.ι_comp_desc]
      simp
    · erw [coprod.inr_desc_assoc]
      ext i
      simp

theorem sigmaFinSuccIso_hom_desc (V : Scheme.{0}) (k : ℕ) :
    (sigmaFinSuccIso V k).hom ≫ coprod.desc (𝟙 V) (Sigma.desc fun _ : Fin k => 𝟙 V) =
      Sigma.desc fun _ : Fin (k + 1) => 𝟙 V := by
  ext i
  induction i using Fin.cases
  · simp only [sigmaFinSuccIso, Sigma.ι_comp_desc_assoc, Fin.cases_zero, Sigma.ι_comp_desc]
    exact coprod.inl_desc _ _
  · simp only [sigmaFinSuccIso, Sigma.ι_comp_desc_assoc, Fin.cases_succ, Sigma.ι_comp_desc,
      Category.assoc]
    erw [coprod.inr_desc, Sigma.ι_comp_desc]

theorem isFinite_sigmaDesc_fin (V : Scheme.{0}) : ∀ k : ℕ, IsFinite (Sigma.desc fun _ : Fin k => 𝟙 V)
  | 0 => by
    have : IsEmpty (∐ fun _ : Fin 0 => V : Scheme.{0}) := by
      exact ⟨fun x => ((sigmaMk fun _ : Fin 0 => V).symm x).1.elim0⟩
    exact ((IsClosedImmersion.iff_isFinite_and_mono _).mp (by infer_instance)).1
  | k + 1 => by
    have := isFinite_sigmaDesc_fin V k
    rw [← sigmaFinSuccIso_hom_desc]
    infer_instance

end GlobalTheory.Et.TrivTors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfSurjectiveTensorSemilinear
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem finite_of_surjective_tensor_semilinear : ∀ (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (O : Type) [CommRing O] (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], Module.Finite Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → Module.Finite (k ⊗[ℤ] O) N := by
  intro Λ _ k _ π O _ M _ _ _ _ hM N _ _ f hf
  classical
  obtain ⟨s, hs⟩ := hM.fg_top
  refine ⟨⟨s.image f, ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro n -
  obtain ⟨m, rfl⟩ := hf n
  have hm : m ∈ Submodule.span Λ (s : Set M) := hs ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have h : a • x = (algebraMap Λ (Λ ⊗[ℤ] O) a) • x := (algebraMap_smul (Λ ⊗[ℤ] O) a x).symm
    rw [h, LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory
end

