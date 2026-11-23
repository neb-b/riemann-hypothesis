module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005

@[expose] public section

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair.Model

open GlobalTheory.LatPair

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

theorem isAdj_sumOp (S S' : Pair k n → Finset (Pair k n)) (w w' : Pair k n → Pair k n → ℂ)
    (hS : ∀ P Q, Q ∈ S P ↔ P ∈ S' Q) (hw : ∀ P Q, Q ∈ S P → w P Q = (starRingEnd ℂ) (w' Q P)) :
    IsAdj (sumOp S w) (sumOp S' w') := by
  classical
  intro φ φ' h h'
  unfold cntIp
  rw [finsum_eq_sum_of_support_subset (s := h'.toFinset) _ (fun P hP => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, map_eq_zero] at hP
      simpa using hP.2),
    finsum_eq_sum_of_support_subset (s := h.toFinset) _ (fun P hP => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hP
      simpa using hP.1)]
  have e1 : ∀ P, sumOp S w φ P = ∑ Q ∈ h.toFinset, if Q ∈ S P then w P Q * φ Q else 0 := fun P => by
    rw [sumOp_apply, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm
    have : φ Q = 0 := by simpa [hQ] using hQ'
    simp [this]
  have e2 : ∀ Q, sumOp S' w' φ' Q = ∑ P ∈ h'.toFinset, if P ∈ S' Q then w' Q P * φ' P else 0 := fun P => by
    rw [sumOp_apply, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm
    have : φ' Q = 0 := by simpa [hQ] using hQ'
    simp [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e1, e2, Finset.sum_mul, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun P _ => ?_
  by_cases hQ : Q ∈ S P
  · rw [if_pos hQ, if_pos ((hS P Q).1 hQ), hw P Q hQ, map_mul]
    ring
  · rw [if_neg hQ, if_neg (fun h => hQ ((hS P Q).2 h))]
    simp

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem sum_char {V : Type*} [AddCommGroup V] [Module 𝓀[k] V] [Fintype V] {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1)
    (g : Module.Dual 𝓀[k] V) [Decidable (g = 0)] : ∑ x, χ (g x) = if g = 0 then (Fintype.card V : ℂ) else 0 := by
  split_ifs with hg
  · simp [hg]
  · refine (AddChar.sum_eq_zero_iff_ne_zero (ψ := χ.compAddMonoidHom g.toAddMonoidHom)).2 fun h => hχ ?_
    ext a
    obtain ⟨x, rfl⟩ := LinearMap.surjective hg a
    exact DFunLike.congr_fun h x

theorem FFStar_FF [Fintype n] (q : Unif k) {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1) (φ : Form k n M) :
    FFStar q χ (FF q χ φ) = (SplitWeil.resCard k ^ Fintype.card n : ℂ) • φ - tr φ := by
  classical
  ext P
  obtain ⟨L, hL, f, rfl⟩ : ∃ (L : Submodule 𝒪[k] (n → k)) (_ : L.IsFullLattice k) (f : _), P = ofDual L f :=
    ⟨P.lat, P.isLat, _, P.ofDual_red.symm⟩
  letI := Fintype.ofFinite (Red L)
  letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
  have hc : (Fintype.card (Red L) : ℂ) = SplitWeil.resCard k ^ Fintype.card n := by
    rw [← Nat.card_eq_fintype_card, Red.card_eq]; push_cast; rfl
  simp only [FFStar_ofDual, FF_up, Finset.smul_sum, smul_smul, Pi.sub_apply, Pi.smul_apply, tr_apply, ofDual_lat,
    sum_withLat]
  rw [Finset.sum_comm]
  have key : ∀ g : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0},
      ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) * χ (g.1 x.1) =
        (if g = f then (Fintype.card (Red L) : ℂ) else 0) - 1 := fun g => by
    have h1 := sum_char hχ (g.1 - f.1)
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0] at h1
    simp only [map_zero, AddChar.map_zero_eq_one, sub_eq_zero, Subtype.val_inj] at h1
    rw [← h1, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul, LinearMap.sub_apply, neg_add_eq_sub]
  simp only [← Finset.sum_smul, key, sub_smul, one_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hc]

theorem sum_stable_eq_zero {φ : Form k n M} (h : φ ∈ Mram k n M) (s : Finset (Pair k n))
    (hs : ∀ (c : 𝓀[k]ˣ) P, c • P ∈ s ↔ P ∈ s) : ∑ P ∈ s, φ P = 0 := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have h1 : ∑ P ∈ s, ∑ c : 𝓀[k]ˣ, φ (c • P) = 0 := Finset.sum_eq_zero fun P _ => (mem_Mram φ).1 h P
  rw [Finset.sum_comm] at h1
  have h2 : ∀ c : 𝓀[k]ˣ, ∑ P ∈ s, φ (c • P) = ∑ P ∈ s, φ P := fun c =>
    Finset.sum_equiv (MulAction.toPerm c) (fun P => (hs c P).symm) fun _ _ => rfl
  simp only [h2, Finset.sum_const, Finset.card_univ] at h1
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

theorem tr_eq_zero {φ : Form k n M} (h : φ ∈ Mram k n M) : tr φ = 0 ∧ tr' φ = 0 :=
  ⟨funext fun P => (tr_apply φ P).trans (sum_stable_eq_zero h _ (by simp)),
    funext fun P => (tr'_apply φ P).trans (sum_stable_eq_zero h _ (by simp))⟩

end GlobalTheory.LatPair.Model
