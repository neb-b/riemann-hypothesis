module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLevelDatumGroupMulPow
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

def levMat {g N : ℕ} (S : Finset (Fin N × Fin N)) (f : S → ZMod g) : Matrix (Fin N) (Fin N) (ZMod g) :=
  fun a b => if h : (a, b) ∈ S then f ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem levMat_det {g N : ℕ} (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) (f : S → ZMod g) :
    (levMat S f).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro a _
    have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
    simp [levMat, this]
  · intro a b hab
    have hab' : b < a := hab
    have : (a, b) ∉ S := fun h => lt_asymm hab' (hS _ h)
    simp [levMat, this, hab'.ne']

theorem card_up_supp (g : ℕ) [Fact g.Prime] (N : ℕ) (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} = g ^ S.card := by
  have e : {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} ≃ (S → ZMod g) :=
    { toFun := fun u p => u.1.val p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (levMat S f) (by rw [levMat_det S hS]; exact one_ne_zero), by
        refine ⟨fun a => ?_, fun a b hab h => ?_⟩
        · have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
          show levMat S f a a = 1
          simp [levMat, this]
        · show levMat S f a b = 0
          simp [levMat, h, hab]⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        ext a b
        show levMat S (fun p => u.1.val p.1.1 p.1.2) a b = u.1.val a b
        unfold levMat
        split_ifs with h1 h2
        · rfl
        · subst h2; exact (u.2.1 a).symm
        · exact (u.2.2 a b h2 h1).symm
      right_inv := fun f => by
        funext p
        show levMat S f p.1.1 p.1.2 = f p
        simp [levMat, p.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod]
  simp

theorem lev_card : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N,
    Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  intro g _ N L
  set U : Finset (Fin N × Fin N) := (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2) with hU
  set R : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun p => L.sharp = true ∧ L.s ≤ p.1 ∧ (p.1 : ℕ) < L.s + L.k ∧ (p.2 : ℕ) = L.s + L.k) with hR
  have hUc : U.card = N * (N - 1) / 2 := by
    rw [hU, Finset.card_product_filter_lt, Nat.choose_two_right]
    simp
  have hRU : R ⊆ U := by
    intro p hp
    simp only [hR, hU, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
    rw [Fin.lt_def]
    omega
  have hRc : R.card = if L.sharp = true then L.k else 0 := by
    split_ifs with h
    · have hk := L.hk
      symm
      rw [← Finset.card_range L.k]
      refine Finset.card_bij (fun i hi => (⟨L.s + i, by have := Finset.mem_range.1 hi; omega⟩, ⟨L.s + L.k, hk⟩)) ?_ ?_ ?_
      · intro i hi
        have := Finset.mem_range.1 hi
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h]
        exact ⟨by omega, by omega, trivial⟩
      · intro i hi j hj hij
        have := congrArg (fun p : Fin N × Fin N => (p.1 : ℕ)) hij
        simp only at this
        omega
      · intro p hp
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h] at hp
        refine ⟨p.1 - L.s, Finset.mem_range.2 (by omega), ?_⟩
        apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
    · simp [hR, h]
  have hM : ∀ u : GG g N, L.Mem u ↔
      ((∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ U \ R → u.val a b = 0) := by
    intro u
    simp only [Lev.Mem, IsUp, hU, hR, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, not_and, not_not]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun a b hab h => ?_⟩
      rcases lt_or_gt_of_ne hab with h' | h'
      · by_contra hne
        exact h h' (fun x1 x2 x3 x4 => hne (h3 x1 a b x2 x3 x4))
      · exact h2 a b h'
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun a b h => h2 a b h.ne' (fun h' => absurd h' (lt_asymm h))⟩, fun x1 a b x2 x3 x4 => ?_⟩
      refine h2 a b (fun h => ?_) (fun _ h => h x1 x2 x3 x4)
      subst h
      omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight hM), card_up_supp g N (U \ R) (fun p hp => by
    have := (Finset.mem_sdiff.1 hp).1
    exact (Finset.mem_filter.1 this).2), ← hRc, ← pow_add, Finset.card_sdiff_add_card_eq_card hRU, hUc]

end GlobalTheory.BadShare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPermExistsStableSubsetLe
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.StableSubset

open Finset Equiv

theorem mem_iff_of_map_eq {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : A.map σ.toEmbedding = A) (x : Fin N) : σ x ∈ A ↔ x ∈ A := by
  conv_lhs => rw [← h]
  exact Finset.mem_map' σ.toEmbedding

theorem map_eq_of_mem_iff {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : ∀ x, x ∈ A → σ x ∈ A) : A.map σ.toEmbedding = A := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    exact h x hx
  · simp

theorem card_stab_le {N : ℕ} (A : Finset (Fin N)) :
    (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card ≤
      A.card.factorial * (N - A.card).factorial := by
  have hsub : (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A) ⊆
      (univ : Finset (Perm {x // x ∈ A} × Perm {x // x ∉ A})).image
        (fun p => Perm.subtypeCongr p.1 p.2) := by
    intro σ hσ
    have h := mem_iff_of_map_eq σ A (Finset.mem_filter.1 hσ).2
    refine Finset.mem_image.2 ⟨(σ.subtypePerm h, σ.subtypePerm (fun x => not_congr (h x))),
      Finset.mem_univ _, ?_⟩
    ext x
    by_cases hx : x ∈ A
    · simp [Perm.subtypeCongr.left_apply _ _ hx]
    · simp [Perm.subtypeCongr.right_apply _ _ hx]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Fintype.card_perm, Fintype.card_subtype_compl]

theorem card_fix_ge {N : ℕ} (A : Finset (Fin N)) (h0 : 0 < A.card) (hN : A.card < N) :
    A.card.factorial * (N - A.card).factorial ≤
      4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧
        (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card := by
  have c1 : Fintype.card {x // x ∈ A} = A.card := by simp
  have c2 : Fintype.card {x // x ∉ A} = N - A.card := by simp [Fintype.card_subtype_compl]
  have h1 := _root_.GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed {x // x ∈ A} (Fintype.card_pos_iff.1 (by omega))
  have h2 := _root_.GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed {x // x ∉ A} (Fintype.card_pos_iff.1 (by omega))
  rw [c1] at h1
  rw [c2] at h2
  refine (Nat.mul_le_mul h1 h2).trans ?_
  rw [mul_mul_mul_comm, ← Finset.card_product]
  refine Nat.mul_le_mul le_rfl ?_
  refine Finset.card_le_card_of_injOn (fun p => Perm.subtypeCongr p.1 p.2) ?_ ?_
  · rintro ⟨e, f⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hp ⊢
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hp
    refine ⟨map_eq_of_mem_iff _ _ ?_, ⟨i, i.2, ?_⟩, ⟨j, j.2, ?_⟩⟩
    · intro x hx
      rw [Perm.subtypeCongr.left_apply _ _ hx]
      exact (e ⟨x, hx⟩).2
    · rw [Perm.subtypeCongr.left_apply_subtype, hi]
    · rw [Perm.subtypeCongr.right_apply_subtype, hj]
  · rintro ⟨e, f⟩ - ⟨e', f'⟩ - h
    have h' : Perm.subtypeCongr e f = Perm.subtypeCongr e' f' := h
    refine Prod.ext ?_ ?_
    · ext x : 2
      have := congrArg (fun s : Perm (Fin N) => s x) h'
      simpa only [Perm.subtypeCongr.left_apply_subtype] using this
    · ext x : 2
      have := congrArg (fun s : Perm (Fin N) => s x) h'
      simpa only [Perm.subtypeCongr.right_apply_subtype] using this

noncomputable def wt {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N)) : ℕ :=
  if A.map σ.toEmbedding = A then
    (if (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j then 4 else 8) else 0

theorem sum_wt_le {N : ℕ} (A : Finset (Fin N)) (h0 : 0 < A.card) (hN : A.card < N) :
    ∑ σ, wt A σ ≤ 7 * (A.card.factorial * (N - A.card).factorial) := by
  have h1 := card_stab_le A
  have h2 := card_fix_ge A h0 hN
  have h3 : ∑ σ, wt A σ + 4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧
        (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card =
      8 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold wt
    by_cases ha : A.map σ.toEmbedding = A <;>
      by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j <;> simp only [ha, hb] <;> simp
  omega

theorem four_le_wt {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N))
    (h : A.map σ.toEmbedding = A) : 4 ≤ wt A σ := by
  unfold wt
  rw [if_pos h]
  split_ifs <;> omega

theorem eight_le_sum_wt {N a : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N)) (hA : A.card = a)
    (h : A.map σ.toEmbedding = A) : 8 ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
  have hAm : A ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hA]
  by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j
  · obtain ⟨⟨i, hi, hσi⟩, ⟨j, hj, hσj⟩⟩ := hb
    set B := insert j (A.erase i) with hB
    have hjB : j ∈ B := Finset.mem_insert_self _ _
    have hne : A ≠ B := fun e => hj (e ▸ hjB)
    have hBc : B.card = a := by
      rw [hB, Finset.card_insert_of_notMem (fun hh => hj (Finset.mem_of_mem_erase hh)),
        Finset.card_erase_add_one hi, hA]
    have hBm : B ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hBc]
    have hBs : B.map σ.toEmbedding = B := by
      apply map_eq_of_mem_iff
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [hσj]; exact hjB
      · refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, ?_⟩)
        · intro e
          exact (Finset.mem_erase.1 hx).1 (σ.injective (e.trans hσi.symm))
        · exact (mem_iff_of_map_eq σ A h x).2 (Finset.mem_erase.1 hx).2
    have hs : ({A, B} : Finset _) ⊆ powersetCard a (univ : Finset (Fin N)) := by
      intro C hC
      rcases Finset.mem_insert.1 hC with rfl | hC
      · exact hAm
      · rw [Finset.mem_singleton.1 hC]; exact hBm
    have := Finset.sum_le_sum_of_subset (f := fun B => wt B σ) hs
    rw [Finset.sum_pair hne] at this
    have h1 := four_le_wt A σ h
    have h2 := four_le_wt B σ hBs
    omega
  · have : wt A σ = 8 := by unfold wt; rw [if_pos h, if_neg hb]
    rw [← this]
    exact Finset.single_le_sum (f := fun B => wt B σ) (fun _ _ => Nat.zero_le _) hAm

theorem card_exists_stable_subset_le : ∀ N a : ℕ, 0 < a → a < N →
    8 * (Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A).card ≤ 7 * N.factorial := by
  intro N a h0 hN
  calc _ ≤ ∑ σ : Perm (Fin N), ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
        rw [Finset.card_filter, Finset.mul_sum]
        refine Finset.sum_le_sum fun σ _ => ?_
        split_ifs with h
        · obtain ⟨A, hA, h⟩ := h
          exact eight_le_sum_wt σ A hA h
        · simp
    _ = ∑ B ∈ powersetCard a (univ : Finset (Fin N)), ∑ σ : Perm (Fin N), wt B σ :=
        Finset.sum_comm
    _ ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)),
          7 * (a.factorial * (N - a).factorial) := by
        refine Finset.sum_le_sum fun B hB => ?_
        have hB' : B.card = a := (Finset.mem_powersetCard.1 hB).2
        have := sum_wt_le B (by omega) (by omega)
        rwa [hB'] at this
    _ = 7 * N.factorial := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, ← Nat.choose_mul_factorial_mul_factorial hN.le]
        ring

end GlobalTheory.StableSubset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZero
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section AvgAux

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem avg_shift {K : Subgroup G} (M : Subgroup K) [M.Normal] [Fintype (K ⧸ M)]
    (π : Representation ℂ G V) (θ : G → ℂ) (s : K ⧸ M → K)
    (hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q) (hone : θ 1 = 1)
    (hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b)
    (w : V) (hw : ∀ m ∈ M, π (m : G) w = w) (hθM : ∀ m ∈ M, θ (m : G) = 1) (h : K) :
    ∑ q, (θ (s q))⁻¹ • π (s q) (π h w) = θ h • ∑ q, (θ (s q))⁻¹ • π (s q) w := by
  have hne : ∀ a : K, θ a ≠ 0 := by
    intro a ha
    have := hmul a a⁻¹
    rw [mul_inv_cancel, ha, zero_mul] at this
    simp [hone] at this
  have key : ∀ q : K ⧸ M, (θ (s q))⁻¹ • π (s q) (π h w) =
      θ h • ((θ (s (q * QuotientGroup.mk h)))⁻¹ • π (s (q * QuotientGroup.mk h)) w) := by
    intro q
    set q' := q * (QuotientGroup.mk h : K ⧸ M)
    set m : K := (s q')⁻¹ * (s q * h) with hm_def
    have hmM : m ∈ M := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [hm_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, q']
      group
    have hsplit : s q * h = s q' * m := by simp [hm_def]
    have h1 : π (s q) (π h w) = π (s q') w := by
      have : π ((s q * h : K) : G) w = π ((s q' * m : K) : G) w := by rw [hsplit]
      simpa [map_mul, hw m hmM] using this
    have h2 : θ (s q) * θ h = θ (s q') := by
      rw [← hmul, hsplit, hmul, hθM m hmM, mul_one]
    rw [h1, smul_smul]
    congr 1
    rw [← h2]
    field_simp [hne (s q), hne h]
  rw [Finset.sum_congr rfl fun q _ => key q, ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk h : K ⧸ M))
    (fun q => (θ (s q))⁻¹ • π (s q) w)

end AvgAux

theorem aug_avg_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    ∀ u ∈ aug π H θ, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧
      ∑ j ∈ R, (θ j)⁻¹ • π j u = 0 := by
  intro G V _ _ _ _ _ π hsm H θ hD u hu
  let K : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hu
  choose h hh w hw using fun i => (g i).2
  have hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b := fun a b => hD.val_mul a a.2 b b.2
  let N : Subgroup K :=
    { carrier := {j | θ j = 1 ∧ ∀ i, π j (w i) = w i}
      mul_mem' := by
        intro a b ha hb
        refine ⟨by rw [hmul, ha.1, hb.1, one_mul], fun i => ?_⟩
        simp [map_mul, ha.2 i, hb.2 i]
      one_mem' := ⟨hD.val_one, fun i => by simp⟩
      inv_mem' := by
        intro a ha
        refine ⟨?_, fun i => ?_⟩
        · have := hmul a a⁻¹
          rw [mul_inv_cancel, ha.1, one_mul] at this
          simpa [hD.val_one] using this.symm
        · have := congrArg (π ((a⁻¹ : K) : G)) (ha.2 i)
          simpa [← map_mul] using this.symm }
  have hNopen : IsOpen (N : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds
    obtain ⟨U, hU, hUθ⟩ := hD.near
    have hS : (U ∩ ⋂ i, {g : G | π g (w i) = w i}) ∈ nhds (1 : G) :=
      Filter.inter_mem hU (Filter.iInter_mem.mpr fun i => (hsm (w i)).mem_nhds (by simp))
    have hS' := continuous_subtype_val.continuousAt.preimage_mem_nhds (x := (1 : K)) hS
    refine Filter.mem_of_superset hS' ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
    exact ⟨hUθ x hx.1 x.2, hx.2⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (show IsCompact (K : Set G) from hD.compact)
  haveI : Finite (K ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNopen
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let M : Subgroup K := N.normalCore
  haveI : Finite (K ⧸ M) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ M) := Fintype.ofFinite _
  classical
  let s : K ⧸ M → K := fun q => if q = 1 then 1 else q.out
  have hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q := by
    intro q
    by_cases hq : q = 1
    · simp [s, hq]
    · simp [s, hq]
  have hMN : ∀ m ∈ M, m ∈ N := fun m hm => Subgroup.normalCore_le N hm
  have hinj : Function.Injective (fun q => ((s q : K) : G)) := by
    intro a b hab
    rw [← hs a, ← hs b, Subtype.ext hab]
  refine ⟨Finset.univ.image (fun q => ((s q : K) : G)), ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [s]⟩
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (s q).2
  · rw [Finset.sum_image fun a _ b _ hab => hinj hab]
    have hgen : ∀ i, ∑ q, (θ (s q))⁻¹ • π (s q) ((g i : V)) = 0 := by
      intro i
      rw [hw i]
      simp only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib]
      have := avg_shift M π θ s hs hD.val_one hmul (w i) (fun m hm => (hMN m hm).2 i)
        (fun m hm => (hMN m hm).1) ⟨h i, hh i⟩
      rw [this, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hc : ∀ q, (θ (s q : G))⁻¹ • c i • π (s q : G) (g i : V) =
        c i • ((θ (s q : G))⁻¹ • π (s q : G) (g i : V)) := fun q => smul_comm _ _ _
    simp only [hc, ← Finset.smul_sum, hgen i, smul_zero]

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfSlTwoIntInvariantBoundedUpperHalfPlane
section
open scoped MatrixGroups
open GlobalTheory.KZ

open UpperHalfPlane ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.KZ.LevelOne

theorem const_of_invariant_bounded :
    ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs → (∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) →
      (∃ M t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z‖ ≤ M) → ∃ c : ℂ, ∀ z ∈ Hs, φ z = c := by
  intro φ hd hinv hb
  let f : ℍ → ℂ := fun τ => φ τ
  have hfinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ := fun γ τ => by
    simp only [f]
    rw [← GlobalTheory.KZ.SiegelModel.mob_ofSL]
    exact hinv γ τ τ.2
  have hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f := by
    ext τ; simpa [SL_slash_apply] using hfinv γ τ
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine hd.congr fun z hz => ?_
    simp only [Function.comp_apply, f]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hbdd : IsBoundedAtImInfty f := by
    obtain ⟨M, t, h⟩ := hb
    refine isBoundedAtImInfty_iff.2 ⟨M, t + 1, fun τ hτ => ?_⟩
    exact h τ τ.2 (by rw [UpperHalfPlane.coe_im]; linarith [hτ])
  let F : ModularForm 𝒮ℒ 0 :=
    { toFun := f
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
      holo' := hholo
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hs γ]
        exact hbdd }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  refine ⟨c, fun z hz => ?_⟩
  have := congrFun hc ⟨z, hz⟩
  exact this

end GlobalTheory.KZ.LevelOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerCosetRepresentativeTraceEqOfLtOneStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_cosetRepresentativeTrace_eq_of_lt_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (U : Subgroup G) [Fintype (G ⧸ U)], AlmostSep v U → ∀ e : L, (∀ g : G, g • e = e) → v e < 1 → ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e := by
  first | exact @GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' | exact GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' | (intros; apply GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisationStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subring_no_monic_factorisation_specialisation : ∀ {F : Type} [Field F] [IsAlgClosed F] (Φ : Polynomial (Polynomial F)), Φ.Monic → Irreducible Φ → ∃ s : Finset F, ∃ Ψ : Polynomial (Polynomial (Subring.closure (s : Set F))), Ψ.map (Polynomial.mapRingHom (Subring.closure (s : Set F)).subtype) = Φ ∧ ∀ (k : Type) [Field k] (φ : Subring.closure (s : Set F) →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
  first | exact @GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | exact GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | (intros; apply GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation <;> assumption)
end

