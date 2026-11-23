module

public import Mathlib

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqOfCover
section
namespace Formalism.HermitianLattices.Ext.L3.LIOrb

open Subgroup

variable {G : Type*} [Group G]

private theorem ncard_orbit_in_stabilizer_eq_relIndex {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  have h1 : MulAction.stabilizer (MulAction.stabilizer G y) t =
      (MulAction.stabilizer G t).subgroupOf (MulAction.stabilizer G y) := by
    ext g
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have h2 : MulAction.orbit (MulAction.stabilizer G y) t = {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [Subgroup.relIndex, ← h1, MulAction.index_stabilizer, h2]

theorem relIndex_eq_of_cover (S C H' : Subgroup G) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) : C.relIndex S = C.relIndex H' := by
  have hS := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ S)
  have hH := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ H')
  rw [MulAction.stabilizer_quotient, MulAction.stabilizer_quotient] at hS hH
  rw [← hS, ← hH]
  have hmem : ∀ (K : Subgroup G) (g : G), g • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ g ∈ K :=
    fun K g => by rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, hmem]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, ht, htg⟩ := h2 g hg
    refine ⟨t⁻¹, H'.inv_mem ht, ?_⟩
    rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using htg
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, h1 hg, rfl⟩

theorem index_tube (H S C H' : Subgroup G) (hS : S ≤ H) (hC : C ≤ H) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) :
    S.relIndex H * C.relIndex H' = C.relIndex H * S.relIndex C := by
  rw [← relIndex_eq_of_cover S C H' h1 h2, ← inf_relIndex_right C S, ← inf_relIndex_right S C, mul_comm,
    relIndex_mul_relIndex _ _ _ inf_le_right hS, mul_comm, relIndex_mul_relIndex _ _ _ inf_le_right hC, inf_comm]

theorem relIndex_cocycle (A B C : Subgroup G) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hCB : B.relIndex C ≠ 0) :
    B.relIndex A * C.relIndex B * A.relIndex C = A.relIndex B * B.relIndex C * C.relIndex A := by
  have hBA' : B.relIndex A ≠ 0 := relIndex_ne_zero_trans hCB hAC
  have hAC' : A.relIndex C ≠ 0 := relIndex_ne_zero_trans hBA hCB
  have orbitMap_conj_smul_one := relIndex_inf_mul_relIndex C B A
  have orbitMap_conj_smul_two := relIndex_inf_mul_relIndex B C A
  have eB1 := relIndex_inf_mul_relIndex A C B
  have eB2 := relIndex_inf_mul_relIndex C A B
  have eC1 := relIndex_inf_mul_relIndex B A C
  have eC2 := relIndex_inf_mul_relIndex A B C
  have EA : C.relIndex (A ⊓ B) * B.relIndex A = B.relIndex (A ⊓ C) * C.relIndex A := by
    rw [inf_comm A B, inf_comm A C, orbitMap_conj_smul_one, orbitMap_conj_smul_two, inf_comm]
  have EB : A.relIndex (B ⊓ C) * C.relIndex B = C.relIndex (A ⊓ B) * A.relIndex B := by
    rw [inf_comm B C, eB1, eB2, inf_comm]
  have EC : B.relIndex (A ⊓ C) * A.relIndex C = A.relIndex (B ⊓ C) * B.relIndex C := by
    rw [eC1, eC2, inf_comm]
  have hu : C.relIndex (A ⊓ B) ≠ 0 := by
    rw [inf_comm]
    exact left_ne_zero_of_mul (by rw [orbitMap_conj_smul_one]; exact relIndex_inf_ne_zero hAC hBA')
  have hv : B.relIndex (A ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC1]; exact relIndex_inf_ne_zero hCB hAC')
  have hw : A.relIndex (B ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC2]; exact relIndex_inf_ne_zero hAC' hCB)
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hu hv) hw))
  calc C.relIndex (A ⊓ B) * B.relIndex (A ⊓ C) * A.relIndex (B ⊓ C) *
        (B.relIndex A * C.relIndex B * A.relIndex C)
      = (C.relIndex (A ⊓ B) * B.relIndex A) * (A.relIndex (B ⊓ C) * C.relIndex B) *
          (B.relIndex (A ⊓ C) * A.relIndex C) := by ring
    _ = (B.relIndex (A ⊓ C) * C.relIndex A) * (C.relIndex (A ⊓ B) * A.relIndex B) *
          (A.relIndex (B ⊓ C) * B.relIndex C) := by rw [EA, EB, EC]
    _ = _ := by ring

theorem ncard_biUnion_finset {ι X : Type*} (s : Finset ι) (f : ι → Set X)
    (hf : ∀ i ∈ s, (f i).Finite) (hd : (s : Set ι).PairwiseDisjoint f) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  revert hf hd
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih hf hd
  have hfa : (f a).Finite := hf a (Finset.mem_insert_self a s)
  have hfs : (⋃ i ∈ s, f i).Finite :=
    Set.Finite.biUnion s.finite_toSet fun i hi => hf i (Finset.mem_insert_of_mem hi)
  have hdisj : Disjoint (f a) (⋃ i ∈ s, f i) := by
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
  rw [Finset.set_biUnion_insert, Finset.sum_insert ha, Set.ncard_union_eq hdisj hfa hfs,
    ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (hd.subset (Finset.coe_subset.2 (Finset.subset_insert a s)))]

theorem ncard_orb {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  exact ncard_orbit_in_stabilizer_eq_relIndex t y

theorem sum_relIndex_fibre {X Y : Type*} [MulAction G X] [MulAction G Y] (π : X → Y)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ x ∈ sX, x ∈ A ∧ π x ∈ sY)
    (hX : ∀ x ∈ A, ∃! t, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ sY, ∀ y' ∈ sY, (∃ g : G, g • y = y') → y = y')
    (hfin : ∀ x ∈ sX, (MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) ≠ 0)
    (w : Y → ℝ) :
    ∑ x ∈ sX, ((MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) : ℝ) * w (π x) =
      ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y := by
  classical
  have hcard : ∀ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) =
      ∑ t ∈ sX.filter (fun t => π t = y),
        ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) := by
    intro y hy
    have hfib : {x | x ∈ A ∧ π x = y} =
        ⋃ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · rintro ⟨hxA, hxy⟩
        obtain ⟨t, ⟨ht, g, hgt⟩, -⟩ := hX x hxA
        have h1 : π t = y := hY (π t) (hsX t ht).2 y hy ⟨g, by rw [← hπ, hgt, hxy]⟩
        refine ⟨t, ⟨ht, h1⟩, g, ?_, hgt⟩
        rw [← h1, ← hπ, hgt, hxy, h1]
      · rintro ⟨t, ⟨ht, h1⟩, g, hg, rfl⟩
        refine ⟨hA g t (hsX t ht).1, ?_⟩
        rw [hπ, h1, hg]
    have hfin' : ∀ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x}.Finite := by
      intro t ht
      rw [Finset.mem_filter] at ht
      apply Set.finite_of_ncard_ne_zero
      rw [ncard_orb, ← ht.2]
      exact hfin t ht.1
    have hdisj : (↑(sX.filter (fun t => π t = y)) : Set X).PairwiseDisjoint
        (fun t => {x : X | ∃ g : G, g • y = y ∧ g • t = x}) := by
      intro t ht t' ht' hne
      refine Set.disjoint_left.2 ?_
      rintro x ⟨g, -, rfl⟩ ⟨g', -, hg'⟩
      rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
      obtain ⟨t0, -, huniq⟩ := hX (g • t) (hA g t (hsX t ht.1).1)
      exact hne ((huniq t ⟨ht.1, g, rfl⟩).trans (huniq t' ⟨ht'.1, g', hg'⟩).symm)
    have hnc : Nat.card {x // x ∈ A ∧ π x = y} = ({x | x ∈ A ∧ π x = y} : Set X).ncard :=
      by exact (Set.ncard_ofPred _).symm
    rw [hnc, hfib, ncard_biUnion_finset _ _ hfin' hdisj]
    push_cast
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_filter] at ht
    rw [ncard_orb, ht.2]
  symm
  calc ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y
      = ∑ y ∈ sY, ∑ t ∈ sX.filter (fun t => π t = y),
          ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) * w (π t) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hcard y hy, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [(Finset.mem_filter.1 ht).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun t ht => (hsX t ht).2) _

end Formalism.HermitianLattices.Ext.L3.LIOrb
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SummableSqGeom
section
open Filter Topology Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {ι : Type*}

def ebox (s : Finset ι) (J : ι → ℕ) : Finset (ι →₀ ℕ) := s.finsupp fun i => range (J i + 1)

theorem mem_ebox {s : Finset ι} {J : ι → ℕ} {v : ι →₀ ℕ} :
    v ∈ ebox s J ↔ v.support ⊆ s ∧ ∀ i ∈ s, v i ≤ J i := by
  classical
  simp [ebox, Finset.mem_finsupp_iff, Nat.lt_succ_iff]

theorem sum_ebox (f : ι → ℕ → ℝ) (hf : ∀ i, f i 0 = 1) (s : Finset ι) (J : ι → ℕ) :
    ∑ v ∈ ebox s J, v.prod f = ∏ i ∈ s, ∑ j ∈ range (J i + 1), f i j := by
  classical
  rw [Finset.prod_sum, ebox, Finset.finsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Finsupp.prod_of_support_subset _ (Finsupp.support_indicator_subset s g) _ (fun i _ => hf i),
    ← Finset.prod_attach s]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.indicator_apply, dite_eq_left i.2]

theorem mem_ebox_support {v w : ι →₀ ℕ} : v ∈ ebox w.support w ↔ v ≤ w := by
  rw [mem_ebox, Finsupp.le_def]
  constructor
  · rintro ⟨hs, hle⟩ i
    by_cases hi : i ∈ w.support
    · exact hle i hi
    · have h0 : v i = 0 := by
        by_contra h
        exact hi (hs (Finsupp.mem_support_iff.mpr h))
      rw [h0]
      exact Nat.zero_le _
  · intro h
    refine ⟨fun i hi => ?_, fun i _ => h i⟩
    rw [Finsupp.mem_support_iff] at hi ⊢
    have := h i
    omega

def dif (R : ι → ℕ → ℝ) (i : ι) : ℕ → ℝ
  | 0 => 1
  | j + 1 => R i (j + 1) - R i j

theorem sum_dif (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), dif R i j = R i J := by
  induction J with
  | zero => simp [dif, hR]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    simp [dif]

theorem prod_eq_sum_dif (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (w : ι →₀ ℕ) :
    w.prod R = ∑ v ∈ ebox w.support w, v.prod (dif R) := by
  rw [sum_ebox (dif R) (fun i => rfl) w.support w, Finsupp.prod]
  exact Finset.prod_congr rfl fun i _ => (sum_dif R hR i (w i)).symm

theorem summable_prod {u : ι → ℕ → ℝ} (hu0 : ∀ i, u i 0 = 1) (hu : ∀ i j, 0 ≤ u i j) {t : ι → ℝ}
    (ht : Summable t) (hut : ∀ i J, ∑ j ∈ range (J + 1), u i j ≤ 1 + t i) :
    Summable fun v : ι →₀ ℕ => v.prod u := by
  classical
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i
    have h := hut i 0
    simp [hu0] at h
    linarith
  apply summable_of_sum_le (c := Real.exp (∑' i, t i)) (fun v => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
  intro F
  have hsub : F ⊆ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i) := by
    intro v hv
    rw [mem_ebox]
    exact ⟨fun i hi => Finset.mem_biUnion.mpr ⟨v, hv, hi⟩,
      fun i _ => Finset.le_sup (f := fun v : ι →₀ ℕ => v i) hv⟩
  calc ∑ v ∈ F, v.prod u
      ≤ ∑ v ∈ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i), v.prod u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun v _ _ => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
    _ = ∏ i ∈ F.biUnion (fun v => v.support), ∑ j ∈ range ((F.sup fun v => v i) + 1), u i j :=
        sum_ebox u hu0 _ _
    _ ≤ ∏ i ∈ F.biUnion (fun v => v.support), Real.exp (t i) := by
        apply Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => hu i j)
        intro i _
        calc _ ≤ 1 + t i := hut i _
          _ ≤ Real.exp (t i) := by linarith [Real.add_one_le_exp (t i)]
    _ = Real.exp (∑ i ∈ F.biUnion (fun v => v.support), t i) := (Real.exp_sum _ t).symm
    _ ≤ Real.exp (∑' i, t i) := Real.exp_le_exp.mpr (ht.sum_le_tsum _ (fun i _ => ht0 i))

theorem summable_sq_geom : Summable fun j : ℕ => 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by
  have h0 := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  refine (((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).mul_left 8).congr fun j => ?_
  first
    | ring
    | (simp only [Pi.add_apply]; ring)
    | (simp; ring)

def cGeom : ℝ := ∑' j : ℕ, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j

variable {q : ι → ℝ}

def nrm (q : ι → ℝ) (v : ι →₀ ℕ) : ℝ := v.prod fun i e => q i ^ e

theorem nrm_pos (hq : ∀ i, 2 ≤ q i) (v : ι →₀ ℕ) : 0 < nrm q v := by
  unfold nrm Finsupp.prod
  exact Finset.prod_pos fun i _ => pow_pos (by linarith [hq i]) _

theorem abs_div_nrm (f : ι → ℕ → ℝ) (v : ι →₀ ℕ) :
    |v.prod f| / nrm q v = v.prod fun i e => |f i e| / q i ^ e := by
  unfold nrm Finsupp.prod
  rw [Finset.abs_prod, ← Finset.prod_div_distrib]

theorem sum_dif_le (hq : ∀ i, 2 ≤ q i) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), |dif R i j| / q i ^ j ≤ 1 + cGeom * (q i ^ 2)⁻¹ := by
  have hq0 : 0 < q i := by linarith [hq i]
  rw [Finset.sum_range_succ']
  simp only [dif, pow_zero, div_one, abs_one]
  rw [add_comm]
  refine add_le_add le_rfl ?_
  have hterm : ∀ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1) ≤
      (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) := by
    intro j _
    have hqj : 0 < q i ^ (j + 1) := pow_pos hq0 _
    have hqne : q i ≠ 0 := hq0.ne'
    rw [div_le_iff₀ hqj]
    have hx : 1 ≤ (q i / 2) ^ j := one_le_pow₀ (by linarith [hq i])
    have hc : 0 ≤ 8 * ((j : ℝ) + 2) ^ 2 := by positivity
    have e : (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1) =
        8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
      have h2 : (q i ^ 2)⁻¹ * q i ^ (j + 1) = q i ^ j / q i := by
        rw [pow_succ (q i) j, sq]
        first
          | (field_simp; ring)
          | field_simp
      calc (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1)
          = 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j * ((q i ^ 2)⁻¹ * q i ^ (j + 1)) := by ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * ((1 / 2 : ℝ) ^ j * q i ^ j) / q i := by rw [h2]; ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by rw [← mul_pow]; ring_nf
    rw [e]
    calc |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i := hRb i j
      _ ≤ 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
        first
          | exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hc hx) hq0.le
          | exact (div_le_div_iff_of_pos_right hq0).mpr (le_mul_of_one_le_right hc hx)
          | exact (div_le_div_right hq0).mpr (le_mul_of_one_le_right hc hx)
  calc ∑ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1)
      ≤ ∑ j ∈ range J, (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) :=
        Finset.sum_le_sum hterm
    _ = (q i ^ 2)⁻¹ * ∑ j ∈ range J, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ (q i ^ 2)⁻¹ * cGeom := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact summable_sq_geom.sum_le_tsum _ (fun j _ => by positivity)
    _ = cGeom * (q i ^ 2)⁻¹ := mul_comm _ _

theorem summable_dif (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) :
    Summable fun v : ι →₀ ℕ => |v.prod (dif R)| / nrm q v := by
  have h := summable_prod (u := fun i e => |dif R i e| / q i ^ e) (fun i => by simp [dif])
    (fun i j => div_nonneg (abs_nonneg _) (pow_nonneg (by linarith [hq i]) _))
    (hsum.mul_left cGeom) (fun i J => sum_dif_le hq hRb i J)
  exact h.congr fun v => (abs_div_nrm (dif R) v).symm

end Formalism.HermitianLattices.Ext.L3.A5
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoTsumDivPow
section
open Module MeasureTheory Filter Topology Bornology Pointwise ZLattice

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LatSum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι]

theorem map_equivFun (μ : Measure E) [μ.IsAddHaarMeasure] (b : Basis ι ℤ L) :
    μ.map (b.ofZLatticeBasis ℝ L).equivFunL = ENNReal.ofReal (covolume L μ) • volume := by
  classical
  set e := (b.ofZLatticeBasis ℝ L).equivFunL with he
  have h := Measure.addHaarMeasure_unique (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι)
  rw [addHaarMeasure_eq_volume_pi] at h
  have hF := ZLattice.isAddFundamentalDomain b μ
  have hc : (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι) = ENNReal.ofReal (covolume L μ) := by
    have h1 : (μ.map e) (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) =
        (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι) := by
      conv_lhs => rw [h]
      rw [Measure.smul_apply, Real.volume_pi_Ico]
      simp
    rw [← h1, Measure.map_apply e.continuous.measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico),
      covolume_eq_measure_fundamentalDomain L μ hF, measureReal_def,
      ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]
    congr 1
    ext x
    simp [ZSpan.mem_fundamentalDomain, Set.mem_pi, he]
  rw [h, hc]

theorem tendsto_tsum_div_pow (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : μ (frontier s) = 0) {G : E → ℝ} (hG : Continuous G) :
    Tendsto (fun n : ℕ ↦ (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (L : Set E)), G x) / (n : ℝ) ^ finrank ℝ E)
      atTop (𝓝 ((∫ x in s, G x ∂μ) / covolume L μ)) := by
  classical

  let b := Module.Free.chooseBasis ℤ L
  let e := (b.ofZLatticeBasis ℝ L).equivFunL
  let eM := e.toHomeomorph.toMeasurableEquiv
  have heM : ∀ x, eM x = e x := fun _ => rfl
  have hcov : 0 < covolume L μ := ZLattice.covolume_pos L μ
  have hne : ENNReal.ofReal (covolume L μ) ≠ 0 := by simpa using hcov
  have hmap : μ.map eM = ENNReal.ofReal (covolume L μ) • volume := map_equivFun L μ b
  have hL : e '' (L : Set E) =
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
        Set (Module.Free.ChooseBasisIndex ℤ L → ℝ)) := by
    have hspan := b.ofZLatticeBasis_span ℝ L
    have hstep : e '' (L : Set E) = e '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E) := by
      rw [hspan]
    rw [hstep]
    have hm := Submodule.map_coe (e.toLinearEquiv.toLinearMap.restrictScalars ℤ)
      (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)))
    rw [Submodule.map_span] at hm
    rw [show e '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E) =
      ((e.toLinearEquiv.toLinearMap.restrictScalars ℤ) '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E))
      from rfl, ← hm, ← Set.range_comp]
    have hfun : ⇑(e.toLinearEquiv.toLinearMap.restrictScalars ℤ) ∘ ⇑(b.ofZLatticeBasis ℝ L) =
        ⇑(Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L)) := by
      funext i
      ext j
      by_cases h : j = i
      · subst h
        simp [e]
      · simp [e, h, Ne.symm h]
    rw [hfun]
  have himg : ∀ n : ℕ, e '' (s ∩ (n : ℝ)⁻¹ • (L : Set E)) =
      e '' s ∩ (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
        Set (Module.Free.ChooseBasisIndex ℤ L → ℝ)) := by
    intro n
    rw [Set.image_inter e.injective, ← hL]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨e a, ⟨a, ha, rfl⟩, (e.map_smul _ a).symm⟩
    · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_ • a, ⟨a, ha, rfl⟩, e.map_smul _ a⟩
  have hsum : ∀ n : ℕ, (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (L : Set E)), G x) =
      ∑' y : ↑(e '' s ∩ (n : ℝ)⁻¹ • (Submodule.span ℤ
        (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
          Set (Module.Free.ChooseBasisIndex ℤ L → ℝ))), G (e.symm y) := by
    intro n
    rw [← himg n, tsum_image (fun y => G (e.symm y)) e.injective.injOn]
    simp
  have hdim : finrank ℝ E = Fintype.card (Module.Free.ChooseBasisIndex ℤ L) := by
    rw [← ZLattice.rank ℝ L]
    exact Module.finrank_eq_card_chooseBasisIndex ℤ L
  have hpre : eM ⁻¹' (e '' s) = s := Set.preimage_image_eq s e.injective
  have hint : (∫ y in e '' s, G (e.symm y)) = (∫ x in s, G x ∂μ) / covolume L μ := by
    have h1 := setIntegral_map_equiv (μ := μ) eM (fun y => G (e.symm y)) (e '' s)
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hcov.le] at h1
    simp only [heM, ContinuousLinearEquiv.symm_apply_apply] at h1
    rw [← h1, smul_eq_mul, mul_div_cancel_left₀ _ hcov.ne']
  have hfr : volume (frontier (e '' s)) = 0 := by
    have h2 := MeasurableEquiv.map_apply (μ := μ) eM (frontier (e '' s))
    have h3 : eM ⁻¹' frontier (e '' s) = frontier s := by
      have hfe : frontier (e '' s) = e '' frontier s := (e.toHomeomorph.image_frontier s).symm
      rw [hfe]
      exact Set.preimage_image_eq _ e.injective
    rw [h3, hs₃, hmap, Measure.smul_apply, smul_eq_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left hne
  have hlim := tendsto_tsum_div_pow_atTop_integral (e '' s) (fun y => G (e.symm y))
    (hG.comp e.symm.continuous) (e.lipschitzWith.isBounded_image hs₁)
    (eM.measurableSet_image.2 hs₂) hfr
  rw [hint] at hlim
  refine hlim.congr fun n => ?_
  rw [hsum n, hdim]

end Formalism.HermitianLattices.Ext.L3.LatSum
end
end

