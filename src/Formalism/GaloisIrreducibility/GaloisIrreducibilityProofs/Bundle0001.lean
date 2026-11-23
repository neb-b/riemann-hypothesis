module

public import Formalism.GaloisIrreducibility.Statement

@[expose] public section

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.AltNotSolvable
section
namespace Formalism.GaloisIrreducibility

theorem alternating_group_not_solvable : AltNotSolvable := by
  intro α _ _ h hA
  have hcard : 5 ≤ Cardinal.mk α := by
    rw [Cardinal.mk_fintype]
    exact_mod_cast h
  refine Equiv.Perm.not_isSolvable α hcard ?_
  exact Group.isSolvable_of_ker_le_range (alternatingGroup α).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact le_rfl)

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
section
namespace Formalism.GaloisIrreducibility
open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

@[simp] lemma zero_ne_succ' {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := ⟨fun h => Fin.succ_ne_zero k h.symm, fun h => h.elim⟩

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R] [IsLocalRing R]

end BorderedIndexCases

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OrbitSubSum
section
namespace Formalism.GaloisIrreducibility

open Classical

lemma orbit_iterate_mem {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O)
    {x : α} (hx : x ∈ O) : ∀ n : ℕ, f^[n] x ∈ O := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hO.1 _ ih

lemma orbit_image_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.image f = O := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hO.1 x hx
  · intro y hy
    obtain ⟨n, hn⟩ := hO.2 (f y) (hO.1 y hy) y hy
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'] at hn
    exact Finset.mem_image.mpr ⟨f^[n] y, orbit_iterate_mem hO hy n, hn⟩

lemma orbit_map_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.val.map f = O.val := by
  have hinj : Set.InjOn f O := by
    rw [← Finset.card_image_iff, orbit_image_eq hO]
  rw [← Finset.image_val_of_injOn hinj, orbit_image_eq hO]

lemma orbit_le {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) {M' : Multiset α}
    (hM : M'.map f = M') {x : α} (hxO : x ∈ O) (hxM : x ∈ M') : O.val ≤ M' := by
  rw [Multiset.le_iff_subset O.nodup]
  intro y hy
  obtain ⟨n, rfl⟩ := hO.2 x hxO y (Finset.mem_val.mp hy)
  clear hy
  induction n with
  | zero => simpa using hxM
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hM]
    exact Multiset.mem_map_of_mem f ih

theorem invariant_multiset_orbit_sum {α ι : Type} (f : α → α) (O : ι → Finset α) (I : Finset ι) :
    ∀ (M' : Multiset α), (∀ i ∈ I, IsOrbit f (O i)) → M' ≤ ∑ i ∈ I, (O i).val →
      M'.map f = M' → ∃ J ⊆ I, M'.card = ∑ i ∈ J, (O i).card := by
  induction I using Finset.strongInduction with
  | H I ih =>
  intro M' hO hle hM
  by_cases h0 : M' = 0
  · exact ⟨∅, Finset.empty_subset _, by simp [h0]⟩
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h0
  have hxs : x ∈ ∑ i ∈ I, (O i).val := Multiset.mem_of_le hle hx
  rw [Multiset.mem_sum] at hxs
  obtain ⟨i0, hi0, hxi⟩ := hxs
  have hle0 : (O i0).val ≤ M' := orbit_le (hO i0 hi0) hM (Finset.mem_val.mp hxi) hx
  obtain ⟨M'', rfl⟩ : ∃ M'', M' = (O i0).val + M'' :=
    ⟨M' - (O i0).val, (add_tsub_cancel_of_le hle0).symm⟩
  have hM'' : M''.map f = M'' := by
    rw [Multiset.map_add (f := _), orbit_map_eq (hO i0 hi0)] at hM
    exact add_left_cancel hM
  have hle'' : M'' ≤ ∑ i ∈ I.erase i0, (O i).val := by
    rw [← Finset.add_sum_erase I _ hi0] at hle
    exact (add_le_add_iff_left _).mp hle
  obtain ⟨J, hJ, hc⟩ := ih (I.erase i0) (Finset.erase_ssubset hi0) M''
    (fun i hi => hO i (Finset.mem_of_mem_erase hi)) hle'' hM''
  refine ⟨insert i0 J, Finset.insert_subset hi0 (hJ.trans (Finset.erase_subset _ _)), ?_⟩
  have hnot : i0 ∉ J := fun h => by simpa using hJ h
  rw [Finset.sum_insert hnot, Multiset.card_add, hc, Finset.card_val]

theorem orbit_subset_sum : OrbitSubSum := by
  intro α ι f O I M' hO hle hM
  exact invariant_multiset_orbit_sum f O I M' hO hle hM

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PermSubSumInv
section
namespace Formalism.GaloisIrreducibility

namespace SubsetSumInvariance

open Equiv Equiv.Perm Finset

variable {α : Type} [Fintype α] [DecidableEq α]

def orbs (σ : Perm α) : Finset (Finset α) :=
  (σ.cycleFactorsFinset.image support) ∪ ((univ \ σ.support).image fun y => {y})

lemma fixed_of_not_mem {σ : Perm α} {y : α} (h : y ∉ σ.support) : σ y = y := Perm.notMem_support.1 h

lemma orbs_stable {σ : Perm α} {O : Finset α} (hO : O ∈ orbs σ) : ∀ x ∈ O, σ x ∈ O := by
  intro x hx
  rcases Finset.mem_union.1 hO with h | h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    rw [← (Perm.mem_cycleFactorsFinset_iff.1 hc).2 x hx]
    exact Perm.apply_mem_support.2 hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_singleton] at hx ⊢
    subst hx
    exact fixed_of_not_mem (Finset.mem_sdiff.1 hy).2

lemma pow_stable {σ : Perm α} {A : Finset α} (hA : ∀ x ∈ A, σ x ∈ A) :
    ∀ m : ℕ, ∀ z ∈ A, (σ ^ m) z ∈ A := by
  intro m
  induction m with
  | zero => intro z hz; simpa using hz
  | succ m ih =>
    intro z hz
    rw [pow_succ', Perm.mul_apply]
    exact hA _ (ih z hz)

lemma orbs_sub {σ : Perm α} {A : Finset α} (hA : ∀ x ∈ A, σ x ∈ A) {O : Finset α}
    (hO : O ∈ orbs σ) {x : α} (hxO : x ∈ O) (hxA : x ∈ A) : O ⊆ A := by
  intro y hy
  rcases Finset.mem_union.1 hO with h | h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    have hcx : c = σ.cycleOf x := Perm.cycle_is_cycleOf hxO hc
    rw [hcx, Perm.mem_support_cycleOf_iff] at hy
    obtain ⟨i, hi⟩ := hy.1.exists_nat_pow_eq
    rw [← hi]
    exact pow_stable hA i x hxA
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_singleton] at hy hxO
    rw [hy, ← hxO]
    exact hxA

lemma orbs_eq {σ : Perm α} {O O' : Finset α} (hO : O ∈ orbs σ) (hO' : O' ∈ orbs σ) {x : α}
    (h1 : x ∈ O) (h2 : x ∈ O') : O = O' := by
  have key : ∀ {O O' : Finset α}, O ∈ orbs σ → O' ∈ orbs σ → x ∈ O → x ∈ O' → O ⊆ O' := by
    intro O O' hO hO' h1 h2
    exact orbs_sub (fun y hy => orbs_stable hO' y hy) hO h1 h2
  exact Finset.Subset.antisymm (key hO hO' h1 h2) (key hO' hO h2 h1)

lemma orbs_pd (σ : Perm α) : (orbs σ : Set (Finset α)).PairwiseDisjoint id := by
  intro O hO O' hO' hne
  rw [Function.onFun, id, id, Finset.disjoint_left]
  intro x h1 h2
  exact hne (orbs_eq hO hO' h1 h2)

lemma orbs_parts (σ : Perm α) : (orbs σ).val.map Finset.card = σ.partition.parts := by
  have hdisj : Disjoint (σ.cycleFactorsFinset.image support) ((univ \ σ.support).image fun y => {y}) := by
    rw [Finset.disjoint_left]
    intro O h1 h2
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h2
    have h2le := (Perm.mem_cycleFactorsFinset_iff.1 hc).1.two_le_card_support
    rw [← hy, Finset.card_singleton] at h2le
    omega
  have hinj1 : Set.InjOn support (σ.cycleFactorsFinset : Set (Perm α)) := by
    intro c hc c' hc' h
    obtain ⟨a, ha⟩ := (Perm.mem_cycleFactorsFinset_iff.1 hc).1.nonempty_support
    rw [Perm.cycle_is_cycleOf ha hc, Perm.cycle_is_cycleOf (h ▸ ha) hc']
  have hinj2 : Set.InjOn (fun y : α => ({y} : Finset α)) ((univ \ σ.support : Finset α) : Set α) := by
    intro y _ z _ h
    exact Finset.singleton_injective h
  rw [orbs, ← Finset.disjUnion_eq_union _ _ hdisj, Finset.disjUnion_val, Multiset.map_add (f := _),
    Finset.image_val_of_injOn hinj1, Finset.image_val_of_injOn hinj2, Multiset.map_map, Multiset.map_map,
    Perm.parts_partition, Perm.cycleType_def]
  congr 1
  have : (Finset.card ∘ fun y : α => ({y} : Finset α)) = fun _ => 1 := by
    funext y
    simp
  rw [this, Multiset.map_const', Finset.card_val, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ]

end SubsetSumInvariance

namespace SubsetSumInvariance

lemma exists_le_map {β γ : Type*} (f : β → γ) (m : Multiset β) :
    ∀ s : Multiset γ, s ≤ m.map f → ∃ t ≤ m, t.map f = s := by
  classical
  induction m using Multiset.induction_on with
  | empty =>
    intro s hs
    refine ⟨0, le_rfl, ?_⟩
    simp only [Multiset.map_zero, nonpos_iff_eq_zero] at hs ⊢
    exact hs.symm
  | cons b m ih =>
    intro s hs
    rw [Multiset.map_cons] at hs
    by_cases hb : f b ∈ s
    · have hle : s.erase (f b) ≤ m.map f := by
        have := Multiset.erase_le_erase (f b) hs
        rwa [Multiset.erase_cons_head] at this
      obtain ⟨t, ht, htf⟩ := ih _ hle
      refine ⟨b ::ₘ t, Multiset.cons_le_cons b ht, ?_⟩
      rw [Multiset.map_cons, htf, Multiset.cons_erase hb]
    · obtain ⟨t, ht, htf⟩ := ih s ((Multiset.le_cons_of_notMem hb).1 hs)
      exact ⟨t, ht.trans (Multiset.le_cons_self _ _), htf⟩

end SubsetSumInvariance

open SubsetSumInvariance in
theorem exists_invariant_of_isSubSum {α : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (a : ℕ)
    (h : IsSubSum σ.partition.parts a) : ∃ A : Finset α, (∀ x ∈ A, σ x ∈ A) ∧ A.card = a := by
  obtain ⟨s, hs, hsum⟩ := h
  rw [← orbs_parts] at hs
  obtain ⟨t, ht, htf⟩ := exists_le_map Finset.card _ s hs
  let T : Finset (Finset α) := ⟨t, Multiset.nodup_of_le ht (orbs σ).nodup⟩
  have hT : T ⊆ orbs σ := fun O hO => Multiset.subset_of_le ht hO
  refine ⟨T.biUnion id, ?_, ?_⟩
  · intro x hx
    obtain ⟨O, hO, hxO⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨O, hO, orbs_stable (hT hO) x hxO⟩
  · rw [Finset.card_biUnion (fun O hO O' hO' hne => orbs_pd σ (hT hO) (hT hO') hne),
      Finset.sum_eq_multiset_sum]
    change (t.map fun O => (id O).card).sum = a
    simpa [htf] using hsum

theorem permutation_subset_sum_invariant : PermSubSumInv := by
  intro α _ _ σ a h
  obtain ⟨A, hA, hcard⟩ := exists_invariant_of_isSubSum σ a h
  exact ⟨A, hA, hcard⟩

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PowerPCycle
section
namespace Formalism.GaloisIrreducibility

theorem power_of_p_cycle : PowerPCycle := by
  intro α _ _ σ p hp hmem hcard
  have hdvd : p ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hmem
  have hpos : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  refine ⟨orderOf σ / p, ?_⟩
  have hord : orderOf (σ ^ (orderOf σ / p)) = p := orderOf_pow_orderOf_div hpos hdvd
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ ^ (orderOf σ / p)) (by rw [hord]; exact hp)
  rw [hord] at hn
  have hsum : (σ ^ (orderOf σ / p)).support.card = (n + 1) * p := by
    rw [← Equiv.Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul]
  have hle : (σ ^ (orderOf σ / p)).support.card ≤ Fintype.card α := Finset.card_le_univ _
  have hn0 : n = 0 := by
    by_contra h
    have h2 : 2 * p ≤ (n + 1) * p := Nat.mul_le_mul_right p (by omega)
    have h3 : 2 * p ≤ Fintype.card α := h2.trans (hsum ▸ hle)
    omega
  subst hn0
  refine ⟨?_, by rw [hsum]; ring⟩
  rw [← Equiv.Perm.card_cycleType_eq_one, hn]
  simp

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PrimitiveOfPCycle
section
namespace Formalism.GaloisIrreducibility

open scoped Pointwise

theorem poc_powSmul_injective {M Y : Type*} [Group M] [MulAction M Y] (s : M) (p : ℕ) (hp : p.Prime)
    (hs : s ^ p = 1) (y : Y) (hy : s • y ≠ y) :
    ∀ i < p, ∀ j < p, s ^ i • y = s ^ j • y → i = j := by
  have key : ∀ d : ℕ, 0 < d → d < p → s ^ d • y ≠ y := by
    intro d hd0 hdp hd
    have hnd : ¬ p ∣ d := fun h => absurd (Nat.le_of_dvd hd0 h) (by omega)
    have hcop : Nat.Coprime d p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
    have h1 : s ^ d ∈ MulAction.stabilizer M y := MulAction.mem_stabilizer_iff.mpr hd
    have h2 : s ^ p ∈ MulAction.stabilizer M y := by rw [hs]; exact one_mem _
    have hb := Nat.gcd_eq_gcd_ab d p
    rw [hcop.gcd_eq_one] at hb
    have e : s = (s ^ d) ^ (Nat.gcdA d p) * (s ^ p) ^ (Nat.gcdB d p) := by
      rw [← zpow_natCast s d, ← zpow_natCast s p, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb,
        Nat.cast_one, zpow_one]
    have h3 : s ∈ MulAction.stabilizer M y := by
      rw [e]; exact mul_mem (zpow_mem h1 _) (zpow_mem h2 _)
    exact hy (MulAction.mem_stabilizer_iff.mp h3)
  have step : ∀ i j : ℕ, i < j → j < p → s ^ i • y = s ^ j • y → False := by
    intro i j hij hjp h
    apply key (j - i) (by omega) (by omega)
    have h' : s ^ i • (s ^ (j - i) • y) = s ^ i • y := by
      rw [smul_smul, ← pow_add, show i + (j - i) = j by omega]
      exact h.symm
    exact (smul_left_cancel_iff _).mp h'
  intro i hi j hj hij
  rcases lt_trichotomy i j with h | h | h
  · exact (step i j h hj hij).elim
  · exact h
  · exact (step j i h hi hij.symm).elim

theorem primitive_of_p_cycle : PrimitiveOfPCycle := by
  unfold PrimitiveOfPCycle
  intro α _ _ G σ p hp hσG hcyc hsupp hcard htr
  refine @MulAction.IsPreprimitive.mk _ _ _ htr ?_
  intro B hB
  by_contra hcon
  unfold MulAction.IsTrivialBlock at hcon
  rw [not_or] at hcon
  obtain ⟨hns, hnt⟩ := hcon
  obtain ⟨b, hb, c, hc, hbc⟩ : ∃ b ∈ B, ∃ c ∈ B, b ≠ c := by
    by_contra h
    push_neg at h
    exact hns (fun u hu v hv => h u hu v hv)
  obtain ⟨z, hz⟩ : ∃ z, z ∉ B := by
    by_contra h
    push_neg at h
    exact hnt (Set.eq_univ_of_forall h)
  have hσp : σ ^ p = 1 := by
    rw [← hsupp, ← hcyc.orderOf]; exact pow_orderOf_eq_one σ
  obtain ⟨x, hxs⟩ : σ.support.Nonempty := Finset.card_pos.mp (by rw [hsupp]; exact hp.pos)
  obtain ⟨s, hsσ⟩ : ∃ s : G, (s : Equiv.Perm α) = σ := ⟨⟨σ, hσG⟩, rfl⟩
  have hs : s ^ p = 1 := Subtype.ext (by simp [hsσ, hσp])
  have hx : s • x ≠ x := by
    rw [Subgroup.smul_def, hsσ, Equiv.Perm.smul_def]; exact Equiv.Perm.mem_support.mp hxs
  obtain ⟨g, hgb⟩ := MulAction.exists_smul_eq G b x
  set t : G := g⁻¹ * s * g with ht
  have htp : t ^ p = 1 := by
    have e : ∀ i : ℕ, t ^ i = g⁻¹ * s ^ i * g := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, ih, ht, pow_succ]; group
    rw [e, hs]; group
  have htb : t • b ≠ b := by
    intro h
    apply hx
    have h2 : g • (t • b) = g • b := by rw [h]
    rw [ht, mul_smul, mul_smul, smul_inv_smul, hgb] at h2
    exact h2
  have blk : ∀ g₁ g₂ : G, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B) := by
    intro g₁ g₂ hne
    rcases hB.smul_eq_or_disjoint (g₂⁻¹ * g₁) with h | h
    · exfalso; apply hne
      rw [mul_smul] at h
      calc g₁ • B = g₂ • (g₂⁻¹ • g₁ • B) := (smul_inv_smul g₂ _).symm
        _ = g₂ • B := by rw [h]
    · rw [Set.disjoint_left]
      intro a ha1 ha2
      rw [Set.mem_smul_set_iff_inv_smul_mem] at ha1 ha2
      have h3 : g₂⁻¹ • a ∈ (g₂⁻¹ * g₁) • B := by
        rw [Set.mem_smul_set_iff_inv_smul_mem, mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
        exact ha1
      exact Set.disjoint_left.mp h h3 ha2
  rcases hB.smul_eq_or_disjoint t with hE | hD
  · have hpow : ∀ i : ℕ, t ^ i • b ∈ B := by
      intro i
      induction i with
      | zero => simpa using hb
      | succ i ih =>
        rw [pow_succ', mul_smul, ← hE]
        exact Set.smul_mem_smul_set ih
    obtain ⟨h, hhb⟩ := MulAction.exists_smul_eq G b z
    have hne : h • B ≠ B := by
      intro e; apply hz; rw [← e, ← hhb]; exact Set.smul_mem_smul_set hb
    have hdis : Disjoint (h • B) B := by
      have h4 := blk h 1 (by rwa [one_smul])
      rwa [one_smul] at h4
    let f : Fin p ⊕ Fin p → α :=
      Sum.elim (fun i => t ^ (i : ℕ) • b) (fun i => h • (t ^ (i : ℕ) • b))
    have hf : Function.Injective f := by
      rintro (i | i) (j | j) hij
      · simp only [f, Sum.elim_inl] at hij
        exact congrArg Sum.inl (Fin.ext (poc_powSmul_injective t p hp htp b htb i i.2 j j.2 hij))
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact (Set.disjoint_left.mp hdis (Set.smul_mem_smul_set (hpow j))
          (by rw [← hij]; exact hpow i)).elim
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact (Set.disjoint_left.mp hdis (Set.smul_mem_smul_set (hpow i))
          (by rw [hij]; exact hpow j)).elim
      · simp only [f, Sum.elim_inr] at hij
        exact congrArg Sum.inr (Fin.ext (poc_powSmul_injective t p hp htp b htb i i.2 j j.2
          ((smul_left_cancel_iff h).mp hij)))
    have hcd := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_sum, Fintype.card_fin] at hcd
    omega
  · have htB : t • B ≠ B := by
      intro e; rw [e] at hD
      exact Set.disjoint_left.mp hD hb hb
    have hinj := poc_powSmul_injective t p hp htp B htB
    have key : ∀ i j : Fin p, ∀ u v : α, u ∈ B → v ∈ B → t ^ (i : ℕ) • u = t ^ (j : ℕ) • v → i = j := by
      intro i j u v hu hv e
      by_contra hij
      have hne : t ^ (i : ℕ) • B ≠ t ^ (j : ℕ) • B := fun h => hij (Fin.ext (hinj i i.2 j j.2 h))
      exact Set.disjoint_left.mp (blk _ _ hne) (Set.smul_mem_smul_set hu)
        (by rw [e]; exact Set.smul_mem_smul_set hv)
    let f : Fin p ⊕ Fin p → α := Sum.elim (fun i => t ^ (i : ℕ) • b) (fun i => t ^ (i : ℕ) • c)
    have hf : Function.Injective f := by
      rintro (i | i) (j | j) hij
      · simp only [f, Sum.elim_inl] at hij
        have := key i j b b hb hb hij; subst this; rfl
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        have := key i j b c hb hc hij; subst this
        exact absurd ((smul_left_cancel_iff _).mp hij) hbc
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        have := key i j c b hc hb hij; subst this
        exact absurd ((smul_left_cancel_iff _).mp hij).symm hbc
      · simp only [f, Sum.elim_inr] at hij
        have := key i j c c hc hc hij; subst this; rfl
    have hcd := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_sum, Fintype.card_fin] at hcd
    omega

end Formalism.GaloisIrreducibility
end

