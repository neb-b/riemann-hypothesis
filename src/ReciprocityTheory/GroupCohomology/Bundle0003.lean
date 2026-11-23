module

public import ReciprocityTheory.GroupCohomology.Bundle0002
public import Mathlib.Topology.Algebra.ClopenNhdofOne

@[expose] public section

-- bundled from ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
section
namespace ReciprocityTheory.Coh

universe u

namespace Cx

variable {R : Type u} [CommRing R] {A B C : Cx R}

theorem Hom.d_f_eq_zero (φ : Hom A B) {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    B.d n (φ.f n x) = 0 := by
  rw [← φ.comm, hx, map_zero]

theorem d_add_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x + y) = 0 := by
  rw [map_add (f := _), hx, hy, add_zero]

theorem d_sub_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x - y) = 0 := by
  rw [map_sub, hx, hy, sub_zero]

theorem d_smul_eq_zero {n : ℕ} (r : R) {x : A.X n} (hx : A.d n x = 0) : A.d n (r • x) = 0 := by
  rw [map_smul, hx, smul_zero]

@[elab_as_elim]
theorem H_ind {n : ℕ} {P : A.H n → Prop} (h : ∀ x hx, P (A.cls n x hx)) (c : A.H n) : P c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact h z.1 z.2

theorem exists_cls {n : ℕ} (c : A.H n) : ∃ x hx, c = A.cls n x hx := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨z.1, z.2, rfl⟩

@[simp] theorem cls_add {n : ℕ} (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx + A.cls n y hy = A.cls n (x + y) (d_add_eq_zero hx hy) := rfl

@[simp] theorem cls_smul {n : ℕ} (r : R) (x : A.X n) (hx : A.d n x = 0) :
    r • A.cls n x hx = A.cls n (r • x) (d_smul_eq_zero r hx) := rfl

theorem cls_eq_iff {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx = A.cls n y hy ↔ x - y ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.eq]
  exact Iff.rfl

@[simp] theorem cls_eq_zero_iff {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    A.cls n x hx = 0 ↔ x ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

theorem cls_congr {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) (h : x = y) :
    A.cls n x hx = A.cls n y hy := by
  subst h
  rfl

theorem mem_B_succ {n : ℕ} {x : A.X (n + 1)} : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x := by
  change x ∈ LinearMap.range (A.d n) ↔ _
  exact LinearMap.mem_range

@[simp] theorem Hom.H_cls (φ : Hom A B) {n : ℕ} (x : A.X n) (hx : A.d n x = 0) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (φ.d_f_eq_zero hx) := rfl

@[simp] theorem Hom.id_H (n : ℕ) : (Hom.id A).H n = LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rfl

end Cx


end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.SectionA
section
open Pointwise Set

namespace ReciprocityTheory.Coh.ContinuousSections

variable {G : Type*} [Group G]

def rel (K N : Subgroup G) [hN : N.Normal] : Setoid G where
  r x y := ∃ k ∈ K, ∃ n ∈ N, y = k * n * x
  iseqv := {
    refl := fun x => ⟨1, K.one_mem, 1, N.one_mem, by simp⟩
    symm := by
      rintro x y ⟨k, hk, n, hn, rfl⟩
      refine ⟨k⁻¹, K.inv_mem hk, k * n⁻¹ * k⁻¹, hN.conj_mem _ (N.inv_mem hn) k, by group⟩
    trans := by
      rintro x y z ⟨k, hk, n, hn, rfl⟩ ⟨k', hk', n', hn', rfl⟩
      refine ⟨k' * k, K.mul_mem hk' hk, k⁻¹ * n' * k * n, N.mul_mem ?_ hn, by group⟩
      simpa using hN.conj_mem n' hn' k⁻¹ }

noncomputable def rep (K N : Subgroup G) [N.Normal] (x : G) : G :=
  (Quotient.mk (rel K N) x).out

lemma rep_eq (K N : Subgroup G) [N.Normal] {x y : G} (h : (rel K N) x y) : rep K N x = rep K N y := by
  unfold rep
  rw [Quotient.sound (s := rel K N) h]

lemma rep_spec (K N : Subgroup G) [N.Normal] (x : G) : ∃ k ∈ K, ∃ n ∈ N, x = k * n * rep K N x := by
  exact Quotient.mk_out (s := rel K N) x

def tr (K N : Subgroup G) [N.Normal] : Set G := {y | y * (rep K N y)⁻¹ ∈ N}

lemma tr_coset (K N : Subgroup G) [N.Normal] {y z : G} (h : z * y⁻¹ ∈ N) :
    z ∈ tr K N ↔ y ∈ tr K N := by
  have hr : rep K N z = rep K N y :=
    (rep_eq K N ⟨1, K.one_mem, z * y⁻¹, h, by group⟩).symm
  show z * (rep K N z)⁻¹ ∈ N ↔ y * (rep K N y)⁻¹ ∈ N
  rw [hr, show z * (rep K N y)⁻¹ = z * y⁻¹ * (y * (rep K N y)⁻¹) by group]
  exact N.mul_mem_cancel_left h

variable [TopologicalSpace G] [IsTopologicalGroup G]

lemma tr_closed (K N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) : IsClosed (tr K N) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  refine ⟨(fun z => z * y⁻¹) ⁻¹' (N : Set G), fun z hz hzt => hy ((tr_coset K N hz).1 hzt),
    hN.preimage (continuous_id.mul continuous_const), ?_⟩
  simp

def admitted (U : Subgroup G) (p : Subgroup G × Set G) : Prop :=
  p.1 ≤ U ∧ IsClosed p.2 ∧ (∀ k ∈ p.1, ∀ s ∈ p.2, k * s ∈ p.2) ∧
  (∀ a ∈ p.2, ∀ b ∈ p.2, a * b⁻¹ ∈ U → a * b⁻¹ ∈ p.1) ∧ ∀ g, ∃ a ∈ p.2, a * g⁻¹ ∈ U

lemma adm_of_section_mem (U K : Subgroup G) (S : Set G) (h : admitted U (K, S)) (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) : admitted U (K ⊓ N, S ∩ tr K N) := by
  obtain ⟨hKU, hSc, hKS, hSK, hSU⟩ := h
  refine ⟨inf_le_left.trans hKU, hSc.inter (tr_closed K N hN), ?_, ?_, ?_⟩
  · rintro k ⟨hkK, hkN⟩ s ⟨hsS, hsT⟩
    refine ⟨hKS k hkK s hsS, (tr_coset K N ?_).2 hsT⟩
    simpa using hkN
  · rintro a ⟨haS, haT⟩ b ⟨hbS, hbT⟩ hab
    have habK := hSK a haS b hbS hab
    refine ⟨habK, ?_⟩
    have hr : rep K N b = rep K N a := rep_eq K N ⟨a * b⁻¹, habK, 1, N.one_mem, by group⟩
    have ha : a * (rep K N a)⁻¹ ∈ N := haT
    have hb : b * (rep K N b)⁻¹ ∈ N := hbT
    rw [hr] at hb
    have := N.mul_mem ha (N.inv_mem hb)
    simpa [mul_assoc] using this
  · intro g
    obtain ⟨a, haS, hag⟩ := hSU g
    obtain ⟨k, hk, n, hn, ha⟩ := rep_spec K N a
    set r := rep K N a with hrdef
    have hrel : rep K N (k⁻¹ * a) = r := (rep_eq K N ⟨k⁻¹, K.inv_mem hk, 1, N.one_mem, by group⟩).symm
    refine ⟨k⁻¹ * a, ⟨hKS _ (K.inv_mem hk) a haS, ?_⟩, ?_⟩
    · show k⁻¹ * a * (rep K N (k⁻¹ * a))⁻¹ ∈ N
      rw [hrel, ha]
      simpa [mul_assoc] using hn
    · rw [mul_assoc]
      exact U.mul_mem (U.inv_mem (hKU hk)) hag

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma admissible_chain_inf [CompactSpace G] (U : Subgroup G) (hU : IsClosed (U : Set G))
    (c : Set (Subgroup G × Set G)) (hc : ∀ p ∈ c, admitted U p)
    (htot : ∀ p ∈ c, ∀ q ∈ c, p ≤ q ∨ q ≤ p) (y : Subgroup G × Set G) (hy : y ∈ c) :
    admitted U (⨅ p ∈ c, p.1, ⋂ p ∈ c, p.2) := by
  refine ⟨(iInf₂_le y hy).trans (hc y hy).1, isClosed_biInter fun p hp => (hc p hp).2.1, ?_, ?_, ?_⟩
  · intro k hk s hs
    simp only [Subgroup.mem_iInf] at hk
    simp only [Set.mem_iInter] at hs ⊢
    exact fun p hp => (hc p hp).2.2.1 k (hk p hp) s (hs p hp)
  · intro a ha b hb hab
    simp only [Set.mem_iInter] at ha hb
    simp only [Subgroup.mem_iInf]
    exact fun p hp => (hc p hp).2.2.2.1 a (ha p hp) b (hb p hp) hab
  · intro g
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    have hne := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun p : c => p.1.2 ∩ {a | a * g⁻¹ ∈ U}) ?_ ?_
      (fun p => ((hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul continuous_const))).isCompact)
      (fun p => (hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul continuous_const)))
    · obtain ⟨a, ha⟩ := hne
      simp only [Set.mem_iInter] at ha
      refine ⟨a, ?_, (ha ⟨y, hy⟩).2⟩
      simp only [Set.mem_iInter]
      exact fun p hp => (ha ⟨p, hp⟩).1
    · intro p q
      rcases htot p.1 p.2 q.1 q.2 with hpq | hqp
      · exact ⟨p, le_rfl, Set.inter_subset_inter_left _ (Prod.le_def.1 hpq).2⟩
      · exact ⟨q, Set.inter_subset_inter_left _ (Prod.le_def.1 hqp).2, le_rfl⟩
    · intro p
      obtain ⟨a, haS, hag⟩ := (hc p.1 p.2).2.2.2.2 g
      exact ⟨a, haS, hag⟩

theorem core [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (U : Subgroup G)
    (hU : IsClosed (U : Set G)) : ∃ t : G → G, Continuous t ∧ (∀ g, t g * g⁻¹ ∈ U) ∧
      ∀ g h, g * h⁻¹ ∈ U → t g = t h := by
  classical
  have hchain : ∀ c ⊆ {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)},
      IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)},
        ∀ z ∈ c, z ≤ ub := by
    intro c hcs hc y hy
    refine ⟨OrderDual.toDual (⨅ p ∈ OrderDual.toDual ⁻¹' c, p.1, ⋂ p ∈ OrderDual.toDual ⁻¹' c, p.2),
      admissible_chain_inf U hU _ (fun p hp => hcs hp) ?_ (OrderDual.ofDual y) hy, ?_⟩
    · intro p hp q hq
      by_cases hpq : p = q
      · exact Or.inl (le_of_eq hpq)
      · rcases hc hp hq (fun h => hpq (OrderDual.toDual.injective h)) with h | h
        · exact Or.inr h
        · exact Or.inl h
    · intro z hz
      exact Prod.le_def.2 ⟨iInf₂_le (OrderDual.ofDual z) hz,
        Set.iInter₂_subset (OrderDual.ofDual z) hz⟩
  have hstart : OrderDual.toDual ((U, Set.univ) : Subgroup G × Set G) ∈
      {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)} :=
    ⟨le_rfl, isClosed_univ, fun _ _ _ _ => Set.mem_univ _, fun _ _ _ _ h => h,
      fun g => ⟨g, Set.mem_univ _, by simp⟩⟩
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ _ hchain _ hstart
  have hA : admitted U (OrderDual.ofDual m) := hm.1
  set K := (OrderDual.ofDual m).1 with hKdef
  set S := (OrderDual.ofDual m).2 with hSdef
  have hK1 : ∀ k ∈ K, k = 1 := by
    intro k hk
    by_contra hne
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isOpen_compl_singleton : IsOpen ({k}ᶜ : Set G)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))
    have hstep := adm_of_section_mem U K S hA N.toSubgroup N.isOpen'
    have hle := hm.2 (y := OrderDual.toDual (K ⊓ N.toSubgroup, S ∩ tr K N.toSubgroup)) hstep
      (Prod.le_def.2 ⟨inf_le_left, Set.inter_subset_left⟩)
    have hkN : k ∈ N.toSubgroup := ((Prod.le_def.1 hle).1 hk).2
    exact hN hkN rfl
  have hex : ∀ g, ∃ a ∈ S, a * g⁻¹ ∈ U := hA.2.2.2.2
  have huniq : ∀ g a a', a ∈ S → a' ∈ S → a * g⁻¹ ∈ U → a' * g⁻¹ ∈ U → a = a' := by
    intro g a a' ha ha' hag ha'g
    have hU' : a * a'⁻¹ ∈ U := by
      have := U.mul_mem hag (U.inv_mem ha'g)
      simpa [mul_assoc] using this
    exact mul_inv_eq_one.1 (hK1 _ (hA.2.2.2.1 a ha a' ha' hU'))
  choose t htS htU using hex
  refine ⟨t, ?_, htU, fun g h hgh => ?_⟩
  · rw [continuous_iff_isClosed]
    intro C hC
    have hset : t ⁻¹' C = (U : Set G) * (S ∩ C) := by
      ext g
      constructor
      · intro hg
        refine Set.mem_mul.2 ⟨g * (t g)⁻¹, ?_, t g, ⟨htS g, hg⟩, by group⟩
        simpa using U.inv_mem (htU g)
      · rintro ⟨u, hu, a, ⟨haS, haC⟩, rfl⟩
        show t (u * a) ∈ C
        rw [huniq (u * a) (t (u * a)) a (htS _) haS (htU _) (by simpa using U.inv_mem hu)]
        exact haC
    rw [hset]
    exact (hU.isCompact.mul (hA.2.1.inter hC).isCompact).isClosed
  · refine huniq g (t g) (t h) (htS g) (htS h) (htU g) ?_
    have : t h * g⁻¹ = (t h * h⁻¹) * (g * h⁻¹)⁻¹ := by group
    rw [this]
    exact U.mul_mem (htU h) (U.inv_mem hgh)

end ReciprocityTheory.Coh.ContinuousSections
end

-- bundled from ReciprocityTheory.GroupCohomology.TransgressionStatement
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section Defs
variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'}

def Pair.h0 (P : Pair M M') : H0 M.rho →ₗ[R] H0 M'.rho :=
  P.u.restrict fun m hm g => by rw [← P.equiv, hm (P.φ g)]

def Pair.h1 (P : Pair M M') : H1 M.rho →ₗ[R] H1 M'.rho :=
  pairH1DecompositionMap M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv

def Pair.h2 (P : Pair M M') : H2 M.rho →ₗ[R] H2 M'.rho :=
  compatiblePairH2 M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv

def IsLow (M : TRep R G) (e₀ : M.H 0 ≃ₗ[R] H0 M.rho) (e₁ : M.H 1 ≃ₗ[R] H1 M.rho)
    (e₂ : M.H 2 ≃ₗ[R] H2 M.rho) : Prop :=
  (∀ x hx, (e₀ (M.coch.cls 0 x hx) : M.V) = x.1 ![]) ∧
  (∀ x hx, ∃ hz : (fun g => x.1 ![g]) ∈ Z1 M.rho, e₁ (M.coch.cls 1 x hx) = Submodule.Quotient.mk ⟨_, hz⟩) ∧
  ∀ x hx, ∃ hz : (fun g : G × G => x.1 ![g.1, g.2]) ∈ Z2 M.rho,
    e₂ (M.coch.cls 2 x hx) = Submodule.Quotient.mk ⟨_, hz⟩

def Cx.FinGen (A : Cx R) (N : ℕ) : Prop :=
  (∀ n, Module.Finite R (A.H n)) ∧ ∀ n, N < n → Subsingleton (A.H n)

def Cx.chiRk (A : Cx R) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1) ^ n * (Module.finrank R (A.H n) : ℤ)
end Defs

def LowNatStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  (M : TRep R G) (M' : TRep R G') (P : Pair M M') e₀ e₁ e₂ e₀' e₁' e₂', IsLow M e₀ e₁ e₂ → IsLow M' e₀' e₁' e₂' →
  (∀ x, e₀' (P.hom.H 0 x) = P.h0 (e₀ x)) ∧ (∀ x, e₁' (P.hom.H 1 x) = P.h1 (e₁ x)) ∧
  ∀ x, e₂' (P.hom.H 2 x) = P.h2 (e₂ x)

def LowLESStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A B C : TRep R G) (i : Pair A B) (p : Pair B C), admitted i p →
  ∃ (δ₀ : H0 C.rho →ₗ[R] H1 A.rho) (δ₁ : H1 C.rho →ₗ[R] H2 A.rho),
    (∀ (c : H0 C.rho) (b : B.V) (a : Z1 A.rho), p.u b = c → (∀ g, i.u (a.1 g) = B.rho g b - b) →
      δ₀ c = Submodule.Quotient.mk a) ∧
    (∀ (c : Z1 C.rho) (b : G → B.V) (a : Z2 A.rho), Continuous b → (∀ g, p.u (b g) = c.1 g) →
      (∀ g, i.u (a.1 g) = d1 B.rho b g) → δ₁ (Submodule.Quotient.mk c) = Submodule.Quotient.mk a) ∧
    Injective i.h0 ∧ Exact i.h0 p.h0 ∧ Exact p.h0 δ₀ ∧ Exact δ₀ i.h1 ∧ Exact i.h1 p.h1 ∧ Exact p.h1 δ₁ ∧
    Exact δ₁ i.h2 ∧ Exact i.h2 p.h2 ∧ (Subsingleton (A.H 3) → Surjective p.h2)

def LowResStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G),
  (∀ (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P →
    Injective P.h1 ∧ Exact P.h1 (resH1 M.rho N.subtype continuous_subtype_val)) ∧
  ∀ (U : Subgroup G) [U.FiniteIndex], IsOpen (U : Set G) →
    (∀ x, resH1 M.rho U.subtype continuous_subtype_val x = 0 → U.index • x = 0) ∧
    ∀ x, resH2 M.rho U.subtype continuous_subtype_val x = 0 → U.index • x = 0

def TransgressionStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal], IsClosed (N : Set G) →
  ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P → ∀ I : Submodule R ((M.resSub N).H 1),
  (∀ x, x ∈ I ↔ ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) →
    (∀ m, c.u m = M.rho s m) → c.hom.H 1 x = x) →
  ∃ tg : I →ₗ[R] Q.H 2,
    (∀ (y : M.coch.X 1) (z : Q.coch.X 2) (hz : Q.coch.d 2 z = 0) hy (x : I), M.coch.d 1 y = P.hom.f 2 z →
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy →
      tg x = Q.coch.cls 2 z hz) ∧
    (∀ x : I, ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), ∃ hy, M.coch.d 1 y = P.hom.f 2 z ∧
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy) ∧
    (∀ x : I, tg x = 0 ↔ x.1 ∈ LinearMap.range ((Pair.res M N.subtype continuous_subtype_val).hom.H 1)) ∧
    Exact tg (P.hom.H 2)

def RankLenStatement : Prop := ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (t : R),
  Irreducible t → ∀ (L C : Cx R) (i : Hom L L) (p : Hom L C) (m N : ℕ), (∀ n x, i.f n x = t ^ m • x) → SES i p →
  L.FinGen N → C.FinLen N ∧ C.chi N = m * L.chiRk N ∧ ∀ n,
    (Module.length R (C.H n)).toNat ≤ m * Module.finrank R (L.H n) +
      (Module.length R (Submodule.torsion R (L.H n))).toNat +
      (Module.length R (Submodule.torsion R (L.H (n + 1)))).toNat ∧
    m * Module.finrank R (L.H n) ≤ (Module.length R (C.H n)).toNat

def LocaliseStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (t : R) (L V : TRep R G) (j : Pair L V),
  j.φ = MonoidHom.id G → Topology.IsOpenEmbedding j.u → (∃ e : V.V ≃ₜ V.V, ∀ v, e v = t • v) →
  (∀ v : V.V, ∃ m : ℕ, t ^ m • v ∈ LinearMap.range j.u) → ∀ n, IsLocalizedModule (Submonoid.powers t) (j.hom.H n)

end

end ReciprocityTheory.Coh
end

