module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.GroupCohomology.MemZpowersQuot
section
namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open Topology
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem comm_of_dense [T2Space G] {s : G} (hs : Dense (Subgroup.zpowers s : Set G)) (a b : G) :
    a * b = b * a := by
  have hcl : IsClosed {p : G × G | p.1 * p.2 = p.2 * p.1} :=
    isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst)
  have hd : Dense ((Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G)) := hs.prod hs
  have hsub : (Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G) ⊆
      {p : G × G | p.1 * p.2 = p.2 * p.1} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact zpow_mul_comm s i j
  have h := hcl.closure_subset_iff.2 hsub
  rw [hd.closure_eq] at h
  exact h (Set.mem_univ (a, b))

theorem normal_of_comm (hc : ∀ a b : G, a * b = b * a) (W : Subgroup G) : W.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩

theorem finite_quot [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Finite (G ⧸ W) := by
  exact Subgroup.quotient_finite_of_isOpen W hW

theorem index_pos [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : 0 < W.index := by
  haveI := finite_quot hc hW
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

variable {s : G}

theorem mem_zpowers_quot (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} [W.Normal]
    (hW : IsOpen (W : Set G)) (x : G ⧸ W) : x ∈ Subgroup.zpowers (QuotientGroup.mk' W s) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  obtain ⟨y, hyU, hy⟩ := hs.inter_open_nonempty _ hU ⟨g, by simp [W.one_mem]⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq.mpr hyU).symm

theorem zpow_mem_iff [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (z : ℤ) :
    s ^ z ∈ W ↔ (W.index : ℤ) ∣ z := by
  haveI := normal_of_comm hc W
  haveI := finite_quot hc hW
  have hord : orderOf (QuotientGroup.mk' W s) = W.index := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (mem_zpowers_quot hs hW)]
    rfl
  rw [← QuotientGroup.eq_one_iff (N := W), ← hord, orderOf_dvd_iff_zpow_eq_one, ← map_zpow,
    QuotientGroup.mk'_apply]

theorem exists_pow [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (g : G) :
    ∃ j : ℕ, g⁻¹ * s ^ j ∈ W := by
  haveI := normal_of_comm hc W
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_quot hs hW (g : G ⧸ W))
  rw [← map_zpow, QuotientGroup.mk'_apply] at hk
  have hgk : g⁻¹ * s ^ k ∈ W := QuotientGroup.eq.mp hk.symm
  have hn : (0 : ℤ) < W.index := by exact_mod_cast index_pos hc hW
  refine ⟨(k % (W.index : ℤ)).toNat, ?_⟩
  have hj : (((k % (W.index : ℤ)).toNat : ℕ) : ℤ) = k % (W.index : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')
  have hd : s ^ (k % (W.index : ℤ) - k) ∈ W := by
    rw [zpow_mem_iff hc hs hW]
    exact ⟨-(k / (W.index : ℤ)), by rw [Int.emod_def]; ring⟩
  have heq : g⁻¹ * s ^ (k % (W.index : ℤ)).toNat =
      (g⁻¹ * s ^ k) * s ^ (k % (W.index : ℤ) - k) := by
    rw [mul_assoc, ← zpow_add, ← zpow_natCast, hj]
    congr 2
    ring
  rw [heq]
  exact W.mul_mem hgk hd

section Desc

variable {X : Type*} (n : ℕ) (T : ℕ → X)

theorem per_mul (hper : ∀ j, T (j + n) = T j) (a t : ℕ) : T (a + n * t) = T a := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]

theorem per_of_dvd (hper : ∀ j, T (j + n) = T j) (a b : ℕ) (h : (n : ℤ) ∣ (b : ℤ) - a) :
    T a = T b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · have h1 : ((b : ℕ) : ℤ) = ((a + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : b = a + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]
  · rw [mul_neg] at hc
    have h1 : ((a : ℕ) : ℤ) = ((b + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : a = b + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]

end Desc

noncomputable def desc (W : Subgroup G) (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*}
    (T : ℕ → X) (g : G) : X :=
  T (Classical.choose (h g))

theorem desc_eq [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G))
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) {g : G} {j : ℕ} (hj : g⁻¹ * s ^ j ∈ W) :
    desc W h T g = T j := by
  have h0 := Classical.choose_spec (h g)
  show T (Classical.choose (h g)) = T j
  have hm : s ^ ((j : ℤ) - (Classical.choose (h g) : ℕ)) ∈ W := by
    have hw := W.mul_mem (W.inv_mem h0) hj
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    rw [zpow_sub, zpow_natCast, zpow_natCast, hc]
    exact hw
  exact per_of_dvd W.index T hper _ _ ((zpow_mem_iff hc hs hW _).mp hm)

theorem desc_continuous [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G))
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} [TopologicalSpace X] (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) : Continuous (desc W h T) := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  have hg : g ∈ (fun y => g⁻¹ * y) ⁻¹' (W : Set G) := by simp [W.one_mem]
  refine (continuousAt_const : ContinuousAt (fun _ : G => desc W h T g) g).congr ?_
  filter_upwards [hU.mem_nhds hg] with y hy
  have h0 := Classical.choose_spec (h g)
  have hy' : y⁻¹ * s ^ Classical.choose (h g) ∈ W := by
    have hw := W.mul_mem (W.inv_mem hy) h0
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    exact hw
  rw [desc_eq hc hs hW h T hper hy']
  rfl

end ProcyclicCohomology

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.RankLenA
section
namespace ReciprocityTheory.Coh.TorsionRankLength

universe u

open Module Submodule Function
open scoped Pointwise TensorProduct

section General

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

abbrev K (M : Type u) [AddCommGroup M] [Module R M] (r : R) : Submodule R M :=
  LinearMap.ker (r • LinearMap.id : M →ₗ[R] M)

theorem mem_K {r : R} {x : M} : x ∈ K M r ↔ r • x = 0 := by
  simp [K]

theorem smul_top_eq_range (r : R) :
    (r • ⊤ : Submodule R M) = LinearMap.range (r • LinearMap.id : M →ₗ[R] M) := by
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_range]
  simp

theorem len_sub_add_quot (N : Submodule R M) :
    Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)

theorem len_K_eq_len_quot (hM : IsFiniteLength R M) (r : R) :
    Module.length R (K M r) = Module.length R (QuotSMulTop r M) := by
  set φ : M →ₗ[R] M := r • LinearMap.id with hφ
  have h1 : Module.length R M = Module.length R (K M r) + Module.length R (LinearMap.range φ) :=
    Module.length_eq_add_of_exact (K M r).subtype φ.rangeRestrict (Submodule.injective_subtype _)
      φ.surjective_rangeRestrict
      (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length R M = Module.length R (r • ⊤ : Submodule R M) + Module.length R (QuotSMulTop r M) :=
    len_sub_add_quot (r • ⊤ : Submodule R M)
  have h3 : Module.length R (r • ⊤ : Submodule R M) = Module.length R (LinearMap.range φ) :=
    (LinearEquiv.ofEq _ _ (smul_top_eq_range r)).length_eq
  have hMt : Module.length R M ≠ ⊤ := Module.length_ne_top_iff.2 hM
  have hL : Module.length R (LinearMap.range φ) ≠ ⊤ := fun h => hMt (by rw [h1, h, add_top])
  rw [h3] at h2
  rw [h1, add_comm (Module.length R (LinearMap.range φ))] at h2
  exact WithTop.add_right_cancel hL h2

end General

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem len_quot_pow {t : R} (ht : Irreducible t) (k : ℕ) :
    Module.length R (R ⧸ Ideal.span {t ^ k}) = k := by
  have hmax : (Ideal.span {t} : Ideal R).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible ht
  have h1 : Module.length R (R ⧸ Ideal.span {t}) = 1 := by
    rw [Module.length_eq_one_iff]
    exact isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 hmax)
  have ht0 : t ≠ 0 := ht.ne_zero
  induction k with
  | zero =>
    haveI : Subsingleton (R ⧸ Ideal.span {t ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.span_singleton_one])
    rw [Nat.cast_zero]
    exact Module.length_eq_zero_iff.2 this
  | succ k ih =>
    have hle : Ideal.span {t} ≤ Submodule.comap (LinearMap.mulLeft R (t ^ k)) (Ideal.span {t ^ (k + 1)}) := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      rw [Ideal.mem_span_singleton']
      exact ⟨y, by ring⟩
    let f := Submodule.mapQ (Ideal.span {t}) (Ideal.span {t ^ (k + 1)}) (LinearMap.mulLeft R (t ^ k)) hle
    have hfac : Ideal.span {t ^ (k + 1)} ≤ Ideal.span {t ^ k} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨t, by ring⟩
    let g := (Ideal.Quotient.factorₐ R hfac).toLinearMap
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker] at hx
      simp only [f, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
      rw [Ideal.mem_span_singleton']
      refine ⟨y, ?_⟩
      have : t ^ k * (y * t) = t ^ k * x := by rw [← hy]; ring
      exact mul_left_cancel₀ (pow_ne_zero _ ht0) this
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ z, rfl⟩
    have hex : Function.Exact f g := by
      intro y
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      constructor
      · intro hz
        have hz' : z ∈ Ideal.span {t ^ k} := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          exact hz
        obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz'
        exact ⟨Submodule.Quotient.mk w, by
          simp only [f, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
          congr 1
          ring⟩
      · rintro ⟨x, hx⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [← hx]
        simp only [f, g, Submodule.mapQ_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
        show Ideal.Quotient.factor hfac (Ideal.Quotient.mk _ (t ^ k * x)) = 0
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
        exact ⟨x, by ring⟩
    rw [Module.length_eq_add_of_exact f g hf hg hex, h1, ih]
    push_cast
    ring

variable (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H]

theorem torsion_finLen : IsFiniteLength R (torsion R H) := by
  obtain ⟨ι, _, p, hp, e, ⟨f⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (R := R) (M := torsion R H) (torsion_isTorsion)
  rw [← Module.length_ne_top_iff, f.length_eq,
    (DirectSum.linearEquivFunOnFintype R ι (fun i => R ⧸ R ∙ p i ^ e i)).length_eq,
    Module.length_pi_of_fintype]
  have : ∀ i, Module.length R (R ⧸ R ∙ p i ^ e i) = e i := fun i => len_quot_pow (hp i) (e i)
  simp only [this]
  exact (ENat.sum_lt_top.mpr fun i _ => ENat.natCast_lt_top _).ne

theorem finrank_torsion_eq_zero : Module.finrank R (torsion R H) = 0 := by
  rw [Module.finrank_eq_zero_iff]
  intro x
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x : H)).1 x.2
  exact ⟨a, nonZeroDivisors.ne_zero a.2, Subtype.ext ha⟩

theorem len_quot_split (r : R) :
    Module.length R (QuotSMulTop r H) = Module.length R (QuotSMulTop r (torsion R H)) +
      Module.finrank R H * Module.length R (R ⧸ Ideal.span {r}) := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := H ⧸ torsion R H)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (torsion R H).mkQ LinearMap.id
    (torsion R H).mkQ_surjective
  have e : (torsion R H × (H ⧸ torsion R H)) ≃ₗ[R] H :=
    lequivProdOfRightSplitExact (torsion R H).injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf
  have hrank : Module.finrank R H = n := by
    have h := Submodule.finrank_quotient_add_finrank (torsion R H)
    rw [finrank_torsion_eq_zero, add_zero, Module.finrank_eq_card_basis b, Fintype.card_fin] at h
    exact h.symm
  have e2 : QuotSMulTop r H ≃ₗ[R]
      ((R ⧸ Ideal.span {r}) ⊗[R] torsion R H) × ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H)) :=
    (QuotSMulTop.congr r e.symm).trans ((QuotSMulTop.equivQuotTensor r _).trans
      (TensorProduct.prodRight R R _ _ _))
  have e3 : ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H)) ≃ₗ[R] (Fin n →₀ (R ⧸ Ideal.span {r})) :=
    (LinearEquiv.lTensor _ b.repr).trans (TensorProduct.finsuppScalarRight R R _ _)
  rw [e2.length_eq, Module.length_prod, ← (QuotSMulTop.equivQuotTensor r _).length_eq,
    e3.length_eq, Module.length_finsupp, hrank]
  simp

theorem len_K_torsion {r : R} (hr : r ≠ 0) :
    Module.length R (K H r) = Module.length R (K (torsion R H) r) := by
  have hmem : ∀ y : H, r • y = 0 → y ∈ torsion R H := fun y hy =>
    (Submodule.mem_torsion_iff y).2 ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, hy⟩
  let f : K (torsion R H) r →ₗ[R] K H r :=
    { toFun := fun x => ⟨((x : torsion R H) : H), by
        have h1 := mem_K.1 x.2
        rw [mem_K]
        simpa using congrArg Subtype.val h1⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : K H r => (z : H)) hxy
    · intro y
      refine ⟨⟨⟨y, hmem y (mem_K.1 y.2)⟩, ?_⟩, rfl⟩
      rw [mem_K]
      apply Subtype.ext
      exact mem_K.1 y.2
  exact ((LinearEquiv.ofBijective f hf).length_eq).symm

end DVR

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem len_quot_eq (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H] {t : R}
    (ht : Irreducible t) (m : ℕ) :
    Module.length R (QuotSMulTop (t ^ m) H) =
        ((m * Module.finrank R H : ℕ) : ℕ∞) + Module.length R (K H (t ^ m)) ∧
      Module.length R (K H (t ^ m)) ≤ Module.length R (torsion R H) ∧
      Module.length R (torsion R H) ≠ ⊤ := by
  have htm : t ^ m ≠ 0 := pow_ne_zero _ ht.ne_zero
  have hT := torsion_finLen (R := R) H
  have hK := len_K_torsion (R := R) H htm
  have hQ := len_K_eq_len_quot hT (t ^ m)
  have hS := len_quot_split (R := R) H (t ^ m)
  have hP := len_quot_pow ht m
  refine ⟨?_, ?_, Module.length_ne_top_iff.2 hT⟩
  · rw [hS, ← hQ, ← hK, hP]
    push_cast
    ring
  · rw [hK]
    have h := len_sub_add_quot (K (torsion R H) (t ^ m))
    rw [h]
    exact le_self_add

end Main

end ReciprocityTheory.Coh.TorsionRankLength
end

