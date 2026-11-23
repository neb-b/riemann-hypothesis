module

public import ReciprocityTheory.GroupCohomology.Bundle0001
public import ReciprocityTheory.GroupCohomology.Bundle0008
public import ReciprocityTheory.GroupCohomology.Bundle0003
public import ReciprocityTheory.GroupCohomology.Bundle0004
public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.Bundle0009

@[expose] public section

-- bundled from ReciprocityTheory.GroupCohomology.ModelComparisonDegreeZeroBijective
section
namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def stab (M : TRep R G) (m : M.V) : Subgroup G where
  carrier := {a | M.rho a m = m}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem stab_isOpen (M : TRep R G) [DiscreteTopology M.V] (m : M.V) : IsOpen (stab M m : Set G) :=
  Subgroup.isOpen_of_mem_nhds _ (FiniteLevelCohomology.stab_mem_nhds M m)

theorem rho_comm (M : TRep R G) (hc : ∀ a b : G, a * b = b * a) (a b : G) (x : M.V) :
    M.rho a (M.rho b x) = M.rho b (M.rho a x) := by
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]

theorem cocycle_eq_of_apply (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hs : Dense (Subgroup.zpowers s : Set G)) (c : G → M.V) (hc : c ∈ Z1 M.rho) (m : M.V)
    (hm : c s = M.rho s m - m) (g : G) : c g = M.rho g m - m := by
  have hcont : Continuous fun a : G => M.rho a m :=
    M.cont.comp (f := fun a : G => (a, m)) (continuous_id.prodMk continuous_const)
  have hcl : IsClosed {a : G | c a = M.rho a m - m} :=
    isClosed_eq hc.1 (hcont.sub continuous_const)
  have step : ∀ a : G, c (a * s) - (M.rho (a * s) m - m) = c a - (M.rho a m - m) := by
    intro a
    rw [hc.2, hm, map_mul, Module.End.mul_apply]
    simp only [map_sub]; abel
  have hz : ∀ i : ℤ, c (s ^ i) = M.rho (s ^ i) m - m := by
    have h0 : c (s ^ (0 : ℤ)) - (M.rho (s ^ (0 : ℤ)) m - m) = 0 := by
      have e := hc.2 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at e
      simp only [zpow_zero, map_one, Module.End.one_apply, sub_self, sub_zero]
      exact (add_eq_left.1 e.symm)
    intro i
    have : c (s ^ i) - (M.rho (s ^ i) m - m) = 0 := by
      induction i using Int.induction_on with
      | zero => exact h0
      | succ i ih => rw [zpow_add_one, step, ih]
      | pred i ih => rw [← ih, ← step, zpow_sub_one, inv_mul_cancel_right]
    exact sub_eq_zero.1 this
  have hsub : (Subgroup.zpowers s : Set G) ⊆ {a : G | c a = M.rho a m - m} := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact hz i
  have h := hcl.closure_subset_iff.2 hsub
  rw [hs.closure_eq] at h
  exact h (Set.mem_univ g)

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def psum (M : TRep R G) (s : G) (m : M.V) (j : ℕ) : M.V :=
  ∑ i ∈ Finset.range j, M.rho (s ^ i) m

theorem psum_add (M : TRep R G) (s : G) (m : M.V) (i j : ℕ) :
    psum M s m (i + j) = psum M s m i + M.rho (s ^ i) (psum M s m j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [psum, Finset.sum_range_add, map_sum, pow_add, map_mul, Module.End.mul_apply]

theorem exists_cocycle [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (m : M.V) (hk : ∃ k : ℕ, 0 < k ∧ k • m = 0) : ∃ c ∈ Z1 M.rho, c s = m := by
  obtain ⟨k, hk0, hkm⟩ := hk
  set V := stab M m
  have hVo := stab_isOpen M m
  set a := V.index
  have ha : 0 < a := index_pos hc hVo
  have hsa : s ^ a ∈ V := by
    have := (zpow_mem_iff hc hs hVo (a : ℤ)).2 dvd_rfl
    simpa using this
  obtain ⟨W0, hW0o, hW0i⟩ := hidx (a * k) (Nat.mul_pos ha hk0)
  set W := V ⊓ W0
  have hWo : IsOpen (W : Set G) := hVo.inter hW0o
  have hWV : W ≤ V := inf_le_left
  have hdvd : a * k ∣ W.index := hW0i ▸ Subgroup.index_dvd_of_le inf_le_right

  have hfixV : ∀ v ∈ V, ∀ j, M.rho v (psum M s m j) = psum M s m j := by
    intro v hv j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [psum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rho_comm M hc]
    rw [show M.rho v m = m from hv]
  have hmul : ∀ t, psum M s m (a * t) = t • psum M s m a := by
    intro t
    induction t with
    | zero => simp [psum]
    | succ t ih =>
      rw [Nat.mul_succ, psum_add, ih, hfixV _ (by rw [pow_mul]; exact V.pow_mem hsa t), succ_nsmul]
  have hN : psum M s m (a * k) = 0 := by
    rw [hmul, psum, Finset.smul_sum]
    simp only [← map_nsmul, hkm, map_zero, Finset.sum_const_zero]
  have hperN : ∀ j, psum M s m (j + a * k) = psum M s m j := by
    intro j; rw [psum_add, hN, map_zero, add_zero]
  have hper : ∀ j, psum M s m (j + W.index) = psum M s m j := by
    obtain ⟨t, ht⟩ := hdvd
    intro j; rw [ht]; exact per_mul _ _ hperN j t
  have hex := exists_pow hc hs hWo
  refine ⟨desc W hex (psum M s m), ⟨desc_continuous hc hs hWo hex _ hper, fun g h => ?_⟩, ?_⟩
  · have hg := Classical.choose_spec (hex g)
    have hh := Classical.choose_spec (hex h)
    set i := Classical.choose (hex g)
    set j := Classical.choose (hex h)
    have hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W := by
      have e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by
        calc (g * h)⁻¹ * s ^ (i + j) = h⁻¹ * (g⁻¹ * s ^ i) * s ^ j := by
              rw [mul_inv_rev, pow_add]; group
          _ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]
      rw [e]; exact W.mul_mem hg hh
    have e1 : desc W hex (psum M s m) (g * h) = psum M s m (i + j) := desc_eq hc hs hWo hex _ hper hgh
    have e2 : desc W hex (psum M s m) g = psum M s m i := rfl
    have e3 : desc W hex (psum M s m) h = psum M s m j := rfl
    rw [e1, e2, e3, psum_add]
    congr 1
    have hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹ := by group
    conv_rhs => rw [hgeq, map_mul, Module.End.mul_apply]
    rw [hfixV _ (hWV (W.inv_mem hg))]
  · have : desc W hex (psum M s m) s = psum M s m 1 :=
      desc_eq hc hs hWo hex _ hper (by simp)
    rw [this]; simp [psum]

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem model_comparison_degree_zero_bijective [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∃ e : H1 M.rho ≃ₗ[R] M.V ⧸ LinearMap.range (M.rho s - LinearMap.id),
      ∀ c : Z1 M.rho, e (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := by
  set P := LinearMap.range (M.rho s - LinearMap.id)
  let f : Z1 M.rho →ₗ[R] M.V ⧸ P := P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 M.rho).subtype)
  have hf : ∀ c : Z1 M.rho, f c = Submodule.Quotient.mk (c.1 s) := fun c => rfl
  have hker : (B1 M.rho).comap (Z1 M.rho).subtype ≤ LinearMap.ker f := by
    intro c hc'
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hc'
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using (hm s).symm⟩
  let φ := ((B1 M.rho).comap (Z1 M.rho).subtype).liftQ f hker
  have hφ : ∀ c : Z1 M.rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) :=
    fun c => rfl
  have hinj : Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hφ, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨m, hm⟩ := hx
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨m, cocycle_eq_of_apply M hs c.1 c.2 m ?_⟩
    rw [← hm]; simp
  have hsurj : Surjective φ := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨c, hcZ, hcs⟩ := exists_cocycle M hc hs hidx m (htor m)
    exact ⟨Submodule.Quotient.mk ⟨c, hcZ⟩, by rw [hφ]; simp [hcs]⟩
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun c => hφ c⟩

end ProcyclicCohomology

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.Transgression
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function InflationRestrictionInvariants InflationTransgression

universe u

theorem transgression_holds : TransgressionStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ N _ hNc Q P hP I hI
  have hE : ∀ x : I, ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), ∃ hy,
      M.coch.d 1 y = P.hom.f 2 z ∧
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy := by
    intro x
    obtain ⟨f0, hf, hx⟩ := exists_cls x.1
    have hinv : ∀ s : G, ∃ m : M.V, ∀ n : N,
        M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m := fun s =>
      (conj_fix_iff M N s f0 hf).1 (by
        rw [← hx]; exact (hI x.1).1 x.2 s (conjN M N s) (fun g => rfl) (fun m => rfl))
    obtain ⟨y, z, hz, hd, hres⟩ := exists_lift M N Q P hP hNc f0 hf hinv
    exact ⟨y, z, hz, by rw [hres]; exact hf, hd, by rw [hx]; exact cls_congr _ _ hres.symm⟩
  choose yf zf hzf hyf hdf hxf using hE
  have key : ∀ (y : M.coch.X 1) (z : Q.coch.X 2) (hz : Q.coch.d 2 z = 0) hy (x : I),
      M.coch.d 1 y = P.hom.f 2 z →
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy →
      Q.coch.cls 2 (zf x) (hzf x) = Q.coch.cls 2 z hz := by
    intro y z hz hy x hd hx
    apply cls_unique M N Q P hP _ _ _ _ _ _ (hdf x) hd
    rw [map_sub, ← cls_eq_iff (hyf x) hy, ← hxf x, ← hx]
  let T : I → Q.H 2 := fun x => Q.coch.cls 2 (zf x) (hzf x)
  have hadd : ∀ x x' : I, T (x + x') = T x + T x' := fun x x' => by
    have hy : (M.resSub N).coch.d 1
        ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x + yf x')) = 0 := by
      rw [map_add (f := _)]; exact d_add_eq_zero (hyf x) (hyf x')
    refine (key (yf x + yf x') (zf x + zf x') (d_add_eq_zero (hzf x) (hzf x')) hy (x + x')
      (by rw [map_add (f := _), map_add (f := _), hdf, hdf]) ?_).trans rfl
    rw [Submodule.coe_add, hxf x, hxf x', cls_add]
    exact cls_congr _ _ (map_add _ _ _).symm
  have hsmul : ∀ (r : R) (x : I), T (r • x) = r • T x := fun r x => by
    have hy : (M.resSub N).coch.d 1
        ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (r • yf x)) = 0 := by
      rw [map_smul]; exact d_smul_eq_zero r (hyf x)
    refine (key (r • yf x) (r • zf x) (d_smul_eq_zero r (hzf x)) hy (r • x)
      (by rw [map_smul, map_smul, hdf]) ?_).trans rfl
    rw [Submodule.coe_smul, hxf x, cls_smul]
    exact cls_congr _ _ (map_smul _ _ _).symm
  let tg : I →ₗ[R] Q.H 2 := { toFun := T, map_add' := hadd, map_smul' := hsmul }
  refine ⟨tg, fun y z hz hy x hd hx => key y z hz hy x hd hx,
    fun x => ⟨yf x, zf x, hzf x, hyf x, hdf x, hxf x⟩, ?_, ?_⟩
  · intro x
    constructor
    · intro h0
      change Q.coch.cls 2 (zf x) (hzf x) = 0 at h0
      rw [cls_eq_zero_iff] at h0
      obtain ⟨v, hv⟩ := mem_B_succ.1 h0
      have hd' : M.coch.d 1 (yf x - P.hom.f 1 v) = 0 := by
        rw [map_sub, hdf, ← P.hom.comm, hv, sub_self]
      refine ⟨M.coch.cls 1 _ hd', ?_⟩
      rw [Hom.H_cls, hxf x]
      apply cls_congr
      have hc : (M.resSub N).coch.d 1
          ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)) = 0 := by
        have e : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v) =
            (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x) -
              (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x - P.hom.f 1 v) := by
          rw [map_sub, sub_sub_cancel]
        rw [e]
        exact d_sub_eq_zero (hyf x) ((Pair.res M N.subtype continuous_subtype_val).hom.d_f_eq_zero hd')
      have h1 := cocycle_one (M.resSub N) _ hc
      have hconst : ∀ g : Fin 1 → N,
          ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)).1 g =
            ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)).1 (e1 1) := fun g => by
        show P.u (v.1 fun i => P.φ (g i : G)) = P.u (v.1 fun _ => P.φ ((1 : N) : G))
        have e : ∀ i, P.φ (g i : G) = 1 := fun i => by
          rw [phi_apply M N Q P hP, (QuotientGroup.eq_one_iff _).2 (g i).2]
        simp only [e, OneMemClass.coe_one, map_one]
      have h0' : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v) = 0 :=
        Subtype.ext (funext fun g => by rw [hconst, h1]; rfl)
      rw [map_sub, h0', sub_zero]
    · rintro ⟨c, hc⟩
      obtain ⟨c0, hc0, rfl⟩ := exists_cls c
      change Q.coch.cls 2 (zf x) (hzf x) = 0
      rw [key c0 0 (map_zero _) ((Pair.res M N.subtype continuous_subtype_val).hom.d_f_eq_zero hc0) x
        (by rw [hc0, map_zero]) (by rw [← hc, Hom.H_cls])]
      rfl
  · intro w
    constructor
    · intro hw
      obtain ⟨z, hz, rfl⟩ := exists_cls w
      rw [Hom.H_cls, cls_eq_zero_iff] at hw
      obtain ⟨y, hy⟩ := mem_B_succ.1 hw
      let q : Q.V := z.1 ![1, 1]
      let vq : Q.coch.X 1 := ⟨fun _ => q, continuous_const⟩
      obtain ⟨z', hz'e⟩ : ∃ z', z' = z - Q.coch.d 1 vq := ⟨_, rfl⟩
      obtain ⟨y', hy'e⟩ : ∃ y', y' = y - P.hom.f 1 vq := ⟨_, rfl⟩
      have hz'c : Q.coch.d 2 z' = 0 := by rw [hz'e, map_sub, hz, Q.coch.dd, sub_zero]
      have hd' : M.coch.d 1 y' = P.hom.f 2 z' := by
        rw [hy'e, hz'e, map_sub, map_sub, hy, P.hom.comm]
      have hz'1 : z'.1 ![1, 1] = 0 := by
        rw [hz'e]
        show z.1 ![1, 1] - (Q.coch.d 1 vq).1 ![1, 1] = 0
        rw [oneDifferential_val]
        show q - (Q.rho 1 q - q + q) = 0
        simp
      have hres : (M.resSub N).coch.d 1
          ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y') = 0 := by
        rw [← (Pair.res M N.subtype continuous_subtype_val).hom.comm 1 y', hd']
        refine Subtype.ext (funext fun g => ?_)
        show P.u (z'.1 fun i => P.φ (g i : G)) = 0
        have e : (fun i => P.φ (g i : G)) = ![1, 1] := funext fun i => by
          rw [phi_apply M N Q P hP, (QuotientGroup.eq_one_iff _).2 (g i).2]
          fin_cases i <;> rfl
        rw [e, hz'1, map_zero]
      have hy'1 : (fun g => y'.1 (e1 g)) 1 = 0 := cocycle_one (M.resSub N) _ hres
      have hID := inflD_of_d M N Q P hP y' z' hd'
      have hmem : (M.resSub N).coch.cls 1 _ hres ∈ I := by
        rw [hI]
        intro s c hφ hu
        exact pair_fix M N s c hφ hu _ hres (y'.1 (e1 s)) (fun n => inflD_conj M N _ hy'1 hID s n)
      refine ⟨⟨_, hmem⟩, ?_⟩
      show Q.coch.cls 2 (zf _) (hzf _) = Q.coch.cls 2 z hz
      rw [key y' z' hz'c hres ⟨_, hmem⟩ hd' rfl, cls_eq_iff]
      exact ⟨-vq, by rw [hz'e, map_neg]; abel⟩
    · rintro ⟨x, rfl⟩
      show P.hom.H 2 (Q.coch.cls 2 (zf x) (hzf x)) = 0
      rw [Hom.H_cls, cls_eq_zero_iff]
      exact ⟨yf x, hdf x⟩

end ReciprocityTheory.Coh
end

