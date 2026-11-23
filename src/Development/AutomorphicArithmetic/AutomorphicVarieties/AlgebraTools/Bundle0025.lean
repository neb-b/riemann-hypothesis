module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkMul
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkMul_out {G : Type} [Group G] (I : Subgroup G) (g : G) :
    ∃ i ∈ I, (g : G ⧸ I).out = g * i := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I g
  exact ⟨h, h.2, hh⟩

private theorem hkMul_mem {G : Type} [Group G] (I : Subgroup G) (x : G) (p : G ⧸ I) :
    p ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, p = ((a * x : G) : G ⧸ I) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem UpperTheory.V.AlgebraTools.hkMul :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (x y : G), HeckePair I → (∀ b ∈ I, ∃ a ∈ I, ∃ c ∈ I, x * b * y = a * (x * y) * c) → (MulAction.orbit I ((x * y : G) : G ⧸ I)).ncard = (MulAction.orbit I (x : G ⧸ I)).ncard * (MulAction.orbit I (y : G ⧸ I)).ncard → hk ρ I x * hk ρ I y = hk ρ I (x * y) := by
  intro A G M _ _ _ _ ρ I x y hI hb hc
  classical
  haveI fx : Fintype (MulAction.orbit I (x : G ⧸ I)) := (hI x).fintype
  haveI fy : Fintype (MulAction.orbit I (y : G ⧸ I)) := (hI y).fintype
  haveI fxy : Fintype (MulAction.orbit I ((x * y : G) : G ⧸ I)) := (hI (x * y)).fintype
  have hmem : ∀ (p : MulAction.orbit I (x : G ⧸ I)) (q : MulAction.orbit I (y : G ⧸ I)),
      (((p : G ⧸ I).out * (q : G ⧸ I).out : G) : G ⧸ I) ∈ MulAction.orbit I ((x * y : G) : G ⧸ I) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨a, ha, rfl⟩ := (hkMul_mem I x p).1 hp
    obtain ⟨b, hb', rfl⟩ := (hkMul_mem I y q).1 hq
    obtain ⟨i, hi, e1⟩ := hkMul_out I (a * x)
    obtain ⟨j, hj, e2⟩ := hkMul_out I (b * y)
    obtain ⟨a', ha', c, hc', e3⟩ := hb (i * b) (mul_mem hi hb')
    refine (hkMul_mem I _ _).2 ⟨a * a', mul_mem ha ha', ?_⟩
    simp only [e1, e2]
    have : a * x * i * (b * y * j) = a * a' * (x * y) * (c * j) := by
      calc a * x * i * (b * y * j) = a * (x * (i * b) * y) * j := by group
        _ = _ := by rw [e3]; group
    rw [this]
    exact QuotientGroup.mk_mul_of_mem _ (mul_mem hc' hj)
  let f : MulAction.orbit I (x : G ⧸ I) × MulAction.orbit I (y : G ⧸ I) →
      MulAction.orbit I ((x * y : G) : G ⧸ I) := fun pq => ⟨_, hmem pq.1 pq.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨a, ha, rfl⟩ := (hkMul_mem I _ r).1 hr
    obtain ⟨i, hi, e1⟩ := hkMul_out I (a * x)
    obtain ⟨j, hj, e2⟩ := hkMul_out I (i⁻¹ * y)
    refine ⟨(⟨_, (hkMul_mem I _ _).2 ⟨a, ha, rfl⟩⟩, ⟨_, (hkMul_mem I _ _).2 ⟨i⁻¹, inv_mem hi, rfl⟩⟩), Subtype.ext ?_⟩
    simp only [f, e1, e2]
    have : a * x * i * (i⁻¹ * y * j) = a * (x * y) * j := by group
    rw [this]
    exact QuotientGroup.mk_mul_of_mem _ hj
  have hbij : Function.Bijective f := by
    refine (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, ?_⟩
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hc]
  refine LinearMap.ext fun v => Subtype.ext ?_
  have h1 := (hkApply A G M ρ I I x (hI x)).1
  have h2 := (hkApply A G M ρ I I y (hI y)).1
  have h3 := (hkApply A G M ρ I I (x * y) (hI _)).1
  rw [Module.End.mul_apply]
  unfold hk
  rw [h1, h2, h3]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum]
  rw [← hbij.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨i, hi, e⟩ := hkMul_out I ((p : G ⧸ I).out * (q : G ⧸ I).out)
  simp only [f, e, map_mul, Module.End.mul_apply]
  rw [v.2 i hi]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkNorm_mem {G : Type} [Group G] (I : Subgroup G) (x y : G) :
    (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, y = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have h : (((a : G) * x : G) : G ⧸ I) = (y : G ⧸ I) := ha
    rw [QuotientGroup.eq] at h
    exact ⟨a, a.2, _, h, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [QuotientGroup.mk_mul_of_mem _ hb]
    rfl

private theorem hkNorm_reps {G : Type} [Group G] (I : Subgroup G) (x : G) (h : FinOrb I I x) :
    ∃ s : Finset G, (∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I)) ∧
      ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q := by
  classical
  refine ⟨(Set.Finite.toFinset h).image Quotient.out, fun y hy => ?_, fun q hq => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']
    exact (Set.Finite.mem_toFinset h).1 hq
  · refine ⟨q.out, ⟨Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset h).2 hq), QuotientGroup.out_eq' q⟩, ?_⟩
    rintro y ⟨hy, rfl⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']

private theorem hkNorm_tr {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (x u w : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (hw : w ∈ Subgroup.normalizer (I : Set G))
    (s : Finset G) (h1 : ∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I))
    (h2 : ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q) (v : fixd ρ I) :
    (hk ρ I (u * x * w) v : M) = ∑ y ∈ s, ρ (u * y * w) v := by
  classical
  have cu : ∀ a ∈ I, u * a * u⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hu a).1 ha
  have cu' : ∀ a ∈ I, u⁻¹ * a * u ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hu a).1 ha
  have cw : ∀ a ∈ I, w * a * w⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hw a).1 ha
  have cw' : ∀ a ∈ I, w⁻¹ * a * w ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hw a).1 ha
  have key := (hkApply A G M ρ I I (u * x * w) (hI _)).2.1 (s.image fun y => u * y * w) ?_ ?_ v
  · rw [Finset.sum_image (fun a _ b _ h => by simpa using h)] at key
    exact key
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I x z).1 (h1 z hz)
    exact (hkNorm_mem I _ _).2 ⟨_, cu a ha, _, cw' b hb, by group⟩
  · intro q hq
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    obtain ⟨y, ⟨hy, hyq⟩, huniq⟩ := h2 ((u⁻¹ * a * u * x : G) : G ⧸ I)
      ((hkNorm_mem I _ _).2 ⟨_, cu' a ha, 1, one_mem _, by group⟩)
    refine ⟨u * y * w, ⟨Finset.mem_image_of_mem _ hy, ?_⟩, ?_⟩
    · rw [QuotientGroup.eq] at hyq ⊢
      convert mul_mem (cw' _ hyq) hb using 1
      group
    · rintro y' ⟨hy', h⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy'
      rw [huniq z ⟨hz, ?_⟩]
      rw [QuotientGroup.eq] at h ⊢
      convert cw _ (mul_mem h (inv_mem hb)) using 1
      group

private theorem hkNorm_one {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (v : fixd ρ I) : (hk ρ I u v : M) = ρ u v := by
  have h := hkNorm_tr ρ I hI 1 u 1 hu (one_mem _) {1} (by simp) (fun q hq => by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    refine ⟨1, ⟨by simp, ?_⟩, fun y hy => by simpa using hy.1⟩
    rw [QuotientGroup.eq]
    simpa using mul_mem ha hb) v
  simpa using h

private theorem hkNorm_mul {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (x : G) :
    hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  obtain ⟨s, h1, h2⟩ := hkNorm_reps I x (hI x)
  have h0 := hkNorm_tr ρ I hI x 1 1 (one_mem _) (one_mem _) s h1 h2
  have hl := hkNorm_tr ρ I hI x u 1 hu (one_mem _) s h1 h2
  have hr := hkNorm_tr ρ I hI x 1 u (one_mem _) hu s h1 h2
  simp only [one_mul, mul_one] at h0 hl hr
  constructor
  · ext v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hl, Module.End.mul_apply, hkNorm_one ρ I hI u hu, h0, map_sum]
    simp only [map_mul, Module.End.mul_apply]
  · ext v
    rw [hr, Module.End.mul_apply, h0, hkNorm_one ρ I hI u hu]
    simp only [map_mul, Module.End.mul_apply]

theorem UpperTheory.V.AlgebraTools.hkNorm :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (u : G), HeckePair I → u ∈ Subgroup.normalizer (I : Set G) → (∀ v : fixd ρ I, (hk ρ I u v : M) = ρ u v) ∧ hk ρ I 1 = 1 ∧ IsUnit (hk ρ I u) ∧ ∀ x : G, hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  intro A G M _ _ _ _ ρ I u hI hu
  have h1 : hk ρ I 1 = 1 := by
    ext v
    rw [hkNorm_one ρ I hI 1 (one_mem _)]
    simp
  refine ⟨hkNorm_one ρ I hI u hu, h1, ⟨⟨hk ρ I u, hk ρ I u⁻¹, ?_, ?_⟩, rfl⟩, hkNorm_mul ρ I hI u hu⟩
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).1, mul_inv_cancel, h1]
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).2, inv_mul_cancel, h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkTrace
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem double_coset_operator_sum {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M)
    (K K' : Subgroup G) (x : G) (h : (MulAction.orbit K (x : G ⧸ K')).Finite) (v : fixd ρ K') :
    (hk2 ρ K K' x v : M) = ∑ q ∈ Set.Finite.toFinset h, ρ q.out v := by
  rw [(hkApply A G M ρ K K' x h).1 v, dc,
    finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ K' => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ h,
    LinearMap.sum_apply]

private theorem mem_orb {G : Type} [Group G] (K K' : Subgroup G) (x g : G) :
    (g : G ⧸ K') ∈ MulAction.orbit K (x : G ⧸ K') ↔ ∃ a ∈ K, ∃ b ∈ K', g = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (((a : G) * x : G) : G ⧸ K') = g := ha
    exact ⟨a, a.2, _, QuotientGroup.eq.1 ha', by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    change ((a * x : G) : G ⧸ K') = _
    exact (QuotientGroup.mk_mul_of_mem _ hb).symm

theorem UpperTheory.V.AlgebraTools.hkTrace :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I K : Subgroup G) (h : I ≤ K) (ι : Type) [Fintype ι] (w : ι → G), HeckePair I → (∀ i, w i ∈ K) → (∀ g ∈ K, ∃! i, ∃ a ∈ I, ∃ b ∈ I, g = a * w i * b) → FinOrb K I 1 ∧ ∑ i, hk ρ I (w i) = inc ρ h ∘ₗ trc ρ K I ∧ ∀ v : fixd ρ K, trc ρ K I (inc ρ h v) = (I.relIndex K : A) • v := by
  intro A G M _ _ _ _ ρ I K h ι _ w hI hw hu
  classical
  replace hI : ∀ x : G, (MulAction.orbit I (x : G ⧸ I)).Finite := hI
  have hK : ∀ g : G, (g : G ⧸ I) ∈ MulAction.orbit K ((1 : G) : G ⧸ I) ↔ g ∈ K := fun g => by
    rw [mem_orb]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => e ▸ mul_mem (mul_mem ha (one_mem _)) (h hb),
      fun hg => ⟨g, hg, 1, one_mem _, by simp⟩⟩
  have hU : MulAction.orbit K ((1 : G) : G ⧸ I) = ⋃ i, MulAction.orbit I (w i : G ⧸ I) := by
    ext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [Set.mem_iUnion, hK, mem_orb]
    exact ⟨fun hg => (hu g hg).exists,
      fun ⟨i, a, ha, b, hb, e⟩ => e ▸ mul_mem (mul_mem (h ha) (hw i)) (h hb)⟩
  have hF : (MulAction.orbit K ((1 : G) : G ⧸ I)).Finite := by
    rw [hU]
    exact Set.finite_iUnion fun i => hI (w i)
  refine ⟨hF, ?_, fun v => ?_⟩
  · ext v
    change _ = (hk2 ρ K I 1 v : M)
    rw [LinearMap.sum_apply, Submodule.coe_sum, double_coset_operator_sum ρ K I 1 hF]
    have e : Set.Finite.toFinset hF = Finset.univ.biUnion fun i => Set.Finite.toFinset (hI (w i)) := by
      ext q
      simp [hU]
    rw [e, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun i _ => double_coset_operator_sum ρ I I (w i) (hI _) v
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro q hi hj
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [Set.Finite.mem_toFinset] at hi hj
      have hg : g ∈ K := (hK g).1 (hU ▸ Set.mem_iUnion.2 ⟨i, hi⟩)
      exact hij ((hu g hg).unique ((mem_orb _ _ _ _).1 hi) ((mem_orb _ _ _ _).1 hj))
  · ext
    change (hk2 ρ K I 1 (inc ρ h v) : M) = _
    rw [double_coset_operator_sum ρ K I 1 hF, Finset.sum_congr rfl (g := fun _ => (v : M))]
    · have hs : MulAction.stabilizer K ((1 : G) : G ⧸ I) = I.subgroupOf K := by
        ext k
        rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
        change (((k : G) * 1 : G) : G ⧸ I) = _ ↔ _
        rw [eq_comm, QuotientGroup.eq]
        simp
      rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hF, ← MulAction.index_stabilizer, hs,
        Submodule.coe_smul, Nat.cast_smul_eq_nsmul]
      rfl
    · intro q hq
      rw [Set.Finite.mem_toFinset, ← q.out_eq'] at hq
      exact v.2 _ ((hK _).1 hq)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwIwQuot
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

section Ring

variable {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] [LinearOrder n]

private theorem q_diag_mul {a b : GL n R} (ha : a ∈ borel R n) (hb : b ∈ borel R n) (i : n) :
    ((a * b : GL n R) : Matrix n n R) i i = (a : Matrix n n R) i i * (b : Matrix n n R) i i := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [(mem_borel R).1 ha i l h, zero_mul]
    · rw [(mem_borel R).1 hb l i h, mul_zero]
  · simp

private theorem q_exD : ∃ D : borel R n →* (n → Rˣ),
    ∀ (g : borel R n) (i : n), (D g i : R) = ((g : GL n R) : Matrix n n R) i i := by
  let D0 : n → (borel R n →* R) := fun i =>
    { toFun := fun g => ((g : GL n R) : Matrix n n R) i i
      map_one' := by simp
      map_mul' := fun a b => q_diag_mul a.2 b.2 i }
  exact ⟨MonoidHom.pi fun i => (D0 i).toHomUnits, fun g i => rfl⟩

private theorem q_map_diagT {S : Type} [CommRing S] (f : R →+* S) (d : n → Rˣ) :
    GeneralLinearGroup.map (n := n) f (diagT R n d) = diagT S n fun i => Units.map f.toMonoidHom (d i) := by
  ext i j
  show f ((diagT R n d : Matrix n n R) i j) = _
  rw [val_diagT, val_diagT, diagonal_apply, diagonal_apply]
  split_ifs
  · rfl
  · simp

end Ring

section Loc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

private theorem q_exF : ∃ F : iwC k n ⊤ →* (Fin n → 𝓀[k]ˣ), ∀ (h : GL (Fin n) 𝒪[k])
    (hh : GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) h ∈ iwC k n ⊤) (i : Fin n),
    (F ⟨_, hh⟩ i : 𝓀[k]) = IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i i) := by
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hinj2 : Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := by
    intro a b hab
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact hinj (congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hab)
  obtain ⟨D, hD⟩ := q_exD (R := 𝓀[k]) (n := Fin n)
  let r := GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k])
  let H := (borel 𝓀[k] (Fin n)).comap r
  have hle : iwC k n ⊤ ≤ H.map (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) :=
    le_of_eq (memIwC k n ⊤).2.1
  let e := H.equivMapOfInjective _ hinj2
  refine ⟨D.comp ((r.subgroupComap _).comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hle))), fun h hh i => ?_⟩
  have hH : h ∈ H := by
    obtain ⟨h', h1, h2⟩ := hle hh
    rwa [← hinj2 h2]
  have : e.symm (Subgroup.inclusion hle ⟨_, hh⟩) = ⟨h, hH⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (D (r.subgroupComap _ (e.symm (Subgroup.inclusion hle ⟨_, hh⟩))) i : 𝓀[k]) = _
  rw [this, hD]
  rfl

end Loc

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.iwQuot :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), ∃ f : iwC k n ⊤ →* (Fin n → 𝓀[k]ˣ ⧸ C), Function.Surjective f ∧ (∀ g : iwC k n ⊤, f g = 1 ↔ (g : GL (Fin n) k) ∈ iwC k n C) ∧ ∀ (u : Fin n → 𝒪[k]ˣ) (h : diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (u i)) ∈ iwC k n ⊤) (i : Fin n), f ⟨_, h⟩ i = ((Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom (u i) : 𝓀[k]ˣ) : 𝓀[k]ˣ ⧸ C) := by
  intro k _ _ _ _ n C
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  obtain ⟨F, hF⟩ := q_exF k n
  let f : iwC k n ⊤ →* (Fin n → 𝓀[k]ˣ ⧸ C) :=
    MonoidHom.pi fun i => (QuotientGroup.mk' C).comp ((Pi.evalMonoidHom _ i).comp F)
  have hf : ∀ g i, f g i = ((F g i : 𝓀[k]ˣ) : 𝓀[k]ˣ ⧸ C) := fun _ _ => rfl
  have h3 : ∀ (u : Fin n → 𝒪[k]ˣ) (h : diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (u i)) ∈ iwC k n ⊤) (i : Fin n), f ⟨_, h⟩ i = ((Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom (u i) : 𝓀[k]ˣ) : 𝓀[k]ˣ ⧸ C) := by
    intro u h i
    have e := q_map_diagT (algebraMap 𝒪[k] k) u
    have h' : GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) (diagT _ _ u) ∈ iwC k n ⊤ := e ▸ h
    have e2 : (⟨_, h⟩ : iwC k n ⊤) = ⟨_, h'⟩ := Subtype.ext e.symm
    rw [hf, e2]
    congr 1
    apply Units.ext
    rw [hF, val_diagT, diagonal_apply_eq]
    rfl
  refine ⟨f, fun y => ?_, fun g => ?_, h3⟩
  · have h1 : ∀ i, ∃ u : 𝒪[k]ˣ,
        ((Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom u : 𝓀[k]ˣ) : 𝓀[k]ˣ ⧸ C) = y i := by
      intro i
      obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (y i)
      obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := 𝒪[k]) (c : 𝓀[k])
      have hu : IsUnit x := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hx]
        exact c.ne_zero
      obtain ⟨u, rfl⟩ := hu
      refine ⟨u, ?_⟩
      rw [← hc]
      congr 1
      exact Units.ext hx
    choose u hu using h1
    have h : diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (u i)) ∈ iwC k n ⊤ :=
      Subgroup.mem_sup_right ⟨_, fun i _ => ⟨u i, trivial, rfl⟩, rfl⟩
    exact ⟨⟨_, h⟩, funext fun i => (h3 u h i).trans (hu i)⟩
  · obtain ⟨g, hg⟩ := g
    have hg' : g ∈ iwahori k (Fin n) := (memIwC k n C).2.1 ▸ hg
    obtain ⟨h, hh, rfl⟩ := id hg'
    rw [(memIwC k n C).1, and_iff_right hg', funext_iff]
    refine forall_congr' fun i => ?_
    rw [hf, Pi.one_apply, QuotientGroup.eq_one_iff]
    have e := hF h hg i
    constructor
    · intro hc
      have hu : IsUnit ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i i) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← e]
        exact Units.ne_zero _
      obtain ⟨d, hd⟩ := hu
      refine ⟨_, ⟨d, ?_, rfl⟩, congrArg (algebraMap 𝒪[k] k) hd⟩
      rw [← hd] at e
      have : Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom d = F ⟨_, hg⟩ i := Units.ext e.symm
      show Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom d ∈ C
      rw [this]
      exact hc
    · rintro ⟨_, ⟨d, hd, rfl⟩, e1⟩
      have e' : (d : 𝒪[k]) = (h : Matrix (Fin n) (Fin n) 𝒪[k]) i i := hinj e1
      rw [← e'] at e
      have : Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom d = F ⟨_, hg⟩ i := Units.ext e.symm
      rw [← this]
      exact hd
end

