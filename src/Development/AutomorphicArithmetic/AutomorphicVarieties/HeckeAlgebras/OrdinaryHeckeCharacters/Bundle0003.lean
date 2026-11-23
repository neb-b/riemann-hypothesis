module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpSum

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCker
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem UpperTheory.V.Hi.propCker_avg {H k M : Type} [Group H] [Field k] [CharZero k] [AddCommGroup M] [Module k M]
    (ρ : Representation k H M) (hs : ∀ m, ∃ K : Subgroup H, K.FiniteIndex ∧ ∀ x ∈ K, ρ x m = m) {w : M}
    (hw : w ∈ Submodule.span k {w | ∃ x m, w = ρ x m - m}) (hfix : ∀ x, ρ x w = w) : w = 0 := by
  have key : ∃ K0 : Subgroup H, K0.FiniteIndex ∧ ∀ (K : Subgroup H) [K.Normal] [Fintype (H ⧸ K)], K ≤ K0 →
      ∑ q : H ⧸ K, ρ q.out w = 0 := by
    clear hfix
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨x, m, rfl⟩ := h
      obtain ⟨K0, h0, h1⟩ := hs m
      refine ⟨K0, h0, fun K _ _ hK => ?_⟩
      simp only [map_sub]
      rw [Finset.sum_sub_distrib, sub_eq_zero,
        ← Equiv.sum_comp (Equiv.mulRight (x : H ⧸ K)) (fun q : H ⧸ K => ρ q.out m)]
      refine Finset.sum_congr rfl fun q _ => ?_
      have h2 : ((q * x).out)⁻¹ * (q.out * x) ∈ K := by
        rw [← QuotientGroup.eq]
        simp
      have h3 := h1 _ (hK h2)
      have h4 : q.out * x = (q * x).out * (((q * x).out)⁻¹ * (q.out * x)) := by group
      rw [Equiv.coe_mulRight, ← mul_apply_eq_comp, ← map_mul, h4, map_mul, mul_apply_eq_comp, h3]
    | zero => exact ⟨⊤, inferInstance, fun K _ _ _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨K1, h1, h1'⟩ := ha
      obtain ⟨K2, h2, h2'⟩ := hb
      refine ⟨K1 ⊓ K2, inferInstance, fun K _ _ hK => ?_⟩
      simp only [map_add (f := _)]
      rw [Finset.sum_add_distrib, h1' K (hK.trans inf_le_left), h2' K (hK.trans inf_le_right), add_zero]
    | smul c a _ ha =>
      obtain ⟨K1, h1, h1'⟩ := ha
      refine ⟨K1, h1, fun K _ _ hK => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, h1' K hK, smul_zero]
  obtain ⟨K0, h0, h1⟩ := key
  have : Fintype (H ⧸ K0.normalCore) := Fintype.ofFinite _
  have h2 := h1 K0.normalCore K0.normalCore_le
  simp only [hfix, Finset.sum_const, Finset.card_univ] at h2
  rw [← Nat.cast_smul_eq_nsmul k, smul_eq_zero] at h2
  exact h2.resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem UpperTheory.V.Hi.propCker :
    ∀ (G : Type) [Group G] (I : Iwa G) (k M : Type) [Field k] [CharZero k] [AddCommGroup M] [Module k M] (π : Representation k G M), I.Smooth π → ∀ v ∈ fixd π I.N, v ∈ I.jacKer π ↔ ∃ j : ℕ, (I.uOp π I.z ^ j) v = 0 := by
  intro G _ I k M _ _ _ _ π hsm v hv
  have mul : ∀ (g h : G) (w : M), π g (π h w) = π (g * h) w := fun g h w => by
    rw [map_mul π g h, mul_apply_eq_comp]
  have hz : ∀ j : ℕ, I.z ^ j ∈ I.P := fun j => pow_mem I.z_mem j
  have hpow : ∀ j : ℕ, (I.uOp π I.z ^ j) v = I.uOp π (I.z ^ j) v := by
    intro j
    induction j with
    | zero => simpa using (uOpMul G I k M π 1 1 (one_mem _) (one_mem _) v hv).2.2.1.symm
    | succ j ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, pow_succ',
        (uOpMul G I k M π _ _ I.z_mem (hz j) v hv).2.1]
  simp only [hpow]
  constructor
  · intro h
    let ρ : Representation k I.N M := π.comp I.N.subtype
    let J : Submodule k M := Submodule.span k {w | ∃ x m, w = ρ x m - m}
    have key : ∃ j0 : ℕ, ∀ j ≥ j0, π (I.z ^ j) v ∈ J := by
      clear hv hpow
      induction h using Submodule.span_induction with
      | mem w h =>
        obtain ⟨x, hx, m, rfl⟩ := h
        obtain ⟨j0, h0⟩ := I.exh x hx
        refine ⟨j0, fun j hj => ?_⟩
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hj
        have h1 := I.P_N _ (hz d) _ h0
        refine Submodule.subset_span ⟨⟨_, h1⟩, π (I.z ^ (d + j0)) m, ?_⟩
        show _ = π _ _ - _
        rw [map_sub, mul, mul]
        congr 3
        simp only [Subgroup.subtype_apply]
        group
      | zero => exact ⟨0, fun j _ => by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨j1, h1⟩ := ha
        obtain ⟨j2, h2⟩ := hb
        refine ⟨max j1 j2, fun j hj => ?_⟩
        rw [map_add (f := _)]
        exact add_mem (h1 j (le_of_max_le_left hj)) (h2 j (le_of_max_le_right hj))
      | smul c a _ ha =>
        obtain ⟨j1, h1⟩ := ha
        refine ⟨j1, fun j hj => ?_⟩
        rw [map_smul]
        exact Submodule.smul_mem _ _ (h1 j hj)
    obtain ⟨j, hj⟩ := key
    have hj := hj j le_rfl
    refine ⟨j, propCker_avg ρ ?_ ?_ ?_⟩
    · intro m
      obtain ⟨c, hc, -⟩ := hsm m
      exact ⟨(I.Nconj (I.z ^ c)).subgroupOf I.N, ⟨I.fin_N _ (hz c)⟩, fun x hx => hc x hx⟩
    · have hfin : ((I.Nconj (I.z ^ j)).subgroupOf I.N).FiniteIndex := ⟨I.fin_N _ (hz j)⟩
      have : Fintype (I.N ⧸ (I.Nconj (I.z ^ j)).subgroupOf I.N) := Fintype.ofFinite _
      rw [Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun q _ => ?_
      have h1 : ρ q.out (π (I.z ^ j) v) - π (I.z ^ j) v ∈ J := Submodule.subset_span ⟨_, _, rfl⟩
      have h2 := add_mem h1 hj
      rw [sub_add_cancel] at h2
      rw [← mul]
      exact h2
    · intro x
      exact (uOpMul G I k M π _ 1 (hz j) (one_mem _) v hv).1 x x.2
  · rintro ⟨j, hj⟩
    have h1 := propCp G I k M π _ (hz j) v hv
    rw [hj, zero_sub, neg_mem_iff, Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 (I.fin_N _ (hz j)))] at h1
    have stab : ∀ t ∈ I.Tf, ∀ w ∈ I.jacKer π, π t w ∈ I.jacKer π := by
      intro t ht w hw
      induction hw using Submodule.span_induction with
      | mem w h =>
        obtain ⟨x, hx, m, rfl⟩ := h
        refine Submodule.subset_span ⟨_, I.Tf_Nf t ht x hx, π t m, ?_⟩
        rw [map_sub, mul, mul]
        congr 3
        group
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _)]; exact add_mem ha hb
      | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
    have h2 := stab _ (inv_mem (I.P_le _ (hz j))) _ h1
    rwa [mul, inv_mul_cancel, map_one, one_apply_eq_self] at h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem uOpLevel_mem {G : Type} [Group G] (I : Iwa G) (a x : G) :
    x ∈ I.Nconj a ↔ a⁻¹ * x * a ∈ I.N := by
  constructor
  · intro h
    obtain ⟨n, hn, e⟩ := Subgroup.mem_map.1 h
    have e2 : a * n * a⁻¹ = x := e
    have : a⁻¹ * x * a = n := by rw [← e2]; group
    rwa [this]
  · intro h
    refine Subgroup.mem_map.2 ⟨_, h, ?_⟩
    show a * (a⁻¹ * x * a) * a⁻¹ = x
    group

private theorem uOpLevel_core {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M]
    [Module A M] (π : Representation A G M) (c : ℕ) {a : G} (ha : a ∈ I.P) {v : M} (hN : v ∈ fixd π I.N)
    (hT : v ∈ fixd π (I.Tc c)) (hm : ∀ y ∈ I.Nm c, π (a⁻¹ * y * a) v = v) :
    I.uOp π a v ∈ fixd π (I.Nm c) := by
  classical
  intro y hy
  have mul : ∀ (g h : G) (w : M), π (g * h) w = π g (π h w) := fun g h w => by
    rw [map_mul π g h, Module.End.mul_apply]
  obtain ⟨⟨s, hs, hu⟩, h2⟩ := uOpSum G I A M π a ha
  have key : ∀ u : s, ∃ u' : s, ∃ k ∈ I.Iw c, π k v = v ∧ y * (u * a) = u' * a * k := by
    intro u
    obtain ⟨x, hx, t, ht, y', hy', e⟩ := I.swap c y hy u (hs _ u.2)
    obtain ⟨u', ⟨hu', hx'⟩, -⟩ := hu x hx
    rw [uOpLevel_mem] at hx'
    have hc : t * a = a * t := I.comm t (I.T_le (I.Tc_le c ht)) a (I.P_le a ha)
    refine ⟨⟨u', hu'⟩, (a⁻¹ * (u'⁻¹ * x) * a) * t * (a⁻¹ * y' * a),
      (iwMem G I c _).1.2 ⟨_, hx', t, I.Tc_le c ht, _, I.P_Nm c a ha y' hy', rfl⟩, ?_, ?_⟩
    · rw [mul, hm y' hy', mul, hT t ht, hN _ hx']
    · have h2 : t = a * t * a⁻¹ := by rw [← hc]; group
      calc y * (u * a) = (y * u) * a := by group
        _ = x * (a * t * a⁻¹) * y' * a := by rw [e, ← h2]
        _ = _ := by simp only []; group
  choose σ k hk hkv he using key
  have inj : Function.Injective σ := by
    intro u w h
    have e : a⁻¹ * ((u : G)⁻¹ * w) * a = (k u)⁻¹ * k w := by
      calc a⁻¹ * ((u : G)⁻¹ * w) * a = (y * (u * a))⁻¹ * (y * (w * a)) := by group
        _ = _ := by rw [he u, he w, h]; group
    have h1 : a⁻¹ * ((u : G)⁻¹ * w) * a ∈ I.Nf := by
      simpa using I.Tf_Nf a⁻¹ (inv_mem (I.P_le a ha)) _
        (I.N_le (mul_mem (inv_mem (hs _ u.2)) (hs _ w.2)))
    have h3 := (iwMem G I c _).2.2 h1 (e ▸ mul_mem (inv_mem (hk u)) (hk w))
    exact Subtype.ext ((hu w (hs _ w.2)).unique ⟨u.2, (uOpLevel_mem I a _).2 h3⟩ ⟨w.2, by simp⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [(h2 s hs hu).2 v hN, map_sum, ← Finset.sum_coe_sort s, ← Finset.sum_coe_sort s,
    ← (Finite.injective_iff_bijective.1 inj).sum_comp (fun u : s => π (u * a) v)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← mul, he u, mul, hkv u]

private theorem fixed_pro_unipotent_iff {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M]
    [Module A M] (π : Representation A G M) (c : ℕ) (v : M) :
    v ∈ fixd π (I.I1 c) ↔ v ∈ fixd π I.N ∧ v ∈ fixd π (I.Tc c) ∧ v ∈ fixd π (I.Nm c) := by
  constructor
  · intro h
    exact ⟨fun u hu => h u (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu)),
      fun u hu => h u (Subgroup.mem_sup_left (Subgroup.mem_sup_right hu)),
      fun u hu => h u (Subgroup.mem_sup_right hu)⟩
  · rintro ⟨h1, h2, h3⟩ g hg
    obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := (iwMem G I c g).2.1.1 hg
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h3 y hy, h2 t ht, h1 x hx]

theorem UpperTheory.V.Hi.uOpLevel :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (c : ℕ), (∀ a ∈ I.P, ∀ v ∈ fixd π (I.I1 c), I.uOp π a v ∈ fixd π (I.I1 c)) ∧ (∀ v, v ∈ fixd π I.N → v ∈ fixd π (I.Tc c) → v ∈ fixd π (I.Nm (c + 1)) → I.uOp π I.z v ∈ fixd π (I.I1 c)) ∧ ∀ φ : I.T →* Aˣ, (∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) → (∀ a ∈ I.P, ∀ v ∈ I.eig π c φ, I.uOp π a v ∈ I.eig π c φ) ∧ ∀ v ∈ I.eig π (c + 1) φ, I.uOp π I.z v ∈ I.eig π c φ := by
  intro G _ I A M _ _ _ π c
  have gen : ∀ a ∈ I.P, ∀ v, v ∈ fixd π I.N → v ∈ fixd π (I.Tc c) → (∀ y ∈ I.Nm c, π (a⁻¹ * y * a) v = v) →
      I.uOp π a v ∈ fixd π (I.I1 c) := by
    intro a ha v hN hT hm
    obtain ⟨h1, -, -, h2, -⟩ := uOpMul G I A M π a a ha ha v hN
    exact (fixed_pro_unipotent_iff I π c _).2 ⟨h1, fun t ht => by rw [h2 t (I.Tc_le c ht), hT t ht],
      uOpLevel_core I π c ha hN hT hm⟩
  refine ⟨fun a ha v hv => ?_, fun v hN hT hm => gen _ I.z_mem v hN hT fun y hy => hm _ (I.z_Nm c y hy),
    fun φ hφ => ?_⟩
  · obtain ⟨hN, hT, hm⟩ := (fixed_pro_unipotent_iff I π c v).1 hv
    exact gen a ha v hN hT fun y hy => hm _ (I.P_Nm c a ha y hy)
  · have gen' : ∀ a ∈ I.P, ∀ v, v ∈ fixd π I.N → (∀ t : I.T, π t v = (((φ t)⁻¹ : Aˣ) : A) • v) →
        (∀ y ∈ I.Nm c, π (a⁻¹ * y * a) v = v) → I.uOp π a v ∈ I.eig π c φ := by
      intro a ha v hN hT hm
      have hT' : v ∈ fixd π (I.Tc c) := fun t ht => by
        have := hT ⟨t, I.Tc_le c ht⟩
        rw [hφ _ ht] at this
        simpa using this
      obtain ⟨h1, -, -, h2, -⟩ := uOpMul G I A M π a a ha ha v hN
      exact ⟨h1, uOpLevel_core I π c ha hN hT' hm, fun t => by rw [h2 t t.2, hT t, map_smul]⟩
    exact ⟨fun a ha v hv => gen' a ha v hv.1 hv.2.2 fun y hy => hv.2.1 _ (I.P_Nm c a ha y hy),
      fun v hv => gen' _ I.z_mem v hv.1 hv.2.2 fun y hy => hv.2.1 _ (I.z_Nm c y hy)⟩
end

