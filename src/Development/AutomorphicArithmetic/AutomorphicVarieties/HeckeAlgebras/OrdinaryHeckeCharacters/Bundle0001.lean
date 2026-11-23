module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CtrlEq
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem UpperTheory.V.Hi.ctrlEq_row {G : Type} [Group G] {I : Iwa G} {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω]
    [Algebra O Ω] (W : WtRep I O Ω) (g x : G) (hx : x ∈ I.Nf) (t : I.Tf) (v : Fin (W.d + 1) → Ω) :
    (((W.ξ (g * (x * t)))⁻¹).val *ᵥ v) 0 = (((W.χ t)⁻¹ : Ωˣ) : Ω) * (((W.ξ g)⁻¹).val *ᵥ v) 0 := by
  have h1 : ∀ w : Fin (W.d + 1) → Ω, ((W.ξ x⁻¹).val *ᵥ w) 0 = w 0 := by
    intro w
    have := W.row_N x⁻¹ (inv_mem hx)
    simp only [mulVec, dotProduct]
    simp_rw [this]
    simp
  have h2 : ∀ w : Fin (W.d + 1) → Ω, ((W.ξ ((t⁻¹ : I.Tf) : G)).val *ᵥ w) 0 = (W.χ t⁻¹ : Ω) * w 0 := by
    intro w
    have := W.torusAction t⁻¹
    simp only [mulVec, dotProduct]
    simp_rw [this]
    simp
  have h3 : (W.ξ (g * (x * t)))⁻¹ = W.ξ ((t⁻¹ : I.Tf) : G) * (W.ξ x⁻¹ * (W.ξ g)⁻¹) := by
    simp [mul_assoc]
  rw [h3, Units.val_mul, Units.val_mul, ← mulVec_mulVec, h2, ← mulVec_mulVec, h1, map_inv]

theorem UpperTheory.V.Hi.ctrlEq :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) Ω), (∀ u F, X.ctrl m W (X.raF (W.d + 1) τ u F) = X.ra τ u (X.ctrl m W F)) ∧ (∀ (a : X.I.P) F, X.ctrl m W (X.UF m W a F) = X.U Ω m a (X.ctrl m W F)) ∧ (∀ u (b : Gp) F, X.raF (W.d + 1) τ u (X.rpF Ω (W.d + 1) m b F) = X.rpF Ω (W.d + 1) m b (X.raF (W.d + 1) τ u F)) := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ
  refine ⟨fun u F => ?_, fun a F => ?_, fun u b F => ?_⟩
  · ext g i
    change (((W.ξ g.2)⁻¹).val *ᵥ fun k => ((τ u).val *ᵥ fun j => F j (g * ((u : Ga), 1)) k) i) 0 =
      ((τ u).val *ᵥ fun j => (((W.ξ (g * ((u : Ga), 1)).2)⁻¹).val *ᵥ F j (g * ((u : Ga), 1))) 0) i
    simp only [mulVec, dotProduct, Prod.snd_mul, mul_one, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  · haveI : Finite (X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N) :=
      Nat.finite_of_card_ne_zero (X.I.fin_N a a.2)
    haveI := Fintype.ofFinite (X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Frame.UF, Frame.U, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ext g i
    have := UpperTheory.V.Hi.ctrlEq_row W g.2 (q.out : X.I.N) (X.I.N_le q.out.2) ⟨a, X.I.P_le a a.2⟩
      (F i (g * (1, ((q.out : X.I.N) : Gp) * a)))
    exact this.symm
  · ext i g k
    change ((τ u).val *ᵥ fun j => F j (g * ((u : Ga), 1) * (1, b)) k) i =
      ((τ u).val *ᵥ fun j => F j (g * (1, b) * ((u : Ga), 1)) k) i
    simp [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcGelfand
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem dcG_mem {H : Type} [Group H] (K : Subgroup H) (x p : H) :
    (p : H ⧸ K) ∈ MulAction.orbit K (x : H ⧸ K) ↔ ∃ k ∈ K, ∃ k' ∈ K, p = k * x * k' := by
  constructor
  · rintro ⟨k, hk⟩
    have h : (((k : H) * x : H) : H ⧸ K) = (p : H ⧸ K) := hk
    exact ⟨k, k.2, _, QuotientGroup.eq.mp h, by group⟩
  · rintro ⟨k, hk, k', hk', rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    change ((k * x : H) : H ⧸ K) = _
    exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hk')

private theorem dcG_sum {α β γ M : Type} [AddCommMonoid M] [DecidableEq γ] (s : Finset α) (t : Finset β)
    (F : α → γ) (G : β → γ) (g : γ → M)
    (h : ∀ r, (s.filter fun a => F a = r).card = (t.filter fun b => G b = r).card) :
    ∑ a ∈ s, g (F a) = ∑ b ∈ t, g (G b) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image F ∪ t.image G) (g := F)
      (fun a ha => Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)),
    ← Finset.sum_fiberwise_of_maps_to (s := t) (t := s.image F ∪ t.image G) (g := G)
      (fun a ha => Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g r) (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
    Finset.sum_congr rfl (s₁ := t.filter fun b => G b = r) (g := fun _ => g r)
      (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
    Finset.sum_const, Finset.sum_const, h]

open Classical in
private theorem dcG_le {H : Type} [Group H] (K : Subgroup H) (s : H → H)
    (hmul : ∀ x y, s (x * y) = s y * s x) (hss : ∀ x, s (s x) = x) (hK : ∀ k ∈ K, s k ∈ K)
    (hd : ∀ x, ∃ k ∈ K, ∃ k' ∈ K, s x = k * x * k')
    (hfin : ∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) (x y : H) (r : H ⧸ K) :
    (((hfin x).toFinset ×ˢ (hfin y).toFinset).filter fun a => a.1.out • a.2 = r).card ≤
      (((hfin y).toFinset ×ˢ (hfin x).toFinset).filter fun a => a.1.out • a.2 = r).card := by
  have h1 : s 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have hinv : ∀ a, s a⁻¹ = (s a)⁻¹ := fun a => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hmul, mul_inv_cancel, h1]
  have hD : ∀ x p : H, (∃ k ∈ K, ∃ k' ∈ K, p = k * x * k') → ∀ a ∈ K, ∀ b ∈ K,
      ∃ k ∈ K, ∃ k' ∈ K, a * s p * b = k * x * k' := by
    rintro x p ⟨k, hk, k', hk', hp⟩ a ha b hb
    obtain ⟨l, hl, l', hl', h⟩ := hd p
    exact ⟨a * l * k, mul_mem (mul_mem ha hl) hk, k' * l' * b, mul_mem (mul_mem hk' hl') hb, by
      rw [h, hp]; group⟩
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective r
  obtain ⟨k, hk, k', hk', hz⟩ := hd z
  let φ : H ⧸ K → H ⧸ K := fun p => ((k⁻¹ * s (p.out⁻¹ * z) * 1 : H) : H ⧸ K)
  refine Finset.card_le_card_of_injOn (fun a => (φ a.1, (φ a.1).out⁻¹ • (z : H ⧸ K))) ?_ ?_
  · rintro ⟨p, q⟩ ha
    simp only [Finset.coe_filter, Finset.mem_product, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at ha ⊢
    obtain ⟨⟨hp, hq⟩, hpq⟩ := ha
    have hq' : q = ((p.out⁻¹ * z : H) : H ⧸ K) := by
      change q = p.out⁻¹ • (z : H ⧸ K)
      rw [← hpq, inv_smul_smul]
    refine ⟨⟨?_, ?_⟩, smul_inv_smul _ _⟩
    · rw [hq', dcG_mem] at hq
      exact (dcG_mem K _ _).mpr (hD _ _ hq _ (inv_mem hk) _ (one_mem _))
    · rw [← QuotientGroup.out_eq' p, dcG_mem] at hp
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (k⁻¹ * s (p.out⁻¹ * z) * 1)
      change (((φ p).out⁻¹ * z : H) : H ⧸ K) ∈ _
      have : (φ p).out⁻¹ * z = (m : H)⁻¹ * s p.out * k'⁻¹ := by
        simp only [φ]
        rw [hm, hmul, hinv, hz]
        group
      rw [this]
      exact (dcG_mem K _ _).mpr (hD _ _ hp _ (inv_mem m.2) _ (inv_mem hk'))
  · rintro ⟨p, q⟩ ha ⟨p', q'⟩ ha' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha ha'
    have h2 : φ p = φ p' := congrArg Prod.fst h
    have h3 := hK _ (QuotientGroup.eq.mp h2)
    have h4 : (k⁻¹ * s (p.out⁻¹ * z) * 1)⁻¹ * (k⁻¹ * s (p'.out⁻¹ * z) * 1) = s (p'.out⁻¹ * p.out) := by
      rw [hmul, hmul, hmul, hinv, hinv]
      group
    rw [h4, hss] at h3
    have h5 : p' = p := by
      rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' p']
      exact QuotientGroup.eq.mpr h3
    subst h5
    have h6 : q = q' := smul_left_cancel p'.out (ha.2.trans ha'.2.symm)
    rw [h6]

private theorem dcG_two {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H)
    (hfin : ∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) (x y : H) (v : M) (hv : v ∈ fixd ρ K) :
    dc ρ K K x (dc ρ K K y v) =
      ∑ a ∈ (hfin x).toFinset ×ˢ (hfin y).toFinset, ρ (a.1.out • a.2 : H ⧸ K).out v := by
  have h : ∀ (x : H) (w : M), dc ρ K K x w = ∑ p ∈ (hfin x).toFinset, ρ p.out w := by
    intro x w
    rw [dc, finsum_set_coe_eq_finsum_mem (f := fun q : H ⧸ K => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ (hfin x),
      LinearMap.sum_apply]
  rw [h, h, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (p.out * q.out)
  have h2 : (p.out • q : H ⧸ K) = ((p.out * q.out : H) : H ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h2, hm, map_mul, map_mul]
  simp only [Module.End.mul_apply]
  rw [hv m m.2]

theorem UpperTheory.V.Hi.dcGelfand :
    ∀ (A H M : Type) [CommRing A] [Group H] [AddCommGroup M] [Module A M] (ρ : Representation A H M) (K : Subgroup H) (s : H → H), (∀ x y, s (x * y) = s y * s x) → (∀ x, s (s x) = x) → (∀ k ∈ K, s k ∈ K) → (∀ x, ∃ k ∈ K, ∃ k' ∈ K, s x = k * x * k') → (∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) → (∀ x : H, (MulAction.orbit K (x : H ⧸ K)).ncard = (MulAction.orbit K ((x⁻¹ : H) : H ⧸ K)).ncard) → ∀ x y, ∀ v ∈ fixd ρ K, dc ρ K K x (dc ρ K K y v) = dc ρ K K y (dc ρ K K x v) := by
  intro A H M _ _ _ _ ρ K s hmul hss hK hd hfin _ x y v hv
  classical
  rw [dcG_two ρ K hfin x y v hv, dcG_two ρ K hfin y x v hv]
  refine dcG_sum _ _ (fun a : (H ⧸ K) × (H ⧸ K) => a.1.out • a.2) (fun a : (H ⧸ K) × (H ⧸ K) => a.1.out • a.2)
    (fun r => ρ r.out v) fun r => ?_
  apply le_antisymm
  · convert dcG_le K s hmul hss hK hd hfin x y r
  · convert dcG_le K s hmul hss hK hd hfin y x r
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem dcSum_eq_of_mk {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K' : Subgroup H) {v : M} (hv : v ∈ fixd ρ K') {y z : H}
    (h : (y : H ⧸ K') = (z : H ⧸ K')) : ρ y v = ρ z v := by
  have h1 : y⁻¹ * z ∈ K' := QuotientGroup.eq.mp h
  have h2 : ρ (y⁻¹ * z) v = v := hv _ h1
  calc ρ y v = ρ y (ρ (y⁻¹ * z) v) := by rw [h2]
    _ = ρ (y * (y⁻¹ * z)) v := by rw [map_mul ρ y]; rfl
    _ = ρ z v := by rw [mul_inv_cancel_left]

private theorem dcSum_apply {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H)
    [Fintype (MulAction.orbit K (x : H ⧸ K'))] (v : M) :
    dc ρ K K' x v = ∑ q : MulAction.orbit K (x : H ⧸ K'), ρ (q : H ⧸ K').out v := by
  rw [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

theorem UpperTheory.V.Hi.dcSum :
    ∀ (A H M : Type) [CommRing A] [Group H] [AddCommGroup M] [Module A M] (ρ : Representation A H M) (K K' : Subgroup H) (x : H), (MulAction.orbit K (x : H ⧸ K')).Finite → (∀ s : Finset H, (∀ y ∈ s, (y : H ⧸ K') ∈ MulAction.orbit K (x : H ⧸ K')) → (∀ q ∈ MulAction.orbit K (x : H ⧸ K'), ∃! y, y ∈ s ∧ (y : H ⧸ K') = q) → ∀ v ∈ fixd ρ K', dc ρ K K' x v = ∑ y ∈ s, ρ y v) ∧ (∀ v ∈ fixd ρ K', dc ρ K K' x v ∈ fixd ρ K) ∧ (∀ V : Subgroup H, (∀ u ∈ V, u * x = x * u ∧ ∀ k ∈ K, u * k = k * u) → ∀ v ∈ fixd ρ K', v ∈ fixd ρ V → dc ρ K K' x v ∈ fixd ρ V) ∧ ∀ (A' M' : Type) [CommRing A'] [AddCommGroup M'] [Module A' M'] (ρ' : Representation A' H M') (f : M →+ M'), (∀ h v, f (ρ h v) = ρ' h (f v)) → ∀ v, f (dc ρ K K' x v) = dc ρ' K K' x (f v) := by
  intro A H M _ _ _ _ ρ K K' x hfin
  letI : Fintype (MulAction.orbit K (x : H ⧸ K')) := hfin.fintype
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs hu v hv
    rw [dcSum_apply]
    symm
    refine Finset.sum_bij (fun y hy => (⟨(y : H ⧸ K'), hs y hy⟩ : MulAction.orbit K (x : H ⧸ K')))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro y hy z hz h
      have h' : (y : H ⧸ K') = (z : H ⧸ K') := congrArg Subtype.val h
      exact (hu _ (hs z hz)).unique ⟨hy, h'⟩ ⟨hz, rfl⟩
    · intro q _
      obtain ⟨y, ⟨hy, hq⟩, -⟩ := hu q.1 q.2
      exact ⟨y, hy, Subtype.ext hq⟩
    · intro y hy
      exact dcSum_eq_of_mk ρ K' hv (QuotientGroup.out_eq' _).symm
  · intro v hv u hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dcSum_apply, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨u, hu⟩ : K)) _ _ ?_
    intro q
    have : ρ u (ρ (q : H ⧸ K').out v) = ρ (u * (q : H ⧸ K').out) v := by rw [map_mul]; rfl
    rw [this]
    apply dcSum_eq_of_mk ρ K' hv
    rw [QuotientGroup.out_eq']
    change _ = u • (q : H ⧸ K')
    conv_rhs => rw [← QuotientGroup.out_eq' (q : H ⧸ K')]
    rfl
  · intro V hV v hv hvV u hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dcSum_apply, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨q, k, hk⟩ _
    have h1 : ρ q.out v = ρ ((k : H) * x) v := by
      apply dcSum_eq_of_mk ρ K' hv
      rw [QuotientGroup.out_eq', ← hk]
      rfl
    have h2 : u * ((k : H) * x) = ((k : H) * x) * u := by
      rw [← mul_assoc, (hV u hu).2 k k.2, mul_assoc, (hV u hu).1, mul_assoc]
    change ρ u (ρ q.out v) = ρ q.out v
    rw [h1]
    calc ρ u (ρ ((k : H) * x) v) = ρ (u * ((k : H) * x)) v := by rw [map_mul ρ u]; rfl
      _ = ρ ((k : H) * x) (ρ u v) := by rw [h2, map_mul ρ _ u]; rfl
      _ = _ := by rw [hvV u hu]
  · intro A' M' _ _ _ ρ' f hf v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dcSum_apply, dcSum_apply, map_sum]
    exact Finset.sum_congr rfl fun q _ => hf _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.FnIndep
section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.fnIndep :
    ∀ (O Ω S ι : Type) [CommRing O] [IsDomain O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ (m : ℕ) (v : ι → S → Fin m → O), LinearIndependent O v → LinearIndependent Ω fun i s j => algebraMap O Ω (v i s j) := by
  intro O Ω S ι _ _ _ _ hinj m v hv
  classical
  letI : Algebra (FractionRing O) Ω := (IsFractionRing.lift hinj).toAlgebra
  have htow : ∀ x : O, algebraMap O Ω x =
      algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) x) :=
    fun x => (IsFractionRing.lift_algebraMap hinj x).symm
  have hu : LinearIndependent (FractionRing O)
      (fun i s j => algebraMap O (FractionRing O) (v i s j)) := by
    rw [← LinearIndependent.iff_fractionRing O (FractionRing O)]
    have hf : Function.Injective
        (((Algebra.linearMap O (FractionRing O)).compLeft (Fin m)).compLeft S) := by
      intro a c hac
      funext s j
      exact IsFractionRing.injective O (FractionRing O) (congrFun (congrFun hac s) j)
    exact hv.map' _ (LinearMap.ker_eq_bot.mpr hf)
  let b := Module.Free.chooseBasis (FractionRing O) Ω
  rw [linearIndependent_iff'] at hu ⊢
  intro s g hg i hi
  refine b.ext_elem fun k => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine hu s (fun i => b.repr (g i) k) ?_ i hi
  funext x y
  have h := congrFun (congrFun hg x) y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
  have h2 := congrArg (fun z => b.repr z k) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zero, Finsupp.zero_apply, Finset.sum_apply'] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : g i * algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) (v i x y)) =
      algebraMap O (FractionRing O) (v i x y) • g i := by
    rw [Algebra.smul_def, mul_comm]
  rw [htow, e, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem iwMem_mul {G : Type} [Group G] (I : Iwa G) (c : ℕ) (S : Subgroup G) (hS : S ≤ I.T)
    (hc : I.Tc c ≤ S) {a b : G} (ha : ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, a = x * t * y)
    (hb : ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, b = x * t * y) :
    ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, a * b = x * t * y := by
  obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := ha
  obtain ⟨x', hx', t', ht', y', hy', rfl⟩ := hb
  obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := I.swap c y hy x' hx'
  refine ⟨x * (t * x2 * t⁻¹), mul_mem hx (I.T_N t (hS ht) x2 hx2), t * s * t',
    mul_mem (mul_mem ht (hc hs)) ht', (t'⁻¹ * y2 * t'⁻¹⁻¹) * y',
    mul_mem (I.T_Nm c t'⁻¹ (inv_mem (hS ht')) y2 hy2) hy', ?_⟩
  calc x * t * y * (x' * t' * y') = x * t * (y * x') * t' * y' := by group
    _ = x * t * (x2 * s * y2) * t' * y' := by rw [h]
    _ = _ := by group

private theorem iwMem_gen {G : Type} [Group G] (I : Iwa G) (c : ℕ) (S : Subgroup G) (hS : S ≤ I.T)
    (hc : I.Tc c ≤ S) (g : G) :
    g ∈ I.N ⊔ S ⊔ I.Nm c ↔ ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, g = x * t * y := by
  constructor
  · intro hg
    have hN : ∀ x ∈ I.N, ∃ x' ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, x = x' * t * y :=
      fun x hx => ⟨x, hx, 1, S.one_mem, 1, (I.Nm c).one_mem, by simp⟩
    have hT : ∀ t ∈ S, ∃ x ∈ I.N, ∃ t' ∈ S, ∃ y ∈ I.Nm c, t = x * t' * y :=
      fun t ht => ⟨1, I.N.one_mem, t, ht, 1, (I.Nm c).one_mem, by simp⟩
    have hY : ∀ y ∈ I.Nm c, ∃ x ∈ I.N, ∃ t ∈ S, ∃ y' ∈ I.Nm c, y = x * t * y' :=
      fun y hy => ⟨1, I.N.one_mem, 1, S.one_mem, y, hy, by simp⟩
    let M : Subgroup G :=
      { carrier := {g | ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, g = x * t * y}
        mul_mem' := fun ha hb => iwMem_mul I c S hS hc ha hb
        one_mem' := hN 1 I.N.one_mem
        inv_mem' := by
          rintro g ⟨x, hx, t, ht, y, hy, rfl⟩
          have e : (x * t * y)⁻¹ = y⁻¹ * t⁻¹ * x⁻¹ := by group
          rw [e]
          exact iwMem_mul I c S hS hc
            (iwMem_mul I c S hS hc (hY _ ((I.Nm c).inv_mem hy)) (hT _ (S.inv_mem ht)))
            (hN _ (I.N.inv_mem hx)) }
    have hle : I.N ⊔ S ⊔ I.Nm c ≤ M :=
      sup_le (sup_le (fun x hx => hN x hx) (fun t ht => hT t ht)) (fun y hy => hY y hy)
    exact hle hg
  · rintro ⟨x, hx, t, ht, y, hy, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right ht))) (Subgroup.mem_sup_right hy)

theorem UpperTheory.V.Hi.iwMem :
    ∀ (G : Type) [Group G] (I : Iwa G) (c : ℕ) (g : G), (g ∈ I.Iw c ↔ ∃ x ∈ I.N, ∃ t ∈ I.T, ∃ y ∈ I.Nm c, g = x * t * y) ∧ (g ∈ I.I1 c ↔ ∃ x ∈ I.N, ∃ t ∈ I.Tc c, ∃ y ∈ I.Nm c, g = x * t * y) ∧ (g ∈ I.Nf → g ∈ I.Iw c → g ∈ I.N) := by
  intro G _ I c g
  refine ⟨iwMem_gen I c I.T le_rfl (I.Tc_le c) g,
    iwMem_gen I c (I.Tc c) (I.Tc_le c) le_rfl g, ?_⟩
  intro hg hw
  obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := (iwMem_gen I c I.T le_rfl (I.Tc_le c) _).1 hw
  have hy0 : y ∈ I.Nm 0 := I.Nm_anti (Nat.zero_le c) hy
  have h := I.uniq ((x * t * y)⁻¹ * x) (I.Nf.mul_mem (I.Nf.inv_mem hg) (I.N_le hx)) t
    (I.T_le ht) y hy0 (by group)
  have e : x * t * y = x := by
    calc x * t * y = x * ((x * t * y)⁻¹ * x)⁻¹ := by group
      _ = x := by rw [h.1]; group
  rw [e]
  exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdLevel
section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.ordLevel :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ U V : Subgroup X.Ub, V ≤ U → V.relIndex U ≠ 0 → X.FinLevel U → X.Free τ θ U → X.FinLevel V ∧ X.Free τ θ V ∧ X.Ord τ θ U = X.Ord τ θ V ⊓ fixd (X.ra τ) U := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθ U V hVU hidx hU hF
  refine ⟨?_, ?_, ?_⟩
  · classical
    unfold Frame.FinLevel at hU ⊢
    obtain ⟨s, hs⟩ := hU
    haveI : (V.subgroupOf U).FiniteIndex := ⟨hidx⟩
    haveI : Fintype (U ⧸ V.subgroupOf U) := Fintype.ofFinite _
    refine ⟨(s ×ˢ (Finset.univ : Finset (U ⧸ V.subgroupOf U))).image
      (fun p => p.1 * ((((Quotient.out p.2 : U) : X.Ub) : Ga), (1 : Gp))), ?_⟩
    intro g
    obtain ⟨γ, x, hx, u, hu, b, hb, rfl⟩ := hs g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf U) (⟨u, hu⟩ : U)
    have hmem : (x, (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ V.subgroupOf U)) ∈
        s ×ˢ (Finset.univ : Finset (U ⧸ V.subgroupOf U)) :=
      Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩
    refine ⟨γ, _, Finset.mem_image_of_mem _ hmem,
      ((h⁻¹ : V.subgroupOf U) : U), Subgroup.mem_subgroupOf.mp (h⁻¹).2, b, hb, ?_⟩
    simp only at hh ⊢
    rw [hh]
    simp [Prod.ext_iff, mul_assoc]
  · unfold Frame.Free at hF ⊢
    intro g γ u hu b hb h
    exact hF g γ u (hVU hu) b hb h
  · have hfix : fixd (X.ra τ) U ≤ fixd (X.ra τ) V := by
      unfold fixd
      intro f hf u hu
      exact hf u (hVU hu)
    unfold Frame.Ord Frame.Sp
    apply le_antisymm
    · intro f hf
      simp only [Submodule.mem_inf] at hf ⊢
      exact ⟨⟨⟨hf.1.1, hfix hf.1.2⟩, hf.2⟩, hf.1.2⟩
    · intro f hf
      simp only [Submodule.mem_inf] at hf ⊢
      exact ⟨⟨hf.1.1.1, hf.2⟩, hf.1.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCp
section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.propCp :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a : G), a ∈ I.P → ∀ v ∈ fixd π I.N, I.uOp π a v - ((I.Nconj a).relIndex I.N : A) • π a v ∈ I.jacKer π := by
  intro G _ I A M _ _ _ π a ha v _
  have hfin : ((I.Nconj a).subgroupOf I.N).FiniteIndex := ⟨I.fin_N a ha⟩
  haveI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _
  have hc : (I.Nconj a).relIndex I.N = Fintype.card (I.N ⧸ (I.Nconj a).subgroupOf I.N) := by
    rw [← Nat.card_eq_fintype_card]; rfl
  have hs : (((I.Nconj a).relIndex I.N : ℕ) : A) • π a v
      = ∑ _q : I.N ⧸ (I.Nconj a).subgroupOf I.N, π a v := by
    rw [Finset.sum_const, Finset.card_univ, hc, Nat.cast_smul_eq_nsmul]
  rw [hs, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_
  refine ⟨(q.out : I.N), I.N_le (q.out).2, π a v, ?_⟩
  rw [map_mul]; rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpNat
section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.uOpNat :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (A' M' : Type) [CommRing A'] [AddCommGroup M'] [Module A' M'] (π' : Representation A' G M') (f : M →+ M') (a : G), a ∈ I.P → ∀ v, (∀ u ∈ I.N, f (π (u * a) v) = π' (u * a) (f v)) → f (I.uOp π a v) = I.uOp π' a (f v) := by
  intro G _ I A M _ _ _ π A' M' _ _ _ π' f a ha v hv
  have hfin : Finite (↥I.N ⧸ (I.Nconj a).subgroupOf I.N) :=
    Subgroup.index_ne_zero_iff_finite.mp (I.fin_N a ha)
  have _ := Fintype.ofFinite (↥I.N ⧸ (I.Nconj a).subgroupOf I.N)
  unfold Iwa.uOp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun q _ => hv _ (Quotient.out q).2
end

