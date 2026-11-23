module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpSum

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwahoriProUnipotentFiniteIndex
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem relIndex_ne_zero_of_cover_ordinary_hecke_characters {G : Type} [Group G] (H K L : Subgroup G) (hHK : H ≤ K) (hLK : L ≤ K)
    (hcov : ∀ k ∈ K, ∃ l ∈ L, ∃ h ∈ H, k = l * h) (hfin : H.relIndex L ≠ 0) : H.relIndex K ≠ 0 := by
  haveI : (H.subgroupOf L).FiniteIndex := ⟨hfin⟩
  let f : L ⧸ H.subgroupOf L → K ⧸ H.subgroupOf K :=
    Quotient.map' (fun l => (⟨l, hLK l.2⟩ : K)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      simpa [Subgroup.mem_subgroupOf] using hab)
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨l, hl, h, hh, e⟩ := hcov k k.2
      refine ⟨QuotientGroup.mk ⟨l, hl⟩, ?_⟩
      show QuotientGroup.mk _ = QuotientGroup.mk k
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [e] using hh
  haveI := Finite.of_surjective f hf
  exact Subgroup.index_ne_zero_of_finite

private theorem iwahori_relIndex_ne_zero {G : Type} [Group G] (I : Iwa G) (c : ℕ) : (I.Iw c).relIndex (I.Iw 0) ≠ 0 := by
  have hNm : I.Nm c ≤ I.Iw c := le_sup_right
  have hT : I.T ≤ I.Iw c := le_trans le_sup_right le_sup_left
  have hN : I.N ≤ I.Iw c := le_trans le_sup_left le_sup_left
  refine relIndex_ne_zero_of_cover_ordinary_hecke_characters (I.Iw c) (I.Iw 0) (I.Nm 0) ?_ le_sup_right ?_ ?_
  · show I.N ⊔ I.T ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm 0
    exact sup_le_sup_left (I.Nm_anti (Nat.zero_le c)) _
  · intro g hg
    obtain ⟨x, hx, t, ht, y, hy, e⟩ := ((iwMem G I 0 g⁻¹).1).1 (inv_mem hg)
    refine ⟨y⁻¹, inv_mem hy, t⁻¹ * x⁻¹, mul_mem (hT (inv_mem ht)) (hN (inv_mem hx)), ?_⟩
    rw [← inv_inv g, e]
    group
  · intro h0
    apply I.fin_Nm c
    have hd := Subgroup.relIndex_dvd_of_le_left (I.Nm 0) hNm
    rw [h0] at hd
    exact Nat.eq_zero_of_zero_dvd hd

private theorem iwahori_pro_unipotent_finite_index {G : Type} [Group G] (I : Iwa G) (c : ℕ) : (I.I1 c).relIndex (I.Iw 0) ≠ 0 := by
  have hTc : I.Tc c ≤ I.I1 c := le_trans le_sup_right le_sup_left
  have hN1 : I.N ≤ I.I1 c := le_trans le_sup_left le_sup_left
  have hNm1 : I.Nm c ≤ I.I1 c := le_sup_right
  have hT : I.T ≤ I.Iw c := le_trans le_sup_right le_sup_left
  have hle : I.I1 c ≤ I.Iw c := by
    show I.N ⊔ I.Tc c ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm c
    exact sup_le_sup_right (sup_le_sup_left (I.Tc_le c) _) _
  have hle' : I.Iw c ≤ I.Iw 0 := by
    show I.N ⊔ I.T ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm 0
    exact sup_le_sup_left (I.Nm_anti (Nat.zero_le c)) _
  have h1 : (I.I1 c).relIndex (I.Iw c) ≠ 0 := by
    refine relIndex_ne_zero_of_cover_ordinary_hecke_characters (I.I1 c) (I.Iw c) I.T hle hT ?_ ?_
    · intro g hg
      obtain ⟨x, hx, t, ht, y, hy, e⟩ := ((iwMem G I c g).1).1 hg
      have hx' : t⁻¹ * x * t ∈ I.N := by
        simpa using I.T_N t⁻¹ (inv_mem ht) x hx
      refine ⟨t, ht, t⁻¹ * x * t * y, mul_mem (hN1 hx') (hNm1 hy), ?_⟩
      rw [e]
      group
    · intro h0
      apply I.fin_Tc c
      have hd := Subgroup.relIndex_dvd_of_le_left I.T hTc
      rw [h0] at hd
      exact Nat.eq_zero_of_zero_dvd hd
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle hle']
  exact mul_ne_zero h1 (iwahori_relIndex_ne_zero I c)

theorem UpperTheory.V.Hi.iwFin :
    ∀ (G : Type) [Group G] (I : Iwa G) (c : ℕ), (I.Iw c).relIndex (I.Iw 0) ≠ 0 ∧ (I.I1 c).relIndex (I.Iw 0) ≠ 0 := by
  intro G _ I c
  exact ⟨iwahori_relIndex_ne_zero I c, iwahori_pro_unipotent_finite_index I c⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem UpperTheory.V.Hi.uOpMul_mem {G : Type} [Group G] (I : Iwa G) (a x : G) :
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

private theorem UpperTheory.V.Hi.uOpMul_sum {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M]
    [Module A M] (π : Representation A G M) {a : G} (ha : a ∈ I.P) {ι : Type} (s : Finset ι) (f : ι → G)
    (hf : ∀ i ∈ s, f i ∈ I.N) (hu : ∀ x ∈ I.N, ∃! i, i ∈ s ∧ a⁻¹ * ((f i)⁻¹ * x) * a ∈ I.N)
    {v : M} (hv : v ∈ fixd π I.N) : I.uOp π a v = ∑ i ∈ s, π (f i * a) v := by
  classical
  have inj : Set.InjOn f s := by
    intro i hi j hj e
    exact (hu (f j) (hf j hj)).unique ⟨hi, by rw [e]; simp⟩ ⟨hj, by simp⟩
  rw [((uOpSum G I A M π a ha).2 (s.image f) ?_ ?_).2 v hv, Finset.sum_image inj]
  · intro u h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
    exact hf i hi
  · intro x hx
    obtain ⟨i, ⟨hi, h⟩, hun⟩ := hu x hx
    refine ⟨f i, ⟨Finset.mem_image_of_mem f hi, (uOpMul_mem I a _).2 h⟩, ?_⟩
    rintro u ⟨h1, h2⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h1
    rw [hun j ⟨hj, (uOpMul_mem I a _).1 h2⟩]

private theorem UpperTheory.V.Hi.uOpMul_ex {G : Type} [Group G] (I : Iwa G) {a : G} (ha : a ∈ I.P) :
    ∃ s : Finset G, (∀ u ∈ s, u ∈ I.N) ∧ ∀ x ∈ I.N, ∃! u, u ∈ s ∧ a⁻¹ * (u⁻¹ * x) * a ∈ I.N := by
  obtain ⟨s, h1, h2⟩ := (uOpSum G I ℤ ℤ (Representation.trivial ℤ G ℤ) a ha).1
  refine ⟨s, h1, fun x hx => ?_⟩
  simpa only [uOpMul_mem] using h2 x hx

theorem UpperTheory.V.Hi.uOpMul :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a b : G), a ∈ I.P → b ∈ I.P → ∀ v ∈ fixd π I.N, I.uOp π a v ∈ fixd π I.N ∧ I.uOp π a (I.uOp π b v) = I.uOp π (a * b) v ∧ I.uOp π 1 v = v ∧ (∀ t ∈ I.T, π t (I.uOp π a v) = I.uOp π a (π t v)) ∧ (a⁻¹ ∈ I.P → I.uOp π a v = π a v) := by
  intro G _ I A M _ _ _ π a b ha hb v hv
  have mul : ∀ (g h : G) (w : M), π g (π h w) = π (g * h) w := fun g h w => by
    rw [map_mul π g h, Module.End.mul_apply]
  have fix : ∀ c ∈ I.P, I.uOp π c v ∈ fixd π I.N := by
    intro c hc n hn
    obtain ⟨s, hs, hu⟩ := uOpMul_ex I hc
    have e1 := uOpMul_sum I π hc s id hs hu hv
    have e2 := uOpMul_sum I π hc s (fun u => n * u) (fun u h => mul_mem hn (hs u h)) (fun x hx => by
      have := hu (n⁻¹ * x) (mul_mem (inv_mem hn) hx)
      simpa only [_root_.mul_inv_rev, mul_assoc] using this) hv
    conv_lhs => rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2, map_sum]
    simp only [mul, id, mul_assoc]
  have unit : ∀ c ∈ I.P, c⁻¹ ∈ I.P → I.uOp π c v = π c v := by
    intro c hc hc'
    rw [uOpMul_sum I π hc ({1} : Finset G) id (by simp) ?_ hv]
    · simp
    · intro x hx
      refine ⟨1, ⟨by simp, by simpa using I.P_N _ hc' x hx⟩, fun y hy => by simpa using hy.1⟩
  refine ⟨fix a ha, ?_, ?_, ?_, unit a ha⟩
  · obtain ⟨s, hs, hu⟩ := uOpMul_ex I ha
    obtain ⟨r, hr, hw⟩ := uOpMul_ex I hb
    rw [uOpMul_sum I π ha s id hs hu (fix b hb), uOpMul_sum I π hb r id hr hw hv,
      uOpMul_sum I π (mul_mem ha hb) (s ×ˢ r) (fun p => p.1 * (a * p.2 * a⁻¹)) ?_ ?_ hv, Finset.sum_product]
    · refine Finset.sum_congr rfl fun u _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [mul]
      congr 2
      simp only [id]
      group
    · intro p hp
      rw [Finset.mem_product] at hp
      exact mul_mem (hs _ hp.1) (I.P_N a ha _ (hr _ hp.2))
    · intro x hx
      have e : ∀ u w : G, (a * b)⁻¹ * ((u * (a * w * a⁻¹))⁻¹ * x) * (a * b) =
          b⁻¹ * (w⁻¹ * (a⁻¹ * (u⁻¹ * x) * a)) * b := fun u w => by group
      obtain ⟨u, ⟨hus, hux⟩, hun⟩ := hu x hx
      obtain ⟨w, ⟨hwr, hwx⟩, hwn⟩ := hw _ hux
      refine ⟨(u, w), ⟨Finset.mem_product.2 ⟨hus, hwr⟩, by rw [e]; exact hwx⟩, ?_⟩
      rintro ⟨u', w'⟩ ⟨hp, h⟩
      rw [Finset.mem_product] at hp
      rw [e] at h
      have h1 : a⁻¹ * (u'⁻¹ * x) * a ∈ I.N := by
        have := mul_mem (hr _ hp.2) (I.P_N b hb _ h)
        convert this using 1
        group
      obtain rfl : u' = u := hun u' ⟨hp.1, h1⟩
      obtain rfl : w' = w := hwn w' ⟨hp.2, h⟩
      rfl
  · rw [unit 1 (one_mem _) (by simpa using one_mem I.P)]
    simp
  · intro t ht
    obtain ⟨s, hs, hu⟩ := uOpMul_ex I ha
    have hc : t * a = a * t := I.comm t (I.T_le ht) a (I.P_le a ha)
    have hN : ∀ x ∈ I.N, t⁻¹ * x * t ∈ I.N := fun x hx => by simpa using I.T_N _ (inv_mem ht) x hx
    have htv : π t v ∈ fixd π I.N := by
      intro n hn
      have : n * t = t * (t⁻¹ * n * t) := by group
      rw [mul, this, ← mul, hv _ (hN n hn)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [uOpMul_sum I π ha s id hs hu hv,
      uOpMul_sum I π ha s (fun u => t * u * t⁻¹) (fun u h => I.T_N t ht u (hs u h)) ?_ htv, map_sum]
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [mul, mul, mul_assoc _ a t, ← hc]
      congr 2
      simp only [id]
      group
    · intro x hx
      have e : ∀ u : G, a⁻¹ * ((t * u * t⁻¹)⁻¹ * x) * a = t * (a⁻¹ * (u⁻¹ * (t⁻¹ * x * t)) * a) * t⁻¹ := by
        intro u
        have h1 : a⁻¹ * t = t * a⁻¹ := (Commute.inv_left (show Commute a t from hc.symm)).eq
        have h2 : a = t * a * t⁻¹ := by rw [hc]; group
        calc a⁻¹ * ((t * u * t⁻¹)⁻¹ * x) * a = (a⁻¹ * t) * (u⁻¹ * t⁻¹ * x) * a := by group
          _ = (t * a⁻¹) * (u⁻¹ * t⁻¹ * x) * (t * a * t⁻¹) := by rw [h1, ← h2]
          _ = _ := by group
      have e' : ∀ y : G, t * y * t⁻¹ ∈ I.N ↔ y ∈ I.N := fun y =>
        ⟨fun h => by simpa [mul_assoc] using hN _ h, I.T_N t ht y⟩
      simpa only [e, e'] using hu _ (hN x hx)
end

