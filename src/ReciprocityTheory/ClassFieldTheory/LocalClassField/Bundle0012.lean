module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0011
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0010
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0009
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsCT
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.BrUnrA

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.BrBound
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem card_le_mul_of_ker {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [Finite B] [Finite C] (f : A →+ B)
    (g : C → A) (hg : ∀ a, f a = 0 → ∃ c, g c = a) : Finite A ∧ Nat.card A ≤ Nat.card C * Nat.card B := by
  classical
  have hsec : ∀ x : A, ∃ c : C, g c = x - Function.invFun f (f x) := fun x => by
    apply hg
    rw [map_sub, sub_eq_zero]
    exact (Function.invFun_eq (f := f) ⟨x, rfl⟩).symm
  choose σ hσ using hsec
  have hinj : Injective fun x : A => (σ x, f x) := fun x y hxy => by
    have h1 : σ x = σ y := congrArg Prod.fst hxy
    have h2 : f x = f y := congrArg Prod.snd hxy
    have e1 := hσ x
    have e2 := hσ y
    rw [h1, h2] at e1
    exact sub_left_injective (e1.symm.trans e2)
  refine ⟨Finite.of_injective _ hinj, ?_⟩
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ hinj

theorem card_BrKer_le_mul {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') (h' : K' ≤ L)
    (h1 : Finite (BrKer h)) (h2 : Finite (BrKer h')) :
    Finite (BrKer (h.trans h')) ∧ Nat.card (BrKer (h.trans h')) ≤ Nat.card (BrKer h) * Nat.card (BrKer h') := by
  let f : BrKer (h.trans h') →+ BrKer h' :=
    { toFun := fun x => ⟨(resPair h).hom.H 2 x.1, by
        show (resPair h').hom.H 2 _ = 0
        rw [← resPair_trans]; exact x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  refine card_le_mul_of_ker f (fun c : BrKer h => ⟨c.1, ?_⟩) (fun a ha => ⟨⟨a.1, congrArg Subtype.val ha⟩, rfl⟩)
  show (resPair (h.trans h')).hom.H 2 c.1 = 0
  rw [resPair_trans h h', show (resPair h).hom.H 2 c.1 = 0 from c.2, map_zero]

theorem card_BrKer_cyclic (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Nat.card (BrKer h) = degLK p K L := by
  rw [BrKer_eq_BrLK hL h, card_BrLK, card_h2_cyclic_layer hK hL h g₀ hg]

theorem card_BrKer_prime (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (hp : (degLK p K L).Prime) : Nat.card (BrKer h) = degLK p K L := by
  have : Fact (degLK p K L).Prime := ⟨hp⟩
  have hc : IsCyclic (GalLK p K L) := isCyclic_of_prime_card (p := degLK p K L) card_GalLK
  obtain ⟨g₀, hg⟩ := hc.exists_generator
  exact card_BrKer_cyclic hK hL h g₀ hg

theorem exists_field_of_quotient (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (N : Subgroup (GalLK p K L)) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ K' ∧ K' ≤ L ∧ FiniteDimensional ℚ_[p] K' ∧
      subG p K K' = N.comap (QuotientGroup.mk' (subG p K L)) ∧ degLK p K K' = N.index := by
  have hle : subG p K L ≤ N.comap (QuotientGroup.mk' (subG p K L)) := fun σ hσ => by
    rw [Subgroup.mem_comap]
    have : QuotientGroup.mk' (subG p K L) σ = 1 := (QuotientGroup.eq_one_iff σ).2 hσ
    rw [this]; exact N.one_mem
  obtain ⟨K', h1, h2, h3⟩ := exists_subG_eq_of_isOpen hK (N.comap (QuotientGroup.mk' (subG p K L)))
    (Subgroup.isOpen_mono hle (isOpen_subG hL))
  refine ⟨K', h1, ?_, h2, h3, ?_⟩
  · have := (subG_le_iff (L' := L) h1).1 (h3 ▸ hle)
    rwa [sup_eq_right.2 h] at this
  · show (subG p K K').index = _
    rw [h3, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem card_BrKer_le_of_prime_pow (l : ℕ) (hl : l.Prime) (k : ℕ) :
    ∀ (K L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → FiniteDimensional ℚ_[p] L →
      ∀ h : K ≤ L, (subG p K L).Normal → degLK p K L = l ^ k →
        Finite (BrKer h) ∧ Nat.card (BrKer h) ≤ l ^ k := by
  have : Fact l.Prime := ⟨hl⟩
  induction k with
  | zero =>
    intro K L hK hL h hn hd
    have hs : Subsingleton (BrKer h) := ⟨fun x y => by
      have h0 : ∀ z : BrKer h, z = 0 := fun z => Subtype.ext (by
        have := degLK_smul_eq_zero hL h z.1 z.2
        rwa [hd, pow_zero, one_smul] at this)
      rw [h0 x, h0 y]⟩
    exact ⟨inferInstance, by rw [Nat.card_unique]; simp⟩
  | succ k ih =>
    intro K L hK hL h hn hd
    have hfin := finite_GalLK (K := K) hL
    have hcard : Nat.card (GalLK p K L) = l ^ (k + 1) := hd
    have hnt : Nontrivial (GalLK p K L) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      exact Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt
    obtain ⟨N, hN, hNi⟩ := exists_normal_index_eq_prime l (IsPGroup.of_card hcard)
    obtain ⟨K', h1, h2, h3, h4, h5⟩ := exists_field_of_quotient hK hL h N
    have hn1 : (subG p K K').Normal := by rw [h4]; infer_instance
    have hn2 : (subG p K' L).Normal := subG_normal_of_le h1 h hn
    have hd1 : degLK p K K' = l := h5.trans hNi
    have hd2 : degLK p K' L = l ^ k := by
      have := degLK_mul h1 h2
      rw [hd, hd1, pow_succ'] at this
      exact (Nat.eq_of_mul_eq_mul_left hl.pos this).symm
    have hc1 : Nat.card (BrKer h1) = l := by
      rw [card_BrKer_prime hK h3 h1 (hd1 ▸ hl), hd1]
    have hf1 : Finite (BrKer h1) := Nat.finite_of_card_ne_zero (hc1 ▸ hl.ne_zero)
    obtain ⟨hf2, hc2⟩ := ih K' L h3 hL h2 hn2 hd2
    obtain ⟨hf, hc⟩ := card_BrKer_le_mul h1 h2 hf1 hf2
    refine ⟨hf, hc.trans ?_⟩
    rw [hc1, pow_succ']
    exact Nat.mul_le_mul_left _ hc2

theorem card_le_of_primary {A : Type*} [AddCommGroup A] (n : ℕ) (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (h : ∀ l : ℕ, l.Prime → Finite {a : A // ∃ k : ℕ, l ^ k • a = 0} ∧
      Nat.card {a : A // ∃ k : ℕ, l ^ k • a = 0} ≤ l ^ n.factorization l) :
    Finite A ∧ Nat.card A ≤ n := by
  classical
  let T : n.primeFactors → Type _ := fun l => {a : A // ∃ k : ℕ, l.1 ^ k • a = 0}
  have hfin : ∀ l, Finite (T l) := fun l => (h l.1 (Nat.prime_of_mem_primeFactors l.2)).1
  let F : A → ∀ l, T l := fun a l => ⟨(n / l.1 ^ n.factorization l.1) • a, n.factorization l.1, by
    rw [smul_smul, Nat.mul_div_cancel' (Nat.ordProj_dvd n l.1)]; exact hA a⟩
  have hF0 : ∀ a : A, (∀ l : n.primeFactors, (n / l.1 ^ n.factorization l.1) • a = 0) → a = 0 := fun a ha => by
    rw [← AddMonoid.addOrderOf_eq_one_iff]
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hqn : q ∣ n := hqd.trans (addOrderOf_dvd_of_nsmul_eq_zero (hA a))
    have hmem : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqn, hn.ne'⟩
    exact Nat.not_dvd_ordCompl hq hn.ne' (hqd.trans (addOrderOf_dvd_of_nsmul_eq_zero (ha ⟨q, hmem⟩)))
  have hinj : Injective F := fun a b hab => by
    rw [← sub_eq_zero]
    refine hF0 _ fun l => ?_
    rw [smul_sub, sub_eq_zero]
    exact congrArg Subtype.val (congrFun hab l)
  refine ⟨Finite.of_injective F hinj, (Nat.card_le_card_of_injective F hinj).trans ?_⟩
  rw [Nat.card_pi]
  calc ∏ l : n.primeFactors, Nat.card (T l) ≤ ∏ l : n.primeFactors, l.1 ^ n.factorization l.1 :=
        Finset.prod_le_prod' fun l _ => (h l.1 (Nat.prime_of_mem_primeFactors l.2)).2
    _ = n := by
        rw [Finset.prod_coe_sort n.primeFactors (fun l => l ^ n.factorization l)]
        exact Nat.prod_factorization_pow_eq_self hn.ne'

theorem exists_sylow_field (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (l : ℕ) (hl : l.Prime) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ K' ∧ K' ≤ L ∧
      degLK p K' L = l ^ (degLK p K L).factorization l ∧ ¬ l ∣ degLK p K K' := by
  have : Fact l.Prime := ⟨hl⟩
  have hfin := finite_GalLK (K := K) hL
  obtain ⟨S⟩ : Nonempty (Sylow l (GalLK p K L)) := inferInstance
  obtain ⟨K', h1, h2, h3, h4, h5⟩ := exists_field_of_quotient hK hL h (S : Subgroup (GalLK p K L))
  refine ⟨K', h1, h2, ?_, h5 ▸ S.not_dvd_index⟩
  have e1 := degLK_mul h1 h2
  have e2 : (S : Subgroup (GalLK p K L)).index * Nat.card (S : Subgroup (GalLK p K L)) = degLK p K L :=
    (S : Subgroup (GalLK p K L)).index_mul_card
  rw [h5, ← e2] at e1
  have e3 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) e1
  rw [← e3, S.card_eq_multiplicity]
  rfl

theorem finiteDimensional_of_le' {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K' ≤ L)
    (hL : FiniteDimensional ℚ_[p] L) : FiniteDimensional ℚ_[p] K' :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap (IntermediateField.inclusion h).injective

theorem eq_of_resPair_eq_of_coprime {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hK' : FiniteDimensional ℚ_[p] K')
    (h : K ≤ K') (l : ℕ) (hl : l.Prime) (hd : ¬ l ∣ degLK p K K') (x y : Br p K) (kx ky : ℕ) (hx : l ^ kx • x = 0)
    (hy : l ^ ky • y = 0) (hxy : (resPair h).hom.H 2 x = (resPair h).hom.H 2 y) : x = y := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_BrKer_of_coprime hK' h _ ?_ (l ^ (kx + ky)) ?_
    (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hd))
  · exact (map_sub ((resPair h).hom.H 2) x y).trans (sub_eq_zero.2 hxy)
  · rw [smul_sub, pow_add, mul_comm, mul_smul, hx, smul_zero, mul_comm, mul_smul, hy, smul_zero, sub_zero]

theorem card_BrKer_le (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] : Finite (BrKer h) ∧ Nat.card (BrKer h) ≤ degLK p K L := by
  refine card_le_of_primary (degLK p K L) (degLK_pos hL)
    (fun a => Subtype.ext (degLK_smul_eq_zero hL h a.1 a.2)) fun l hl => ?_
  obtain ⟨K', h1, h2, h3, h4⟩ := exists_sylow_field hK hL h l hl
  have hK' := finiteDimensional_of_le' h2 hL
  obtain ⟨hf, hc⟩ := card_BrKer_le_of_prime_pow l hl _ K' L hK' hL h2 (subG_normal_of_le h1 h inferInstance) h3
  let F : {a : BrKer h // ∃ k : ℕ, l ^ k • a = 0} → BrKer h2 := fun a => ⟨(resPair h1).hom.H 2 a.1.1, by
    show (resPair h2).hom.H 2 _ = 0
    rw [← resPair_trans h1 h2]; exact a.1.2⟩
  have hinj : Injective F := fun a b hab => by
    obtain ⟨ka, hka⟩ := a.2
    obtain ⟨kb, hkb⟩ := b.2
    exact Subtype.ext (Subtype.ext (eq_of_resPair_eq_of_coprime hK' h1 l hl h4 a.1.1 b.1.1 ka kb
      (congrArg Subtype.val hka) (congrArg Subtype.val hkb) (congrArg Subtype.val hab)))
  exact ⟨Finite.of_injective F hinj, (Nat.card_le_card_of_injective F hinj).trans hc⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.InflationH2InjectiveOfSameRamification
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

theorem admissible_valuation_layer {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (he : 0 < eK p L) (h : K ≤ L)
    [(subG p K L).Normal] : admitted (layerUIncl p K L) (vLayer p K L) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology
      (layerUIncl_injective p) fun _ _ => isOpen_discrete _).isEmbedding
  · intro y
    rw [← LinearMap.mem_ker, ker_vLayer p he h]
    rfl
  · exact ⟨Function.surjInv (vLayer_surjective p he h), continuous_of_discreteTopology, Function.surjInv_eq _⟩

theorem eK_Kn_pos (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : 0 < eK p (Kn p K n) := by
  rw [eK_Kn p hK hn]; exact eK_pos p K hK

theorem eK_Kur_pos (hK : FiniteDimensional ℚ_[p] K) : 0 < eK p (MaximalUnramifiedExtension p K) := by
  rw [eK_Kur p hK]; exact eK_pos p K hK

theorem valuation_unramified_layer_h2_bijective (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Bijective ((vLayer p K (Kn p K n)).hom.H 2) :=
  bijective_H_of_adm (admissible_valuation_layer (eK_Kn_pos hK hn) le_sup_left) 2
    (layerU_Kn_H_subsingleton hK hn 2 two_pos) (layerU_Kn_H_subsingleton hK hn 3 three_pos)

theorem valuation_unramified_closure_h2_bijective (hK : FiniteDimensional ℚ_[p] K) :
    Bijective ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2) :=
  bijective_H_of_adm (admissible_valuation_layer (eK_Kur_pos hK) le_Kur) 2
    (layerU_Kur_H_subsingleton hK 2 two_pos) (layerU_Kur_H_subsingleton hK 3 three_pos)

theorem card_h2_unramified_layer (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Nat.card ((layer p K (Kn p K n)).H 2) = n := by
  have hL := finiteDimensional_Kn p K hK hn
  have := discreteTopology_GalLK (K := K) hL
  have := finite_GalLK (K := K) hL
  rw [Nat.card_congr (Equiv.ofBijective _ (valuation_unramified_layer_h2_bijective hK hn)),
    card_h2_trivial_int_cyclic _ (frobLK p K (Kn p K n)) (mem_zpowers_frobLK_Kn hK hn), card_GalLK, degLK_Kn hK hn]

theorem vLayerMap_Kur_eq_one (hK : FiniteDimensional ℚ_[p] K) (π : (urT p K).V)
    (hπ : (eK p K : ℝ) * vbar p π.1 = 1) : vLayerMap p K (MaximalUnramifiedExtension p K) π = 1 := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p le_Kur, eK_Kur p hK, hπ, Int.cast_one]

theorem vLayer_Kur_cls (hK : FiniteDimensional ℚ_[p] K) (π : (urT p K).V)
    (hπ : (eK p K : ℝ) * vbar p π.1 = 1) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ)
    (z : (urT p K).coch.X 2) (hz : (urT p K).coch.d 2 z = 0) (hzm : ∀ g, z.1 g = m g • π)
    (y : (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.X 2) (hy : (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.d 2 y = 0)
    (hym : y.1 = m) :
    (vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz) =
      (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.cls 2 y hy := by
  rw [Cx.Hom.H_cls]
  apply Cx.cls_congr
  apply Subtype.ext
  funext g
  show vLayerMap p K (MaximalUnramifiedExtension p K) (z.1 fun i => g i) = y.1 g
  rw [hym, hzm, map_zsmul, vLayerMap_Kur_eq_one hK π hπ]
  simp

theorem exists_invariant_of_connecting_map (hK : FiniteDimensional ℚ_[p] K) :
    ∃ f : (urT p K).H 2 ≃+ QZ, IsInv p K f.toAddMonoidHom ∧
      ∀ δ, Cx.IsConn (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ)).hom
        (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ (c : (urT p K).H 2) (x) (hx),
        (vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c = δ 1 ((trivRep (GalLK p K (MaximalUnramifiedExtension p K)) QZ).coch.cls 1 x hx) →
        f c = x.1 ![frobLK p K (MaximalUnramifiedExtension p K)] := by
  obtain ⟨e, he⟩ := exists_h2_int_equiv_rat_mod_int (GalLK p K (MaximalUnramifiedExtension p K)) (frobLK p K (MaximalUnramifiedExtension p K)) (isZHat_GalKur hK)
  refine ⟨(AddEquiv.ofBijective ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2).toAddMonoidHom
    (valuation_unramified_closure_h2_bijective hK)).trans e, ?_, ?_⟩
  · intro π t m z hz _ hπ ht hm hzm
    have hadm : admitted
        (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ))
        (trivMap _ (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · have hi : Injective (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ)).u :=
          Int.cast_injective (α := ℚ)
        exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology
          hi fun _ _ => isOpen_discrete _).isEmbedding
      · intro (y : ℚ)
        show (QuotientAddGroup.mk y : QZ) = 0 ↔ y ∈ Set.range (Int.castAddHom ℚ)
        rw [QuotientAddGroup.eq_zero_iff]
        rfl
      · exact ⟨Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range),
          continuous_of_discreteTopology, Function.surjInv_eq _⟩
    have s := admissibility_holds ℤ _ _ _ _ _ _ hadm
    obtain ⟨⟨δ, h1, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s
    obtain ⟨x, hx, y, hy, e1, e2, e3⟩ := conn_cls_of_lift δ h1 t ht m hm
    show e ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz)) = _
    rw [vLayer_Kur_cls hK π hπ m z hz hzm y hy e2]
    exact (congrArg e e3.symm).trans ((he δ h1 x hx).trans (e1 _))
  · intro δ hδ c x hx h
    show e ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c) = _
    exact (congrArg e h).trans (he δ hδ x hx)

theorem exists_isInv (hK : FiniteDimensional ℚ_[p] K) :
    ∃ f : (urT p K).H 2 ≃+ QZ, IsInv p K f.toAddMonoidHom := by
  obtain ⟨f, hf, -⟩ := exists_invariant_of_connecting_map hK
  exact ⟨f, hf⟩

theorem exists_uniformiser_Kur (hK : FiniteDimensional ℚ_[p] K) :
    ∃ π : (urT p K).V, π.1 ∈ multOf p K ∧ (eK p K : ℝ) * vbar p π.1 = 1 := by
  obtain ⟨x, hx⟩ := vOn_surjective p K hK 1
  have h1 := vOn_spec p K x
  rw [hx, Int.cast_one] at h1
  have hx' : x.1 ∈ multOf p (MaximalUnramifiedExtension p K) := le_Kur (K := K) x.2
  exact ⟨toLayer p ⟨x.1, hx'⟩, x.2, h1.symm⟩

theorem exists_std_cocycle (hK : FiniteDimensional ℚ_[p] K) (c : (urT p K).H 2) :
    ∃ (π : (urT p K).V) (t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ)
      (z : (urT p K).coch.X 2) (hz : (urT p K).coch.d 2 z = 0),
      π.1 ∈ multOf p K ∧ (eK p K : ℝ) * vbar p π.1 = 1 ∧ IsLocallyConstant t ∧
      (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ (∀ g, z.1 g = m g • π) ∧
      c = (urT p K).coch.cls 2 z hz := by
  obtain ⟨π, hπK, hπ⟩ := exists_uniformiser_Kur hK
  obtain ⟨t, m, y, hy, ht, hm, hym, hc⟩ := exists_cocycle_form ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c)
  have hinv := (layer_invariant_iff π).2 hπK
  have hyc : Continuous y.1 := y.2
  have hzc : Continuous fun g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K) => m g • π := by
    have h0 : Continuous fun k : (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).V => (show ℤ from k) • π :=
      continuous_of_discreteTopology
    rw [← hym]
    exact h0.comp hyc
  let z : (urT p K).coch.X 2 := ⟨fun g => m g • π, hzc⟩
  have hz : (urT p K).coch.d 2 z = 0 := by
    apply LowDeg.coch_d_eq_zero
    funext g
    have h0 := congrFun (LowDeg.dn_eq_zero _ hy) g
    rw [LowDeg.dn_two_apply, hym] at h0
    have h1 : m ![g 1, g 2] - m ![g 0 * g 1, g 2] + m ![g 0, g 1 * g 2] - m ![g 0, g 1] = 0 := h0
    rw [LowDeg.dn_two_apply]
    show (urT p K).rho (g 0) (m ![g 1, g 2] • π) - m ![g 0 * g 1, g 2] • π + m ![g 0, g 1 * g 2] • π -
      m ![g 0, g 1] • π = 0
    rw [map_zsmul, hinv, ← sub_smul, ← add_smul, ← sub_smul, h1, zero_smul]
  refine ⟨π, t, m, z, hz, hπK, hπ, ht, hm, fun _ => rfl, ?_⟩
  apply (valuation_unramified_closure_h2_bijective hK).1
  rw [hc, vLayer_Kur_cls hK π hπ m z hz (fun _ => rfl) y hy hym]

theorem IsInv.unique (hK : FiniteDimensional ℚ_[p] K) {f g : (urT p K).H 2 →+ QZ} (hf : IsInv p K f)
    (hg : IsInv p K g) : f = g := by
  ext c
  obtain ⟨π, t, m, z, hz, h1, h2, h3, h4, h5, rfl⟩ := exists_std_cocycle hK c
  rw [hf π t m z hz h1 h2 h3 h4 h5, hg π t m z hz h1 h2 h3 h4 h5]

theorem isInv_invUr (hK : FiniteDimensional ℚ_[p] K) : IsInv p K (invUr p K) := by
  obtain ⟨f, hf⟩ := exists_isInv hK
  have h : ∃ f, IsInv p K f := ⟨_, hf⟩
  unfold invUr
  rw [dite_eq_left h]
  exact h.choose_spec

theorem invUr_bijective (hK : FiniteDimensional ℚ_[p] K) : Bijective (invUr p K) := by
  obtain ⟨f, hf⟩ := exists_isInv hK
  rw [IsInv.unique hK (isInv_invUr hK) hf]
  exact f.bijective

theorem invUr_eq (hK : FiniteDimensional ℚ_[p] K) (δ)
    (hδ : Cx.IsConn (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ)).hom
      (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (c : (urT p K).H 2) (x) (hx)
    (h : (vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c = δ 1 ((trivRep (GalLK p K (MaximalUnramifiedExtension p K)) QZ).coch.cls 1 x hx)) :
    invUr p K c = x.1 ![frobLK p K (MaximalUnramifiedExtension p K)] := by
  obtain ⟨f, hf, hf'⟩ := exists_invariant_of_connecting_map hK
  rw [IsInv.unique hK (isInv_invUr hK) hf]
  exact hf' δ hδ c x hx h

theorem layerInfl_u_val {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] (x : (layer p K L).V) : ((layerInfl (K := K) h).u x).1 = x.1 := rfl

theorem vLayerMap_layerInfl {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : K ≤ L) (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] (he : eK p L' = eK p L) (x : (layer p K L).V) :
    vLayerMap p K L' ((layerInfl (K := K) h).u x) = vLayerMap p K L x := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p (hL.trans h), vLayerMap_spec p hL, he, layerInfl_u_val]

theorem layerInfl_φ_surjective {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] : Surjective (layerInfl (K := K) h).φ := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H σ => exact ⟨QuotientGroup.mk σ, rfl⟩

theorem vLayer_layerInfl_H {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : K ≤ L) (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] (he : eK p L' = eK p L) (i : ℕ) (c : (layer p K L).H i) :
    (vLayer p K L').hom.H i ((layerInfl (K := K) h).hom.H i c) =
      (trivInfl (layerInfl (K := K) h).φ (layerInfl (K := K) h).φ_cont ℤ).hom.H i
        ((vLayer p K L).hom.H i c) := by
  obtain ⟨x, hx, rfl⟩ := Cx.exists_cls c
  rw [Cx.Hom.H_cls, Cx.Hom.H_cls, Cx.Hom.H_cls, Cx.Hom.H_cls]
  apply Cx.cls_congr
  apply Subtype.ext
  funext g
  exact vLayerMap_layerInfl hL h he _

theorem inflation_h2_injective_of_same_ramification {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : K ≤ L) (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] (he : eK p L' = eK p L)
    (hv : Injective ((vLayer p K L).hom.H 2)) : Injective ((layerInfl (K := K) h).hom.H 2) := by
  intro a b hab
  apply hv
  apply trivial_inflation_h2_int_injective _ (layerInfl (K := K) h).φ_cont (layerInfl_φ_surjective h)
  rw [← vLayer_layerInfl_H hL h he, ← vLayer_layerInfl_H hL h he, hab]

theorem inflation_unramified_layer_h2_injective (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Injective ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2) :=
  inflation_h2_injective_of_same_ramification (L := Kn p K n) le_sup_left (Kn_le_Kur hn) ((eK_Kur p hK).trans (eK_Kn p hK hn).symm)
    (valuation_unramified_layer_h2_bijective hK hn).1

theorem mem_range_layerInfl_Kn_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (x : (urT p K).H 2) :
    x ∈ LinearMap.range ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2) ↔ n • x = 0 := by
  have hsub : Set.range ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2) ⊆
      {x : (urT p K).H 2 | n • x = 0} := by
    rintro _ ⟨y, rfl⟩
    show n • _ = 0
    have h0 : n • y = 0 := by
      have h1 := card_nsmul_eq_zero' (x := y)
      rwa [card_h2_unramified_layer hK hn] at h1
    rw [← map_nsmul, h0, map_zero]
  obtain ⟨f, -⟩ := exists_isInv hK
  have hT : Nat.card {x : (urT p K).H 2 | n • x = 0} = n := by
    refine (Nat.card_congr (Equiv.subtypeEquiv f.toEquiv fun a => ?_)).trans (card_QZ_torsion n hn)
    show n • a = 0 ↔ n • f a = 0
    rw [← map_nsmul, map_eq_zero_iff f f.injective]
  have hfin : ({x : (urT p K).H 2 | n • x = 0} : Set _).Finite :=
    Nat.finite_of_card_ne_zero (by rw [hT]; exact hn.ne')
  have hS : Nat.card (Set.range ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2)) = n := by
    rw [Nat.card_range_of_injective (inflation_unramified_layer_h2_injective hK hn), card_h2_unramified_layer hK hn]
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hT, hS]) hfin
  show x ∈ Set.range _ ↔ _
  rw [heq]
  rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

