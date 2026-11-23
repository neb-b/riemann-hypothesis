module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierSchurOfRankLeAleph0
section
open Polynomial

namespace GlobalTheory

theorem isUnit_aeval_of_forall_isUnit_sub {A : Type*} [Ring A] [Algebra ℂ A] (T : A)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ A c)) (q : ℂ[X]) (hq : q ≠ 0) :
    IsUnit (aeval T q) := by
  have hs : spectrum ℂ T = ∅ := by
    ext c
    simp only [Set.mem_empty_iff_false, iff_false, spectrum.notMem_iff]
    simpa using (h c).neg
  by_cases hd : 0 < q.degree
  · have h1 := spectrum.map_polynomial_aeval_of_degree_pos T q hd
    rw [hs, Set.image_empty] at h1
    have h0 : (0 : ℂ) ∉ spectrum ℂ (aeval T q) := by rw [h1]; simp
    exact (spectrum.zero_notMem_iff ℂ).1 h0
  · have h2 : q = C (q.coeff 0) := eq_C_of_degree_le_zero (not_lt.1 hd)
    have h3 : q.coeff 0 ≠ 0 := fun h => hq (by rw [h2, h, C_0])
    rw [h2, aeval_C]
    exact (IsUnit.mk0 _ h3).map _

theorem linearIndependent_of_sub_apply_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c))
    (v : V) (hv : v ≠ 0) (w : ℂ → V)
    (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  set q : ℂ[X] := ∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j) with hqdef
  have hq0 : aeval T q v = 0 := by
    have h1 : ∀ k ∈ s, aeval T (C (g k) * ∏ j ∈ s.erase k, (X - C j)) v
        = aeval T (∏ j ∈ s, (X - C j : ℂ[X])) (g k • w k) := by
      intro k hk
      rw [← Finset.prod_erase_mul s _ hk, ← hw k, map_mul, map_mul, aeval_C, map_sub, aeval_X,
        aeval_C, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
        map_smul, map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hqdef, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl h1, ← map_sum, hg, map_zero]
  have hq : q = 0 := by
    by_contra hne
    have hu := isUnit_aeval_of_forall_isUnit_sub T h q hne
    have hinj := ((Module.End.isUnit_iff _).1 hu).1
    exact hv (hinj (by rw [hq0, map_zero]))
  have h2 : eval i q = g i * ∏ j ∈ s.erase i, (i - j) := by
    rw [hqdef, Polynomial.eval_finsetSum, Finset.sum_eq_single i]
    · simp [eval_prod]
    · intro k _ hki
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hki.symm, hi⟩)
        (by simp), mul_zero]
    · intro h; exact absurd hi h
  rw [hq, eval_zero] at h2
  refine (mul_eq_zero.1 h2.symm).resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (Finset.mem_erase.1 hj).1.symm

theorem dixmier_schur_of_rank_le_aleph0 :
    ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V),
      Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
      (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by
  intro V ι _ _ ρ T hV hrank hirr hcomm
  by_contra hne
  push_neg at hne
  have hunit : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c) := by
    intro c
    set S := T - algebraMap ℂ (Module.End ℂ V) c with hS
    have hS0 : S ≠ 0 := by
      intro h0
      apply hne c
      rw [← Algebra.algebraMap_eq_smul_one]
      exact sub_eq_zero.1 h0
    have hSc : ∀ i x, S (ρ i x) = ρ i (S x) := by
      intro i x
      have := LinearMap.congr_fun (hcomm i) x
      simp only [Module.End.mul_apply] at this
      simp [hS, this, Module.algebraMap_end_apply]
    rw [Module.End.isUnit_iff]
    constructor
    · rw [← LinearMap.ker_eq_bot]
      refine (hirr _ ?_).resolve_right ?_
      · intro i x hx
        rw [LinearMap.mem_ker] at hx ⊢
        rw [hSc, hx, map_zero]
      · rw [LinearMap.ker_eq_top]; exact hS0
    · rw [← LinearMap.range_eq_top]
      refine (hirr _ ?_).resolve_left ?_
      · rintro i _ ⟨x, rfl⟩
        exact ⟨ρ i x, hSc i x⟩
      · rw [LinearMap.range_eq_bot]; exact hS0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  choose w hw using fun c => ((Module.End.isUnit_iff _).1 (hunit c)).2 v
  have hli := linearIndependent_of_sub_apply_eq T hunit v hv w hw
  have h1 := hli.cardinal_le_rank.trans hrank
  rw [Cardinal.mk_complex] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetCardDivCardInfCommutativeSubgroup
section
open scoped Pointwise

namespace GlobalTheory.DCIndex

variable {A : Type} [Group A]

theorem normal_of_comm (hc : ∀ a b : A, a * b = b * a) (V : Subgroup A) : V.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩

theorem mem_sup_iff (hc : ∀ a b : A, a * b = b * a) (P Q : Subgroup A) {x : A} :
    x ∈ P ⊔ Q ↔ ∃ p ∈ P, ∃ q ∈ Q, p * q = x := by
  haveI : Q.Normal := normal_of_comm hc Q
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem card_quot_eq_index (hc : ∀ a b : A, a * b = b * a) (P V : Subgroup A) :
    Nat.card (DoubleCoset.Quotient (P : Set A) (V : Set A)) = (P ⊔ V).index := by
  rw [Subgroup.index]
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl A) ?_
  intro x y
  simp only [Equiv.refl_apply]
  rw [DoubleCoset.rel_iff, QuotientGroup.leftRel_apply, mem_sup_iff hc]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [hc a x, mul_assoc, inv_mul_cancel_left]
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [hc a x, mul_assoc, h, mul_inv_cancel_left]

theorem relIndex_split (hc : ∀ a b : A, a * b = b * a) (h u c : Subgroup A) (huc : u ≤ c) :
    u.relIndex c = (h ⊓ u).relIndex (h ⊓ c) * (h ⊔ u).relIndex (h ⊔ c) := by
  haveI : u.Normal := normal_of_comm hc u
  haveI : (h ⊔ u).Normal := normal_of_comm hc (h ⊔ u)
  have hM : (h ⊔ u) ⊓ c = (h ⊓ c) ⊔ u := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff hc h u).1 hx1
      have hpc : p ∈ c := by
        have := c.mul_mem hx2 (c.inv_mem (huc hq))
        rwa [mul_inv_cancel_right] at this
      exact (mem_sup_iff hc _ _).2 ⟨p, Subgroup.mem_inf.2 ⟨hp, hpc⟩, q, hq, rfl⟩
    · exact sup_le (inf_le_inf_right c le_sup_left) (le_inf le_sup_right huc)
  have e1 := Subgroup.relIndex_mul_relIndex (H := u) (K := (h ⊔ u) ⊓ c) (L := c)
    (le_inf le_sup_right huc) inf_le_right
  have e2 : ((h ⊔ u) ⊓ c).relIndex c = (h ⊔ u).relIndex (h ⊔ c) := by
    rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_sup_right (H := c) (K := h ⊔ u)]
    congr 1
    apply le_antisymm
    · exact sup_le le_sup_right (sup_le le_sup_left (huc.trans le_sup_right))
    · exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  have e3 : u.relIndex ((h ⊔ u) ⊓ c) = (h ⊓ u).relIndex (h ⊓ c) := by
    rw [hM, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right (H := u) (K := h ⊓ c)]
    congr 1
    apply le_antisymm
    · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
    · exact le_inf inf_le_right (inf_le_inf_left h huc)
  rw [← e1, e2, e3]

theorem card_split (h u c : Subgroup A) (huc : u ≤ c) :
    (h ⊓ u).relIndex (h ⊓ c) * Nat.card (h ⊓ u : Subgroup A) = Nat.card (h ⊓ c : Subgroup A) := by
  have hle : h ⊓ u ≤ h ⊓ c := inf_le_inf_left h huc
  have := Subgroup.card_mul_index ((h ⊓ u).subgroupOf (h ⊓ c))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at this
  rw [Subgroup.relIndex, mul_comm, this]

end GlobalTheory.DCIndex

namespace GlobalTheory.DCIndex

theorem card_inf_subgroupOf {G : Type} [Group G] (T H U : Subgroup G) (hUT : U ≤ T) :
    Nat.card (H.subgroupOf T ⊓ U.subgroupOf T : Subgroup T) = Nat.card (H ⊓ U : Subgroup G) := by
  have he : H.subgroupOf T ⊓ U.subgroupOf T = (H ⊓ U).subgroupOf T := by
    ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [he]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hUT)).toEquiv

theorem index_identity : ∀ {G : Type} [Group G] (T H U C : Subgroup G), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → U ≤ C → C ≤ T → U.relIndex C ≠ 0 → (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ U : Subgroup G) : ℂ) = (U.relIndex C : ℂ) * (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ C : Subgroup G) : ℂ) := by
  intro G _ T H U C hcomm hUC hCT hne
  have hc : ∀ a b : T, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  have hu'c' : U.subgroupOf T ≤ C.subgroupOf T := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hUC hx
  have hrel : (U.subgroupOf T).relIndex (C.subgroupOf T) = U.relIndex C :=
    Subgroup.relIndex_subgroupOf hCT
  rw [card_quot_eq_index hc, card_quot_eq_index hc, ← card_inf_subgroupOf T H U (hUC.trans hCT),
    ← card_inf_subgroupOf T H C hCT, ← hrel]
  rw [← hrel] at hne
  have hU := (Subgroup.relIndex_mul_index
    (sup_le_sup_left hu'c' (H.subgroupOf T))).symm
  have hsplit := relIndex_split hc (H.subgroupOf T) _ _ hu'c'
  have hcard := card_split (H.subgroupOf T) _ _ hu'c'
  rw [hU, hsplit, ← hcard]
  rw [hsplit] at hne
  have hs : (((H.subgroupOf T ⊓ U.subgroupOf T).relIndex (H.subgroupOf T ⊓ C.subgroupOf T) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (left_ne_zero_of_mul hne)
  push_cast
  rw [mul_assoc, mul_div_mul_left _ _ hs]

end GlobalTheory.DCIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetRelIndexInfConjConst
section
namespace GlobalTheory.DoubleCosetWeight

open Subgroup

theorem inf_map_conj_mul_eq {G : Type} [Group G] (T K : Subgroup G) {t k : G}
    (ht : t ∈ T) (hk : k ∈ K) (q : G) :
    T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom =
      (T ⊓ K.map (MulAut.conj q).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hxT, y, hy, rfl⟩
    refine ⟨q * (k * y * k⁻¹) * q⁻¹, ⟨?_, k * y * k⁻¹, K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk), rfl⟩, ?_⟩
    · have : q * (k * y * k⁻¹) * q⁻¹ = t⁻¹ * (t * q * k * y * (t * q * k)⁻¹) * t := by group
      rw [this]; exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
    · group
  · rintro ⟨z, ⟨hzT, y, hy, rfl⟩, rfl⟩
    refine ⟨T.mul_mem (T.mul_mem ht hzT) (T.inv_mem ht), k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    group

def gen {G : Type} [Group G] (T K : Subgroup G) : Subgroup G :=
  ⨆ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom

theorem gen_map_le {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom ≤ gen T K := by
  rw [map_le_iff_le_comap]
  refine iSup_le fun q => ?_
  intro x hx
  rw [mem_comap]
  have h1 : (MulAut.conj t).toMonoidHom x ∈ T ⊓ K.map (MulAut.conj (t * q * 1)).toMonoidHom := by
    rw [inf_map_conj_mul_eq T K ht K.one_mem q]
    exact mem_map_of_mem _ hx
  exact (le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) (t * q * 1)) h1

theorem gen_map_eq {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom = gen T K := by
  refine le_antisymm (gen_map_le T K ht) fun x hx => ?_
  have : (MulAut.conj t⁻¹).toMonoidHom x ∈ gen T K :=
    gen_map_le T K (T.inv_mem ht) (mem_map_of_mem _ hx)
  refine ⟨_, this, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem relIndex_eq {G : Type} [Group G] (T C K : Subgroup G)
    (hC : ∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) :
    ∀ t ∈ T, ∀ k ∈ K, ∀ q : G,
      (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C =
        (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  intro t ht k hk q
  have hN : gen T K ≤ C := iSup_le hC
  have hA : ∀ p : G, T ⊓ K.map (MulAut.conj p).toMonoidHom ≤ gen T K := fun p =>
    le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) p
  have e1 := relIndex_mul_relIndex _ _ _ (hA (t * q * k)) hN
  have e2 := relIndex_mul_relIndex _ _ _ (hA q) hN
  rw [← e1, ← e2, inf_map_conj_mul_eq T K ht hk q]
  congr 1
  conv_lhs => rw [← gen_map_eq T K ht]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj t).injective

end GlobalTheory.DoubleCosetWeight

theorem GlobalTheory.doubleCoset_relIndex_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C :=
  fun G _ T C K hC => GlobalTheory.DoubleCosetWeight.relIndex_eq T C K hC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSemidirectRepSurjective
section
namespace GlobalTheory

theorem doubleCoset_semidirect_surj :
    ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P),
      (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) →
      ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N),
        (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) →
        ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM →
          (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) →
          (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) →
          ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N,
            DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X)
              = d := by
  intro P M N _ _ _ s π u hs _ hker KP KM L hKs _ _ TM CM TP CP _ hTP _ _ d
  obtain ⟨t, ht, k, hk, hm⟩ := (@DoubleCoset.eq _ _ TM KM
    (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) (π (Quotient.out d))).1
    (DoubleCoset.out_eq' _)
  generalize Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d))) = q at hm ⊢
  obtain ⟨X, hX⟩ := (hker ((s q)⁻¹ * (s t)⁻¹ * Quotient.out d * (s k)⁻¹)).1 (by
    simp only [map_mul, map_inv, hs]
    rw [hm]; group)
  refine ⟨X, ?_⟩
  rw [hX]
  conv_rhs => rw [← DoubleCoset.out_eq' d]
  rw [DoubleCoset.eq]
  exact ⟨s t, (hTP _).2 ⟨t, ht, rfl⟩, s k, hKs k hk, by group⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
section
open MeasureTheory

namespace GlobalTheory.DoubleCosetAdjoint

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)


omit [μ.IsMulLeftInvariant] [Countable Γ] in
theorem isFundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) ⁻¹' 𝓕) μ :=
  h𝓕.preimage_of_equiv (measurePreserving_mul_right μ y).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g h => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])

omit [μ.IsMulLeftInvariant] [Countable Γ] [μ.IsMulRightInvariant] [TopologicalSpace H]
  [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] in
theorem preimage_preimage_mul (y : H) :
    (fun h => h * y) ⁻¹' ((fun h => h * y⁻¹) ⁻¹' 𝓕) = 𝓕 := by
  ext h; simp

theorem setIntegral_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  have h1 := (measurePreserving_mul_right μ y).setIntegral_preimage_emb
    (measurableEmbedding_mulRight y) u ((fun h => h * y⁻¹) ⁻¹' 𝓕)
  rw [preimage_preimage_mul] at h1
  rw [h1]
  exact (isFundamentalDomain_mul_right μ Γ 𝓕 h𝓕 y⁻¹).setIntegral_eq h𝓕
    (fun g h => hu g g.2 h)

theorem integrableOn_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by
  have h1 := (measurePreserving_mul_right μ y).integrableOn_comp_preimage
    (measurableEmbedding_mulRight y) (f := u) (s := (fun h => h * y⁻¹) ⁻¹' 𝓕)
  rw [preimage_preimage_mul] at h1
  refine h1.2 ?_
  exact ((isFundamentalDomain_mul_right μ Γ 𝓕 h𝓕 y⁻¹).integrableOn_iff h𝓕
    (fun g h => hu g g.2 h)).2 hi


omit [Group H] [IsTopologicalGroup H] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
theorem integrableOn_star_mul (F F' : H → ℂ) (hF : Continuous F) (hF' : Continuous F')
    (h1 : IntegrableOn (fun h => star (F h) * F h) 𝓕 μ)
    (h2 : IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ) :
    IntegrableOn (fun h => star (F h) * F' h) 𝓕 μ := by
  refine Integrable.mono' (h1.norm.add h2.norm)
    (hF.star.mul hF').aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
  simp only [Pi.add_apply, norm_mul, norm_star]
  nlinarith [sq_nonneg (‖F h‖ - ‖F' h‖), mul_nonneg (norm_nonneg (F h)) (norm_nonneg (F' h))]

end GlobalTheory.DoubleCosetAdjoint


open GlobalTheory.DoubleCosetAdjoint in
theorem GlobalTheory.doubleCosetSum_adjoint : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K : Subgroup H) [Countable Γ] (𝓕 : Set H) (x : H) (A A' : Finset H) (F F' : H → ℂ), IsFundamentalDomain Γ 𝓕 μ → (∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) → (∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) → A.card = A'.card → Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ γ ∈ Γ, ∀ h, F' (γ * h) = F' h) → (∀ k ∈ K, ∀ h, F (h * k) = F h) → (∀ k ∈ K, ∀ h, F' (h * k) = F' h) → IntegrableOn (fun h => star (F h) * F h) 𝓕 μ → IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ → ∫ h in 𝓕, star (∑ a ∈ A, F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F h) * ∑ a ∈ A', F' (h * a) ∂μ := by
  intro H _ _ _ _ _ μ _ _ Γ K _ 𝓕 x A A' F F' h𝓕 hA hA' hc cF cF' lF lF' rF rF' iF iF'
  set u : H → ℂ := fun h => star (F (h * x)) * F' h with hu
  have lu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h := by
    intro γ hγ h
    simp only [hu, mul_assoc, lF γ hγ, lF' γ hγ]
  have iu : IntegrableOn u 𝓕 μ := by
    refine integrableOn_star_mul μ 𝓕 (fun h => F (h * x)) F'
      (cF.comp (continuous_mul_const x)) cF' ?_ iF'
    exact integrableOn_mul_right μ Γ 𝓕 h𝓕 (fun h => star (F h) * F h)
      (fun γ hγ h => by simp only [lF γ hγ]) x iF
  have eA : ∀ a ∈ A, ∃ y, ∀ h, star (F (h * a)) * F' h = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine ⟨k₁, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF k₂ hk₂, rF' k₁ hk₁]
  have eA' : ∀ a ∈ A', ∃ y, ∀ h, star (F h) * F' (h * a) = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine ⟨k₁ * x⁻¹, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF' k₂ hk₂, inv_mul_cancel_right, rF k₁ hk₁]
  have key : ∀ (B : Finset H) (t : H → H → ℂ), (∀ a ∈ B, ∃ y, ∀ h, t a h = u (h * y)) →
      ∫ h in 𝓕, ∑ a ∈ B, t a h ∂μ = B.card • ∫ h in 𝓕, u h ∂μ := by
    intro B t ht
    rw [MeasureTheory.integral_finsetSum, ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨y, hy⟩ := ht a ha
      simp only [hy]
      exact setIntegral_mul_right μ Γ 𝓕 h𝓕 u lu y
    · intro a ha
      obtain ⟨y, hy⟩ := ht a ha
      have : t a = fun h => u (h * y) := funext hy
      rw [this]
      exact integrableOn_mul_right μ Γ 𝓕 h𝓕 u lu y iu
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [key A (fun a h => star (F (h * a)) * F' h) eA,
    key A' (fun a h => star (F h) * F' (h * a)) eA', hc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberDeformationExtendsAway
section
namespace GlobalTheory

def dualNumberRingHomMap {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') :
    DualNumber S →+* DualNumber S' where
  toFun x := TrivSqZeroExt.inl (f x.fst) + TrivSqZeroExt.inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, mul_comm] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

theorem dualNumber_deformation_extends_away :
    ∀ {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] (g : S) [IsLocalization.Away g S']
      (d : S →+* DualNumber S), (∀ s, (d s).fst = s) →
      ∃ d' : S' →+* DualNumber S', (∀ s, (d' s).fst = s) ∧
        ∀ s, (d' (algebraMap S S' s)).snd = algebraMap S S' (d s).snd := by
  intro S S' _ _ _ g _ d hd
  let ψ : S →+* DualNumber S' := (dualNumberRingHomMap (algebraMap S S')).comp d
  have hψ : ∀ s, ψ s = TrivSqZeroExt.inl (algebraMap S S' (d s).fst)
      + TrivSqZeroExt.inr (algebraMap S S' (d s).snd) := fun s => rfl
  have hu : IsUnit (ψ g) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ]
    simpa [hd] using IsLocalization.Away.algebraMap_isUnit (S := S') g
  refine ⟨IsLocalization.Away.lift g hu, ?_, ?_⟩
  · have h : (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (IsLocalization.Away.lift g hu)
        = RingHom.id S' := by
      apply IsLocalization.ringHom_ext (Submonoid.powers g)
      ext s
      simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ, hd]
    intro s
    exact congrArg (fun F : S' →+* S' => F s) h
  · intro s
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ]
    rw [Algebra.smul_def, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualProdLogDerivModSq
section
open MvPolynomial

namespace GlobalTheory

theorem dualProd_logDeriv_modSq : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R) {N : ℕ} (e f : Fin N → R) (I : Ideal R), (∀ i, δ (e i) = 0) → (∀ i, e i ^ 2 ∈ I) → δ (∏ i, (1 + e i * f i)) - (∏ i, (1 + e i * f i)) * ∑ i, e i * δ (f i) ∈ I := by
  intro K R _ _ _ δ N
  induction N with
  | zero => intro e f I _ _; simp
  | succ n ih =>
    intro e f I he he2
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    have h := ih (fun i => e i.succ) (fun i => f i.succ) I (fun i => he _) (fun i => he2 _)
    set P := ∏ i : Fin n, (1 + e i.succ * f i.succ)
    set S := ∑ i : Fin n, e i.succ * δ (f i.succ)
    have key : δ ((1 + e 0 * f 0) * P) - (1 + e 0 * f 0) * P * (e 0 * δ (f 0) + S)
        = (1 + e 0 * f 0) * (δ P - P * S) - e 0 ^ 2 * (f 0 * P * δ (f 0)) := by
      simp only [Derivation.leibniz, map_add (f := _), Derivation.map_one_eq_zero, he 0, smul_eq_mul]
      ring
    rw [key]
    exact I.sub_mem (I.mul_mem_left _ h) (I.mul_mem_right _ (he2 0))

end GlobalTheory
end

