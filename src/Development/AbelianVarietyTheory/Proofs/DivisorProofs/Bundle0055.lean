module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetEqFinprodLocalSums
section
open Filter
open scoped Classical

namespace GlobalTheory.DoubleCosetEuler

theorem finsum_doubleCoset_trivial_eq_one (H : Type) [Group H] (TH KH : Subgroup H) (f : H → ℂ)
    (hf : ∀ x, f x = if ∃ t ∈ TH, ∃ k ∈ KH, x = t * k then 1 else 0) :
    ∑ᶠ q : DoubleCoset.Quotient (TH : Set H) (KH : Set H), f (Quotient.out q) = 1 := by
  have h1 : ∀ q : DoubleCoset.Quotient (TH : Set H) (KH : Set H), q ≠ DoubleCoset.mk TH KH 1 →
      f (Quotient.out q) = 0 := by
    intro q hq
    rw [hf, if_neg]
    rintro ⟨t, ht, k, hk, he⟩
    apply hq
    rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
    exact ⟨t⁻¹, inv_mem ht, k⁻¹, inv_mem hk, by rw [he]; group⟩
  rw [finsum_eq_single _ (DoubleCoset.mk TH KH 1) h1, hf, if_pos]
  obtain ⟨a, ha, b, hb, he⟩ := DoubleCoset.mk_out_eq_mul TH KH (1 : H)
  exact ⟨a, ha, b, hb, by rw [he, mul_one]⟩

theorem finsum_pi_prod_eq_prod_finsum (J : Type) [Fintype J] (α : J → Type) (f : ∀ j, α j → ℂ)
    (hf : ∀ j, (Function.support (f j)).Finite) :
    ∑ᶠ y : (∀ j, α j), ∏ j, f j (y j) = ∏ j, ∑ᶠ a, f j a := by
  have hR : ∀ j, ∑ᶠ a, f j a = ∑ a ∈ (hf j).toFinset, f j a := fun j =>
    finsum_eq_sum_of_support_subset _ (by simp)
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  apply finsum_eq_sum_of_support_subset
  intro y hy
  rw [Function.mem_support, Finset.prod_ne_zero_iff] at hy
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro j
  simpa using hy j (Finset.mem_univ j)

theorem eval_eq_ite_prod_of_finprod (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ) (S0 : Finset ι)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0)
    (hprod : ∀ g, s g = ∏ᶠ i, s' i (p i g)) (g : G) :
    s g = if ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k then ∏ i ∈ S0, s' i (p i g) else 0 := by
  rw [hprod]
  have hfin : {i | p i g ∉ KH i}.Finite := Filter.eventually_cofinite.mp (hcof g)
  set B : Finset ι := S0 ∪ hfin.toFinset with hB
  have hone : ∀ i ∉ B, s' i (p i g) = 1 := by
    intro i hi
    simp only [B, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    rw [hS0 i hi.1, if_pos ⟨1, (TH i).one_mem, p i g, hi.2, (one_mul _).symm⟩]
  rw [finprod_eq_prod_of_mulSupport_subset (f := fun i => s' i (p i g)) (s := B) (fun i hi => by by_contra h; exact hi (hone i h))]
  split_ifs with hgood
  · symm
    apply Finset.prod_subset Finset.subset_union_left
    intro i _ hi
    rw [hS0 i hi, if_pos (hgood i hi)]
  · push_neg at hgood
    obtain ⟨i, hi, hbad⟩ := hgood
    apply Finset.prod_eq_zero (i := i)
    · refine Finset.mem_union_right _ ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hk
      exact hbad 1 (TH i).one_mem (p i g) hk (one_mul _).symm
    · rw [hS0 i hi, if_neg (by push_neg; exact hbad)]

theorem doubleCoset_mk_eq_of_local (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (S0 : Finset ι)
    (hsurj : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (g g' : G) (hg : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k)
    (hg' : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * k)
    (h : ∀ i ∈ S0, DoubleCoset.mk (TH i) (KH i) (p i g) = DoubleCoset.mk (TH i) (KH i) (p i g')) :
    DoubleCoset.mk T K g = DoubleCoset.mk T K g' := by
  have hloc : ∀ i, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * p i g * k ∧
      (p i g ∈ KH i → p i g' ∈ KH i → t = 1) := by
    intro i
    by_cases hk : p i g ∈ KH i ∧ p i g' ∈ KH i
    · exact ⟨1, (TH i).one_mem, (p i g)⁻¹ * p i g', mul_mem (inv_mem hk.1) hk.2, by group,
        fun _ _ => rfl⟩
    · by_cases hi : i ∈ S0
      · obtain ⟨t, ht, k, hk', he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 (h i hi)
        exact ⟨t, ht, k, hk', he, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
      · obtain ⟨a, ha, b, hb, hab⟩ := hg i hi
        obtain ⟨a', ha', b', hb', hab'⟩ := hg' i hi
        refine ⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), b⁻¹ * b', mul_mem (inv_mem hb) hb', ?_,
          fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
        rw [hab, hab']; group
  choose t ht k hk he h1 using hloc
  obtain ⟨x, hx⟩ := hsurj t (by
    filter_upwards [hcof g, hcof g'] with i hi hi'
    rw [h1 i hi hi']; exact (KH i).one_mem)
  rw [DoubleCoset.eq]
  refine ⟨x, (hT x).2 (fun i => by rw [hx]; exact ht i), g⁻¹ * x⁻¹ * g', (hK _).2 (fun i => ?_), by group⟩
  rw [map_mul, map_mul, map_inv, map_inv, hx, he i]
  convert hk i using 1
  group

theorem finsum_doubleCoset_eq_finprod_local : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ t ∈ TH i, ∀ k ∈ KH i, ∀ x, s' i (t * x * k) = s' i x) → (∀ i, {q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)) | s' i (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ i in cofinite, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0) → (∀ g, s g = ∏ᶠ i, s' i (p i g)) → ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) = ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q) := by
  intro ι G _ H _ p T K TH KH s s' hsurj hcof hK hT hinv hfin hgood hprod
  have hS0fin := Filter.eventually_cofinite.mp hgood
  set S0 : Finset ι := hS0fin.toFinset with hS0def
  have hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0 := by
    intro i hi
    simpa [S0] using hi
  have hloc : ∀ i (x : H i), s' i (Quotient.out (DoubleCoset.mk (TH i) (KH i) x)) = s' i x := by
    intro i x
    obtain ⟨a, ha, b, hb, he⟩ := DoubleCoset.mk_out_eq_mul (TH i) (KH i) x
    rw [he, hinv i a ha b hb]
  have hR : ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q)
      = ∏ i : S0, ∑ᶠ q : DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)), s' i.1 (Quotient.out q) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S0)]
    · exact (Finset.prod_coe_sort S0 (fun i => ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q))).symm
    · intro i hi
      by_contra h
      exact hi (finsum_doubleCoset_trivial_eq_one (H i) (TH i) (KH i) (s' i) (hS0 i h))
  rw [hR, ← finsum_pi_prod_eq_prod_finsum S0 (fun i : S0 => DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)))
    (fun i q => s' i.1 (Quotient.out q)) (fun i => hfin i.1)]
  obtain ⟨A, hAdef⟩ : ∃ A : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)),
      ∀ q, q ∈ A ↔ ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k :=
    ⟨{q | ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k}, fun q => Iff.rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : DoubleCoset.Quotient (T : Set G) (K : Set G) →
      ∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)),
      ∀ q i, Φ q i = DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q)) :=
    ⟨fun q i => DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q)), fun _ _ => rfl⟩
  have hLHS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) =
      ∑ᶠ (_ : q ∈ A), ∏ i : S0, s' i.1 (Quotient.out (Φ q i)) := by
    intro q
    rw [finsum_eq_if, eval_eq_ite_prod_of_finprod ι G H p TH KH s s' S0 hcof hS0 hprod (Quotient.out q)]
    by_cases hq : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k
    · rw [if_pos hq, if_pos ((hAdef q).2 hq), ← Finset.prod_coe_sort S0]
      simp only [hΦ, hloc]
    · rw [if_neg hq, if_neg (fun h => hq ((hAdef q).1 h))]
  refine (finsum_congr hLHS).trans ?_
  refine (finsum_mem_eq_of_bijOn (t := Set.univ)
    (g := fun y : (∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1))) =>
      ∏ j : S0, s' j.1 (Quotient.out (y j))) Φ ?_ (fun q _ => rfl)).trans (finsum_mem_univ _)
  refine ⟨fun q _ => Set.mem_univ _, ?_, ?_⟩
  · intro q hq q' hq' he
    rw [← DoubleCoset.out_eq' q, ← DoubleCoset.out_eq' q']
    refine doubleCoset_mk_eq_of_local ι G H p T K TH KH S0 hsurj hcof hK hT _ _ ((hAdef q).1 hq) ((hAdef q').1 hq') (fun i hi => ?_)
    have := congrFun he ⟨i, hi⟩
    rwa [hΦ, hΦ] at this
  · intro y _
    obtain ⟨g, hg⟩ := hsurj (fun i => if hi : i ∈ S0 then Quotient.out (y ⟨i, hi⟩) else 1) (by
      filter_upwards [S0.finite_toSet.compl_mem_cofinite] with i hi
      rw [dite_eq_right (by simpa using hi)]; exact (KH i).one_mem)
    obtain ⟨a, ha, b, hb, he⟩ := DoubleCoset.mk_out_eq_mul T K g
    refine ⟨DoubleCoset.mk T K g, ?_, ?_⟩
    · rw [hAdef]
      intro i hi
      refine ⟨p i a, (hT a).1 ha i, p i b, (hK b).1 hb i, ?_⟩
      rw [he, map_mul, map_mul, hg i, dite_eq_right hi, mul_one]
    · funext i
      rw [hΦ, he, map_mul, map_mul, hg i.1, dite_eq_left i.2]
      show DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) = y i
      have h1 : DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) =
          DoubleCoset.mk (TH i.1) (KH i.1) (Quotient.out (y i)) :=
        (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(p i.1 a)⁻¹, inv_mem ((hT a).1 ha i.1), (p i.1 b)⁻¹,
          inv_mem ((hK b).1 hb i.1), by group⟩
      rw [h1, DoubleCoset.out_eq']

end GlobalTheory.DoubleCosetEuler
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRegroupFibreBij
section
namespace GlobalTheory

theorem finsum_regroup_fibre_bij {α ι : Type} {κ : ι → Type} (U : α → ℂ)
    (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i)
    (hU : (Function.support U).Finite)
    (hval : ∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a)
    (hinj : ∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a')
    (hsurj : ∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) :
    ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  classical
  set S : Finset α := hU.toFinset with hS
  have hmem : ∀ a, a ∈ S ↔ U a ≠ 0 := fun a => by simp [hS]
  have hin : ∀ i, ∑ᶠ c, W i c = ∑ a ∈ S.filter (fun a => π a = i), U a := by
    intro i
    have h1 : Function.support (W i) ⊆
        ((S.filter (fun a => π a = i)).image (Φ i) : Finset (κ i)) := by
      intro c hc
      obtain ⟨a, ha, hUa, hac⟩ := hsurj i c hc
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
      exact ⟨a, ⟨(hmem a).2 hUa, ha⟩, hac⟩
    rw [finsum_eq_sum_of_support_subset _ h1, Finset.sum_image]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      subst ha2
      exact hval a ((hmem a).1 ha1)
    · intro a ha a' ha' h
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      obtain ⟨ha1', ha2'⟩ := Finset.mem_filter.1 ha'
      subst ha2
      exact hinj a a' ((hmem a).1 ha1) ((hmem a').1 ha1') ha2' h
  simp only [hin]
  have h2 : Function.support (fun i => ∑ a ∈ S.filter (fun a => π a = i), U a) ⊆
      (S.image π : Finset ι) := by
    intro i hi
    obtain ⟨a, ha, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨a, ha1, ha2⟩
  rw [finsum_eq_sum_of_support_subset _ h2, finsum_eq_sum U hU,
    Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem π ha)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiveElementaryInequalitiesEventually
section
open Filter Real

namespace GlobalTheory

theorem eventually_const_mul_rpow_le_rpow (a b c : ℝ) (h : a < b) :
    ∀ᶠ x : ℝ in atTop, c * x ^ a ≤ x ^ b := by
  have ht := tendsto_rpow_atTop (sub_pos.2 h)
  filter_upwards [ht.eventually_ge_atTop c, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have e : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

theorem sqrt_mul_rpow_neg_eq (eps x : ℝ) (hx : 0 < x) :
    Real.sqrt (x * x ^ (-(eps / 8))) = x ^ (1 / 2 - eps / 16) := by
  have h1 : x * x ^ (-(eps / 8)) = x ^ (1 - eps / 8) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  ring_nf

theorem five_elementary_inequalities_eventually :
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧
      11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧
      2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧
      44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
  intro eps he he1
  have h1 := eventually_const_mul_rpow_le_rpow (eps / 4) eps 20 (by linarith)
  have h2 := eventually_const_mul_rpow_le_rpow (eps / 3) eps 20 (by linarith)
  have h3 := eventually_const_mul_rpow_le_rpow 0 eps 20 he
  have h4 := (isLittleO_log_rpow_atTop he).bound (show (0:ℝ) < 1 / 60 by norm_num)
  have h5 := eventually_const_mul_rpow_le_rpow 0 (eps / 5) 11 (by linarith)
  have h6 := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1 / 4 by norm_num)
  have h7 := eventually_const_mul_rpow_le_rpow (eps / 5 + eps / 100) (1 / 2 - eps / 16) 2
    (by linarith)
  have h8 := eventually_const_mul_rpow_le_rpow 0 (1 / 2 - eps / 16) 44 (by linarith)
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, eventually_gt_atTop (0 : ℝ)]
    with x h1 h2 h3 h4 h5 h6 h7 h8 hx
  rw [Real.rpow_zero] at h3 h5 h8
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)] at h4
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx] at h6
  rw [sqrt_mul_rpow_neg_eq eps x hx]
  have hl := le_abs_self (Real.log x)
  refine ⟨by linarith, by linarith, ?_, h7, by linarith⟩
  nlinarith [abs_nonneg (Real.log x), sq_abs (Real.log x)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedFieldKerToPermFiniteIsGaloisFinrankDvd
section
open IntermediateField

namespace GlobalTheory

theorem fixedField_ker_toPerm_finite_isGalois_finrank_dvd (Ω K : Type) [Field Ω] [Field K]
    [Algebra Ω K] [IsAlgClosure Ω K] [CharZero Ω] (n : ℕ)
    (φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin n)) :
    FiniteDimensional Ω (IntermediateField.fixedField φ.ker) ∧
      IsGalois Ω (IntermediateField.fixedField φ.ker) ∧
      Module.finrank Ω (IntermediateField.fixedField φ.ker) ∣ n.factorial := by
  haveI : Algebra.IsAlgebraic Ω K := IsAlgClosure.isAlgebraic
  haveI : Normal Ω K := IsAlgClosure.normal Ω K
  haveI : IsGalois Ω K := ⟨⟩
  set E : IntermediateField Ω K := fixedField φ.ker with hE
  have hHF : φ.ker ≤ E.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hker : φ.ker.index ∣ n.factorial := by
    rw [Subgroup.index_ker]
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hF : E.fixingSubgroup.index ∣ n.factorial :=
    (Subgroup.index_dvd_of_le hHF).trans hker
  haveI : E.fixingSubgroup.FiniteIndex :=
    ⟨fun h => (Nat.factorial_pos n).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hF))⟩
  have hopen : IsOpen (E.fixingSubgroup : Set (K ≃ₐ[Ω] K)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (InfiniteGalois.fixingSubgroup_isClosed E)
  haveI hfin : FiniteDimensional Ω E := (InfiniteGalois.isOpen_iff_finite E).1 hopen
  have hnorm : E.fixingSubgroup.Normal := by
    constructor
    intro σ hσ g
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hx' : g⁻¹ x ∈ E := by
      rw [hE, IntermediateField.mem_fixedField_iff] at hx ⊢
      intro h hh
      have hc : g * h * g⁻¹ ∈ φ.ker := (MonoidHom.normal_ker φ).conj_mem h hh g
      have := hx _ hc
      calc h (g⁻¹ x) = g⁻¹ ((g * h * g⁻¹) x) := by simp [AlgEquiv.mul_apply]
        _ = g⁻¹ x := by rw [this]
    have h2 := hσ _ hx'
    simp only [AlgEquiv.mul_apply]
    change g (σ (g⁻¹ x)) = x
    rw [h2]
    exact g.apply_symm_apply x
  haveI hgal : IsGalois Ω E := (InfiniteGalois.normal_iff_isGalois E).1 hnorm
  refine ⟨hfin, hgal, ?_⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  exact hF

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNorms
section
open NumberField

namespace GlobalTheory

theorem units_ringOfIntegers_mod_sq (L : Type) [Field L] [NumberField L] :
    ∃ R : Finset (𝓞 L)ˣ, ∀ x : (𝓞 L)ˣ, ∃ ρ ∈ R, ∃ w : (𝓞 L)ˣ, x = ρ * w ^ 2 := by
  classical
  let N : Submodule ℤ (Additive (𝓞 L)ˣ) := LinearMap.range ((2 : ℤ) • LinearMap.id)
  haveI : Module.Finite ℤ (Additive (𝓞 L)ˣ) := inferInstance
  haveI : Finite (Additive (𝓞 L)ˣ ⧸ N) := by
    refine Module.finite_of_fg_torsion _ fun q => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      show (2 : ℤ) • (Submodule.Quotient.mk (p := N) x) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, rfl⟩
  haveI : Fintype (Additive (𝓞 L)ˣ ⧸ N) := Fintype.ofFinite _
  let rep := Function.surjInv (Submodule.Quotient.mk_surjective N)
  refine ⟨Finset.univ.image (fun q => Additive.toMul (rep q)), fun x => ?_⟩
  let q : Additive (𝓞 L)ˣ ⧸ N := Submodule.Quotient.mk (Additive.ofMul x)
  refine ⟨Additive.toMul (rep q), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have hq : Submodule.Quotient.mk (p := N) (rep q) = q := Function.surjInv_eq _ q
  have hmem : Additive.ofMul x - rep q ∈ N := by
    rw [← Submodule.Quotient.eq]; exact hq.symm
  obtain ⟨y, hy⟩ := hmem
  refine ⟨Additive.toMul y, ?_⟩
  have h2 : Additive.toMul ((2 : ℤ) • y) = Additive.toMul (Additive.ofMul x - rep q) := by
    simpa using congrArg Additive.toMul hy
  rw [toMul_zsmul, toMul_sub, toMul_ofMul] at h2
  rw [eq_div_iff_mul_eq'] at h2
  rw [← h2]; exact mul_comm _ _

theorem units_fixed_eq_mul_mul_conj : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∃ S : Finset L, ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) → c ε = ε →
      ∃ f ∈ S, ∃ η : Lˣ, IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ (ε : L) = f * ((η : L) * c η) := by
  intro L _ _ c _hc
  classical
  obtain ⟨R, hR⟩ := units_ringOfIntegers_mod_sq L
  let φ : 𝓞 L →* L := (algebraMap (𝓞 L) L : 𝓞 L →* L)
  have hA : ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) →
      ∃ ρ ∈ R, ∃ w : (𝓞 L)ˣ, (ε : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2 := by
    intro ε h1 h2
    let u : (𝓞 L)ˣ := ⟨⟨ε, h1⟩, ⟨((ε⁻¹ : Lˣ) : L), h2⟩,
      by apply RingOfIntegers.ext; exact ε.mul_inv, by apply RingOfIntegers.ext; exact ε.inv_mul⟩
    obtain ⟨ρ, hρ, w, hw⟩ := hR u
    refine ⟨ρ, hρ, w, ?_⟩
    calc (ε : L) = φ (u : 𝓞 L) := rfl
      _ = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2 := by rw [hw, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  let P : (𝓞 L)ˣ → Prop := fun ρ => ∃ e : Lˣ, IsIntegral ℤ (e : L) ∧ IsIntegral ℤ ((e⁻¹ : Lˣ) : L) ∧
    c e = e ∧ ∃ w : (𝓞 L)ˣ, (e : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2
  let pick : (𝓞 L)ˣ → Finset L := fun ρ =>
    if h : P ρ then {((Classical.choose h : Lˣ) : L), -((Classical.choose h : Lˣ) : L)} else ∅
  refine ⟨R.biUnion pick, ?_⟩
  intro ε h1 h2 hfix
  obtain ⟨ρ, hρ, w, hw⟩ := hA ε h1 h2
  have hP : P ρ := ⟨ε, h1, h2, hfix, w, hw⟩
  obtain ⟨_g1, _g2, gfix, w', hw'⟩ := Classical.choose_spec hP
  have hpick : pick ρ = {((Classical.choose hP : Lˣ) : L), -((Classical.choose hP : Lˣ) : L)} := by
    simp only [pick, dif_pos hP]
  set e : Lˣ := Classical.choose hP with he
  let W : Lˣ := Units.map φ (w * w'⁻¹)
  have hint : ∀ v : (𝓞 L)ˣ, IsIntegral ℤ (φ (v : 𝓞 L)) := fun v => RingOfIntegers.isIntegral_coe _
  have hWint : IsIntegral ℤ (W : L) := hint _
  have hWint' : IsIntegral ℤ ((W⁻¹ : Lˣ) : L) := by
    have : W⁻¹ = Units.map φ (w * w'⁻¹)⁻¹ := (map_inv _ _).symm
    rw [this]; exact hint _
  have hw'0 : φ (w' : 𝓞 L) ≠ 0 := (Units.map φ w').ne_zero
  have hWval : (W : L) = φ (w : 𝓞 L) * (φ (w' : 𝓞 L))⁻¹ := by
    have : W = Units.map φ w * (Units.map φ w')⁻¹ := by simp only [W, map_mul, map_inv]
    rw [this, Units.val_mul, Units.val_inv_eq_inv_val]; rfl
  have key : (ε : L) = (e : L) * (W : L) ^ 2 := by
    rw [hWval, hw', hw]; field_simp
  have he0 : (e : L) ≠ 0 := e.ne_zero
  have hsq : (c (W : L)) ^ 2 = (W : L) ^ 2 := by
    have h3 : c (ε : L) = c (e : L) * (c (W : L)) ^ 2 := by rw [key, map_mul, map_pow]
    rw [hfix, gfix, key] at h3
    exact (mul_left_cancel₀ he0 h3).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · refine ⟨(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩
    rw [key, h]; ring
  · refine ⟨-(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩
    rw [key, h]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfForallFinsetSubsetFlat
section
open TensorProduct LinearMap

namespace GlobalTheory

theorem flat_of_forall_finset_subset_flat :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M],
      (∀ s : Finset M, ∃ N : Submodule R M, (↑s : Set M) ⊆ ↑N ∧ Module.Flat R ↥N) →
        Module.Flat R M := by
  intro R M _ _ _ h
  refine Module.Flat.iff_lTensor_injective'.mpr fun I => ?_
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨J, hfg, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype (R := R) (M := ↥I) x
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨N, hsN, hN⟩ := h s
  have hJN : J ≤ N := hs ▸ Submodule.span_le.mpr hsN
  obtain ⟨y', hy'⟩ : ∃ y' : ↥N ⊗[R] ↥I, y' = rTensor (↥I) (Submodule.inclusion hJN) y := ⟨_, rfl⟩
  have hxy : rTensor (↥I) J.subtype y = rTensor (↥I) N.subtype y' := by
    rw [hy', ← rTensor_comp_apply]; rfl
  rw [hxy] at hx ⊢
  have hcomm : lTensor M I.subtype (rTensor (↥I) N.subtype y') =
      rTensor R N.subtype (lTensor (↥N) I.subtype y') := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, lTensor_comp_rTensor, rTensor_comp_lTensor]
  rw [hcomm] at hx
  have hinj1 : Function.Injective (rTensor R N.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R) N.subtype Subtype.val_injective
  have h0 : lTensor (↥N) I.subtype y' = 0 := hinj1 (by rw [hx, map_zero])
  have hinj2 : Function.Injective (lTensor (↥N) I.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := ↥N) I.subtype Subtype.val_injective
  have : y' = 0 := hinj2 (by rw [h0, map_zero])
  rw [this, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSubschemeOfQuotientFlatAffine
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem closedSub_flat_of_quotient_flat : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  intro V _ X _ p J h
  have : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  set U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : (J.subschemeι ≫ p).appTop.hom =
      (J.subschemeObjIso U).inv.hom.comp
        (((Ideal.Quotient.mk (J.ideal U)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).comp
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom) := by
    have h2 := J.subschemeι_app U
    have h3 : J.subschemeι.appTop = CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)) ≫ (J.subschemeObjIso U).inv := h2
    rw [Scheme.Hom.comp_appTop, h3]
    ext x
    change (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom x)) =
      (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x))))
    rw [Iso.hom_inv_id_apply]
  rw [e]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (J.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.bijective)
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.bijective) h

end GlobalTheory
end

