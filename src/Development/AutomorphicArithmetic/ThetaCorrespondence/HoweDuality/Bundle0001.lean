module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0052

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Nak
section
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.nak :
    ∀ {M T R : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T] (j : R → M →ₗ[ℂ] T) (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (N : Submodule ℂ T), (⨆ r, LinearMap.range (j r)) = ⊤ → (∀ g ∈ Op, ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (g x)) ∧ ∀ t ∈ N, Φ t ∈ N) → (∀ r, ∀ x ∈ Rel, j r x ∈ N) → RadFin Op Rel K → N ⊔ (⨆ r, K.map (j r)) = ⊤ → N = ⊤ := by
  intro M T R _ _ _ _ j Op Rel K N hspan hOp hRel hRad hsup
  classical
  have h1 : ∀ e ∈ Algebra.adjoin ℂ Op,
      ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (e x)) ∧ ∀ t ∈ N, Φ t ∈ N := by
    intro e he
    induction he using Algebra.adjoin_induction with
    | mem g hg => exact hOp g hg
    | algebraMap c =>
      refine ⟨c • (1 : Module.End ℂ T), fun r x => ?_, fun t ht => ?_⟩
      · simp [Algebra.algebraMap_eq_smul_one]
      · simpa using N.smul_mem c ht
    | add a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A + B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using N.add_mem (hAN t ht) (hBN t ht)
    | mul a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A * B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using hAN _ (hBN t ht)
  have h2 : ∀ u ∈ (⨆ r, K.map (j r)), ∃ S : Finset M, (∀ k ∈ S, k ∈ K) ∧
      ∀ (e : Module.End ℂ M) (Φ : Module.End ℂ T), (∀ r x, Φ (j r x) = j r (e x)) →
        (∀ k ∈ S, e k ∈ Rel) → Φ u ∈ N := by
    intro u hu
    induction hu using Submodule.iSup_induction' with
    | mem r x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨{k}, by simpa using hk, fun e Φ hΦ hS => ?_⟩
      rw [hΦ]
      exact hRel r _ (hS k (Finset.mem_singleton_self k))
    | zero => exact ⟨∅, by simp, fun e Φ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨S, hS, hS'⟩ := hx
      obtain ⟨S2, hS2, hS2'⟩ := hy
      refine ⟨S ∪ S2, fun k hk => ?_, fun e Φ hΦ h => ?_⟩
      · rcases Finset.mem_union.1 hk with h | h
        · exact hS k h
        · exact hS2 k h
      · rw [map_add (f := _)]
        exact N.add_mem (hS' e Φ hΦ fun k hk => h k (Finset.mem_union_left _ hk))
          (hS2' e Φ hΦ fun k hk => h k (Finset.mem_union_right _ hk))
  obtain ⟨s, hGen, hs⟩ := hRad
  have h3 : ∀ r, j r s ∈ N := by
    intro r
    have hm : j r s ∈ N ⊔ (⨆ r, K.map (j r)) := by rw [hsup]; trivial
    obtain ⟨n, hn, u, hu, hnu⟩ := Submodule.mem_sup.1 hm
    obtain ⟨S, hSK, hS⟩ := h2 u hu
    obtain ⟨e, he, hes, heS⟩ := hs S hSK
    obtain ⟨Φ, hΦ, hΦN⟩ := h1 e he
    have : j r s = Φ n + Φ u := by rw [← map_add (f := _), hnu, hΦ, hes]
    rw [this]
    exact N.add_mem (hΦN n hn) (hS e Φ hΦ heS)
  have h4 : ∀ r, N.comap (j r) = ⊤ := by
    intro r
    refine hGen _ (fun x hx => hRel r x hx) (fun g hg x hx => ?_) (h3 r)
    obtain ⟨Φ, hΦ, hΦN⟩ := hOp g hg
    show j r (g x) ∈ N
    rw [← hΦ]
    exact hΦN _ hx
  rw [eq_top_iff, ← hspan]
  refine iSup_le fun r => ?_
  rintro _ ⟨x, rfl⟩
  have : x ∈ N.comap (j r) := by rw [h4 r]; trivial
  exact this
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.PartStable
section
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.partStable :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
      {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
      (i : ι) (K : Submodule ℂ (M i)),
      (∀ g : Module.End ℂ M₀, ∀ t ∈ part (M₀ := M₀) i K,
        TensorProduct.map g LinearMap.id t ∈ part (M₀ := M₀) i K) ∧
      (∀ g : Module.End ℂ (M i), (∀ x ∈ K, g x ∈ K) → ∀ t ∈ part (M₀ := M₀) i K,
        factorOp i g t ∈ part (M₀ := M₀) i K) ∧
      ∀ l, l ≠ i → ∀ g : Module.End ℂ (M l), ∀ t ∈ part (M₀ := M₀) i K,
        factorOp l g t ∈ part (M₀ := M₀) i K := by
  intro ι _ _ M₀ _ _ M _ _ i K
  have mem : ∀ (r : M₀ × ∀ j, M j), ∀ x ∈ K,
      intersection_update_fsHerm_neg_one i r x ∈ part (M₀ := M₀) i K := fun r x hx =>
    (le_iSup (fun r : M₀ × ∀ j, M j => K.map (intersection_update_fsHerm_neg_one i r)) r) (Submodule.mem_map_of_mem hx)
  have key : ∀ Φ : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ (r : M₀ × ∀ j, M j), ∀ x ∈ K,
        Φ (intersection_update_fsHerm_neg_one i r x) ∈ part (M₀ := M₀) i K) →
      ∀ t ∈ part (M₀ := M₀) i K, Φ t ∈ part (M₀ := M₀) i K := by
    intro Φ h t ht
    have : part (M₀ := M₀) i K ≤ (part (M₀ := M₀) i K).comap Φ :=
      iSup_le fun r => Submodule.map_le_iff_le_comap.2 fun x hx => h r x hx
    exact this ht
  refine ⟨fun g => key _ fun r x hx => ?_, fun g hg => key _ fun r x hx => ?_,
    fun l hl g => key _ fun r x hx => ?_⟩
  · have := mem (g r.1, r.2) x hx
    simpa [position_apply] using this
  · have := mem r (g x) (hg x hx)
    rw [position_apply] at this
    rw [position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    convert this using 3
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  · have := mem (r.1, Function.update r.2 l (g (r.2 l))) x hx
    rw [position_apply] at this
    rw [position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    convert this using 3
    funext j
    by_cases hj : j = i
    · subst hj; simp [Function.update_of_ne hl.symm]
    · by_cases hj' : j = l
      · subst hj'; simp [Function.update_of_ne hj]
      · simp [Function.update_of_ne hj, Function.update_of_ne hj']
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadFin
section
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

private theorem UpperTheory.Lit.HoweDuality.radFin_adjoin_stable {M : Type} [AddCommGroup M] [Module ℂ M]
    (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) (hP : Stable Op P)
    (e : Module.End ℂ M) (he : e ∈ Algebra.adjoin ℂ Op) : ∀ x ∈ P, e x ∈ P :=
  _root_.UpperTheory.Reformulated.B.Qj9.radFin_adjoin_stable Op P hP e he

theorem UpperTheory.Lit.HoweDuality.radFin :
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M), Stable Op Rel → Stable Op K → Rad Op Rel K → RadFin Op Rel K := by
  intro M _ _ Op Rel K hRel hK hRad
  classical
  obtain ⟨s, hs, h⟩ := hRad
  refine ⟨s, hs, fun S => ?_⟩
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨1, one_mem _, rfl, by simp⟩
  | insert k S _ ih =>
    intro hS
    obtain ⟨e', he', hs', hk'⟩ := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    have hkK : e' k ∈ K :=
      radFin_adjoin_stable Op K hK e' he' k (hS k (Finset.mem_insert_self _ _))
    obtain ⟨e'', he'', hs'', hk''⟩ := h _ hkK
    refine ⟨e'' * e', mul_mem he'' he', by simp [hs', hs''], fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using hk''
    · simpa using radFin_adjoin_stable Op Rel hRel e'' he'' _ (hk' x hx)
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.SlotBasic
section
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.slotFacts :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι), (⨆ r : M₀ × (∀ j, M j), LinearMap.range (intersection_update_fsHerm_neg_one i r)) = ⊤ ∧ ∀ (g : Module.End ℂ (M i)) (r : M₀ × (∀ j, M j)) (x : M i), factorOp i g (intersection_update_fsHerm_neg_one i r x) = intersection_update_fsHerm_neg_one i r (g x) := by
  intro ι _ _ M₀ _ _ M _ _ i
  refine ⟨?_, ?_⟩
  · rw [Submodule.eq_top_iff']
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul x₀ w =>
      induction w using PiTensorProduct.induction_on with
      | smul_tprod c y =>
        rw [TensorProduct.tmul_smul]
        refine Submodule.smul_mem _ c ?_
        refine Submodule.mem_iSup_of_mem (x₀, y) ⟨y i, ?_⟩
        rw [position_apply]
        simp only [Function.update_eq_self]
      | add a b ha hb =>
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb
  · intro g r x
    rw [position_apply, position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
end

