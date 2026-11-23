module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsAutomorphismPreservingTranslatesCoordOne
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem unimodular_to_coord_one : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n →
    ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R),
      (∀ x, ψ x ∈ low R (n + 1) ↔ x ∈ low R (n + 1)) ∧ (∀ j x, ψ x ∈ aff R (n + 1) j ↔ x ∈ aff R (n + 1) j) ∧
      ψ v n = 1 := by
  intro R _ s hs n hn v hv
  obtain ⟨F, hF⟩ := hv
  let f := F ⟨0, by simp⟩
  have hfv : f v = 1 := by
    have := hF ⟨0, by simp⟩ ⟨0, by simp⟩
    simpa [f] using this
  let a : Fin n → R := fun i => f (Finsupp.single (i : ℕ) 1)
  let h : (ℕ →₀ R) →ₗ[R] R := f - ∑ i : Fin n, a i • Finsupp.lapply (i : ℕ)
  have hh : ∀ x, h x = f x - ∑ i : Fin n, a i * x i := by
    intro x; simp [h]
  let r : Fin (n + 1) → R := Fin.snoc (fun i : Fin n => v i) (h v)
  have hr : Unimodular R r := by
    rw [Unimodular, Ideal.eq_top_iff_one]
    have e : (1:R) = ∑ i : Fin n, a i * r i.castSucc + 1 * r (Fin.last n) := by
      simp only [r, Fin.snoc_castSucc, Fin.snoc_last, hh, hfv, one_mul]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨t', ht'⟩ := hs n hn r hr
  simp only [r, Fin.snoc_castSucc, Fin.snoc_last] at ht'
  let t : ℕ →₀ R := ∑ j : Fin n, Finsupp.single (j : ℕ) (t' j)
  have htapp : ∀ k, t k = if hk : k < n then t' ⟨k, hk⟩ else 0 := by
    intro k
    simp only [t, Finsupp.finsetSum_apply, Finsupp.single_apply]
    split_ifs with hk
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro b _ hb; rw [if_neg]; intro e; apply hb; ext; exact e
      · simp
    · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; intro e; apply hk; rw [← e]; exact b.2
  have htlow : t ∈ low R n := fun k hk => by rw [htapp, dite_eq_right (by omega)]
  have htlow' : t ∈ low R (n + 1) := fun k hk => htlow k (by omega)
  have hht : h t = 0 := by
    rw [hh]
    have h1 : f t = ∑ j : Fin n, t' j * a j := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [t, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
    have h2 : ∑ i : Fin n, a i * t i = ∑ j : Fin n, t' j * a j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htapp, dite_eq_left j.2, mul_comm]
    rw [h1, h2, sub_self]
  obtain ⟨ψ1, hψ1, hψ1l, hψ1a⟩ := GlobalTheory.T.exists_transvection_preserving_low_and_aff R (n + 1) h t htlow' hht
  have hv' : ∀ i : Fin n, ψ1 v i = v i + t' i * h v := by
    intro i
    rw [hψ1, Finsupp.add_apply, Finsupp.smul_apply, htapp, dite_eq_left i.2, smul_eq_mul, mul_comm]
  have hv'n : ψ1 v n = v n := by
    rw [hψ1, Finsupp.add_apply, Finsupp.smul_apply, htapp, dite_eq_right (lt_irrefl n), smul_zero, add_zero]
  have hmem : (1 - v n) ∈ Ideal.span (Set.range fun i : Fin n => v i + t' i * h v) := by
    rw [ht']; trivial
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
  let h2 : (ℕ →₀ R) →ₗ[R] R := ∑ i : Fin n, c i • Finsupp.lapply (i : ℕ)
  have hh2 : ∀ x, h2 x = ∑ i : Fin n, c i * x i := by
    intro x; simp [h2]
  have ht2low : Finsupp.single n (1 : R) ∈ low R (n + 1) := fun k hk => by
    rw [Finsupp.single_apply, if_neg (by omega)]
  have hht2 : h2 (Finsupp.single n 1) = 0 := by
    rw [hh2]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := i.2
    rw [Finsupp.single_apply, if_neg (by omega), mul_zero]
  obtain ⟨ψ2, hψ2, hψ2l, hψ2a⟩ := GlobalTheory.T.exists_transvection_preserving_low_and_aff R (n + 1) h2 _ ht2low hht2
  refine ⟨ψ1.trans ψ2, fun x => ?_, fun j x => ?_, ?_⟩
  · rw [LinearEquiv.trans_apply, hψ2l, hψ1l]
  · rw [LinearEquiv.trans_apply, hψ2a, hψ1a]
  · rw [LinearEquiv.trans_apply, hψ2, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, hh2, hv'n]
    have : ∑ i : Fin n, c i * ψ1 v i = 1 - v n := by
      rw [← hc]; exact Finset.sum_congr rfl fun i _ => by rw [hv' i]
    rw [this]; ring

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_automorphism_preserving_translates_coord_one : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n → ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x ∈ low R (n + 1) ↔ x ∈ low R (n + 1)) ∧ (∀ j x, ψ x ∈ aff R (n + 1) j ↔ x ∈ aff R (n + 1) j) ∧ ψ v n = 1 := by
  first
  | exact @GlobalTheory.unimodular_to_coord_one
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyMapEqOfInnerConj
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.ConjMap

noncomputable def actHom {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) :
    B ⟶ Rep.res (MulAut.conj g).toMonoidHom B :=
  Rep.ofHom (X := B.V) (Y := B.V) (ρ := B.ρ) (σ := (Rep.res (MulAut.conj g).toMonoidHom B).ρ)
    ⟨B.ρ g, fun h => by ext x; simp [Rep.res]⟩

lemma actHom_apply {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) (x : B) :
    (actHom B g).hom x = B.ρ g x := rfl

end GlobalTheory.HomStab.ConjMap

open GlobalTheory.HomStab.ConjMap in
theorem GlobalTheory.HomStab.groupHomology_map_conj : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (A : Rep k H) (B : Rep k G) (f₁ f₂ : H →* G) (u₁ : A ⟶ Rep.res f₁ B) (u₂ : A ⟶ Rep.res f₂ B) (g : G), (∀ h, f₂ h = g * f₁ h * g⁻¹) → (∀ a, u₂.hom a = B.ρ g (u₁.hom a)) → ∀ n : ℕ, groupHomology.map f₂ u₂ n = groupHomology.map f₁ u₁ n := by
  intro k G H _ _ _ A B f₁ f₂ u₁ u₂ g hf hu n
  have hf' : f₂ = (MulAut.conj g).toMonoidHom.comp f₁ := by
    ext h; simp [hf h]
  have e : groupHomology.map f₂ u₂ n =
      groupHomology.map ((MulAut.conj g).toMonoidHom.comp f₁)
        (u₁ ≫ (Rep.resFunctor f₁).map (actHom B g)) n := by
    apply groupHomology.map_congr hf'
    ext a
    simp [hu a, actHom_apply]
    rfl
  rw [e, groupHomology.map_comp, GlobalTheory.T.innerAut_acts_trivially_groupHomology k G g n B (actHom B g) (fun a => rfl),
    Category.comp_id]

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.LinkInUniMEqShorterOfFormEqOne
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem linkIn_uniM_eq_of_form :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (S : Set M),
      (∀ x ∈ S, φ x = 0) → ∀ τ ∈ uniM R M, ∀ v ∈ τ, φ v = 1 →
        ∃ τ' ∈ uniM R M, τ'.length + 1 = τ.length ∧
          linkIn (uniM R M) S τ = linkIn (uniM R M) S τ' := by
  intro R M _ _ _ φ S hS τ hτ v hv hφv
  classical
  have hperm := (GlobalTheory.T.subClosed_and_perm_and_linearEquiv_invariant_uniM R M).2.1
  have hmod := GlobalTheory.T.cons_mem_uniM_iff_map_sub_smul R M φ v hφv
  have hp : τ.Perm (v :: τ.erase v) := List.perm_cons_erase hv
  refine ⟨(τ.erase v).map (fun x => x - φ x • v), ?_, ?_, ?_⟩
  · exact (hmod _).1 (hperm _ _ hp hτ)
  · simp [List.length_erase_of_mem hv]
    have := List.length_pos_of_mem hv
    omega
  · ext w
    simp only [linkIn, Set.mem_setOf_eq]
    refine and_congr_right fun hw => ?_
    have hpw : (τ ++ w).Perm (v :: (τ.erase v ++ w)) := hp.append_right w
    have hwfix : w.map (fun x => x - φ x • v) = w := by
      conv_rhs => rw [← List.map_id w]
      apply List.map_congr_left
      intro x hx
      simp [hS x (hw x hx)]
    constructor
    · intro h
      have h1 := (hmod _).1 (hperm _ _ hpw h)
      rwa [List.map_append, hwfix] at h1
    · intro h
      have h1 : (τ.erase v ++ w).map (fun x => x - φ x • v) ∈ uniM R M := by
        rwa [List.map_append, hwfix]
      exact hperm _ _ hpw.symm ((hmod _).2 h1)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.linkIn_uniM_eq_shorter_of_form_eq_one : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (S : Set M), (∀ x ∈ S, φ x = 0) → ∀ τ ∈ uniM R M, ∀ v ∈ τ, φ v = 1 → ∃ τ' ∈ uniM R M, τ'.length + 1 = τ.length ∧ linkIn (uniM R M) S τ = linkIn (uniM R M) S τ' := by
  first
  | exact @GlobalTheory.SeqCx.linkIn_uniM_eq_of_form
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.QuillenStabilisationSurjectiveBottom
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem stab_surj_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  intro k G _ _ i C d hd hs hex M e s hiso hsq hinj hsur
  have hsurjH : Function.Surjective (hMap (d 0) i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i C d hd hs hex ?_
    intro p q hp hpq
    refine GlobalTheory.T.homology_row_exact_of_stabilisation_pattern k G C d hd M e s (i + 2) hiso hsq p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev (by obtain ⟨r, hr⟩ := hev; omega) hpq
    · intro hodd
      exact hsur (p + 1) q hodd.add_one (by omega) (by omega)
  have h0 : e 1 i ≫ hMap (d 0) i = s 0 i ≫ e 0 i := by
    have hev : Even 0 := ⟨0, rfl⟩
    rw [hsq 0 i (by omega)]
    exact if_pos hev
  haveI := hiso 0 i (by omega)
  haveI := hiso 1 i (by omega)
  have b0 := ConcreteCategory.bijective_of_isIso (e 0 i)
  have b1 := ConcreteCategory.bijective_of_isIso (e 1 i)
  intro y
  obtain ⟨w, hw⟩ := hsurjH (e 0 i y)
  obtain ⟨x, rfl⟩ := b1.2 w
  refine ⟨x, b0.1 ?_⟩
  rw [← hw]
  have h1 := congrArg (fun f : M 1 i ⟶ groupHomology (C 0) i => f.hom x) h0
  simpa using h1.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.quillen_stabilisation_surjective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  first
  | exact @GlobalTheory.HomStab.stab_surj_bottom
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ShapiroLemmaTransitiveGroupHomology
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem shapiro_pt : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), Function.Injective φ → φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → (∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n)) ∧ ∀ n : ℕ, IsIso (ptH (k := k) φ x hx n) := by
  intro k G H X _ _ _ _ φ x hx hi hr ht
  have key : ∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n) := by
    intro n
    induction n with
    | zero => exact fun A => GlobalTheory.T.shapiro_isIso_groupHomology_zero k G H X φ x hx hr ht A
    | succ n ih =>
      intro A
      obtain ⟨ι, K, i, e, h, hS⟩ := GlobalTheory.T.exists_free_resolution_short_exact k G A
      have hX := hS.map_of_exact (Rep.resFunctor (k := k) φ)
      obtain ⟨hz, hY⟩ := GlobalTheory.T.permCoef_preserves_shortExact k G X _ hS
      refine GlobalTheory.T.groupHomology_dimension_shift_isIso k G H φ _ _ hX hY (ptMap φ x hx K) (ptMap φ x hx (Rep.free k G ι))
        (ptMap φ x hx A) ?_ ?_ n (GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k H _ (GlobalTheory.T.projective_res_free_rep_of_injective k G H φ hi ι) n)
        (GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k G _ (GlobalTheory.T.projective_perm_tensor_free k G X ι) n) (ih K) (ih _)
      · intro a
        exact (Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom i))).symm
      · intro a
        exact (Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom e))).symm
  exact ⟨key, fun n => key n (Rep.trivial k G k)⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.shapiro_lemma_transitive_groupHomology : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), Function.Injective φ → φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → (∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n)) ∧ ∀ n : ℕ, IsIso (ptH (k := k) φ x hx n) := by
  first
  | exact @GlobalTheory.HomStab.shapiro_pt
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSequenceRepComplexExact
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab.SplitEx

theorem main : ∀ (R : Type) [CommRing R] (n : ℕ), (∀ p, splitD R n (p + 1) ≫ splitD R n p = 0) ∧
    (ExactAt (splitSeq R n) 0 → Function.Surjective (splitD R n 0).hom) ∧
    ∀ p, ExactAt (splitSeq R n) (p + 1) → Function.Exact (splitD R n (p + 1)).hom (splitD R n p).hom := by
  intro R _ n
  have key := T.splitSet_permRep_chains_iso_splitSeq_chains R n
  have hzero : ∀ p (x : SplitSet R n (p + 1 + 1) →₀ ℤ),
      (splitD R n p).hom ((splitD R n (p + 1)).hom x) = 0 := by
    intro p x
    apply (key p).1
    have h1 := (key p).2.2 ((splitD R n (p + 1)).hom x)
    have h2 := (key (p + 1)).2.2 x
    rw [h2, T.seqChain_boundary_comp_boundary_apply] at h1
    exact h1.trans (Finsupp.mapDomain_zero
      (f := (Subtype.val : SplitSet R n p → List ((Fin n → R) × (Fin n → R)))) (M := ℤ)).symm
  refine ⟨fun p => ?_, fun h0 => ?_, fun p hp => ?_⟩
  · ext c a
    simp [hzero]
  · intro (y : SplitSet R n 0 →₀ ℤ)
    have hy : Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y
        ∈ chains (splitSeq R n) 0 := by
      rw [← (key 0).2.1]
      exact LinearMap.mem_range.mpr ⟨y, rfl⟩
    have hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y) = 0 := by
      have hsup : ↑(Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y).support
          ⊆ {l | l ∈ splitSeq R n ∧ l.length = 0} := (Finsupp.mem_supported ℤ _).mp hy
      rw [bd, Finsupp.linearCombination_apply, Finsupp.sum]
      apply Finset.sum_eq_zero
      intro l hl
      have hlen : l.length = 0 := (hsup hl).2
      simp [hlen]
    obtain ⟨b, hb, hbeq⟩ := h0 _ hy hbd
    have hb' : b ∈ LinearMap.range
        (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n 1 → List ((Fin n → R) × (Fin n → R)))) := by
      rw [(key 1).2.1]
      exact hb
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hb'
    refine ⟨x, (key 0).1 ?_⟩
    exact ((key 0).2.2 x).trans hbeq
  · intro (y : SplitSet R n (p + 1) →₀ ℤ)
    constructor
    · intro hy0
      have hy : Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y
          ∈ chains (splitSeq R n) (p + 1) := by
        rw [← (key (p + 1)).2.1]
        exact LinearMap.mem_range.mpr ⟨y, rfl⟩
      have hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y) = 0 := by
        have h1 := (key p).2.2 y
        rw [hy0] at h1
        exact h1.symm.trans Finsupp.mapDomain_zero
      obtain ⟨b, hb, hbeq⟩ := hp _ hy hbd
      have hb' : b ∈ LinearMap.range
          (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n (p + 1 + 1) → List ((Fin n → R) × (Fin n → R)))) := by
        rw [(key (p + 1 + 1)).2.1]
        exact hb
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hb'
      refine ⟨x, (key (p + 1)).1 ?_⟩
      exact ((key (p + 1)).2.2 x).trans hbeq
    · rintro ⟨x, rfl⟩
      exact hzero p x

end GlobalTheory.HomStab.SplitEx

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.splitSequence_rep_complex_exact : ∀ (R : Type) [CommRing R] (n : ℕ), (∀ p, splitD R n (p + 1) ≫ splitD R n p = 0) ∧ (ExactAt (splitSeq R n) 0 → Function.Surjective (splitD R n 0).hom) ∧ ∀ p, ExactAt (splitSeq R n) (p + 1) → Function.Exact (splitD R n (p + 1)).hom (splitD R n p).hom := by
  first
  | exact @GlobalTheory.HomStab.SplitEx.main
end
end

