module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.CokerTors
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.cokerTors :
    ∀ (ι : Type) (A b : ℕ) (L : Set (ι →₀ ℤ)), CardLe ι A → 1 ≤ b → (∀ x ∈ L, l1 x ≤ b) →
      TorsLe ((ι →₀ ℤ) ⧸ Submodule.span ℤ L) (b ^ A) := by
  intro ι A b L hι hb hL
  obtain ⟨hfin, hA⟩ := hι
  haveI : IsAddTorsionFree (ι →₀ ℤ) :=
    Function.Injective.isAddTorsionFree (Finsupp.coeFnAddHom : (ι →₀ ℤ) →+ (ι → ℤ))
      DFunLike.coe_injective
  obtain ⟨b₀, -, hb₀L, hb₀i, hb₀⟩ := maxIndep (ι →₀ ℤ) ∅ L (Set.empty_subset _)
    (linearIndepOn_empty _ _)
  obtain ⟨b₁, h01, hb₁s, hb₁i, hb₁⟩ := maxIndep (ι →₀ ℤ) b₀
    (b₀ ∪ Set.range fun k : ι => Finsupp.single k (1 : ℤ)) Set.subset_union_left hb₀i
  obtain ⟨v, hv, hvr⟩ := fullEnum ι b₁ hb₁i fun k => hb₁ _ (Or.inr ⟨k, rfl⟩)
  have hshort : ∀ i, l1 (v i) ≤ b := by
    intro i
    have hi : v i ∈ b₁ := hvr ▸ Set.mem_range_self i
    rcases hb₁s hi with h | ⟨k, hk⟩
    · exact hL _ (hb₀L h)
    · rw [← hk]
      unfold l1
      rw [Finsupp.sum_single_index (by simp)]
      simpa using hb
  have hc := indexLe ι v b hv hshort
  have ht := torsSat (ι →₀ ℤ) ι L v _ hv (fun x hx => by
    obtain ⟨n, hn, hnx⟩ := hb₀ x hx
    refine ⟨n, hn, Submodule.span_mono ?_ hnx⟩
    rw [hvr]
    exact Set.subset_inter h01 hb₀L) hc
  exact ⟨ht.1, ht.2.trans (Nat.pow_le_pow_right hb hA)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.ImportsAlt
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.kill :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ) (z : HZ S (j + 1)), Nat.card S • z = 0 := by
  intro S _ _ j z
  classical
  haveI : Fintype S := Fintype.ofFinite S
  let v : S →₀ ℤ := ∑ s : S, Finsupp.single s 1
  have hv : ∀ g : S, perm S S g v = v := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [v, map_sum, perm_single]
    exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
  let fi : (Rep.trivial ℤ S ℤ).ρ.IntertwiningMap (permRep S S).ρ :=
    ⟨LinearMap.toSpanSingleton ℤ _ v, fun g => by
      apply LinearMap.ext_ring
      simp [Rep.trivial_ρ, permRep, hv]⟩
  let gi : (permRep S S).ρ.IntertwiningMap (Rep.trivial ℤ S ℤ).ρ :=
    ⟨aug S, fun g => by
      apply Finsupp.lhom_ext
      intro x c
      simp [Rep.trivial_ρ, permRep, perm_single, aug_single]⟩
  have hcomp : ∀ a : Rep.trivial ℤ S ℤ,
      (Rep.Hom.hom (Rep.ofHom gi)) ((Rep.Hom.hom (Rep.ofHom fi)) a) = Nat.card S • a := by
    intro a
    change aug S (a • v) = Nat.card S • a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [v, map_smul, map_sum, aug_single, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      nsmul_eq_mul, Nat.card_eq_fintype_card, mul_one]
    ring
  have hsub : Subsingleton (groupHomology (permRep S S) (j + 1)) := by
    obtain ⟨e⟩ := shapiro S S (1 : S) (j + 1)
    haveI : Subsingleton (MulAction.stabilizer S (1 : S)) := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a * 1 = 1 := ha
      have hb' : b * 1 = 1 := hb
      simp only [mul_one] at ha' hb'
      subst ha' hb'
      rfl
    have hz := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_groupHomology_succ_of_subsingleton
        (Rep.trivial ℤ (MulAction.stabilizer S (1 : S)) ℤ) j)
    exact e.injective.subsingleton
  exact mapNsmul S (Rep.trivial ℤ S ℤ) (permRep S S) (Rep.ofHom fi) (Rep.ofHom gi) (Nat.card S) (j + 1) hcomp hsub z
end

