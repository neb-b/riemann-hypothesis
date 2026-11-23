module

public import Mathlib
public import Formalism.PieriBlockIdeals.Bundle0004
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
public import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds

@[expose] public section

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.WorkedExample

open Formalism.CohomologicalDescent

theorem weight_reflection_holds : MwFlip := by
  intro l b h t κ U
  unfold mwCount
  apply Finset.card_bij' (fun u _ => h - u) (fun u _ => h - u)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc] at hu ⊢
    obtain ⟨⟨⟨w, hw, rfl⟩, hB⟩, x, hx, hxu⟩ := hu
    refine ⟨⟨by simpa using hw, fun hc => hB ⟨by omega, by omega⟩⟩, h - x, ⟨by omega, by omega⟩, ?_⟩
    exact (Int.ModEq.refl h).sub hxu
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc] at hu ⊢
    obtain ⟨⟨hw, hB⟩, x, hx, hxu⟩ := hu
    refine ⟨⟨⟨u, hw, rfl⟩, fun hc => hB ⟨by omega, by omega⟩⟩, h - x, ⟨by omega, by omega⟩, ?_⟩
    exact (Int.ModEq.refl h).sub hxu
  · intro u _; ring
  · intro u _; ring

theorem prod_comp_eq_prod_comp {K : Type} [CommRing K] {N : ℕ} (f : Fin N → Polynomial K) (g : Polynomial K) :
    (∏ a, f a).comp g = ∏ a, (f a).comp g :=
  map_prod (Polynomial.compRingHom g) f Finset.univ

theorem linkage_reflection_holds : LinkageFlip := by
  intro K _ N U U' c c' h H
  have H2 := congrArg (fun p => p.comp (-Polynomial.X + Polynomial.C (((-h - c' - c : ℤ)) : K))) H
  simp only [prod_comp_eq_prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp] at H2
  have e : ∀ W : Fin N → ℤ, ∀ a : Fin N, -Polynomial.X + Polynomial.C (((-h - c' - c : ℤ)) : K) +
      Polynomial.C (((W a + c : ℤ)) : K) = -(Polynomial.X + Polynomial.C (((h - W a + c' : ℤ)) : K)) := by
    intro W a
    rw [neg_add, add_assoc, ← Polynomial.C_add, ← Polynomial.C_neg]
    congr 2
    push_cast
    ring
  simp only [e, Finset.prod_neg] at H2
  exact ((isUnit_neg_one).pow _).mul_left_cancel H2

theorem prod_X_add_C_shift_eq {K : Type} [CommRing K] {N : ℕ} (U U' : Fin N → ℤ) (c c' : ℤ)
    (H : (∏ a, (Polynomial.X + Polynomial.C (((U a + c : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c : ℤ)) : K))) :
    (∏ a, (Polynomial.X + Polynomial.C (((U a + c' : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c' : ℤ)) : K)) := by
  have H2 := congrArg (fun p => p.comp (Polynomial.X + Polynomial.C (((c' - c : ℤ)) : K))) H
  simp only [prod_comp_eq_prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp] at H2
  have e : ∀ W : Fin N → ℤ, ∀ a : Fin N, Polynomial.X + Polynomial.C (((c' - c : ℤ)) : K) +
      Polynomial.C (((W a + c : ℤ)) : K) = Polynomial.X + Polynomial.C (((W a + c' : ℤ)) : K) := by
    intro W a
    rw [add_assoc, ← Polynomial.C_add]
    congr 2
    push_cast
    ring
  simpa only [e] using H2

theorem weight_letters_holds : MwLetters := by
  intro ι N D σ h t hR l κ i
  obtain ⟨_, _, _, hU, _, hbot⟩ := hR
  unfold Labels.mw
  have himg : Finset.univ.image (D.U (D.cc i)) =
      (Finset.univ.image (D.U i)).image (fun u => (h : ℤ) - u) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨D.U i (Fin.rev a), ⟨_, rfl⟩, (hU i a).symm⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨Fin.rev a, by rw [hU, Fin.rev_rev]⟩
  rw [himg, hbot]
  exact weight_reflection_holds l (D.bot i) h t κ _

theorem linked_all_holds : LinkedAll := by
  intro ι N D σ h t F _ cst hR hL
  obtain ⟨hinv, _, hΦ, hU, hU', hbot⟩ := hR
  have hc : ∀ i ∈ D.Φ, StrictAnti (D.U (D.cc i)) ∧ StrictAnti (D.U' (D.cc i)) ∧
      (∀ s : Fin t, ∃ a, D.U (D.cc i) a = D.bot (D.cc i) + ((s : ℕ) : ℤ)) ∧
      (∏ a, (Polynomial.X + Polynomial.C (((D.U (D.cc i) a + 0 : ℤ)) : F))) =
        ∏ a, (Polynomial.X + Polynomial.C (((D.U' (D.cc i) a + 0 : ℤ)) : F)) := by
    intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := hL i hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      rw [hU, hU]
      have := h1 (Fin.rev_lt_rev.mpr hab)
      omega
    · intro a b hab
      rw [hU', hU']
      have := h2 (Fin.rev_lt_rev.mpr hab)
      omega
    · intro s
      obtain ⟨a, ha⟩ := h3 (Fin.rev s)
      refine ⟨Fin.rev a, ?_⟩
      rw [hU, Fin.rev_rev, ha, hbot]
      have e1 : ((Fin.rev s : Fin t) : ℕ) = t - (s + 1) := Fin.val_rev s
      have e2 := s.isLt
      omega
    · have e := linkage_reflection_holds F N (D.U i) (D.U' i) (cst i) 0 h h4
      have r1 := Equiv.prod_comp Fin.revPerm
        (fun a => (Polynomial.X + Polynomial.C ((((h : ℤ) - D.U i a + 0 : ℤ)) : F)))
      have r2 := Equiv.prod_comp Fin.revPerm
        (fun a => (Polynomial.X + Polynomial.C ((((h : ℤ) - D.U' i a + 0 : ℤ)) : F)))
      simp only [Fin.revPerm_apply] at r1 r2
      simp only [hU, hU']
      rw [r1, r2, e]
  intro i
  rcases hΦ i with hi | hi
  · obtain ⟨h1, h2, h3, h4⟩ := hL i hi
    exact ⟨h1, h2, h3, prod_X_add_C_shift_eq _ _ _ _ h4⟩
  · have := hc (D.cc i) hi
    rwa [hinv i] at this

theorem reflection_carried_facts {ι : Type} {N : ℕ} (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) (ep : ι → ι)
    (J : ι → Fin N → ℤ) (botJ : ι → ℤ) (hR : D.Refl σ h t) (hC : D.Carried ep J botJ) :
    (∀ i, ep (ep i) = i) ∧ (∀ i, σ (ep i) = ep (σ i)) ∧ (∀ i, J i = D.U' (ep i)) ∧
      (∀ i, botJ i = D.bot (ep i)) := by
  obtain ⟨hinv, hcom, _⟩ := hR
  obtain ⟨hep, hJ, hb⟩ := hC
  have h1 : ∀ i, ep (ep i) = i := by
    rcases hep with rfl | rfl
    · intro i; rfl
    · exact hinv
  have h2 : ∀ i, σ (ep i) = ep (σ i) := by
    rcases hep with rfl | rfl
    · intro i; rfl
    · exact hcom
  refine ⟨h1, h2, fun i => ?_, fun i => ?_⟩
  · rw [← hJ (ep i), h1]
  · rw [← hb (ep i), h1]

theorem orientation_lattice_holds : WEOrientLattice := by
  intro ι _ σ k j t q l h _ O F L _ _ _ _ _ _ I _ W u c D cst ep J botJ kap τ ζ em jj hl hsmall hR hL
    hC hW hS
  obtain ⟨hinv, hcom, hJ, hb⟩ := reflection_carried_facts D σ h t ep J botJ hR hC
  have all := linked_all_holds ι _ D σ h t F cst hR hL
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have e1 : D.U (ep (ep τ)) = D.U τ := by rw [hinv]
  have e2 : J (ep τ) = D.U' τ := hC.2.1 τ
  have e3 : botJ (ep τ) = D.bot τ := hC.2.2 τ
  have e4 : σ (ep τ) = ep (σ τ) := hcom τ
  have e5 : botJ (ep (σ τ)) = D.bot (σ τ) := hC.2.2 _
  have e6 : D.U (ep (ep (σ τ))) = D.U (σ τ) := by rw [hinv]
  have key := FrobeniusPeriodChange.weight_exponents_from_lattice ι σ k j t q l h O F L I W u c (fun i => D.U (ep i)) J botJ
    (fun _ => 0) kap (ep τ) ζ em jj
    hl hsmall hW (fun i => (all (ep i)).1) (fun i => by rw [hJ]; exact (all (ep i)).2.1)
    (fun i s => by rw [hb]; exact (all (ep i)).2.2.1 s)
    (fun i => by rw [hJ]; exact (all (ep i)).2.2.2)
    (by intro a; show 0 ≤ D.U (ep (ep τ)) a; rw [e1]; exact hS1 a)
    (by show ∑ a, D.U (ep (ep τ)) a = _; rw [e1, e2]; exact hS2)
    (by intro a h1 h2; show D.U (ep (ep τ)) a = _; rw [e1, e3]; exact hS3 a h1 h2)
  simp only [e4, e1, e2, e3, e5, e6] at key
  exact key

end Formalism.CohomologicalDescent.WorkedExample
