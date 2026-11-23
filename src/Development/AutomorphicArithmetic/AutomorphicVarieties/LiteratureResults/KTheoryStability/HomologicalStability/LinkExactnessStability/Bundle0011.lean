module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtOfLinksOutsideExactAtOfConed
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem exactAt_of_links_cone : ∀ (V : Type) (F : Set (List V)) (S : Set V) (y : V), SubClosed F →
    (∀ l ∈ linkIn F S [], y :: l ∈ F) → ∀ (p : ℕ),
    (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p →
      ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  intro V F S y hF hy p hlink c hc hbd
  obtain ⟨b, hb, hc', hbd'⟩ := GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p hlink c hc hbd
  obtain ⟨b', hb', hbb'⟩ := GlobalTheory.T.seqChain_cycle_bounded_by_cone V F (linkIn F S []) y hy p (c - bd V b) hc' hbd'
  refine ⟨b + b', Submodule.add_mem _ hb hb', ?_⟩
  rw [map_add (f := _), hbb']
  abel

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsBdOfCycleFormsKillUnimodularVector
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx

theorem cycle_formsKill_bound_splitSeq : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') → ∀ (p : ℕ) (u : Fin n → R), [u] ∈ uniSeq R n → 2 * p + s + 1 ≤ n → ∀ c ∈ chains {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} p, bd _ c = 0 → ∃ b ∈ chains (splitSeq R n) (p + 1), bd _ b = c := by
  intro R _ s hs n hlow p u hu hpn c hc hcz
  obtain ⟨f, hf⟩ := hu
  obtain ⟨w, hwu⟩ : ∃ w : Fin n → R, w ⬝ᵥ u = 1 := ⟨_, by simpa using hf ⟨0, by simp⟩ ⟨0, by simp⟩⟩
  obtain ⟨hsc, -, hchar, -⟩ := GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff R n
  have hγF : [(u, w)] ∈ splitSeq R n := by
    rw [hchar]
    simp [hwu]
  have hGeq : {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} =
      {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0} := by
    ext σ
    simp
  rw [hGeq] at hc
  have hG'sc : SubClosed {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0} := by
    intro l hl l' hl'
    exact ⟨hsc l hl.1 l' hl', fun y hy => hl.2 y (hl'.subset hy)⟩
  have hlinks : ∀ τ ∈ {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0},
      ∀ (x : (Fin n → R) × (Fin n → R)), τ.getLast? = some x →
        x ∉ {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ [(u, w)], z.2 ⬝ᵥ y.1 = 0} → τ.length ≤ p →
        ExactAt (linkIn {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0}
          {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ [(u, w)], z.2 ⬝ᵥ y.1 = 0} τ) (p - τ.length) := by
    intro τ hτ x hlast hxS hlen
    obtain ⟨ρ, hρ, hρlen, hlink⟩ := GlobalTheory.T.exists_splitSeq_linkIn_orthogonal_eq_linkIn R n _ τ hγF hτ.1 hτ.2
    rw [hlink]
    have ht : 1 ≤ τ.length := by
      cases τ with
      | nil => simp at hlast
      | cons a t => simp
    simp only [List.length_singleton] at hρlen
    refine GlobalTheory.T.exactAt_linkIn_splitSeq_of_exactAt_splitSeq R s hs n (n - ρ.length) (p - τ.length) ρ hρ ?_ ?_ ?_
    · omega
    · omega
    · apply hlow
      · omega
      · omega
  obtain ⟨b1, hb1, hc1, hz1⟩ := GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links _ _ _ hG'sc p hlinks c hc hcz
  have hcone : ∀ l ∈ linkIn {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0}
      {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ [(u, w)], z.2 ⬝ᵥ y.1 = 0} [],
      (u, w) :: l ∈ splitSeq R n := by
    intro l hl
    obtain ⟨hlS, hlG⟩ := hl
    simp only [List.nil_append] at hlG
    obtain ⟨hlF, hlo⟩ := hlG
    rw [hchar] at hlF ⊢
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hwu
      · exact hlF.1 y hy
    · rw [List.pairwise_cons]
      refine ⟨fun z hz => ⟨?_, ?_⟩, hlF.2⟩
      · simpa using hlS z hz
      · simpa using hlo z hz
  obtain ⟨b2, hb2, hbd2⟩ := GlobalTheory.T.seqChain_cycle_bounded_by_cone _ (splitSeq R n) _ (u, w) hcone p _ hc1 hz1
  refine ⟨b1 + b2, ?_, ?_⟩
  · refine Submodule.add_mem _ ?_ hb2
    refine Finsupp.supported_mono ?_ hb1
    intro l hl
    exact ⟨hl.1.1, hl.2⟩
  · rw [map_add (f := _), hbd2]
    abel

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_bd_of_cycle_forms_kill_unimodular_vector : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') → ∀ (p : ℕ) (u : Fin n → R), [u] ∈ uniSeq R n → 2 * p + s + 1 ≤ n → ∀ c ∈ chains {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} p, bd _ c = 0 → ∃ b ∈ chains (splitSeq R n) (p + 1), bd _ b = c := by
  first
  | exact @GlobalTheory.SeqCx.cycle_formsKill_bound_splitSeq
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PtHCompPermMapOfEquivariant
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem ptH_comp_permMap_eq : ∀ (k G H H' X Y : Type) [CommRing k] [Group G] [Group H] [Group H'] [MulAction G X] [MulAction G Y] (φ : H →* G) (φ' : H' →* G) (σ : H' →* H) (x : X) (hx : ∀ h, φ' h • x = x) (y : Y) (hy : ∀ h, φ h • y = y) (f : X → Y) (hf : ∀ (g : G) z, f (g • z) = g • f z) (g : G), φ.comp σ = φ' → g • f x = y → (∀ h, g * φ' h = φ' h * g) → ∀ n : ℕ, ptH (k := k) φ' x hx n ≫ hMap (permMap f hf (Rep.trivial k G k)) n = groupHomology.map (A := Rep.trivial k H' k) (B := Rep.trivial k H k) σ (𝟙 (Rep.trivial k H' k)) n ≫ ptH (k := k) φ y hy n := by
  intro k G H H' X Y _ _ _ _ _ _ φ φ' σ x hx y hy f hf g hσ hgy hc n
  subst hσ
  have hfx : ∀ h, (φ.comp σ) h • f x = f x := fun h => by rw [← hf, hx]
  have hy' : ∀ h, (φ.comp σ) h • y = y := fun h => hy (σ h)
  have h1 := groupHomology.map_comp (A := Rep.trivial k H' k) (B := perm (k := k) (G := G) X) (C := perm (k := k) (G := G) Y)
    (φ.comp σ) (MonoidHom.id G) (ptMap (φ.comp σ) x hx (Rep.trivial k G k))
    (permMap f hf (Rep.trivial k G k)) n
  have hmor : (ptMap (φ.comp σ) x hx (Rep.trivial k G k) ≫
      (Rep.resFunctor (φ.comp σ)).map (permMap f hf (Rep.trivial k G k)) :
        Rep.trivial k H' k ⟶ Rep.res (φ.comp σ) (perm (k := k) (G := G) Y)) =
      ptMap (φ.comp σ) (f x) hfx (Rep.trivial k G k) := by
    ext a
    change (Finsupp.mapDomain f (Finsupp.single x (1:k))) a = (Finsupp.single (f x) (1:k)) a
    rw [Finsupp.mapDomain_single]
  have hL : ptH (k := k) (φ.comp σ) x hx n ≫ hMap (permMap f hf (Rep.trivial k G k)) n =
      groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) (f x) hfx (Rep.trivial k G k)) n :=
    h1.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor)
  have h2 := groupHomology.map_comp (A := Rep.trivial k H' k) (B := Rep.trivial k H k) (C := perm (k := k) (G := G) Y)
    σ φ (𝟙 (Rep.trivial k H' k)) (ptMap φ y hy (Rep.trivial k G k)) n
  have hmor2 : (𝟙 (Rep.trivial k H' k) ≫ (Rep.resFunctor σ).map (ptMap φ y hy (Rep.trivial k G k)) :
        Rep.trivial k H' k ⟶ Rep.res (φ.comp σ) (perm (k := k) (G := G) Y)) =
      ptMap (φ.comp σ) y hy' (Rep.trivial k G k) := by
    ext a
    rfl
  have hR : groupHomology.map (A := Rep.trivial k H' k) (B := Rep.trivial k H k) σ
      (𝟙 (Rep.trivial k H' k)) n ≫ ptH (k := k) φ y hy n =
      groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) y hy' (Rep.trivial k G k)) n :=
    h2.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor2)
  rw [hL, hR]
  symm
  refine GlobalTheory.HomStab.groupHomology_map_conj k G H' (Rep.trivial k H' k) (perm (k := k) (G := G) Y) (φ.comp σ) (φ.comp σ)
    (ptMap (φ.comp σ) (f x) hfx (Rep.trivial k G k)) (ptMap (φ.comp σ) y hy' (Rep.trivial k G k)) g
    (fun h => by rw [hc h, mul_inv_cancel_right]) (fun a => ?_) n
  subst hgy
  change Finsupp.single (g • f x) a = Finsupp.mapDomain (fun z => g • z) (Finsupp.mapRange id rfl (Finsupp.single (f x) a))
  rw [Finsupp.mapRange_id, Finsupp.mapDomain_single]

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.QuillenStabilisationInjectiveBottom
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory

theorem injective_stabilisation_bottom_of_rows_exact : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  intro k G _ _ i C d hdd hsurj hex M e s hiso hcomm hinj hsur
  have hE : Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
    refine T.exact_hMap_one_zero_of_staircase k G i C d hdd hsurj hex ?_
    intro p q hp hpq
    refine T.homology_row_exact_of_stabilisation_pattern k G C d hdd M e s (i + 3) hiso hcomm p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev hp hpq
    · intro hodd
      have h3 : 3 ≤ p := by
        obtain ⟨m, rfl⟩ := hodd
        omega
      exact hsur (p + 1) q (by simpa using hodd.add_one) (by omega) (by omega)
  have h0 := hcomm 0 i (by omega)
  have h1 := hcomm 1 i (by omega)
  simp only [Even.zero, if_true] at h0
  have h1' : e 2 i ≫ hMap (d 1) i = 0 := by
    simpa using h1
  haveI := hiso 1 i (by omega)
  haveI := hiso 2 i (by omega)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hx1 : (hMap (d 0) i).hom ((e 1 i).hom x) = 0 := by
    have := congrArg (fun f => f.hom x) h0
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this, hx, map_zero]
  obtain ⟨y, hy⟩ := (hE _).mp hx1
  have hy2 : y = (e 2 i).hom ((inv (e 2 i)).hom y) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.inv_hom_id]
    rfl
  have hzero : (e 1 i).hom x = 0 := by
    rw [← hy, hy2]
    have := congrArg (fun f => f.hom ((inv (e 2 i)).hom y)) h1'
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this]
    rfl
  have : x = (inv (e 1 i)).hom ((e 1 i).hom x) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.hom_inv_id]
    rfl
  rw [this, hzero, map_zero]

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.quillen_stabilisation_injective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  first
  | exact @GlobalTheory.injective_stabilisation_bottom_of_rows_exact
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqComplexExactAtOfAllLinksExactAt
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem SeqCx.exactAt_of_links : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ),
    (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  intro V F S hF p h c hc hcb
  have hsubF : ∀ q, chains (linkIn F S []) q ≤ chains F q := by
    intro q
    apply Finsupp.supported_mono
    rintro l ⟨⟨_, hl⟩, hlen⟩
    exact ⟨by simpa using hl, hlen⟩
  by_cases h0 : ([] : List V) ∈ F
  · obtain ⟨b, hb, hcb', hcyc⟩ :=
      T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p (fun τ hτ _ _ _ hl => h τ hτ hl) c hc hcb
    obtain ⟨b', hb', hbd⟩ := h [] h0 (by simp) (c - bd V b) (by simpa using hcb') hcyc
    refine ⟨b + b', (chains F (p + 1)).add_mem hb (hsubF _ (by simpa using hb')), ?_⟩
    rw [map_add (f := _), hbd]
    abel
  · have hFe : ∀ l, l ∉ F := fun l hl => h0 (hF l hl [] (List.nil_sublist l))
    have hc0 : c = 0 := by
      have : {l : List V | l ∈ F ∧ l.length = p} = ∅ := by
        ext l
        simp [hFe l]
      have hc' := hc
      simp only [chains, this, Finsupp.supported_empty, Submodule.mem_bot] at hc'
      exact hc'
    exact ⟨0, Submodule.zero_mem _, by simp [hc0]⟩

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqComplex_exactAt_of_all_links_exactAt : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ), (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_of_links
end
end

