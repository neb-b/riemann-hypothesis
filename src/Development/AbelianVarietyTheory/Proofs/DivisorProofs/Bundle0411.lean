module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.Basis

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']

theorem span_map_eq_top (F : C ⥤ CommAlgCat.{0} R) {S S' : C} (u : S ⟶ S') {n : ℕ}
    {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by
  have := congrArg (Ideal.map (mp F u)) hb
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

theorem eq_zero_of_local (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by
  obtain ⟨w₁⟩ := h₁
  obtain ⟨w₂⟩ := h₂
  obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S w₁ w₂
  exact sep_std (H := H) (hb := hb) z fun S' ψ ⟨i, hi⟩ ↦ by
    obtain ⟨t₃, h1, h2, h3⟩ := h i S' ψ hi
    exact hz t₃ S' ψ h1 h2 h3

theorem eq_zero_of_local₃ (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ t₃ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S))
    (h₃ : Nonempty (G.obj t₃ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → Nonempty (t₃ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by
  refine eq_zero_of_local F G H hdir h₁ h₂ z fun t S' ψ h1 h2 ⟨w⟩ ↦ ?_
  obtain ⟨w₃⟩ := h₃
  obtain ⟨a1⟩ := h1
  obtain ⟨a2⟩ := h2
  refine eq_zero_of_local F G H hdir ⟨w⟩ ⟨w₃ ≫ ψ⟩ _ fun t' S'' χ ⟨a⟩ h3 h4 ↦ ?_
  rw [← mp_comp]
  exact hz t' S'' (ψ ≫ χ) ⟨a1 ≫ a⟩ ⟨a2 ≫ a⟩ h3 h4

theorem exists_glue_points (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) [Quiver.IsThin C] (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    (t₁ t₂ : C') (s : ∀ t, F.obj (G.obj t))
    (hs : ∀ t t' (a : t ⟶ t'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → s t' = mp F (G.map a) (s t)) :
    ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
      ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
        mp F ψ (x S) = mp F w (s t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
        x S' = mp F ψ (x S)) := by
  have key : ∀ t t' (S : C) (w : G.obj t ⟶ S) (w' : G.obj t' ⟶ S), Nonempty (t₁ ⟶ t) →
      Nonempty (t₂ ⟶ t) → Nonempty (t₁ ⟶ t') → Nonempty (t₂ ⟶ t') →
      mp F w (s t) = mp F w' (s t') := by
    intro t t' S w w' h1 h2 h1' h2'
    refine sub_eq_zero.1 (eq_zero_of_local F G H hdir ⟨w⟩ ⟨w'⟩ _ fun t'' S' ψ ⟨a⟩ ⟨a'⟩ ⟨w''⟩ ↦ ?_)
    have e1 : w ≫ ψ = G.map a ≫ w'' := Subsingleton.elim _ _
    have e2 : w' ≫ ψ = G.map a' ≫ w'' := Subsingleton.elim _ _
    rw [map_sub, ← mp_comp, ← mp_comp, e1, e2, mp_comp, mp_comp, ← hs t t'' a h1 h2,
      ← hs t' t'' a' h1' h2', sub_self]
  classical
  let σ : ∀ S, F.obj S := fun S ↦
    if h : ∃ t, Nonempty (t₁ ⟶ t) ∧ Nonempty (t₂ ⟶ t) ∧ Nonempty (G.obj t ⟶ S) then
      mp F h.choose_spec.2.2.some (s h.choose) else 0
  have hσ : ∀ t S (w : G.obj t ⟶ S), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
      σ S = mp F w (s t) := by
    intro t S w h1 h2
    have h : ∃ t, Nonempty (t₁ ⟶ t) ∧ Nonempty (t₂ ⟶ t) ∧ Nonempty (G.obj t ⟶ S) :=
      ⟨t, h1, h2, ⟨w⟩⟩
    simp only [σ, dif_pos h]
    exact key _ _ _ _ _ h.choose_spec.1 h.choose_spec.2.1 h1 h2
  have h1 : ∀ S, ∃ x : F.obj S, Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
      ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
        mp F ψ x = mp F w (s t) := by
    intro S
    by_cases hS : Nonempty (G.obj t₁ ⟶ S) ∧ Nonempty (G.obj t₂ ⟶ S)
    · obtain ⟨⟨w₁⟩, ⟨w₂⟩⟩ := hS
      obtain ⟨n, b, hb, hcov⟩ := hdir t₁ t₂ S w₁ w₂
      obtain ⟨x, hx⟩ := glue_std (H := H) (hb := hb) (fun S' _ ↦ σ S') fun S' S'' ψ χ ⟨i, hi⟩ ↦ by
        obtain ⟨t, h1, h2, ⟨w⟩⟩ := hcov i S' ψ hi
        show σ S'' = mp F χ (σ S')
        rw [hσ t S'' (w ≫ χ) h1 h2, hσ t S' w h1 h2, mp_comp]
      refine ⟨x, fun _ _ t S' ψ w h1 h2 ↦
        sub_eq_zero.1 <| sep_std (H := H) (hb := span_map_eq_top F ψ hb) _ fun S'' χ ⟨i, hi⟩ ↦ ?_⟩
      have hi' : IsUnit (mp F (ψ ≫ χ) (b i)) := by rw [mp_comp]; exact hi
      rw [map_sub, ← mp_comp, hx S'' (ψ ≫ χ) ⟨i, hi'⟩, ← mp_comp, hσ t S'' (w ≫ χ) h1 h2,
        sub_self]
    · exact ⟨0, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hS⟩
  choose x hx using h1
  refine ⟨x, hx, fun S S' ψ h1 h2 ↦ ?_⟩
  obtain ⟨w₁⟩ := h1
  obtain ⟨w₂⟩ := h2
  refine sub_eq_zero.1 (eq_zero_of_local F G H hdir ⟨w₁ ≫ ψ⟩ ⟨w₂ ≫ ψ⟩ _ fun t S'' χ h1' h2' ⟨w⟩ ↦ ?_)
  rw [map_sub, hx S' ⟨w₁ ≫ ψ⟩ ⟨w₂ ≫ ψ⟩ t S'' χ w h1' h2', ← mp_comp,
    hx S ⟨w₁⟩ ⟨w₂⟩ t S'' (ψ ≫ χ) w h1' h2', sub_self]

theorem oneCocycle_coboundary_comma_localBasis (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) [Quiver.IsThin C] [Quiver.IsThin C']
    (H : HasLoc F) (hcov : (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) →
        ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u))
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'))
    (hy : ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
      y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) :
    ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'),
      g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  classical

  let yb : ∀ t t' : C', F.obj (G.obj t') := fun t t' ↦
    if h : Nonempty (T ⟶ G.obj t) ∧ Nonempty (t ⟶ t') then y t t' h.1.some h.2.some else 0
  have hyb : ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), y t t' u a = yb t t' := by
    intro t t' u a
    have h : Nonempty (T ⟶ G.obj t) ∧ Nonempty (t ⟶ t') := ⟨⟨u⟩, ⟨a⟩⟩
    simp only [yb, dif_pos h]
    exact congrArg₂ (y t t') (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hyc : ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
      yb t t'' = mp F (G.map b) (yb t t') + yb t' t'' := by
    intro t t' t'' u a b
    rw [← hyb t t'' u (a ≫ b), ← hyb t t' u a, ← hyb t' t'' (u ≫ G.map a) b]
    exact hy t t' t'' u a b

  obtain ⟨n, b, hb, hcT⟩ := hcov T
  have hpt : ∀ i : Fin n, ∃ (p : C') (_ : T ⟶ G.obj p), ∀ S (u : T ⟶ S),
      IsUnit (mp F u (b i)) → Nonempty (G.obj p ⟶ S) := by
    intro i
    obtain ⟨T', l, hl, -, -, huniv⟩ := H T (b i)
    obtain ⟨p, v, w, -⟩ := hcT i T' l hl
    exact ⟨p, v, fun S u hu ↦ by obtain ⟨m, -⟩ := huniv S u hu; exact ⟨w ≫ m⟩⟩
  choose p v hp using hpt

  have hc0 : ∀ i j : Fin n, ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj (p i) ⟶ S) →
      Nonempty (G.obj (p j) ⟶ S) → ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (p i ⟶ t) →
        Nonempty (p j ⟶ t) → mp F ψ (x S) = mp F w (yb (p j) t - yb (p i) t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj (p i) ⟶ S) → Nonempty (G.obj (p j) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i j
    refine exists_glue_points F G H hdir (p i) (p j) _ fun t t' a ⟨ai⟩ ⟨aj⟩ ↦ ?_
    rw [map_sub, hyc (p j) t t' (v j) aj a, hyc (p i) t t' (v i) ai a]
    ring
  choose c hc hc' using hc0
  have hs : ∀ i j, IsSec F (fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j)))
      (fun S (_ : T ⟶ S) ↦ c i j S) := fun i j S S' u ψ h ↦
    hc' i j S S' ψ (hp i S u h.1) (hp j S u h.2)
  have hcc : ∀ i j k S (u : T ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      IsUnit (mp F u (b k)) → c j k S - c i k S + c i j S = 0 := by
    intro i j k S u hi hj hk
    refine eq_zero_of_local₃ F G H hdir (hp i S u hi) (hp j S u hj) (hp k S u hk) _
      fun t S' ψ ai aj ak ⟨w⟩ ↦ ?_
    rw [map_add (f := _), map_sub, hc j k S (hp j S u hj) (hp k S u hk) t S' ψ w aj ak,
      hc i k S (hp i S u hi) (hp k S u hk) t S' ψ w ai ak,
      hc i j S (hp i S u hi) (hp j S u hj) t S' ψ w ai aj]
    simp only [map_sub]
    ring
  obtain ⟨e, he, he'⟩ := cech1 (H := H) (hb := hb) (fun i j S (_ : T ⟶ S) ↦ c i j S) hs hcc
  have he'' : ∀ i j S (u : T ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      c i j S = e j S u - e i S u := he'

  have hX0 : ∀ i (t : C') (_ : T ⟶ G.obj t), ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t ⟶ S) →
      Nonempty (G.obj (p i) ⟶ S) → ∀ t' S' (ψ : S ⟶ S') (w : G.obj t' ⟶ S'), Nonempty (t ⟶ t') →
        Nonempty (p i ⟶ t') → mp F ψ (x S) = mp F w (yb (p i) t' - yb t t')) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t ⟶ S) → Nonempty (G.obj (p i) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i t u
    refine exists_glue_points F G H hdir t (p i) _ fun t' t'' a ⟨a0⟩ ⟨ai⟩ ↦ ?_
    rw [map_sub, hyc (p i) t' t'' (v i) ai a, hyc t t' t'' u a0 a]
    ring
  choose X hX hX' using hX0

  have indep : ∀ t (u : T ⟶ G.obj t) S (ψ : G.obj t ⟶ S) i j, IsUnit (mp F (u ≫ ψ) (b i)) →
      IsUnit (mp F (u ≫ ψ) (b j)) → X i t u S - e i S (u ≫ ψ) = X j t u S - e j S (u ≫ ψ) := by
    intro t u S ψ i j hi hj
    have key : X i t u S - X j t u S + c i j S = 0 :=
      eq_zero_of_local₃ F G H hdir ⟨ψ⟩ (hp i S _ hi) (hp j S _ hj) _ fun t' S' χ a0 ai aj ⟨w⟩ ↦ by
        rw [map_add (f := _), map_sub, hX i t u S ⟨ψ⟩ (hp i S _ hi) t' S' χ w a0 ai,
          hX j t u S ⟨ψ⟩ (hp j S _ hj) t' S' χ w a0 aj,
          hc i j S (hp i S _ hi) (hp j S _ hj) t' S' χ w ai aj]
        simp only [map_sub]
        ring
    linear_combination key - he'' i j S (u ≫ ψ) hi hj

  have hg0 : ∀ t (u : T ⟶ G.obj t), ∃ x : F.obj (G.obj t), ∀ S (ψ : G.obj t ⟶ S) i,
      IsUnit (mp F (u ≫ ψ) (b i)) → mp F ψ x = X i t u S - e i S (u ≫ ψ) := by
    intro t u
    let σ : ∀ S, (G.obj t ⟶ S) → F.obj S := fun S ψ ↦
      if h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) then X h.choose t u S - e h.choose S (u ≫ ψ) else 0
    have hσ : ∀ S ψ i, IsUnit (mp F (u ≫ ψ) (b i)) → σ S ψ = X i t u S - e i S (u ≫ ψ) := by
      intro S ψ i hi
      have h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := ⟨i, hi⟩
      simp only [σ, dif_pos h]
      exact indep t u S ψ _ i h.choose_spec hi
    obtain ⟨x, hx⟩ := glue_std (H := H) (hb := span_map_eq_top F u hb) σ fun S S' ψ χ ⟨i, hi⟩ ↦ by
      have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
      have hi'' : IsUnit (mp F (u ≫ ψ ≫ χ) (b i)) := by
        rw [← Category.assoc, mp_comp]; exact hi'.map _
      rw [hσ S' (ψ ≫ χ) i hi'', hσ S ψ i hi', map_sub, ← hX' i t u S S' χ ⟨ψ⟩ (hp i S _ hi'),
        ← he i S S' (u ≫ ψ) χ hi', Category.assoc]
    exact ⟨x, fun S ψ i hi ↦ by
      rw [hx S ψ ⟨i, by rw [mp_comp] at hi; exact hi⟩, hσ S ψ i hi]⟩
  choose g hg using hg0
  refine ⟨g, fun t t' u a ↦ ?_⟩
  rw [hyb]
  refine sub_eq_zero.1 (sep_std (H := H) (hb := span_map_eq_top F (u ≫ G.map a) hb) _ fun S χ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F ((u ≫ G.map a) ≫ χ) (b i)) := by rw [mp_comp]; exact hi
  have hi'' : IsUnit (mp F (u ≫ G.map a ≫ χ) (b i)) := by rw [← Category.assoc]; exact hi'
  rw [map_sub, map_sub, hg t' (u ≫ G.map a) S χ i hi', ← mp_comp, hg t u S (G.map a ≫ χ) i hi'',
    Category.assoc]
  have key : X i t' (u ≫ G.map a) S - X i t u S - mp F χ (yb t t') = 0 :=
    eq_zero_of_local F G H hdir ⟨χ⟩ (hp i S _ hi') _ fun t'' S' ψ ⟨a'⟩ ai ⟨w⟩ ↦ by
      rw [map_sub, map_sub, hX i t' (u ≫ G.map a) S ⟨χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a'⟩ ai,
        hX i t u S ⟨G.map a ≫ χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a ≫ a'⟩ ai, ← mp_comp,
        (Subsingleton.elim _ _ : χ ≫ ψ = G.map a' ≫ w), mp_comp, hyc t t' t'' u a a']
      simp only [map_sub, map_add (f := _)]
      ring
  linear_combination key

theorem oneCocycle_vanishing_comma_of_basis : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T y hy
  exact oneCocycle_coboundary_comma_localBasis F G H hcov hdir T y hy

end GlobalTheory.CatCoh.Desc.Basis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulP
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)


open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
set_option autoImplicit false in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.transl_eq_of_cobOne_eq_pullTwo (n : ℕ) (x : G.A (n + 1))
    (t : G.A n ⊗[R] G.A n)
    (h : _root_.GlobalTheory.PDiv.cobOne R _ x = _root_.GlobalTheory.PDiv.pullbackTwo (G.mulP n) t)
    (h1 : G.resOne n x = 0) :
    G.transl n x = x ⊗ₜ 1 := by
  set f := G.mulP n
  set ρ := G.resOne n
  have hcomul : comul x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x +
      TensorProduct.map (f : G.A n →ₗ[R] G.A (n + 1))
        (f : G.A n →ₗ[R] G.A (n + 1)) t := by
    have := h
    unfold _root_.GlobalTheory.PDiv.cobOne _root_.GlobalTheory.PDiv.pullbackTwo at this
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply] at this
    rw [← this]; abel
  have hε : counit x = (0 : R) := by
    have := CoalgHomClass.counit_comp_apply ρ x
    rw [h1, map_zero] at this
    exact this.symm
  have hρf : (ρ : G.A (n + 1) →ₗ[R] G.A 1) ∘ₗ
      (f : G.A n →ₗ[R] G.A (n + 1))
        = Algebra.linearMap R _ ∘ₗ counit := by
    ext a
    exact _root_.GlobalTheory.PDivGroup.resOne_mulP G n a
  have hεf : (counit : _ →ₗ[R] R) ∘ₗ
      (f : G.A n →ₗ[R] G.A (n + 1)) = counit := by
    ext a
    exact CoalgHomClass.counit_comp_apply f a
  have hzero : TensorProduct.map (f : G.A n →ₗ[R] G.A (n + 1))
      (counit : _ →ₗ[R] R) t = 0 := by
    have := congrArg (LinearMap.lTensor _ (counit : _ →ₗ[R] R)) hcomul
    rw [Coalgebra.lTensor_counit_comul, map_add (f := _), map_add (f := _), LinearMap.lTensor_tmul,
      LinearMap.lTensor_tmul, hε, counit_one, ← LinearMap.comp_apply, LinearMap.lTensor_comp_map,
      hεf, tmul_zero, add_zero] at this
    simpa using this
  rw [_root_.GlobalTheory.PDivGroup.transl_apply, hcomul, map_add (f := _), map_add (f := _), LinearMap.lTensor_tmul,
    LinearMap.lTensor_tmul, ← LinearMap.comp_apply, LinearMap.lTensor_comp_map, hρf,
    ← LinearMap.lTensor_comp_map, LinearMap.comp_apply, hzero, map_zero, add_zero]
  have h1' : G.resOne n x = 0 := h1
  simp [h1']

end PDivGroup


open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
set_option autoImplicit false in
theorem _root_.GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP :
    ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
      (c : G.cocycles) (B : G.funs),
        G.cob B = _root_.GlobalTheory.PDivGroup.cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c → B.1 1 = 0 →
        c ∈ LinearMap.range G.cob := by
  intro p _ R _ G c B hB hB1
  have hcobf : ∀ {m m' : ℕ} (f : G.A m →ₐc[R] G.A m') (a),
      _root_.GlobalTheory.PDiv.cobOne R _ (f a)
        = _root_.GlobalTheory.PDiv.pullbackTwo f (_root_.GlobalTheory.PDiv.cobOne R _ a) := by
    intro m m' f a
    unfold _root_.GlobalTheory.PDiv.cobOne _root_.GlobalTheory.PDiv.pullbackTwo
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply, map_sub,
      TensorProduct.map_tmul]
    rw [← CoalgHomClass.map_comp_comul_apply f a]
    simp
  have hpull : ∀ {m m' m'' : ℕ} (f : G.A m' →ₐc[R] G.A m'')
      (g : G.A m →ₐc[R] G.A m') (z),
      _root_.GlobalTheory.PDiv.pullbackTwo (f.comp g) z
        = _root_.GlobalTheory.PDiv.pullbackTwo f (_root_.GlobalTheory.PDiv.pullbackTwo g z) := by
    intro m m' m'' f g z
    unfold _root_.GlobalTheory.PDiv.pullbackTwo
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    rfl
  have hlevel : ∀ n, _root_.GlobalTheory.PDiv.cobOne R _ (B.1 (n + 1))
      = _root_.GlobalTheory.PDiv.pullbackTwo (G.mulP n) (c.1 n) := by
    intro n
    have h := congrArg (fun z => z.1 (n + 1)) hB
    unfold _root_.GlobalTheory.PDivGroup.cob _root_.GlobalTheory.PDivGroup.cocyclesMap at h
    simp only [LinearMap.coe_mk, AddHom.coe_mk] at h
    rw [h, _root_.GlobalTheory.PDivGroup.natCast_smul_id_app, ← _root_.GlobalTheory.PDivGroup.mulP_comp_res, hpull]
    congr 1
    exact (c.2 n).2
  have hres1 : ∀ n, G.resOne n (B.1 (n + 1)) = 0 := by
    intro n
    rw [_root_.GlobalTheory.PDivGroup.resOne_funs, hB1]
  have hex : ∀ n, ∃ e, G.mulP n e = B.1 (n + 1) := fun n =>
    _root_.GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq G n _
      (_root_.GlobalTheory.PDivGroup.transl_eq_of_cobOne_eq_pullTwo G n _ _ (hlevel n) (hres1 n))
  choose e he using hex
  have hcompat : ∀ n, G.res n (e (n + 1)) = e n := by
    intro n
    apply _root_.GlobalTheory.PDivGroup.Test.mulP_injective G n
    rw [_root_.GlobalTheory.PDivGroup.mulP_res, ← _root_.GlobalTheory.PDivGroup.res_mulP, he, he]
    exact B.2 (n + 1)
  refine ⟨⟨e, hcompat⟩, ?_⟩
  apply Subtype.ext
  funext n
  apply _root_.GlobalTheory.PDivGroup.pullbackTwo_mulP_injective G n
  rw [← hlevel, ← he, hcobf]
  rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverAffine
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

theorem pair_cover_affine {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u := by
  intro T
  have hT : IsAffineOpen T.unop.1 := T.unop.2
  let G : Set Γ(X', T.unop.1) :=
    {f | ∃ V : X.affineOpens, X'.basicOpen f ≤ φ ⁻¹ᵁ V.1}
  have hG : Ideal.span G = ⊤ := by
    rw [← hT.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (φ x)) isOpen_univ
    obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := φ ⁻¹ᵁ V) ⟨x, hxV⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨⟨V, hV⟩, hf⟩⟩, hxf⟩
  obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
  · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X', T.unop.1)) := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
      · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
    exact hR ▸ hF
  · intro i S u hu
    obtain ⟨V, hV⟩ := hFG (F.equivFin.symm i).2
    set f : Γ(X', T.unop.1) := (F.equivFin.symm i).1
    have hW : IsAffineOpen (X'.basicOpen f) := hT.basicOpen f
    have hWT : X'.basicOpen f ≤ T.unop.1 := X'.basicOpen_le f
    let t : Pair φ := ⟨(⟨_, hW⟩, V), hV⟩
    have hSW : S.unop.1 ≤ X'.basicOpen f := by
      have h1 : X'.basicOpen (X'.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
        X'.basicOpen_of_isUnit hu
      rw [Scheme.basicOpen_res] at h1
      rw [← h1]; exact inf_le_right
    refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X'.affineOpens) ≤ T.unop from hWT)).op,
      (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X'.affineOpens) from hSW)).op, ?_⟩
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

end GlobalTheory.CechDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleModelCochainComplexIsStrictlyGE
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem cochain_chains_subsingleton {R : Type} [CommRing R] (E : Spc) (I : Cx R) (hI : I.IsStrictlyGE 0) (n : ℤ)
    (hn : n < 0) : Subsingleton (Cochain ((chains R).obj E) I n) := by
  constructor
  intro a b
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · have hz : IsZero (((chains R).obj E).X p) :=
      HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p (fun i hi => by
        change -(i : ℤ) = p at hi
        omega)
    exact hz.eq_of_src _ _
  · have hz : IsZero (I.X q) := I.isZero_of_isStrictlyGE 0 q (by omega)
    exact hz.eq_of_tgt _ _

theorem Jcx_isStrictlyGE (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (hI : I.IsStrictlyGE 0) :
    (Jcx R q N I).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have hpre : IsZero (cotPre R q N I n) := by
    refine Functor.isZero _ (fun U => ?_)
    have h := cochain_chains_subsingleton (sch.obj U.unop ⨯ fibQ q N) I hI n hn
    letI : Subsingleton ((cotPre R q N I n).obj U) := h
    exact ModuleCat.isZero_of_subsingleton _
  exact (presheafToSheaf Scheme.etaleTopology.{0} _).map_isZero hpre

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleCochainApplyBisimplex
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc

theorem evT_finsetSum {R : Type} [CommRing R] {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} {ι : Type} (S : Finset ι)
    (γ : ι → Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (∑ j ∈ S, γ j) a b s h U y = ∑ j ∈ S, evT (γ j) a b s h U y := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, evT_zero]
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, evT_add, ih]

theorem evT_phi : ∀ (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U), evT (phi q V ℓ i z n α) a b s h U y = ∑ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b : ℤ) + 2 * ((j : ℕ) : ℤ)) s (by push_cast at h; omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b _ rfl U (vertS V ℓ y)) := by
  intro q E N V B ℓ i z n α a b s h U y
  rw [phi_apply, evT_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [evT_crossT]
  have he : Even (2 * ((j : ℕ) : ℤ) * (a : ℤ)) := by
    rw [mul_assoc]; exact even_two_mul _
  rw [Int.negOnePow_even _ he, one_smul]

end GlobalTheory.PBFc

end
end

