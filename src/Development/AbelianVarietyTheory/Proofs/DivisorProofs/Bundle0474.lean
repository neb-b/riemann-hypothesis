module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0458

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslCoactionFreeCoassocCounital
section
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.TranslFree

variable {R A B : Type} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B] [Bialgebra R B]
  (f : A →ₐc[R] B)

theorem coassoc (a : A) :
    TensorProduct.assoc R A B B (((f : A →ₗ[R] B).lTensor A ∘ₗ comul).rTensor B
      ((f : A →ₗ[R] B).lTensor A (comul a))) =
      (comul (R := R) (A := B)).lTensor A ((f : A →ₗ[R] B).lTensor A (comul a)) := by
  let F : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] (B ⊗[R] B) :=
    (TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B)).lTensor A
  have h1 : ∀ w : A ⊗[R] A,
      TensorProduct.assoc R A B B (((f : A →ₗ[R] B).lTensor A ∘ₗ comul).rTensor B
        ((f : A →ₗ[R] B).lTensor A w)) =
      F (TensorProduct.assoc R A A A ((comul (R := R)).rTensor A w)) := by
    intro w
    induction w with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply]
      generalize comul (R := R) a = w
      induction w with
      | add u v hu hv => simp only [map_add (f := _), add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : A ⊗[R] A,
      (comul (R := R) (A := B)).lTensor A ((f : A →ₗ[R] B).lTensor A w) =
      F ((comul (R := R)).lTensor A w) := by
    intro w
    induction w with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, F]
      congr 1
      exact (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) b).symm
  rw [h1, h2, Coalgebra.coassoc_apply]

theorem counit_law (a : A) :
    TensorProduct.rid R A ((counit (R := R) (A := B)).lTensor A
      ((f : A →ₗ[R] B).lTensor A (comul a))) = a := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, CoalgHomClass.counit_comp,
    Coalgebra.lTensor_counit_comul]
  simp

end GlobalTheory.TranslFree

theorem GlobalTheory.PDivGroup.transl_free :
    ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ), (∀ a, TensorProduct.assoc R (G.A (n + 1)) (G.A 1) (G.A 1) ((G.transl n).toLinearMap.rTensor (G.A 1) (G.transl n a)) = (Coalgebra.comul (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) ∧ (∀ a, TensorProduct.rid R (G.A (n + 1)) ((Coalgebra.counit (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) = a) ∧ Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) (G.transl n)) := by
  intro p R _ G n
  have htransl : (G.transl n).toLinearMap =
      (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor (G.A (n + 1)) ∘ₗ comul := by
    apply LinearMap.ext
    intro a
    simpa only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] using G.transl_apply n a
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simpa only [htransl, transl_apply] using GlobalTheory.TranslFree.coassoc (G.resOne n) a
  · intro a
    simpa only [transl_apply] using GlobalTheory.TranslFree.counit_law (G.resOne n) a
  · intro z
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (G.A (n + 1))
      (g := (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1)) (G.resOne_surjective n) z
    obtain ⟨x, rfl⟩ := GlobalTheory.HopfQuot.shear_surjective (R := R) y
    refine ⟨x, ?_⟩
    induction x with
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
    | tmul u v =>
      rw [Algebra.TensorProduct.productMap_apply_tmul, GlobalTheory.HopfQuot.shear_tmul, transl_apply]
      generalize comul (R := R) v = w
      induction w with
      | add s t hs ht => simp only [map_add (f := _), mul_add, smul_add, hs, ht]
      | tmul s t => simp [TensorProduct.smul_tmul']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOnUnitLocusPiece
section
open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis


open Classical in
theorem coboundary_on_piece : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (p : C') (v : T ⟶ G.obj p), (∀ (S : C) (u : T ⟶ S), IsUnit (mp F u e) → Nonempty (G.obj p ⟶ S)) → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hdir T e p v he z hz
  have cov : ∀ (t : C') (u : T ⟶ G.obj t), IsUnit (mp F u e) →
      CovBy F (fun S ↦ ∃ (t' : C') (_ : t ⟶ t'), Nonempty (p ⟶ t') ∧ Nonempty (G.obj t' ⟶ S))
        (G.obj t) := by
    intro t u hu
    obtain ⟨w⟩ := he _ u hu
    obtain ⟨n, b, hb, h⟩ := hdir t p (G.obj t) (𝟙 _) w
    refine ⟨n, b, hb, fun i S' u' hi ↦ ?_⟩
    obtain ⟨t₃, ⟨a⟩, h2, h3⟩ := h i S' u' hi
    exact ⟨t₃, a, h2, h3⟩
  have up : ∀ (t t' t'' : C') (_ : t ⟶ t') (_ : t' ⟶ t''), Nonempty (p ⟶ t') → Nonempty (p ⟶ t'') :=
    fun _ _ _ _ b ⟨α⟩ ↦ ⟨α ≫ b⟩
  exact coboundary_of_restrict (G ⋙ F) (E := fun t ↦ T ⟶ G.obj t) (fun u a ↦ u ≫ G.map a)
    (fun _ _ _ ↦ Subsingleton.elim _ _) (fun t u ↦ IsUnit (mp F u e))
    (fun t _ ↦ Nonempty (p ⟶ t)) (fun _ _ _ a h ↦ isUnit_comp (G.map a) h)
    (fun t u hu ↦ sep_of_covBy F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.glue_upward_of_cov F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    z (fun t t' t'' t''' u a b c _ ↦ hz t t' t'' t''' u a b c)
    (fun t t' _ a ↦ if h : Nonempty (p ⟶ t) then z p t t' v h.some a else 0)
    (fun t t' t'' u a b hp ↦ by
      have hp' := up t t t' (𝟙 t) a hp
      simp only [dif_pos hp, dif_pos hp']
      have k := hz p t t' t'' v hp.some a b
      rw [Subsingleton.elim (v ≫ G.map hp.some) u,
        Subsingleton.elim (hp.some ≫ a) hp'.some] at k
      change mp F (G.map b) (z p t t' v hp.some a) - z p t t'' v hp.some (a ≫ b) +
        z p t' t'' v hp'.some b = z t t' t'' u a b
      linear_combination k)

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCommaCoboundaryOfStandardCover
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc


open Classical in
theorem twoCocycle_comma_coboundary_of_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → (∀ i : Fin n, ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u (d i)) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), (∃ i, IsUnit (mp F u (d i))) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hcov hfil T n d hd z hz hy
  choose y hy using hy
  have hu : ∀ {t t' : C'} {u : T ⟶ G.obj t} (a : t ⟶ t') {x : F.obj T}, IsUnit (mp F u x) →
      IsUnit (mp F (u ≫ G.map a) x) := fun a _ h ↦ isUnit_comp _ h
  have h1 := fun i j : Fin n ↦ _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary F G H hcov hfil T (d i * d j)
    (fun t t' u a ↦ y j t t' u a - y i t t' u a) fun t t' t'' u a b h ↦ by
      rw [map_mul, IsUnit.mul_iff] at h
      rw [map_sub]
      linear_combination hy i t t' t'' u a b h.1 - hy j t t' t'' u a b h.2
  choose β hβ' using h1
  have hβ : ∀ i j t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u (d i)) →
      IsUnit (mp F u (d j)) →
      β i j t' (u ≫ G.map a) - mp F (G.map a) (β i j t u) = y j t t' u a - y i t t' u a :=
    fun i j t t' u a hi hj ↦ hβ' i j t t' u a (by rw [map_mul]; exact hi.mul hj)
  have h2 := fun i j k : Fin n ↦ _root_.GlobalTheory.CatCoh.Desc.sec_of_basis_unit F G H hcov hfil T (d i * d j * d k)
    (fun t u ↦ β j k t u - β i k t u + β i j t u) fun t t' u a h ↦ by
      rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at h
      rw [map_add (f := _), map_sub]
      linear_combination hβ j k t t' u a h.1.2 h.2 - hβ i k t t' u a h.1.1 h.2 +
        hβ i j t t' u a h.1.1 h.1.2
  choose x hx' hxs' using h2
  have hx : ∀ i j k, IsSec F (fun S u ↦ (IsUnit (mp F u (d i)) ∧ IsUnit (mp F u (d j))) ∧
      IsUnit (mp F u (d k))) (x i j k) := fun i j k S S' u ψ h ↦
    hx' i j k S S' u ψ (by
      show IsUnit _
      rw [map_mul, map_mul]; exact (h.1.1.mul h.1.2).mul h.2)
  have hxs : ∀ i j k t (u : T ⟶ G.obj t), IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      IsUnit (mp F u (d k)) → x i j k (G.obj t) u = β j k t u - β i k t u + β i j t u :=
    fun i j k t u hi hj hk ↦ hxs' i j k t u (by rw [map_mul, map_mul]; exact (hi.mul hj).mul hk)
  obtain ⟨e, he, he'⟩ := cech2 H hd x hx (fun l i j k S u hl hi hj hk ↦ by
    obtain ⟨m, b, hb, hb'⟩ := hcov S
    refine sep_std H hb _ fun S' ψ ⟨r, hr⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' r S' ψ hr
    have hl' := isUnit_comp v hl
    have hi' := isUnit_comp v hi
    have hj' := isUnit_comp v hj
    have hk' := isUnit_comp v hk
    rw [mp_comp, map_sub (mp F v), map_add (mp F v), map_sub (mp F v),
      ← hx i j k S _ u v ⟨⟨hi, hj⟩, hk⟩, ← hx l j k S _ u v ⟨⟨hl, hj⟩, hk⟩,
      ← hx l i k S _ u v ⟨⟨hl, hi⟩, hk⟩, ← hx l i j S _ u v ⟨⟨hl, hi⟩, hj⟩,
      hxs _ _ _ _ _ hi' hj' hk', hxs _ _ _ _ _ hl' hj' hk', hxs _ _ _ _ _ hl' hi' hk',
      hxs _ _ _ _ _ hl' hi' hj']
    ring_nf
    exact map_zero _)
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ i j t u,
      IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      γ j t u - γ i t u = β i j t u - e i j (G.obj t) u := by
    refine ⟨fun i t u ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      β h.choose i t u - e h.choose i _ u else 0, fun i j t u hi hj ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination -he' _ i j _ u h.choose_spec hi hj + hxs _ i j t u h.choose_spec hi hj
  obtain ⟨α, hα⟩ : ∃ α : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ i t t' u a,
      IsUnit (mp F u (d i)) →
      α t t' u a = y i t t' u a - (γ i t' (u ≫ G.map a) - mp F (G.map a) (γ i t u)) := by
    refine ⟨fun t t' u a ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      y h.choose t t' u a - (γ h.choose t' (u ≫ G.map a) - mp F (G.map a) (γ h.choose t u)) else 0,
      fun i t t' u a hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    have k1 := congrArg (mp F (G.map a)) (hγ i _ t u hi h.choose_spec)
    have k2 := hγ i _ t' (u ≫ G.map a) (hu a hi) (hu a h.choose_spec)
    have k3 := he i _ _ _ u (G.map a) ⟨hi, h.choose_spec⟩
    have k4 := hβ i _ t t' u a hi h.choose_spec
    simp only [map_sub] at k1
    linear_combination k1 - k2 + k3 - k4
  refine ⟨α, fun t t' t'' u a b ⟨i, hi⟩ ↦ ?_⟩
  rw [hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (hu a hi)]
  simp only [map_sub, mp_comp, Category.assoc, G.map_comp]
  linear_combination hy i t t' t'' u a b hi

end GlobalTheory.CatCoh.Desc
end

