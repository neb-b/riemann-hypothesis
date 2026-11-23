module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussUnitsNormSq
section
open ComplexConjugate Finset

namespace GlobalTheory

namespace GaussUnits

variable {R : Type} [CommRing R] [Fintype R]

theorem sum_ideal_of_exists (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ)
    (hψ : ∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) (b : R) (hb : ∃ x ∈ I, b * x ≠ 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
  obtain ⟨x₀, hx₀I, hx₀⟩ := hb
  have hne : ¬ ∀ r, ψ (b * x₀ * r) = 1 := fun h => hx₀ (hψ _ h)
  push_neg at hne
  obtain ⟨r, hr⟩ := hne
  have hyI : x₀ * r ∈ I := I.mul_mem_right r hx₀I
  have hby : ψ (b * (x₀ * r)) ≠ 1 := by rwa [← mul_assoc]
  have hshift := Fintype.sum_equiv (Equiv.addRight (x₀ * r))
    (fun x => if x + x₀ * r ∈ I then ψ (b * (x + x₀ * r)) else 0)
    (fun x => if x ∈ I then ψ (b * x) else 0) (fun _ => rfl)
  have hS : ∑ x, (if x ∈ I then ψ (b * x) else 0)
      = ψ (b * (x₀ * r)) * ∑ x, (if x ∈ I then ψ (b * x) else 0) := by
    conv_lhs => rw [← hshift]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x ∈ I
    · have h' : x + x₀ * r ∈ I := I.add_mem hx hyI
      rw [if_pos h', if_pos hx, mul_add, AddChar.map_add_eq_mul, mul_comm]
    · have h' : x + x₀ * r ∉ I := fun h => hx (by simpa using I.sub_mem h hyI)
      rw [if_neg h', if_neg hx, mul_zero]
  have h1 : (1 - ψ (b * (x₀ * r))) * ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hby
  · exact h

theorem sum_ideal_of_forall (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ) (b : R)
    (hb : ∀ x ∈ I, b * x = 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = ((univ.filter (· ∈ I)).card : ℂ) := by
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_filter] at hx
  rw [hb x hx.2, AddChar.map_zero_eq_one, Nat.cast_one]

theorem sum_units_eq (m : Ideal R) [DecidablePred (· ∈ m)] [Fintype Rˣ]
    (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (f : R → ℂ) :
    ∑ u : Rˣ, f u = ∑ x, f x - ∑ x, (if x ∈ m then f x else 0) := by
  have h : ∑ u : Rˣ, f u = ∑ x ∈ univ.filter (fun x => ¬ x ∈ m), f x := by
    refine Finset.sum_bij (fun u _ => (u : R)) ?_ ?_ ?_ ?_
    · intro u _
      rw [Finset.mem_filter]
      exact ⟨mem_univ _, (hm u).mp u.isUnit⟩
    · intro a _ b _ h
      exact Units.ext h
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact ⟨((hm x).mpr hx.2).unit, mem_univ _, rfl⟩
    · intro u _
      rfl
  rw [h, eq_sub_iff_add_eq, ← Finset.sum_filter, add_comm, Finset.sum_filter_add_sum_filter_not]

end GaussUnits


open GaussUnits in
theorem gauss_units_norm_sq : ∀ {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [Fintype Rˣ]
    (m : Ideal R), (∀ x : R, IsUnit x ↔ x ∉ m) → ∀ (ψ : AddChar R ℂ),
    (∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) → ∀ (χ : Rˣ → ℂ), (∀ u v, χ (u * v) = χ u * χ v) →
    (∀ u, ‖χ u‖ = 1) → ∀ (t₀ : Rˣ), (∀ x ∈ m, ((t₀ : R) - 1) * x = 0) → χ t₀ ≠ 1 →
    ‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 = Fintype.card R := by
  intro R _ _ _ _ m hm ψ hψ χ hχ hχn t₀ ht₀ hχt₀
  classical
  have hχ0 : ∀ u, χ u ≠ 0 := fun u h => by simpa [h] using hχn u
  have hχ1 : χ 1 = 1 := by
    have h := hχ 1 1
    rw [mul_one] at h
    have h2 : χ 1 * (χ 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (hχ0 1)
    · exact sub_eq_zero.mp h3
  have hconj : conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u) = ∑ z : Rˣ, χ z * ψ (-(z : R)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [map_mul, Complex.inv_eq_conj (hχn z), Complex.conj_conj, AddChar.map_neg_eq_conj]
  have hexp : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = ∑ t : Rˣ, (χ t)⁻¹ * ∑ z : Rˣ, ψ (((t : R) - 1) * z) := by
    rw [hconj, Finset.sum_mul_sum, Finset.sum_comm]
    have hz : ∀ z : Rˣ, ∑ y : Rˣ, (χ y)⁻¹ * ψ y * (χ z * ψ (-(z : R)))
        = ∑ t : Rˣ, (χ t)⁻¹ * ψ (((t : R) - 1) * z) := by
      intro z
      refine Fintype.sum_equiv (Equiv.mulRight z⁻¹) _ _ (fun y => ?_)
      have hzinv : χ z⁻¹ = (χ z)⁻¹ := by
        have h := hχ z z⁻¹
        rw [mul_inv_cancel, hχ1] at h
        exact eq_inv_of_mul_eq_one_right h.symm
      have harg : (((y * z⁻¹ : Rˣ) : R) - 1) * (z : R) = (y : R) + -(z : R) := by
        rw [sub_mul, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          mul_one, one_mul, sub_eq_add_neg]
      simp only [Equiv.coe_mulRight]
      rw [harg, AddChar.map_add_eq_mul, hχ, hzinv, mul_inv, inv_inv]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hz z), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
  have hinner : ∀ t : Rˣ, ∑ z : Rˣ, ψ (((t : R) - 1) * z) =
      (if t = 1 then (Fintype.card R : ℂ) else 0) -
      (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then ((univ.filter (· ∈ m)).card : ℂ) else 0) := by
    intro t
    rw [sum_units_eq m hm (fun x => ψ (((t : R) - 1) * x))]
    congr 1
    · have htop : ∑ x, ψ (((t : R) - 1) * x)
          = ∑ x, (if x ∈ (⊤ : Ideal R) then ψ (((t : R) - 1) * x) else 0) := by simp
      rw [htop]
      split_ifs with h
      · subst h
        rw [sum_ideal_of_forall ⊤ ψ _ (by simp)]
        simp
      · apply sum_ideal_of_exists ⊤ ψ hψ
        refine ⟨1, Submodule.mem_top, ?_⟩
        rw [mul_one, sub_ne_zero]
        exact fun h' => h (Units.val_eq_one.mp h')
    · split_ifs with h
      · exact sum_ideal_of_forall m ψ _ h
      · push_neg at h
        exact sum_ideal_of_exists m ψ hψ _ h
  have hcond : ∀ t : Rˣ, (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) ↔
      (∀ x ∈ m, ((t : R) - 1) * x = 0) := by
    intro t
    constructor
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul] at h1
      have h3 : (t₀ : R) * (((t : R) - 1) * x) = 0 := by linear_combination h1 - h2
      exact t₀.isUnit.mul_right_eq_zero.mp h3
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul]
      linear_combination (t₀ : R) * h1 + h2
  have hS : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
    have e := Fintype.sum_equiv (Equiv.mulLeft t₀)
      (fun t => if (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) then (χ (t₀ * t))⁻¹ else 0)
      (fun t => if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) (fun _ => rfl)
    have hS' : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)
        = (χ t₀)⁻¹ * ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) := by
      conv_lhs => rw [← e]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only [hcond t, hχ, mul_inv, mul_ite, mul_zero]
    have hne : (χ t₀)⁻¹ ≠ 1 := fun h => hχt₀ (inv_eq_one.mp h)
    have h1 : (1 - (χ t₀)⁻¹) *
        ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
      rw [sub_mul, one_mul, ← hS', sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hmain : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = (Fintype.card R : ℂ) := by
    rw [hexp]
    simp_rw [hinner, mul_sub, mul_ite, mul_zero]
    rw [Finset.sum_sub_distrib]
    have h2 : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then
        (χ t)⁻¹ * ((univ.filter (· ∈ m)).card : ℂ) else 0)
        = (∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)) *
          ((univ.filter (· ∈ m)).card : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs <;> simp
    rw [h2, hS, zero_mul, sub_zero]
    simp [hχ1]
  have hn : ((‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 : ℝ) : ℂ) = (Fintype.card R : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hmain]
  exact_mod_cast hn

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueFlatOverPullbackOfSubsingleton
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchDeg

theorem elem_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (hP : IsPullback f₁ f₂ g₁ g₂) :
    (∀ x y, f₁.hom x = f₁.hom y → f₂.hom x = f₂.hom y → x = y) ∧
      ∀ a b, g₁.hom a = g₂.hom b → ∃ x, f₁.hom x = a ∧ f₂.hom x = b := by
  have H := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H.2.1 x y ⟨hx, hy⟩, fun a b h ↦ H.2.2 a b h⟩

theorem subsingleton_or_subsingleton {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (hP : IsPullback f₁ f₂ g₁ g₂) [Subsingleton R₀]
    [IsLocalRing P] : Subsingleton R₁ ∨ Subsingleton R₂ := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback hP
  obtain ⟨e, he₁, he₂⟩ := hex 1 0 (Subsingleton.elim _ _)
  have hidem : e * e = e := hinj _ _ (by simp [he₁]) (by simp [he₂])
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · have h1 : e = 1 := by
      obtain ⟨u, rfl⟩ := hu
      simpa using congrArg (fun t ↦ t * (↑u⁻¹ : P)) hidem
    right
    rw [h1, map_one] at he₂
    exact subsingleton_of_zero_eq_one he₂.symm
  · have h0 : 1 - e = 1 := by
      have hid : (1 - e) * (1 - e) = 1 - e := by
        rw [sub_mul, one_mul, mul_sub, mul_one, hidem, sub_self, sub_zero]
      obtain ⟨u, hu⟩ := hu
      rw [← hu] at hid ⊢
      simpa using congrArg (fun t ↦ t * (↑u⁻¹ : P)) hid
    have he : e = 0 := by
      have := congrArg (fun t ↦ 1 - t) h0
      simpa using this
    left
    rw [he, map_zero] at he₁
    exact subsingleton_of_zero_eq_one he₁

theorem glue_of_subsingleton_right (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂)
    (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (hP : IsPullback f₁ f₂ g₁ g₂) [Subsingleton R₀]
    [Subsingleton R₂] (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀))
    (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left) (hY₁ : Flat Y₁.hom) :
    ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left),
      IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧
        Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback hP
  have hbij : Function.Bijective f₁.hom :=
    ⟨fun x y h ↦ hinj x y h (Subsingleton.elim _ _),
      fun a ↦ (hex a 0 (Subsingleton.elim _ _)).imp fun x hx ↦ hx.1⟩
  haveI : IsIso f₁ := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  haveI : IsEmpty (Spec R₂) := inferInstanceAs (IsEmpty (PrimeSpectrum R₂))
  haveI : IsEmpty Y₂.left := ⟨fun x ↦ isEmptyElim (Y₂.hom.base x)⟩
  haveI : IsEmpty Y₀.left := ⟨fun x ↦ isEmptyElim (i₂.base x)⟩
  let Y : Over (Spec P) := Over.mk (Y₁.hom ≫ Spec.map f₁)
  refine ⟨Y, 𝟙 _, isInitialOfIsEmpty.to _, ?_, ?_, ?_, ?_⟩
  · exact IsPullback.of_horiz_isIso ⟨by simp [Y]⟩
  · have hpb := IsPullback.of_hasPullback Y.hom (Spec.map f₂)
    haveI : IsEmpty ((pullback Y.hom (Spec.map f₂) : Scheme.{0})) :=
      ⟨fun x ↦ isEmptyElim ((pullback.snd Y.hom (Spec.map f₂)).base x)⟩
    let e : pullback Y.hom (Spec.map f₂) ≅ Y₂.left :=
      isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty
    refine IsPullback.of_iso hpb e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    all_goals first
      | exact isInitialOfIsEmpty.hom_ext _ _
      | simp
  · show Flat (Y₁.hom ≫ Spec.map f₁)
    infer_instance
  · haveI : IsIso i₂ := ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _,
      isInitialOfIsEmpty.hom_ext _ _⟩
    exact IsPushout.of_vert_isIso ⟨isInitialOfIsEmpty.hom_ext _ _⟩

theorem glue_of_subsingleton : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Subsingleton R₀ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP h₀ hloc _ _ _ Y₁ Y₂ Y₀ i₁ i₂ _ _ hY₁ hY₂
  rcases subsingleton_or_subsingleton hP with h₁ | h₂
  · obtain ⟨Y, j₂, j₁, hp₂, hp₁, hf, hpo⟩ :=
      glue_of_subsingleton_right P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip Y₂ Y₁ Y₀ i₂ i₁ hY₂
    exact ⟨Y, j₁, j₂, hp₁, hp₂, hf, hpo.flip⟩
  · exact glue_of_subsingleton_right P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP Y₁ Y₂ Y₀ i₁ i₂ hY₁

end GlobalTheory.PinchDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetChangeOfBases
section
open Matrix Polynomial

namespace GlobalTheory

theorem gramChange_gram_eq_mul {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type} [Fintype ι]
    (u : ι → Fin n → K) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k) = (Matrix.of u).map σ * (Matrix.of u)ᵀ := by
  ext i j
  simp [Matrix.mul_apply]

theorem gramChange_square {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type}
    [Fintype ι] [DecidableEq ι] (u v : ι → Fin n → K) (hu : LinearIndependent K u)
    (hv : LinearIndependent K v) (hvu : ∀ i, v i ∈ Submodule.span K (Set.range u)) :
    ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (v i k) * v j k).det
      = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  classical
  let b := Module.Basis.span hu
  let P : Matrix ι ι K := Matrix.of fun i a => b.repr ⟨v i, hvu i⟩ a
  have hV : ∀ i, v i = ∑ a, P i a • u a := by
    intro i
    have h := congrArg Subtype.val (b.sum_repr ⟨v i, hvu i⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, b, Module.Basis.span_apply] at h
    exact h.symm
  have hVm : Matrix.of v = P * Matrix.of u := by
    ext i k
    rw [Matrix.mul_apply, Matrix.of_apply,
      show v i k = (∑ a, P i a • u a) k from congrFun (hV i) k]
    simp [Finset.sum_apply]
  refine ⟨P.det, ?_, ?_⟩
  · intro hd
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    have h1 : w ᵥ* Matrix.of v = 0 := by
      rw [hVm, ← Matrix.vecMul_vecMul, hw, Matrix.zero_vecMul]
    have h2 : ∑ i, w i • v i = 0 := by
      rw [← h1]
      ext k
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    exact hw0 (funext fun i => Fintype.linearIndependent_iff.mp hv w h2 i)
  · rw [gramChange_gram_eq_mul, gramChange_gram_eq_mul, hVm, Matrix.map_mul, transpose_mul,
      show P.map σ * (Matrix.of u).map σ * ((Matrix.of u)ᵀ * Pᵀ)
        = P.map σ * ((Matrix.of u).map σ * (Matrix.of u)ᵀ) * Pᵀ by
          simp only [Matrix.mul_assoc],
      det_mul, det_mul, det_transpose, RingHom.map_det,
      RingHom.mapMatrix_apply]
    ring

theorem gram_det_change_of_bases {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K) :
    LinearIndependent K u → Submodule.span K (Set.range u) = W → LinearIndependent K u' →
      Submodule.span K (Set.range u') = W → ∃ d : K, d ≠ 0 ∧
        (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det
          = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  intro hu hsu hu' hsu'
  have hc : Fintype.card ι' = Fintype.card ι := by
    rw [← finrank_span_eq_card hu', ← finrank_span_eq_card hu, hsu', hsu]
  let e : ι' ≃ ι := Fintype.equivOfCardEq hc
  have hvu : ∀ i, (u' ∘ e.symm) i ∈ Submodule.span K (Set.range u) := by
    intro i
    rw [hsu, ← hsu']
    exact Submodule.subset_span ⟨e.symm i, rfl⟩
  obtain ⟨d, hd, hdet⟩ := gramChange_square σ u (u' ∘ e.symm) hu
    (hu'.comp e.symm e.symm.injective) hvu
  refine ⟨d, hd, ?_⟩
  rw [← hdet, ← det_submatrix_equiv_self e.symm]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetNeZeroOfKerOrth
section
open Matrix Polynomial

theorem GlobalTheory.gram_det_ne_zero_of_ker_orth {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K) (hli : LinearIndependent K u) (hsp : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A)) (horth : ∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) (hdec : ∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) : (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hGc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set x : Fin n → K := ∑ j, c j • u j with hxdef
  have hx0 : x ≠ 0 := by
    intro hx
    apply hc0
    funext j
    exact Fintype.linearIndependent_iff.mp hli c hx j
  have hxspan : x ∈ Submodule.span K (Set.range u) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hAx : A *ᵥ x = 0 := by
    rw [hsp, LinearMap.mem_ker, Matrix.toLin'_apply] at hxspan
    exact hxspan
  have hu : ∀ i, ∑ k, σ (u i k) * x k = 0 := by
    intro i
    have := congrFun hGc i
    rw [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.of_apply, Pi.zero_apply] at this
    rw [← this]
    simp only [hxdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hy : ∀ y ∈ LinearMap.ker (Matrix.toLin' A), ∑ k, σ (y k) * x k = 0 := by
    intro y hy
    rw [← hsp] at hy
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ k, σ (d i) * σ (u i k) * x k = σ (d i) * ∑ k, σ (u i k) * x k := by
      intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    simp [this, hu]
  have hall : ∀ v : Fin n → K, ∑ k, σ (v k) * x k = 0 := by
    intro v
    obtain ⟨z, y, hAy, rfl⟩ := hdec v
    have h1 := horth x z hAx
    have h2 := hy y (by rw [LinearMap.mem_ker, Matrix.toLin'_apply]; exact hAy)
    simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, h1, h2, add_zero]
  apply hx0
  funext k
  have := hall (Pi.single k 1)
  simpa [Pi.single_apply] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresUniqueAe
section
namespace GlobalTheory

theorem unitsMod_away_of_unique_prime (B D : Type) [CommRing B] [CommRing D] [Algebra B D]
    (f : B) (P : Ideal B) (Q : Ideal D) (g : D)
    (hQP : Q.comap (algebraMap B D) = P)
    (huniq : ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) :
    ∀ s : B, s ∉ P → ∃ t : Localization.Away g,
      algebraMap B (Localization.Away g) s * t - 1 ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
  intro s hs
  set A := Localization.Away g
  by_cases hI : Ideal.span {algebraMap B A s, algebraMap B A f} = ⊤
  · have h1 : (1 : A) ∈ Ideal.span {algebraMap B A s, algebraMap B A f} := by
      rw [hI]; exact Submodule.mem_top
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h1
    refine ⟨a, ?_⟩
    have : algebraMap B A s * a - 1 = (-b) * algebraMap B A f := by
      rw [← hab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exfalso
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
    have hMp : (M.comap (algebraMap D A)).IsPrime := Ideal.comap_isPrime _ _
    have hf : algebraMap B D f ∈ M.comap (algebraMap D A) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hIM (Ideal.subset_span (by simp))
    have hg : g ∉ M.comap (algebraMap D A) := by
      intro hgM
      rw [Ideal.mem_comap] at hgM
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hgM
        (IsLocalization.Away.algebraMap_isUnit g))
    have hEq := huniq _ hMp hf hg
    apply hs
    rw [← hQP, Ideal.mem_comap, ← hEq, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hIM (Ideal.subset_span (by simp))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
section
noncomputable section

namespace GlobalTheory.SliceSchwartz

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def inrL (κ κ' : Type) [Fintype κ] [Fintype κ'] : (κ' → V) →L[ℝ] (κ ⊕ κ' → V) :=
  ContinuousLinearMap.pi fun i =>
    Sum.elim (fun _ : κ => (0 : (κ' → V) →L[ℝ] V)) (fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ' => V) j) i

theorem elim_eq_add {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    (fun y : κ' → V => (Sum.elim x y : κ ⊕ κ' → V)) = fun y => Sum.elim x 0 + inrL κ κ' y := by
  funext y i
  cases i with
  | inl i => simp [inrL]
  | inr j => simp [inrL]

theorem hasTemperateGrowth_elim {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    Function.HasTemperateGrowth (fun y : κ' → V => (Sum.elim x y : κ ⊕ κ' → V)) := by
  rw [elim_eq_add]
  exact (Function.HasTemperateGrowth.const _).add (ContinuousLinearMap.hasTemperateGrowth (inrL (V := V) κ κ'))

theorem norm_le_norm_elim {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (y : κ' → V) :
    ‖y‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inr j)

theorem elim_upper {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    ∃ (k : ℕ) (C : ℝ), ∀ y : κ' → V, ‖y‖ ≤ C * (1 + ‖(Sum.elim x y : κ ⊕ κ' → V)‖) ^ k :=
  ⟨1, 1, fun y => by rw [pow_one, one_mul]; linarith [norm_le_norm_elim x y]⟩

def sliceR {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) :
    SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_elim x) (elim_upper x) f

@[simp] theorem sliceR_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V)
    (y : κ' → V) : sliceR f x y = f (Sum.elim x y) := rfl

def sliceRL {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_elim x) (elim_upper x)

theorem sliceRL_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    sliceRL x f = sliceR f x := rfl

end GlobalTheory.SliceSchwartz
end
end

