module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullback
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ggeo.LocalLift

theorem exists_mul_eq_of_isPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (po : IsPushout f g h k) (M : Submonoid A)
    (hg : ∀ c : C, ∃ a, ∃ m ∈ M, c * g.hom m = g.hom a) (d : D) :
    ∃ m ∈ M, ∃ b, d * h.hom (f.hom m) = h.hom b := by
  have GlobalTheory.CompanionTheory.Ar.Conj.hw : ∀ a, h.hom (f.hom a) = k.hom (g.hom a) := fun a => by
    have := congrArg (fun φ : A ⟶ D => φ.hom a) po.w
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have GlobalTheory.CompanionTheory.RedCov.Levi.hd : d ∈ Subring.closure
      (Set.range (ConcreteCategory.hom h) ∪ Set.range (ConcreteCategory.hom k)) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout po]
    exact Subring.mem_top d
  refine Subring.closure_induction
    (p := fun x _ => ∃ m ∈ M, ∃ b, x * h.hom (f.hom m) = h.hom b) ?_ ?_ ?_ ?_ ?_ ?_ GlobalTheory.CompanionTheory.RedCov.Levi.hd
  · rintro x (⟨b, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1, M.one_mem, b, ?_⟩
      show h.hom b * h.hom (f.hom 1) = h.hom b
      simp
    · show ∃ m ∈ M, ∃ b, k.hom c * h.hom (f.hom m) = h.hom b
      obtain ⟨a, m, hm, hca⟩ := hg c
      refine ⟨m, hm, f.hom a, ?_⟩
      rw [GlobalTheory.CompanionTheory.Ar.Conj.hw, GlobalTheory.CompanionTheory.Ar.Conj.hw, ← map_mul, hca]
  · exact ⟨1, M.one_mem, 0, by simp⟩
  · exact ⟨1, M.one_mem, 1, by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨m₁, hm₁, b₁, e₁⟩ := hx
    obtain ⟨m₂, hm₂, b₂, e₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, b₁ * f.hom m₂ + b₂ * f.hom m₁, ?_⟩
    simp only [map_mul, map_add (f := _)]
    linear_combination h.hom (f.hom m₂) * e₁ + h.hom (f.hom m₁) * e₂
  · intro x _ hx
    obtain ⟨m, hm, b, e⟩ := hx
    exact ⟨m, hm, -b, by rw [neg_mul, e, map_neg]⟩
  · intro x y _ _ hx hy
    obtain ⟨m₁, hm₁, b₁, e₁⟩ := hx
    obtain ⟨m₂, hm₂, b₂, e₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, b₁ * b₂, ?_⟩
    simp only [map_mul]
    linear_combination (y * h.hom (f.hom m₂)) * e₁ + h.hom b₁ * e₂

theorem stalk_exists_mul_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U)
    (c : X.presheaf.stalk p) :
    ∃ a m : Γ(X, U), IsUnit ((X.presheaf.germ U p hp).hom m) ∧
      c * (X.presheaf.germ U p hp).hom m = (X.presheaf.germ U p hp).hom a := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  have hloc := hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨⟨a, m⟩, hm⟩ := @IsLocalization.surj _ _ _ _ _ _ hloc c
  exact ⟨a, m, @IsLocalization.map_units _ _ _ _ _ _ hloc m, hm⟩

theorem fromSpecStalk_appLE {X : Scheme.{0}} {U : X.Opens} {p : X} (hp : p ∈ U)
    (h : (⊤ : (Spec (X.presheaf.stalk p)).Opens) ≤ X.fromSpecStalk p ⁻¹ᵁ U) :
    (X.fromSpecStalk p).appLE U ⊤ h =
      X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso (X.presheaf.stalk p)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hp, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  have e : (homOfLE (le_top : X.fromSpecStalk p ⁻¹ᵁ U ≤ ⊤)).op ≫ (homOfLE h).op =
      𝟙 (Opposite.op (⊤ : (Spec (X.presheaf.stalk p)).Opens)) := by
    first
    | exact Subsingleton.elim _ _
    | rfl
  rw [e]
  exact (congrArg (fun t => X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso (X.presheaf.stalk p)).inv ≫ t)
    ((Spec (X.presheaf.stalk p)).presheaf.map_id _)).trans (by simp only [Category.comp_id])

theorem exists_extension {X Y Z P : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y) (hy : π y₀ = p)
    (fst : P ⟶ Y) (snd : P ⟶ Spec (X.presheaf.stalk p))
    (H : IsPullback fst snd π (X.fromSpecStalk p)) (c : Z ⟶ P) [IsClosedImmersion c]
    (s : Γ(Z, ⊤)) :
    ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧ ((c ≫ fst).app W).hom f =
      Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ W ≤ ⊤)).op s := by
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := p) (by simp)
  have hy₀ : y₀ ∈ π ⁻¹ᵁ V := (Scheme.Hom.mem_preimage π).2 (by rw [hy]; exact hpV)
  obtain ⟨W₀, hW₀, hy₀W₀, hW₀V⟩ := exists_isAffineOpen_mem_and_subset hy₀
  have hUSX : W₀ ≤ π ⁻¹ᵁ V := fun x hx => hW₀V hx
  have hUST : (⊤ : (Spec (X.presheaf.stalk p)).Opens) ≤ X.fromSpecStalk p ⁻¹ᵁ V := by
    intro x _
    have hx : X.fromSpecStalk p x ∈ Set.range (X.fromSpecStalk p) := ⟨x, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hx
    have hx' : X.fromSpecStalk p x ⤳ p := hx
    exact (Scheme.Hom.mem_preimage _).2 (Specializes.mem_open hx' V.isOpen hpV)
  obtain ⟨UY, hUY⟩ : ∃ UY, UY = fst ⁻¹ᵁ W₀ ⊓ snd ⁻¹ᵁ ⊤ := ⟨_, rfl⟩
  have hUYle : UY ≤ fst ⁻¹ᵁ W₀ := by
    rw [hUY]
    exact inf_le_left
  have hpo := (isIso_pushoutSection_iff H hUST hUSX hUY).1
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hV (isAffineOpen_top _) hW₀)
  have hUYaff : IsAffineOpen UY := by
    have hpb := Scheme.Hom.isPullback_resLE H hUST hUSX hUY
    haveI : IsAffine (W₀ : Scheme.{0}) := hW₀
    haveI : IsAffine (V : Scheme.{0}) := hV
    haveI : IsAffine ((⊤ : (Spec (X.presheaf.stalk p)).Opens) : Scheme.{0}) :=
      isAffineOpen_top _
    haveI := Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (π.resLE V W₀ hUSX) ((X.fromSpecStalk p).resLE V ⊤ hUST)
    exact IsAffine.of_isIso hpb.isoPullback.hom
  obtain ⟨d, GlobalTheory.CompanionTheory.RedCov.Levi.hd⟩ := Scheme.Hom.app_surjective c UY hUYaff
    ((Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op).hom s)
  have hd' : (c.app UY).hom d = (Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op).hom s :=
    GlobalTheory.CompanionTheory.RedCov.Levi.hd
  have hg : ∀ c' : Γ(Spec (X.presheaf.stalk p), ⊤), ∃ a, ∃ m ∈
      (IsUnit.submonoid (X.presheaf.stalk p)).comap (X.presheaf.germ V p hpV).hom,
      c' * ((X.fromSpecStalk p).appLE V ⊤ hUST).hom m =
        ((X.fromSpecStalk p).appLE V ⊤ hUST).hom a := by
    intro c'
    obtain ⟨a, m, hmu, hm⟩ := GlobalTheory.CompanionTheory.Ggeo.LocalLift.stalk_exists_mul_eq hV hpV
      ((Scheme.ΓSpecIso (X.presheaf.stalk p)).hom.hom c')
    refine ⟨a, m, Submonoid.mem_comap.2 ((IsUnit.mem_submonoid_iff _).2 hmu), ?_⟩
    rw [GlobalTheory.CompanionTheory.Ggeo.LocalLift.fromSpecStalk_appLE hpV, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
      ← hm, map_mul]
    exact congrArg (fun t => t * _) (CommRingCat.inv_hom_apply _ c').symm
  obtain ⟨m, hmM, b, hb⟩ := GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_mul_eq_of_isPushout hpo _ hg d
  have hmu : IsUnit ((X.presheaf.germ V p hpV).hom m) :=
    (IsUnit.mem_submonoid_iff _).1 (Submonoid.mem_comap.1 hmM)
  have hy₀W : y₀ ∈ Y.basicOpen ((π.appLE V W₀ hUSX).hom m) := by
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.basicOpen_res]
    refine TopologicalSpace.Opens.mem_inf.2 ⟨hy₀W₀, ?_⟩
    rw [← Scheme.preimage_basicOpen, Scheme.Hom.mem_preimage, hy]
    exact (X.mem_basicOpen m p hpV).2 hmu
  obtain ⟨fm, hfm⟩ : ∃ fm, (π.appLE V W₀ hUSX).hom m = fm := ⟨_, rfl⟩
  rw [hfm] at hb hy₀W
  have hWW₀ : Y.basicOpen fm ≤ W₀ := Y.basicOpen_le fm
  have hu : IsUnit ((Y.presheaf.map (homOfLE hWW₀).op).hom fm) :=
    RingedSpace.isUnit_res_basicOpen _ fm
  refine ⟨Y.basicOpen fm, (Y.presheaf.map (homOfLE hWW₀).op).hom b * ↑hu.unit⁻¹, hy₀W, ?_⟩
  have hQ : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ c ⁻¹ᵁ UY := by
    rw [hUY]
    intro z hz
    exact (Scheme.Hom.mem_preimage c).2 (TopologicalSpace.Opens.mem_inf.2
      ⟨(Scheme.Hom.mem_preimage fst).2 (hWW₀ ((Scheme.Hom.mem_preimage (c ≫ fst)).1 hz)),
        (Scheme.Hom.mem_preimage snd).2 (by simp)⟩)
  have E₁ : Y.presheaf.map (homOfLE hWW₀).op ≫ (c ≫ fst).app (Y.basicOpen fm) =
      fst.appLE W₀ UY hUYle ≫ c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
  have e₁ : ∀ x, ((c ≫ fst).app (Y.basicOpen fm)).hom
      ((Y.presheaf.map (homOfLE hWW₀).op).hom x) =
      (c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ).hom ((fst.appLE W₀ UY hUYle).hom x) := by
    intro x
    have := congrArg (fun φ => CommRingCat.Hom.hom φ x) E₁
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have E₂ : Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op ≫
      Z.presheaf.map (homOfLE hQ).op =
      Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ ⊤)).op := by
    (rw [← Functor.map_comp]) <;> rfl
  have e₂ : (c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ).hom d =
      (Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ ⊤)).op).hom s := by
    have h₂ := congrArg (fun φ => CommRingCat.Hom.hom φ s) E₂
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h₂
    rw [← h₂, ← hd', Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [map_mul, e₁ b, ← hb, map_mul, e₂, ← e₁ fm, mul_assoc, ← map_mul, hu.mul_val_inv,
    map_one, mul_one]

theorem exists_open_extension : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y), π y₀ = p →
    ∀ (c : Z ⟶ pullback π (X.fromSpecStalk p)) [IsClosedImmersion c] (s : Γ(Z, ⊤)),
    ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧
      ((c ≫ pullback.fst π (X.fromSpecStalk p)).app W).hom f =
        Z.presheaf.map (homOfLE (le_top : (c ≫ pullback.fst π (X.fromSpecStalk p)) ⁻¹ᵁ W ≤ ⊤)).op s := by
  intro X Y Z π p y₀ hy c _ s
  exact exists_extension π p y₀ hy _ _ (IsPullback.of_hasPullback π (X.fromSpecStalk p)) c s

end GlobalTheory.CompanionTheory.Ggeo.LocalLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothMapLocalizationCompat
section
namespace GlobalTheory.CompanionTheory.Ar.LocalisedSmooth

def denomMonoid {R : Type} [CommRing R] (c : R) : Submonoid R where
  carrier := {x | ∃ n k : ℕ, n ≠ 0 ∧ x = (n : R) * c ^ k}
  one_mem' := ⟨1, 0, one_ne_zero, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, k, hn, rfl⟩ ⟨m, l, hm, rfl⟩
    exact ⟨n * m, k + l, mul_ne_zero hn hm, by push_cast; ring⟩

theorem map_denomMonoid {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (c : R) :
    (denomMonoid c).map f = denomMonoid (f c) := by
  ext x
  constructor
  · rintro ⟨_, ⟨n, k, hn, rfl⟩, rfl⟩
    exact ⟨n, k, hn, by simp⟩
  · rintro ⟨n, k, hn, rfl⟩
    exact ⟨_, ⟨n, k, hn, rfl⟩, by simp⟩

theorem exists_nat_mul_mem {Ω : Type} [Field Ω] [CharZero Ω] (A : Subalgebra ℤ Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (A : Set Ω)) : ∃ N : ℕ, N ≠ 0 ∧ (N : Ω) * x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_nz, ?_⟩
    have : (r.den : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [this]
    exact intCast_mem A _
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (x + y) = (m : Ω) * ((n : Ω) * x) + (n : Ω) * ((m : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem A _) hnx) (mul_mem (natCast_mem A _) hmy)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (x * y) = ((n : Ω) * x) * ((m : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact mul_mem hnx hmy

theorem isLocalization_adjoin {Ω : Type} [Field Ω] [CharZero Ω] (A : Subalgebra ℤ Ω)
    (S : Subalgebra ℚ Ω) [Algebra A S] (hι : ∀ a : A, ((algebraMap A S a : S) : Ω) = a)
    (c : A) (N : ℕ) (hN : N ≠ 0) (h : Ω) (h0 : h ≠ 0) (hc : (c : Ω) = N * h)
    (hS : S = Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω))) :
    IsLocalization (denomMonoid c) S := by
  have hNΩ : (N : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hinv : h⁻¹ ∈ S := hS ▸ Algebra.subset_adjoin (Set.mem_insert _ _)
  have hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (algebraMap A S (n : A)) := by
    intro n hn
    have hnΩ : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
    refine IsUnit.of_mul_eq_one (algebraMap ℚ S (n : ℚ)⁻¹) (Subtype.ext ?_)
    have h1 : ((algebraMap ℚ S (n : ℚ)⁻¹ : S) : Ω) = (n : Ω)⁻¹ := by
      change algebraMap ℚ Ω (n : ℚ)⁻¹ = _
      simp
    rw [Subalgebra.coe_mul, hι, h1]
    simp [hnΩ]
  have hcu : IsUnit (algebraMap A S c) := by
    refine IsUnit.of_mul_eq_one (algebraMap ℚ S (N : ℚ)⁻¹ * ⟨h⁻¹, hinv⟩) (Subtype.ext ?_)
    have h1 : ((algebraMap ℚ S (N : ℚ)⁻¹ : S) : Ω) = (N : Ω)⁻¹ := by
      change algebraMap ℚ Ω (N : ℚ)⁻¹ = _
      simp
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hι, h1, hc]
    simp only [Subalgebra.coe_one]
    field_simp
  have hcmem : c ∈ denomMonoid c := ⟨1, 1, one_ne_zero, by simp⟩
  have hnmem : ∀ n : ℕ, n ≠ 0 → (n : A) ∈ denomMonoid c := fun n hn => ⟨n, 0, hn, by simp⟩
  have key : ∀ w ∈ Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω)),
      ∃ (a : A) (m : denomMonoid c), w * (((m : A)) : Ω) = a := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · refine ⟨(N : A), ⟨c, hcmem⟩, ?_⟩
        simp only [hc]
        push_cast
        field_simp
      · exact ⟨⟨x, hx⟩, 1, by simp⟩
    | algebraMap r =>
      refine ⟨(r.num : A), ⟨(r.den : A), hnmem _ r.den_nz⟩, ?_⟩
      have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
      push_cast
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    | add x y _ _ hx hy =>
      obtain ⟨a, m, hx⟩ := hx
      obtain ⟨b, l, hy⟩ := hy
      refine ⟨a * (l : A) + b * (m : A), m * l, ?_⟩
      push_cast
      rw [← hx, ← hy]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨a, m, hx⟩ := hx
      obtain ⟨b, l, hy⟩ := hy
      refine ⟨a * b, m * l, ?_⟩
      push_cast
      rw [← hx, ← hy]
      ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, k, hn, rfl⟩
    simp only [map_mul, map_pow]
    exact (hnat n hn).mul (hcu.pow k)
  · intro z
    obtain ⟨a, m, hz⟩ := key z (hS ▸ z.2)
    refine ⟨(a, m), Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hι, hι]
    exact hz
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : Ω) = y := by rw [← hι, ← hι, hxy]
    rw [Subtype.ext this]

end GlobalTheory.CompanionTheory.Ar.LocalisedSmooth


open GlobalTheory.CompanionTheory.Ar.LocalisedSmooth in
theorem GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised
    (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (A₀ : Subalgebra ℤ Ω₀) (A₁ : Subalgebra ℤ Ω) (φ : A₀ →+* A₁)
    (hφ : ∀ a, ((φ a : A₁) : Ω) = algebraMap Ω₀ Ω a) (hsm : φ.Smooth)
    (h : Ω₀) (hh : h ∈ Algebra.adjoin ℚ (A₀ : Set Ω₀)) (h0 : h ≠ 0)
    (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω)
    (hS : S = Algebra.adjoin ℚ (insert h⁻¹ (A₀ : Set Ω₀)))
    (hT : T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (A₁ : Set Ω))) :
    ∃ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) ∧ ψ.Smooth := by
  obtain ⟨N, hN, hNh⟩ := exists_nat_mul_mem A₀ hh
  let c₀ : A₀ := ⟨(N : Ω₀) * h, hNh⟩
  have hc₀ : (c₀ : Ω₀) = N * h := rfl
  have hc₁ : ((φ c₀ : A₁) : Ω) = N * algebraMap Ω₀ Ω h := by
    rw [hφ, hc₀, map_mul, map_natCast]
  have hAS : ∀ a : A₀, (a : Ω₀) ∈ S := fun a =>
    hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ a.2)
  have hAT : ∀ a : A₁, (a : Ω) ∈ T := fun a =>
    hT ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ a.2)
  let ι₀ : A₀ →+* S := (A₀.val : A₀ →+* Ω₀).codRestrict S.toSubsemiring hAS
  let ι₁ : A₁ →+* T := (A₁.val : A₁ →+* Ω).codRestrict T.toSubsemiring hAT
  letI : Algebra A₀ S := ι₀.toAlgebra
  letI : Algebra A₁ T := ι₁.toAlgebra
  haveI L₀ : IsLocalization (denomMonoid c₀) S :=
    isLocalization_adjoin A₀ S (fun _ => rfl) c₀ N hN h h0 hc₀ hS
  haveI L₁ : IsLocalization (denomMonoid (φ c₀)) T :=
    isLocalization_adjoin A₁ T (fun _ => rfl) (φ c₀) N hN (algebraMap Ω₀ Ω h)
      ((map_ne_zero _).2 h0) hc₁ hT
  have hle : denomMonoid c₀ ≤ (denomMonoid (φ c₀)).comap φ := by
    intro x hx
    rw [Submonoid.mem_comap, ← map_denomMonoid]
    exact ⟨x, hx, rfl⟩
  let ψ : S →+* T := IsLocalization.map T φ hle
  have hψ : ∀ a : A₀, ψ (algebraMap A₀ S a) = algebraMap A₁ T (φ a) := fun a =>
    IsLocalization.map_eq hle a
  refine ⟨ψ, ?_, ?_⟩
  · have : ((T.val : T →+* Ω).comp ψ) = (algebraMap Ω₀ Ω).comp (S.val : S →+* Ω₀) := by
      refine IsLocalization.ringHom_ext (denomMonoid c₀) (RingHom.ext fun a => ?_)
      change ((ψ (algebraMap A₀ S a) : T) : Ω) = algebraMap Ω₀ Ω (a : Ω₀)
      rw [hψ]
      exact hφ a
    exact fun s => RingHom.congr_fun this s
  · letI : Algebra S T := ψ.toAlgebra
    letI : Algebra A₀ A₁ := φ.toAlgebra
    letI : Algebra A₀ T := ((algebraMap A₁ T).comp φ).toAlgebra
    haveI : IsScalarTower A₀ A₁ T := .of_algebraMap_eq' rfl
    haveI : IsScalarTower A₀ S T := .of_algebraMap_eq fun a => (hψ a).symm
    have hsub : Algebra.algebraMapSubmonoid A₁ (denomMonoid c₀) = denomMonoid (φ c₀) :=
      map_denomMonoid φ c₀
    haveI : IsLocalization (Algebra.algebraMapSubmonoid A₁ (denomMonoid c₀)) T := by
      rw [hsub]; exact L₁
    haveI P : Algebra.IsPushout A₀ A₁ S T :=
      Algebra.isPushout_of_isLocalization (denomMonoid c₀) S A₁ T
    exact RingHom.Smooth.isStableUnderBaseChange A₀ A₁ S T hsm
end

