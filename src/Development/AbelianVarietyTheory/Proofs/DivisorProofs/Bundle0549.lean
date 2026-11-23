module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0015
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0531
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplication
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.JInt

theorem not_four_sq {u Δ : ℤ} (hu : Δ ≤ u) (hΔ : 0 < Δ) (r : ℤ) : u ^ 2 + Δ ≠ 4 * (r * r) := by
  intro h
  have h2 : (2 * |r|) ^ 2 = u ^ 2 + Δ := by rw [mul_pow, sq_abs]; linarith
  have hr0 : 0 ≤ 2 * |r| := by positivity
  have hu0 : 0 ≤ u := by linarith
  have a1 : u < 2 * |r| := by nlinarith
  have a2 : 2 * |r| < u + 1 := by nlinarith
  omega

theorem disc_pos {A B C D : ℤ} {τ : ℍ} (hC : C ≠ 0)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : 0 < -((D - A) ^ 2 + 4 * B * C) := by
  set x := (τ : ℂ).re
  set y := (τ : ℂ).im
  have hy : 0 < y := τ.im_pos
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
    Complex.mul_im] at hre him
  have h1 : ((D : ℝ) - A + 2 * C * x) * y = 0 := by linear_combination -him
  have h1' : (D : ℝ) - A + 2 * C * x = 0 := (mul_eq_zero.mp h1).resolve_right hy.ne'
  have key : (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) = 4 * (C : ℝ) ^ 2 * y ^ 2 := by
    push_cast
    linear_combination (-(D : ℝ) + A - 2 * C * x) * h1' - 4 * (C : ℝ) * hre
  have hCr : (0 : ℝ) < (C : ℝ) ^ 2 := by positivity
  have : (0 : ℝ) < (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) := by rw [key]; positivity
  exact_mod_cast this

theorem main : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ) (α : ℂ), IsTauOf L c τ → MulStable L α → α.im ≠ 0 →
    IsIntegral ℤ (jT τ) := by
  intro L c τ α hτ hα him
  obtain ⟨hc, hlat⟩ := hτ
  have h1 : c * (τ : ℂ) ∈ L.lattice := (hlat _).2 ⟨1, 0, by simp⟩
  have h2 : c ∈ L.lattice := (hlat _).2 ⟨0, 1, by simp⟩
  obtain ⟨A, B, hAB⟩ := (hlat _).1 (hα _ h1)
  obtain ⟨C, D, hCD⟩ := (hlat _).1 (hα _ h2)
  have e1 : α * (τ : ℂ) = A * τ + B := by apply mul_left_cancel₀ hc; linear_combination hAB
  have e2 : α = C * τ + D := by apply mul_left_cancel₀ hc; linear_combination hCD
  have hfix : (A : ℂ) * τ + B = τ * (C * τ + D) := by rw [← e1, e2]; ring
  have hC : C ≠ 0 := by
    rintro rfl
    apply him; rw [e2]; simp
  have hΔ := disc_pos hC hfix
  set Δ := -((D - A) ^ 2 + 4 * B * C) with hΔdef
  set t := A + D
  set k := Δ + |t|
  set M := (A + k) * (D + k) - B * C with hM
  have h4M : 4 * M = (2 * k + t) ^ 2 + Δ := by rw [hM, hΔdef]; ring
  have hu : Δ ≤ 2 * k + t := by
    have := neg_abs_le t; have := abs_nonneg t; linarith
  have hMpos : 0 < M := by nlinarith
  have hm : 0 < M.toNat := by omega
  have hMc : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hMpos.le
  refine jT_isIntegral hm ?_ (Gm_vanish hm τ (A + k) B C (D + k) (by rw [hMc]) ?_)
  · rintro ⟨r, hr⟩
    have : M = (r : ℤ) * r := by rw [← hMc, hr]; push_cast; ring
    exact not_four_sq hu hΔ r (by rw [← h4M, this])
  · push_cast; linear_combination hfix

end GlobalTheory.JInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAwayFib
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem isLocalization_away_eqLocus {A B C A' B' C' : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing A'] [CommRing B'] [CommRing C'] (f : B →+* A) (g : C →+* A)
    (f' : B' →+* A') (g' : C' →+* A') (ρA : A →+* A') (ρB : B →+* B') (ρC : C →+* C')
    (hB : f'.comp ρB = ρA.comp f) (hC : g'.comp ρC = ρA.comp g)
    (x : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)))
    (φ : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)) →+*
      RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')))
    (hφ : ∀ y, (φ y : B' × C') = (ρB (y : B × C).1, ρC (y : B × C).2))
    (hlB : letI := ρB.toAlgebra; IsLocalization.Away (x : B × C).1 B')
    (hlC : letI := ρC.toAlgebra; IsLocalization.Away (x : B × C).2 C')
    (hlA : letI := ρA.toAlgebra; IsLocalization.Away (f (x : B × C).1) A') :
    letI := φ.toAlgebra
    IsLocalization.Away x
      (RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C'))) := by
  letI := ρB.toAlgebra
  letI := ρC.toAlgebra
  letI := ρA.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨⟨b, c⟩, hx⟩ := x
  have hx' : f b = g c := hx
  have eB : ∀ y, f' (ρB y) = ρA (f y) := fun y ↦ RingHom.congr_fun hB y
  have eC : ∀ y, g' (ρC y) = ρA (g y) := fun y ↦ RingHom.congr_fun hC y
  have hfst : ∀ y, ((φ y : B' × C')).1 = ρB (y : B × C).1 := fun y ↦ by rw [hφ]
  have hsnd : ∀ y, ((φ y : B' × C')).2 = ρC (y : B × C).2 := fun y ↦ by rw [hφ]
  have hpow : ∀ (y : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)))
      (k : ℕ), ((y ^ k : RingHom.eqLocus (f.comp (RingHom.fst B C))
        (g.comp (RingHom.snd B C))) : B × C) = ((y : B × C).1 ^ k, (y : B × C).2 ^ k) :=
    fun y k ↦ by rw [SubmonoidClass.coe_pow, Prod.pow_def]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  ·
    have hu : IsUnit (φ ⟨(b, c), hx⟩) := by
      obtain ⟨u₁, hu₁⟩ := IsLocalization.Away.algebraMap_isUnit (S := B') b
      obtain ⟨u₂, hu₂⟩ := IsLocalization.Away.algebraMap_isUnit (S := C') c
      have hu₁' : (u₁ : B') = ρB b := hu₁
      have hu₂' : (u₂ : C') = ρC c := hu₂
      have e0 : f' u₁ = g' u₂ := by rw [hu₁', hu₂', eB, eC, hx']
      have e1 : f' ↑u₁⁻¹ = g' ↑u₂⁻¹ := by
        calc f' ↑u₁⁻¹ = f' ↑u₁⁻¹ * (g' u₂ * g' ↑u₂⁻¹) := by
                rw [← map_mul, Units.mul_inv, map_one, mul_one]
          _ = f' ↑u₁⁻¹ * f' u₁ * g' ↑u₂⁻¹ := by rw [e0, mul_assoc]
          _ = g' ↑u₂⁻¹ := by rw [← map_mul, Units.inv_mul, map_one, one_mul]
      refine isUnit_iff_exists_inv.mpr ⟨⟨(↑u₁⁻¹, ↑u₂⁻¹), e1⟩, ?_⟩
      apply Subtype.ext
      change (φ ⟨(b, c), hx⟩ : B' × C') * ((↑u₁⁻¹ : B'), (↑u₂⁻¹ : C')) = (1 : B' × C')
      rw [hφ]
      ext
      · change ρB b * ↑u₁⁻¹ = 1
        rw [← hu₁', Units.mul_inv]
      · change ρC c * ↑u₂⁻¹ = 1
        rw [← hu₂', Units.mul_inv]
    rintro ⟨_, n, rfl⟩
    change IsUnit (φ (⟨(b, c), hx⟩ ^ n))
    rw [map_pow]
    exact hu.pow n
  ·
    rintro ⟨⟨z₁, z₂⟩, hz⟩
    have hz' : f' z₁ = g' z₂ := hz
    obtain ⟨n₁, y₁, h₁⟩ := IsLocalization.Away.surj b z₁
    obtain ⟨n₂, y₂, h₂⟩ := IsLocalization.Away.surj c z₂
    have h₁' : z₁ * ρB b ^ (n₁ + n₂) = ρB (y₁ * b ^ n₂) := by
      change z₁ * ρB b ^ n₁ = ρB y₁ at h₁
      rw [pow_add, ← mul_assoc, h₁, map_mul, map_pow]
    have h₂' : z₂ * ρC c ^ (n₁ + n₂) = ρC (y₂ * c ^ n₁) := by
      change z₂ * ρC c ^ n₂ = ρC y₂ at h₂
      rw [add_comm, pow_add, ← mul_assoc, h₂, map_mul, map_pow]
    have hA : algebraMap A A' (f (y₁ * b ^ n₂)) = algebraMap A A' (g (y₂ * c ^ n₁)) := by
      change ρA _ = ρA _
      have k₁ := congrArg f' h₁'
      have k₂ := congrArg g' h₂'
      rw [map_mul, map_pow, eB, eB] at k₁
      rw [map_mul, map_pow, eC, eC] at k₂
      rw [← k₁, ← k₂, hz', hx']
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (f b)) hA
    change f b ^ m * f (y₁ * b ^ n₂) = f b ^ m * g (y₂ * c ^ n₁) at hm
    have hmem : f (b ^ m * (y₁ * b ^ n₂)) = g (c ^ m * (y₂ * c ^ n₁)) := by
      rw [map_mul f (b ^ m), map_pow f, hm, map_mul g (c ^ m), map_pow g, hx']
    refine ⟨(⟨(b ^ m * (y₁ * b ^ n₂), c ^ m * (y₂ * c ^ n₁)), hmem⟩,
      ⟨⟨(b, c), hx⟩ ^ (m + (n₁ + n₂)), m + (n₁ + n₂), rfl⟩), ?_⟩
    apply Subtype.ext
    change ((⟨(z₁, z₂), hz⟩ : RingHom.eqLocus _ _) : B' × C') * (φ (⟨(b, c), hx⟩ ^ (m + (n₁ + n₂))) : B' × C') = (φ _ : B' × C')
    rw [hφ, hφ, hpow]
    ext
    · change z₁ * ρB (b ^ (m + (n₁ + n₂))) = ρB (b ^ m * (y₁ * b ^ n₂))
      rw [map_mul, ← h₁']
      simp only [map_pow]
      ring
    · change z₂ * ρC (c ^ (m + (n₁ + n₂))) = ρC (c ^ m * (y₂ * c ^ n₁))
      rw [map_mul, ← h₂']
      simp only [map_pow]
      ring
  ·
    intro y y' e
    have e' : φ y = φ y' := e
    have e₁ : algebraMap B B' (y : B × C).1 = algebraMap B B' (y' : B × C).1 := by
      change ρB _ = ρB _
      rw [← hfst, ← hfst]; exact congrArg (fun t : RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')) ↦ (t : B' × C').1) e'
    have e₂ : algebraMap C C' (y : B × C).2 = algebraMap C C' (y' : B × C).2 := by
      change ρC _ = ρC _
      rw [← hsnd, ← hsnd]; exact congrArg (fun t : RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')) ↦ (t : B' × C').2) e'
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers b) e₁
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers c) e₂
    change b ^ n * _ = b ^ n * _ at hn
    change c ^ k * _ = c ^ k * _ at hk
    refine ⟨⟨⟨(b, c), hx⟩ ^ (n + k), n + k, rfl⟩, ?_⟩
    apply Subtype.ext
    change ((⟨(b, c), hx⟩ ^ (n + k) : RingHom.eqLocus _ _) : B × C) * (y : B × C) =
      ((⟨(b, c), hx⟩ ^ (n + k) : RingHom.eqLocus _ _) : B × C) * (y' : B × C)
    rw [hpow]
    ext
    · change b ^ (n + k) * _ = b ^ (n + k) * _
      calc b ^ (n + k) * (y : B × C).1 = b ^ k * (b ^ n * (y : B × C).1) := by ring
        _ = b ^ k * (b ^ n * (y' : B × C).1) := by rw [hn]
        _ = _ := by ring
    · change c ^ (n + k) * _ = c ^ (n + k) * _
      calc c ^ (n + k) * (y : B × C).2 = c ^ n * (c ^ k * (y : B × C).2) := by ring
        _ = c ^ n * (c ^ k * (y' : B × C).2) := by rw [hk]
        _ = _ := by ring

end GlobalTheory.FerrandPush

namespace GlobalTheory.FerrandPush

section Geo
variable {Y₀ Y₁ Y₂ : Scheme.{0}}

theorem upOpen_basicOpen (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i] (U : Y₀.Opens)
    (s : Γ(Y₁, upOpen i U)) : upOpen i (Y₀.basicOpen ((res i U).hom s)) = Y₁.basicOpen s := by
  have h1 : Y₀.basicOpen ((res i U).hom s) = U ⊓ i ⁻¹ᵁ Y₁.basicOpen s :=
    Scheme.basicOpen_appLE i U (upOpen i U) (preimage_upOpen i U).ge s
  have h2 : i ⁻¹ᵁ Y₁.basicOpen s ≤ U :=
    le_trans ((Scheme.Hom.preimage_mono i) (Y₁.basicOpen_le s)) (preimage_upOpen i U).le
  rw [h1, inf_eq_right.mpr h2, upOpen_preimage]

variable (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁]
  [IsClosedImmersion i₂] [Surjective i₂]

end Geo
end GlobalTheory.FerrandPush

namespace GlobalTheory.FerrandPush

theorem isLocalization_away_fib : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂],
    ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U),
    letI := ((GlobalTheory.FerrandPush.fib i₁ i₂).map (homOfLE (Y₀.basicOpen_le
      (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a))).op).hom.toAlgebra;
    IsLocalization.Away a ((GlobalTheory.FerrandPush.fib i₁ i₂).obj
      (op (Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a)))) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ _ U hU a
  obtain ⟨hU0, hU1, hU2⟩ := hU
  have hD : Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a) ≤ U := Y₀.basicOpen_le _
  have hs2 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₂ U).hom ((cone i₁ i₂ U).snd.hom a) := a.2
  have e1 : upOpen i₁ (Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a)) =
      Y₁.basicOpen ((cone i₁ i₂ U).fst.hom a) := upOpen_basicOpen i₁ U _
  have e2 : upOpen i₂ (Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a)) =
      Y₂.basicOpen ((cone i₁ i₂ U).snd.hom a) := by
    rw [hs2]; exact upOpen_basicOpen i₂ U _
  exact isLocalization_away_eqLocus (res i₁ U).hom (res i₂ U).hom (res i₁ _).hom (res i₂ _).hom
    (Y₀.presheaf.map (homOfLE hD).op).hom (Y₁.presheaf.map (homOfLE (upOpen_mono i₁ hD)).op).hom
    (Y₂.presheaf.map (homOfLE (upOpen_mono i₂ hD)).op).hom
    (congrArg CommRingCat.Hom.hom (res_naturality i₁ hD))
    (congrArg CommRingCat.Hom.hom (res_naturality i₂ hD)) a
    ((fib i₁ i₂).map (homOfLE hD).op).hom (fun _ ↦ rfl)
    (hU1.isLocalization_of_eq_basicOpen _ (homOfLE (upOpen_mono i₁ hD)) e1)
    (hU2.isLocalization_of_eq_basicOpen _ (homOfLE (upOpen_mono i₂ hD)) e2)
    (hU0.isLocalization_of_eq_basicOpen _ (homOfLE hD) rfl)

end GlobalTheory.FerrandPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyDirectedOfBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.ThickGlue


set_option backward.isDefEq.respectTransparency false in
theorem isLocallyDirected_of_basis : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : B₀, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → ∀ (F : 𝒰 ⥤ Scheme.{0}), (∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)) → ∀ (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U), (∀ U, Function.Injective (e U)) → (∀ U, Function.Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → (F ⋙ Scheme.forget).IsLocallyDirected := by
  intro B₀ 𝒰 hbas F _hF e hinj hsurj hnat
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme),
      F.map f (e U x) = e V (B₀.homOfLE (show U.1 ≤ V.1 from f.le) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]
    rfl
  have key : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme), x.1 = y.1 →
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    intro U V x y h
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 x.1 x.2 (h ▸ y.2)
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ ⟨x.1, hxW⟩, ?_, ?_⟩
    · rw [hnat']; congr 1; apply Subtype.ext; simp
    · rw [hnat']; congr 1; apply Subtype.ext; simpa using h
  constructor
  intro U V W f g x y h
  obtain ⟨x, rfl⟩ := hsurj U x
  obtain ⟨y, rfl⟩ := hsurj V y
  have h' : F.map f (e U x) = F.map g (e V y) := h
  rw [hnat', hnat'] at h'
  have h'' := congrArg Subtype.val (hinj _ h')
  exact key x y (by simpa using h'')

end GlobalTheory.ThickGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionSpecMapOfThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.ThickGlue


set_option backward.isDefEq.respectTransparency false in
theorem isOpenImmersion_specMap_of_thickening : ∀ (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, IsAffineOpen U) → ∀ (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) (π : 𝒜 ⟶ B₀.presheaf), (∀ U ∈ 𝒰, Function.Surjective (π.app (op U)).hom ∧ IsNilpotent (RingHom.ker (π.app (op U)).hom)) → (∀ U ∈ 𝒰, ∀ a : 𝒜.obj (op U), letI := (𝒜.map (homOfLE (B₀.basicOpen_le ((π.app (op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a (𝒜.obj (op (B₀.basicOpen ((π.app (op U)).hom a))))) → ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V, IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
  intro B₀ 𝒰 haff 𝒜 p hp hloc
  have hloc' : ∀ U ∈ 𝒰, ∀ (a : 𝒜.obj (Opposite.op U)) (W : B₀.Opens)
      (_ : W = B₀.basicOpen ((p.app (Opposite.op U)).hom a)) (h : W ≤ U),
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    rintro U hU a W rfl h
    letI := (𝒜.map (homOfLE h).op).hom.toAlgebra
    haveI := hloc U hU a
    exact IsOpenImmersion.of_isLocalization
      (S := 𝒜.obj (Opposite.op (B₀.basicOpen ((p.app (Opposite.op U)).hom a)))) a
  have hci : ∀ U ∈ 𝒰, IsClosedImmersion (toSpec p U) := fun U hU ↦
    isClosedImmersion_toSpec p (haff U hU) (hp U hU).1
  have hsu : ∀ U ∈ 𝒰, Surjective (toSpec p U) := fun U hU ↦
    surjective_toSpec p (haff U hU) (hp U hU).1 (hp U hU).2
  have hnat : ∀ {U V : B₀.Opens} (h : U ≤ V) (x : U.toScheme),
      Spec.map (𝒜.map (homOfLE h).op) (toSpec p U x) = toSpec p V (B₀.homOfLE h x) :=
    fun h x ↦ congr($(toSpec_naturality p h) x).symm
  intro U hU V hV h
  have := hci V hV
  have := hsu U hU
  apply IsOpenImmersion.of_forall_source_exists
  · intro x y hxy
    obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
    obtain ⟨y, rfl⟩ := (toSpec p U).surjective y
    rw [hnat, hnat] at hxy
    rw [(B₀.homOfLE h).isOpenEmbedding.injective
      ((toSpec p V).isClosedEmbedding.injective hxy)]
  · intro x
    obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
    obtain ⟨f, hf, hxf⟩ := (haff V hV).exists_basicOpen_le (V := U) ⟨x.1, x.2⟩ (h x.2)
    obtain ⟨a, rfl⟩ := (hp V hV).1 f
    have h1 := hloc' U hU ((𝒜.map (homOfLE h).op).hom a) _ (by
      have := congr($(p.naturality (homOfLE h).op).hom a)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [this, Scheme.basicOpen_res]
      exact (inf_eq_right.mpr hf).symm) hf
    refine ⟨_, _, h1, ⟨toSpec p _ ⟨x.1, hxf⟩, ?_⟩, ?_⟩
    · rw [hnat]
      congr 1
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← Spec.map_comp, ← 𝒜.map_comp]
      exact hloc' V hV a _ rfl (hf.trans h)

end GlobalTheory.ThickGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotypicPartExteriorProductInflatedSurjection
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem kills_prod_comp_surj : ∀ (P G₁ G₂ : Type) [Group P] [Finite P] [Group G₁] [Group G₂] (π : P →* G₁ × G₂), Function.Surjective π → ∀ (φ₁ Y₁ : G₁ → ℂ) (φ₂ Y₂ : G₂ → ℂ), IsChar ℂ ℂ Y₁ → IsChar ℂ ℂ Y₂ → Kills φ₁ Y₁ → Kills φ₂ Y₂ → Kills (fun p => φ₁ (π p).1 * φ₂ (π p).2) (fun p => Y₁ (π p).1 * Y₂ (π p).2) := by
  intro P G₁ G₂ _ _ _ _ π hπ φ₁ Y₁ φ₂ Y₂ hY₁ hY₂ h₁ h₂
  haveI : Finite G₁ := Finite.of_surjective (fun p => (π p).1) (fun g => by
    obtain ⟨p, hp⟩ := hπ (g, 1); exact ⟨p, by simp [hp]⟩)
  haveI : Finite G₂ := Finite.of_surjective (fun p => (π p).2) (fun g => by
    obtain ⟨p, hp⟩ := hπ (1, g); exact ⟨p, by simp [hp]⟩)
  haveI := Fintype.ofFinite P
  haveI := Fintype.ofFinite G₁
  haveI := Fintype.ofFinite G₂
  have hY : IsChar ℂ ℂ (fun p => Y₁ (π p).1 * Y₂ (π p).2) := by
    obtain ⟨n, ρ, hρ⟩ := hY₁
    obtain ⟨m, σ, hσ⟩ := hY₂
    exact isChar_mul_complex (a := fun p => Y₁ (π p).1) (b := fun p => Y₂ (π p).2)
      ⟨n, ρ.comp ((MonoidHom.fst G₁ G₂).comp π), fun p => hρ _⟩
      ⟨m, σ.comp ((MonoidHom.snd G₁ G₂).comp π), fun p => hσ _⟩
  obtain ⟨k₁, hk₁⟩ := (GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution G₁ φ₁ Y₁ hY₁).1 h₁
  obtain ⟨k₂, hk₂⟩ := (GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution G₂ φ₂ Y₂ hY₂).1 h₂
  apply (GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution P _ _ hY).2
  set c : ℕ := (Finset.univ.filter fun q : P => π q = 1).card with hcdef
  have hc : (c : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    apply Finset.card_ne_zero_of_mem (a := (1 : P))
    simp
  refine ⟨fun p => k₁ (π p).1 * k₂ (π p).2 / c, fun x => ?_⟩
  rw [hk₁, hk₂]
  simp only [finsum_eq_sum_of_fintype]
  set F : G₁ × G₂ → ℂ := fun g => Y₁ g.1 * Y₂ g.2 * (k₁ (g.1⁻¹ * (π x).1) * k₂ (g.2⁻¹ * (π x).2)) with hF
  have hR : ∀ q : P, Y₁ (π q).1 * Y₂ (π q).2 * (k₁ (π (q⁻¹ * x)).1 * k₂ (π (q⁻¹ * x)).2 / c) = F (π q) / c := by
    intro q
    simp only [hF, map_mul, map_inv, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    ring
  simp only [hR]
  rw [← Finset.sum_div]
  have hfib : ∑ q : P, F (π q) = ∑ g : G₁ × G₂, (c : ℂ) * F g := by
    rw [← Finset.sum_fiberwise Finset.univ (fun q => π q) (fun q => F (π q))]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : ∀ q ∈ Finset.univ.filter (fun q : P => π q = g), F (π q) = F g := by
      intro q hq; rw [(Finset.mem_filter.1 hq).2]
    rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul, hcdef,
      MonoidHom.card_fiber_eq_of_mem_range π (hπ g) (hπ 1)]
  rw [hfib, ← Finset.mul_sum, mul_div_cancel_left₀ _ hc, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [hF]
  ring

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem jT_eq_latDisc (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) :
    jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ :=
  (ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT h).symm

theorem pow_twelve_eq_DD (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) (Ω : ℂ)
    (hΩ : Ω ^ 12 = latDisc Λ) : (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ := by
  have hc : c ≠ 0 := h.1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ^ 12 = 1 := by
    rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, Complex.I_pow_four, one_pow]
  have hd : latDisc Λ = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ :=
    ReciprocityTheory.ChartRestriction.L1.disc_eq h
  rw [div_pow, mul_pow, mul_pow, mul_pow, hI, hΩ, hd]
  field_simp
  ring

theorem jT_eq_and_pow_twelve_eq_DD : ∀ (Λ : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf Λ c τ → jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ ∧ ∀ Ω : ℂ, Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ :=
  fun Λ c τ h => ⟨jT_eq_latDisc Λ c τ h, pow_twelve_eq_DD Λ c τ h⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionBocksteinAdd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem Bock_add : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ x x' z z'
  rintro ⟨f, w, hd, ⟨c, hc, hcx⟩, ⟨e, he, hez⟩⟩ ⟨f', w', hd', ⟨c', hc', hcx'⟩, ⟨e', he', hez'⟩⟩
  refine ⟨f + f', w + w', by rw [map_add (f := _), hd, hd', smul_add], ⟨c + c', fun p q a ↦ ?_, ?_⟩,
    ⟨e + e', fun p q r a b ↦ ?_, ?_⟩⟩
  · simp only [Submodule.coe_add, Pi.add_apply, hc, hc', map_add (f := _)]
  · rw [map_add (f := _), hcx, hcx', map_add (f := _)]
  · simp only [Submodule.coe_add, Pi.add_apply, he, he', map_add (f := _)]
  · rw [map_add (f := _), hez, hez', map_add (f := _)]

end GlobalTheory.AbCoh
end

