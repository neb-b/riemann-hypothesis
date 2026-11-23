module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbedding
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo

namespace OverUnique

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [NumberField F]

theorem evC_eq_aeval (z : (Σ k, ι k) → ℂ) (g : MRing ι) : evC z g = aeval z g := by
  have h : algebraMap ℤ ℂ = Int.castRingHom ℂ := RingHom.ext_int _ _
  simp only [evC, eval_map, aeval_def, h]

theorem homog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k0, i0⟩ := p
  by_cases h : k = k0
  · subst h
    simp [Finsupp.single_apply]
  · have h' : ∀ i : ι k, ¬ ((⟨k0, i0⟩ : Σ k, ι k) = ⟨k, i⟩) := fun i e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, h', h]

theorem homog_sub {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d) :
    IsMultiHomog (g - h) d := by
  rw [sub_eq_add_neg]
  refine isMultiHomog_add hg ?_
  intro m hm
  exact hh m (by simpa using hm)

theorem exists_form (c : ∀ k, ι k) (G : MRing ι) :
    ∃ (D : K → ℕ) (H M : MRing ι), IsMultiHomog H D ∧ IsMultiHomog M D ∧
      ∀ (L : Type) [Field L] (w : (Σ k, ι k) → L), (∀ k, w ⟨k, c k⟩ ≠ 0) →
        aeval w M ≠ 0 ∧ aeval w H = aeval w M * aeval (fun p => w p / w ⟨p.1, c p.1⟩) G := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, 1, ?_, isMultiHomog_one, fun L _ w hw => ?_⟩
    · intro m hm k
      have := support_monomial_subset hm
      simp at this
      simp [this]
    · simp
  | add p q hp hq =>
    obtain ⟨D₁, H₁, M₁, h₁, m₁, e₁⟩ := hp
    obtain ⟨D₂, H₂, M₂, h₂, m₂, e₂⟩ := hq
    refine ⟨D₁ + D₂, H₁ * M₂ + H₂ * M₁, M₁ * M₂,
      isMultiHomog_add (isMultiHomog_mul h₁ m₂) (by rw [add_comm D₁]; exact isMultiHomog_mul h₂ m₁),
      isMultiHomog_mul m₁ m₂, fun L _ w hw => ?_⟩
    obtain ⟨n₁, f₁⟩ := e₁ L w hw
    obtain ⟨n₂, f₂⟩ := e₂ L w hw
    refine ⟨by rw [map_mul]; exact mul_ne_zero n₁ n₂, ?_⟩
    simp only [map_add (f := _), map_mul, f₁, f₂]
    ring
  | mul_X p i hp =>
    obtain ⟨D, H, M, h, m, e⟩ := hp
    have hX₁ : IsMultiHomog (X i : MRing ι) (Pi.single i.1 1 : K → ℕ) := homog_X i
    have hX₂ : IsMultiHomog (X ⟨i.1, c i.1⟩ : MRing ι) (Pi.single i.1 1 : K → ℕ) :=
      homog_X (⟨i.1, c i.1⟩ : Σ k, ι k)
    have hH := isMultiHomog_mul h hX₁
    have hM := isMultiHomog_mul m hX₂
    refine ⟨_, _, _, hH, hM, fun L _ w hw => ?_⟩
    obtain ⟨n, f⟩ := e L w hw
    have hc := hw i.1
    refine ⟨by rw [map_mul, aeval_X]; exact mul_ne_zero n hc, ?_⟩
    simp only [map_mul, aeval_X, f]
    field_simp

variable {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem aeval_eq_zero {P : MRing ι} {d : K → ℕ} (hz : z ∈ mcPts (mCoordIdeal y)) (hP : IsMultiHomog P d)
    (h0 : aeval y P = 0) : aeval z P = 0 := by
  rw [← evC_eq_aeval]
  exact hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hP h0)

theorem chart_ne {k : K} {i : ι k} (hz : z ∈ mcPts (mCoordIdeal y)) (h : z ⟨k, i⟩ ≠ 0) : y ⟨k, i⟩ ≠ 0 := by
  classical
  intro h0
  apply h
  have := aeval_eq_zero hz (homog_X (⟨k, i⟩ : Σ k, ι k)) (by rw [aeval_X]; exact h0)
  simpa using this

theorem chart_ker (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) {G : MRing ι} (h0 : aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = 0) :
    aeval (fun p => z p / z ⟨p.1, c p.1⟩) G = 0 := by
  obtain ⟨D, H, M, h, m, e⟩ := exists_form c G
  obtain ⟨-, fy⟩ := e Ω y hy
  obtain ⟨nz, fz⟩ := e ℂ z hc
  rw [h0, mul_zero] at fy
  have := aeval_eq_zero hz h fy
  rw [fz] at this
  exact (mul_eq_zero.mp this).resolve_left nz

theorem exists_intHom (φ : F →+* Ω) (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F)) :
    ∃ τ : 𝓞 F →+* ℂ, ∀ (a : 𝓞 F) (G : MRing ι), aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) →
      τ a = aeval (fun p => z p / z ⟨p.1, c p.1⟩) G := by
  set v : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hv
  set u : (Σ k, ι k) → ℂ := fun p => z p / z ⟨p.1, c p.1⟩ with hu
  let A : MRing ι →ₐ[ℤ] Ω := aeval v
  let ψ : MRing ι →+* A.range := (A.rangeRestrict : MRing ι →+* A.range)
  let ψ' : MRing ι →+* ℂ := ((aeval u : MRing ι →ₐ[ℤ] ℂ) : MRing ι →+* ℂ)
  have hs : Function.Surjective ψ := A.rangeRestrict_surjective
  have hker : RingHom.ker ψ ≤ RingHom.ker ψ' := by
    intro G hGk
    rw [RingHom.mem_ker] at hGk ⊢
    have h1 : aeval v G = 0 := congrArg Subtype.val hGk
    exact chart_ker hz hc hy h1
  let l : A.range →+* ℂ := RingHom.liftOfSurjective ψ hs ⟨ψ', hker⟩
  have hl : ∀ G, l (ψ G) = ψ' G := fun G =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨ψ', hker⟩ G
  let ρ : 𝓞 F →+* A.range := (φ.comp (algebraMap (𝓞 F) F)).codRestrict A.range (fun a => by
    obtain ⟨G, hG'⟩ := hG a
    exact ⟨G, hG'⟩)
  refine ⟨l.comp ρ, fun a G h => ?_⟩
  have : ρ a = ψ G := Subtype.ext h.symm
  rw [RingHom.comp_apply, this, hl]
  rfl

theorem intHom_injective (τ : 𝓞 F →+* ℂ) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

end OverUnique


open OverUnique GroundTheory.Heights₂.Heights.LowerBoundFree in
theorem existsUnique_ptOver (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (hO : OverInt y φ) :
    ∀ z ∈ mcPts (mCoordIdeal y), ∃! σ : F →+* ℂ, PtOver y φ σ z := by
  classical
  intro z hz
  choose c hc using hz.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => chart_ne hz (hc k)
  have hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) := by
    intro a
    have h := hO.2 c hy a
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at h
    exact h
  obtain ⟨τ, hτ⟩ := exists_intHom φ hz hc hy hG
  have hinj := intHom_injective τ
  let σ : F →+* ℂ := IsFractionRing.lift hinj
  have hσ : ∀ a : 𝓞 F, σ (a : F) = τ a := fun a => IsFractionRing.lift_algebraMap hinj a
  refine ⟨σ, ⟨hz, fun a d g h hg hh he => ?_⟩, fun σ' hσ' => ?_⟩
  · obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    have ha₂' : algebraMap (𝓞 F) F a₂ ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha₂
    obtain ⟨G₁, e₁⟩ := hG a₁
    obtain ⟨G₂, e₂⟩ := hG a₂
    obtain ⟨D₁, H₁, M₁, h₁, m₁, f₁⟩ := exists_form c G₁
    obtain ⟨D₂, H₂, M₂, h₂, m₂, f₂⟩ := exists_form c G₂
    obtain ⟨ny₁, y₁⟩ := f₁ Ω y hy
    obtain ⟨ny₂, y₂⟩ := f₂ Ω y hy
    obtain ⟨nz₁, z₁⟩ := f₁ ℂ z hc
    obtain ⟨nz₂, z₂⟩ := f₂ ℂ z hc
    have hP : IsMultiHomog (H₂ * M₁ * g - H₁ * M₂ * h) (D₁ + D₂ + d) := by
      refine homog_sub ?_ (isMultiHomog_mul (isMultiHomog_mul h₁ m₂) hh)
      rw [add_comm D₁]
      exact isMultiHomog_mul (isMultiHomog_mul h₂ m₁) hg
    have h0 : aeval y (H₂ * M₁ * g - H₁ * M₂ * h) = 0 := by
      have hφ : φ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
      simp only [map_sub, map_mul, y₁, y₂, he, e₁, e₂]
      rw [map_div₀]
      field_simp
      ring
    have h1 := aeval_eq_zero hz hP h0
    simp only [map_sub, map_mul, z₁, z₂, ← hτ a₁ G₁ e₁, ← hτ a₂ G₂ e₂, ← evC_eq_aeval z g,
      ← evC_eq_aeval z h, ← hσ] at h1
    have hs₂ : σ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
    rw [map_div₀]
    have hM : aeval z M₁ * aeval z M₂ ≠ 0 := mul_ne_zero nz₁ nz₂
    have h2 : σ (algebraMap (𝓞 F) F a₂) * evC z g = σ (algebraMap (𝓞 F) F a₁) * evC z h := by
      apply mul_left_cancel₀ hM
      linear_combination h1
    field_simp
    linear_combination h2
  · refine RingHom.ext fun a => ?_
    have key : ∀ a : 𝓞 F, σ' (a : F) = σ (a : F) := by
      intro a
      obtain ⟨G, e⟩ := hG a
      obtain ⟨D, H, M, h, m, f⟩ := exists_form c G
      obtain ⟨-, fy⟩ := f Ω y hy
      obtain ⟨nz, fz⟩ := f ℂ z hc
      have hy' : aeval y H = φ (a : F) * aeval y M := by rw [fy, e, mul_comm]
      have h1 := hσ'.2 (a : F) D H M h m hy'
      rw [evC_eq_aeval, evC_eq_aeval, fz] at h1
      rw [hσ, hτ a G e]
      have := mul_left_cancel₀ nz (h1.trans (mul_comm _ _))
      exact this.symm
    obtain ⟨a₁, a₂, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    rw [map_div₀, map_div₀]
    exact congrArg₂ _ (key a₁) (key a₂)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.RegSection

theorem section_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (s t : Γ(X, U))
    (e : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) =
      genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq t)) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => h.inj ⟨q, hU q hq⟩ (e q hq)

theorem existsUnique_section : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω), (U : Set X).Nonempty → (∀ q (hq : q ∈ U), a ∈ regAt ξ ⟨q, hU q hq⟩) → ∃! g : Γ(X, U), ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq g) = a := by
  intro X Ω _ ξ _ h U hU a _ ha
  have loc : ∀ x : U, ∃ (W : X.Opens) (_ : W ≤ U) (hx : x.1 ∈ W) (t : Γ(X, W)),
      genMap ξ ⟨x.1, hU x.1 x.2⟩ (X.presheaf.germ W x.1 hx t) = a := by
    intro x
    obtain ⟨g, hg⟩ := ha x.1 x.2
    obtain ⟨W, hx, t, rfl⟩ := X.presheaf.exists_germ_eq g
    refine ⟨W ⊓ U, inf_le_right, ⟨hx, x.2⟩, X.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
    exact (congrArg (genMap ξ ⟨x.1, hU x.1 x.2⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) x.1 ⟨hx, x.2⟩ t)).trans hg
  choose W hWU hx t ht using loc
  have val : ∀ (x : U) (y : X) (hy : y ∈ W x),
      genMap ξ ⟨y, hU y (hWU x hy)⟩ (X.presheaf.germ (W x) y hy (t x)) = a := fun x y hy =>
    (genMap_germ_eq_genMap_germ ξ (W x) ⟨y, hU y (hWU x hy)⟩ ⟨x.1, hU x.1 x.2⟩ hy (hx x) (t x)).trans (ht x)
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    apply h.inj ⟨y, hU y (hWU i hi)⟩
    exact (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i))).trans
      ((val i y hi).trans ((val j y hj).symm.trans
        (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j))).symm))
  have hcov : U ≤ iSup W := fun y hy =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U (fun i => homOfLE (hWU i)) hcov t compat
  have spec : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) = a := by
    intro q hq
    have e := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hWU ⟨q, hq⟩)) q (hx ⟨q, hq⟩) s
    have e2 : (X.presheaf.map (homOfLE (hWU ⟨q, hq⟩)).op).hom s = t ⟨q, hq⟩ := hs ⟨q, hq⟩
    exact (congrArg (genMap ξ ⟨q, hU q hq⟩) e).symm.trans
      ((congrArg (fun z => genMap ξ ⟨q, hU q hq⟩ ((X.presheaf.germ (W ⟨q, hq⟩) q (hx ⟨q, hq⟩)).hom z)) e2).trans
        (ht ⟨q, hq⟩))
  exact ⟨s, spec, fun s' hs' => section_eq h U hU s' s fun q hq => (hs' q hq).trans (spec q hq).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RegSection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSchemeMapFromSpecialFibre
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.CompanionTheory.FinFlatModel

open IsLocalRing

section Model

variable {R : Type} [CommRing R] [IsLocalRing R]

noncomputable def quotEquiv : (R ⧸ maximalIdeal R ^ (0 + 1)) ≃+* ResidueField R :=
  Ideal.quotEquivOfEq (by simp)

noncomputable def specIso :
    Spec (CommRingCat.of (ResidueField R)) ≅
      Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))) where
  hom := Spec.map (CommRingCat.ofHom (quotEquiv (R := R)).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (quotEquiv (R := R)).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (quotEquiv (R := R)).toRingHom.comp (quotEquiv (R := R)).symm.toRingHom =
        RingHom.id _ := by
      ext x
      simp
    rw [this]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (quotEquiv (R := R)).symm.toRingHom.comp (quotEquiv (R := R)).toRingHom =
        RingHom.id _ := by
      ext x
      simp
    rw [this]
    exact Spec.map_id _

theorem specIso_hom_thick :
    (specIso (R := R)).hom ≫ thick R (maximalIdeal R) 0 =
      Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) := by
  simp only [specIso, thick]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem isPullback_fibre {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := P)).toRingHom) ≫
        i.inv)
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (specIso (R := R)).hom)
      X.hom (thick R (maximalIdeal R) 0) := by
  refine IsPullback.of_iso
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R (ResidueField R) P)).flip
    (Iso.refl _) i.symm specIso (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [hi]
  · simp [specIso_hom_thick]

theorem exists_model (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    ∃ (P : Type) (_ : CommRing P) (_ : Algebra R P) (i : X.left ≅ Spec (CommRingCat.of P)),
      X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  obtain ⟨g, hg⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let _ : Algebra R Γ(X.left, ⊤) := g.hom.toAlgebra
  refine ⟨Γ(X.left, ⊤), inferInstance, g.hom.toAlgebra, X.left.isoSpec, ?_⟩
  have : CommRingCat.ofHom (algebraMap R Γ(X.left, ⊤)) = g := rfl
  erw [this, hg]
  simp

theorem map_left_eq {P Q : Type} [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (φ : Q →ₐ[R] P)
    (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)))
    (hj : Y.hom = j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)))
    (hf : f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv) :
    ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left =
      (isPullback_fibre X i hi).isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
        (isPullback_fibre Y j hj).isoPullback.hom := by
  have e1 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := Q)).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := P)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have e2 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := ResidueField R) (B := Q))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := ResidueField R) (B := P))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp
  apply pullback.hom_ext
  · have h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫
        pullback.fst Y.hom (thick R (maximalIdeal R) 0) =
        pullback.fst X.hom (thick R (maximalIdeal R) 0) ≫ f.left := pullback.lift_fst _ _ _
    rw [h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst,
      reassoc_of% e1, ← (isPullback_fibre X i hi).isoPullback_inv_fst, hf]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · have h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫
        pullback.snd Y.hom (thick R (maximalIdeal R) 0) =
        pullback.snd X.hom (thick R (maximalIdeal R) 0) := pullback.lift_snd _ _ _
    rw [h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd,
      reassoc_of% e2, ← (isPullback_fibre X i hi).isoPullback_inv_snd]

theorem finite_of_model {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    Module.Finite R P := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
  have h' : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R P))) := by
    rw [h]
    infer_instance
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h')

theorem flat_of_model {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) (hX : Flat X.hom)
    (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    Module.Flat R P := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
  have h' : Flat (Spec.map (CommRingCat.ofHom (algebraMap R P))) := by
    rw [h]
    infer_instance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h')

end Model

theorem exists_algHom_model :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y), ∃ (P Q : Type) (_ : CommRing P) (_ : CommRing Q) (_ : Algebra R P) (_ : Algebra R Q) (φ : Q →ₐ[R] P) (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q)) (i₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj X).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] P))) (j₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj Y).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] Q))), Module.Finite R P ∧ Module.Finite R Q ∧ (Flat X.hom → Module.Flat R P) ∧ f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv ∧ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map f).left = i₀.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) ≫ j₀.inv := by
  intro R _ _ X Y _ _ f
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  obtain ⟨P, _, _, i, hi⟩ := exists_model X
  obtain ⟨Q, _, _, j, hj⟩ := exists_model Y
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i.inv ≫ f.left ≫ j.hom)
  have hcomm : CommRingCat.ofHom (algebraMap R Q) ≫ ψ = CommRingCat.ofHom (algebraMap R P) := by
    apply Spec.map_injective
    have hw : f.left ≫ Y.hom = X.hom := Over.w f
    rw [Spec.map_comp, hψ]
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
    have h2 : j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)) = Y.hom := hj.symm
    rw [h1, ← hw]
    simp only [Category.assoc, h2]
  let φ : Q →ₐ[R] P :=
    { ψ.hom with
      commutes' := fun r => by
        have := congrArg (fun g => g.hom r) hcomm
        simpa using this }
  have hφ : CommRingCat.ofHom φ.toRingHom = ψ := rfl
  have hf : f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv := by
    rw [hφ, hψ]
    simp
  refine ⟨P, Q, inferInstance, inferInstance, inferInstance, inferInstance, φ, i, j,
    (isPullback_fibre X i hi).isoPullback.symm, (isPullback_fibre Y j hj).isoPullback.symm,
    finite_of_model X i hi, finite_of_model Y j hj, fun h => flat_of_model X h i hi, hf, ?_⟩
  exact map_left_eq f φ i j hi hj hf

end GlobalTheory.CompanionTheory.FinFlatModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormulaStatement
section
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_trdeg_formula : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E : Type) [AddCommGroup E] [Module Ω₀ E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω₀ E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ), IsGenericFlag (Ω' := Ω) j V b₀ d → Algebra.trdeg Ω₀ Ω = ((∑ σ, r σ * (r σ - 1) / 2 : ℕ) : Cardinal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChangeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_triangular_change : ∀ (L Li : Type) [Field L] [AddCommGroup Li] [Module L Li] (r : ℕ) (f b g : Fin r → Li) (v w : Matrix (Fin r) (Fin r) L), LinearIndependent L f → LinearIndependent L b → (∀ k, v k k = 1) → (∀ l k, l < k → v l k = 0) → (∀ l k, k < l → w l k = 0) → (∀ k, w k k ≠ 0) → (∀ k, g k = ∑ j, (v * w) j k • f j) → (∀ i : ℕ, GlobalTheory.CompanionTheory.Ar.flagStep L b i = GlobalTheory.CompanionTheory.Ar.flagStep L g i) → ∃ Tm : Matrix (Fin r) (Fin r) L, (∀ i, b i = ∑ m, Tm i m • ∑ j, v j m • f j) ∧ (∀ i m, i < m → Tm i m = 0) ∧ ∀ i, Tm i i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular | exact GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeFiniteIndexStatement
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_lattice_finite_index : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (T : FinitePlace L → Matrix (Fin n) (Fin n) L), (∀ v, (T v).det ≠ 0) → {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite → (glued T).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧ (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (glued T).toAddSubgroup ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeLocalizationStatement
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_lattice_localization : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (T : FinitePlace L → Matrix (Fin n) (Fin n) L), (∀ v, (T v).det ≠ 0) → {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite → ∀ v, locAt v (glued T) = locAt v (frame (T v)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued <;> assumption)
end

