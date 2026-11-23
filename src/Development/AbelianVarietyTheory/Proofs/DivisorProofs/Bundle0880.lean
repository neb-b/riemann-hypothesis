module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0850
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabEqStabilizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupSchemeIdealGeneratedByDimElements
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FinSubGen

theorem pullback_lift_iff : ∀ (K : Type) [Field K] (A A' H : Over (Sp K)) [GrpObj A'] (j : H ⟶ A) (q : A ⟶ A'), IsPullback j (toUnit H) q η[A'] → ∀ (T : Scheme.{0}) (y' : T ⟶ A.left), (∃ y : T ⟶ H.left, y ≫ j.left = y') ↔ ∃ z : T ⟶ Sp K, z ≫ (η[A']).left = y' ≫ q.left := by
  intro K _ A A' H _ j q hpb T y'
  have h2 := hpb.map (Over.forget (Sp K))
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (toUnit H).left, ?_⟩
    simp only [Category.assoc, ← Over.comp_left, hpb.w]
  · rintro ⟨z, hz⟩
    exact ⟨h2.lift y' z hz.symm, h2.lift_fst _ _ _⟩

theorem section_factor_iff : ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) (s : Sp K ⟶ X), s ≫ f = 𝟙 _ → ∀ x : X, x ∈ Set.range s.base → ∀ (R' : Type) [CommRing R'] (φ : X.presheaf.stalk x →+* R'), (∃ z : Sp R' ⟶ Sp K, z ≫ s = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x) ↔ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤ RingHom.ker φ := by
  intro K _ X f s hs x hx R' _ φ
  obtain ⟨p, rfl⟩ := hx
  obtain rfl : p = IsLocalRing.closedPoint (CommRingCat.of K) := Subsingleton.elim _ _
  set r := Scheme.stalkClosedPointTo s
  have hr : Spec.map r ≫ X.fromSpecStalk _ = s := Scheme.Spec_stalkClosedPointTo_fromSpecStalk s
  set c : K →+* X.presheaf.stalk (s.base (IsLocalRing.closedPoint (CommRingCat.of K))) :=
    (Spec.preimage (X.fromSpecStalk _ ≫ f)).hom with hcdef
  have hc : Spec.map (CommRingCat.ofHom c) = X.fromSpecStalk _ ≫ f := by simp [c]
  have hrc : ∀ t : K, r.hom (c t) = t := by
    have h1 : Spec.map (CommRingCat.ofHom c ≫ r) = Spec.map (𝟙 (CommRingCat.of K)) := by
      rw [Spec.map_comp, hc, ← Category.assoc, hr, hs, Spec.map_id]
    have h2 := Spec.map_injective h1
    intro t
    exact congrArg (fun u : CommRingCat.of K ⟶ CommRingCat.of K => u.hom t) h2
  have hm : ∀ a, a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (s.base (IsLocalRing.closedPoint (CommRingCat.of K)))) → r.hom a = 0 := by
    intro a ha
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_map_unit r.hom a (isUnit_iff_ne_zero.mpr h))
  constructor
  · rintro ⟨z, hz⟩ a ha
    have hz2 : (z ≫ Spec.map r) ≫ X.fromSpecStalk _ = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk _ := by
      rw [Category.assoc, hr]; exact hz
    have hz' := (cancel_mono _).mp hz2
    rw [← Spec.map_preimage z, ← Spec.map_comp] at hz'
    have h3 := Spec.map_injective hz'
    have h4 : φ a = (Spec.preimage z).hom (r.hom a) :=
      (congrArg (fun u : _ ⟶ CommRingCat.of R' => u.hom a) h3).symm
    rw [RingHom.mem_ker, h4, hm a ha, map_zero]
  · intro hφ
    refine ⟨Spec.map (CommRingCat.ofHom (φ.comp c)), ?_⟩
    have e1 : Spec.map (CommRingCat.ofHom (φ.comp c)) ≫ Spec.map r ≫ X.fromSpecStalk _ = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk _ := by
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      show φ (c (r.hom a)) = φ a
      have hmem : c (r.hom a) - a ∈ IsLocalRing.maximalIdeal _ := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have := hu.map r.hom
        rw [map_sub, hrc, sub_self] at this
        exact not_isUnit_zero this
      have := hφ hmem
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
      exact this
    rwa [hr] at e1

theorem stalk_regular_of_section : ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) [IsSeparated f] (g : ℕ), SmoothOfRelativeDimension g f → ∀ (s : Sp K ⟶ X), s ≫ f = 𝟙 _ → ∀ x : X, x ∈ Set.range s.base → IsNoetherianRing (X.presheaf.stalk x) ∧ IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) = g := by
  intro K _ X f _ g hg s hs x hx
  have hci : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id f s hs
  have hcl : IsClosed ({x} : Set X) := by
    have e : Set.range s.base = {x} := by
      obtain ⟨p, rfl⟩ := hx
      ext y
      constructor
      · rintro ⟨p', rfl⟩
        rw [Subsingleton.elim p' p]
        rfl
      · rintro rfl
        exact ⟨p, rfl⟩
    rw [← e]
    exact s.isClosedEmbedding.isClosed_range
  set σ : K →+* X.presheaf.stalk x := (Spec.preimage (X.fromSpecStalk x ≫ f)).hom with hσdef
  have hσ : X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) := by
    simp [σ]
  haveI : IsLocalHom σ := ⟨fun a ha => isUnit_iff_ne_zero.mpr (by rintro rfl; simp at ha)⟩
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.StabFlat.stalk_of_smooth_local K X f g hg x hcl σ hσ inferInstance
  have hb : (IsLocalRing.maximalIdeal K).map σ = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  let e : (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal K).map σ) ≃+* X.presheaf.stalk x :=
    (Ideal.quotEquivOfEq hb).trans (RingEquiv.quotientBot _)
  exact ⟨h1, IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h4⟩

theorem ideal_eq_span_fin : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → ∃ f : Fin g → A.left.presheaf.stalk x₀, Ideal.span (Set.range f) = J := by
  intro K _ _ A _ g hA hg H _ j hj hci hfin x₀ hx₀ J hJ
  have hmono : Mono j := Over.mono_of_mono_left j
  obtain ⟨A', _, hA', q, hq, hqfin, hqflat, hqsurj, hpb⟩ := _root_.GlobalTheory.AbelianQuotientField.exists_quotient K A hA H j hj hmono hfin
  have hη : η[A] ≫ q = η[A'] := IsMonHom.one_hom q
  have hsA : (η[A]).left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have hsA' : (η[A']).left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  obtain ⟨p, hp⟩ := hx₀
  have hx' : q.left.base x₀ ∈ Set.range (η[A']).left.base := ⟨p, by
    rw [← hp, ← hη]; rfl⟩
  have hAs := hA.smooth
  have hAp := hA.proper
  have hA's := hA'.smooth
  have hA'p := hA'.proper
  have hA'c := hA'.geomConnected
  have : ConnectedSpace A'.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A'.hom) (𝟙 _) (𝟙 _) A'.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected A'.hom (q.left.base x₀)
  have Lreg : IsRegularLocalRing (A'.left.presheaf.stalk (q.left.base x₀)) :=
    (stalk_regular_of_section K A'.left A'.hom n hn _ hsA' _ hx').2.1
  have Ldim := stalk_regular_of_section K A.left A.hom g hg _ hsA x₀ ⟨p, hp⟩
  set σ := (q.left.stalkMap x₀).hom
  have key : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), J ≤ RingHom.ker ψ ↔ (IsLocalRing.maximalIdeal (A'.left.presheaf.stalk (q.left.base x₀))).map σ ≤ RingHom.ker ψ := by
    intro R' _ ψ
    rw [← hJ, pullback_lift_iff K A A' H j q hpb, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
      ← section_factor_iff K A'.left A'.hom _ hsA' _ hx' R' (ψ.comp σ)]
    have e : Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀ ≫ q.left =
        Spec.map (CommRingCat.ofHom (ψ.comp σ)) ≫ A'.left.fromSpecStalk (q.left.base x₀) := by
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp]
      rfl
    simp only [Category.assoc, e]
  have Lgeo : J = (IsLocalRing.maximalIdeal (A'.left.presheaf.stalk (q.left.base x₀))).map σ := by
    apply le_antisymm
    · simpa using (key _ (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (A'.left.presheaf.stalk (q.left.base x₀))).map σ))).2 (by simp)
    · simpa using (key _ (Ideal.Quotient.mk J)).1 (by simp)
  obtain ⟨_, hart⟩ := _root_.GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing K A H j hj hci hfin x₀ ⟨p, hp⟩ J hJ
  have hflat : σ.Flat := Flat.stalkMap q.left x₀
  haveI := Ldim.1
  rw [Lgeo] at hart ⊢
  exact _root_.GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre _ _ σ inferInstance hflat hart g Ldim.2.2

end GlobalTheory.FinSubGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetEqFinsumOrbit
section
open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

variable {Γ G : Type} [Group Γ] [Group G]

noncomputable def doubleCosetToOrbit (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G) →
      MulAction.orbitRel.Quotient H (LeftCosets ι K) :=
  Quotient.lift (fun x => (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x))) (by
    intro a b hab
    obtain ⟨_, ⟨h, hh, rfl⟩, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
    refine (Quotient.sound ?_).symm
    refine ⟨⟨h, hh⟩, ?_⟩
    show LeftCosets.mk ι K (ι h * a) = LeftCosets.mk ι K (ι h * a * k)
    rw [LeftCosets.mk_eq_mk]
    convert hk using 1
    group)

theorem doubleCosetToOrbit_mk (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) (x : G) :
    doubleCosetToOrbit ι H K (DoubleCoset.mk _ _ x) =
      Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x) := rfl

theorem doubleCosetToOrbit_bijective (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    Function.Bijective (doubleCosetToOrbit ι H K) := by
  constructor
  · intro p q hpq
    rw [← DoubleCoset.out_eq' p, ← DoubleCoset.out_eq' q] at hpq ⊢
    rw [doubleCosetToOrbit_mk, doubleCosetToOrbit_mk] at hpq
    obtain ⟨h, hh⟩ := Quotient.exact hpq
    have hh' : LeftCosets.mk ι K (ι (h : Γ) * q.out) = LeftCosets.mk ι K p.out := hh
    rw [LeftCosets.mk_eq_mk] at hh'
    refine ((@DoubleCoset.eq _ _ _ _ _ _).2 ⟨ι h, Subgroup.mem_map_of_mem ι h.2, _, hh', ?_⟩).symm
    group
  · intro o
    induction o using Quotient.inductionOn with
    | h y =>
      refine ⟨DoubleCoset.mk _ _ (LeftCosets.rep ι K y), ?_⟩
      rw [doubleCosetToOrbit_mk, LeftCosets.mk_rep]

theorem finsum_doubleCoset_eq_finsum_orbit {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (H : Subgroup Γ)
    (K : Subgroup G) (g : LeftCosets ι K → ℂ) (hg : ∀ h ∈ H, ∀ y : LeftCosets ι K, g (h • y) = g y) :
    ∑ᶠ q : DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G), g (LeftCosets.mk ι K (Quotient.out q)) =
      ∑ᶠ o : MulAction.orbitRel.Quotient H (LeftCosets ι K), g (Quotient.out o) := by
  let e := Equiv.ofBijective _ (doubleCosetToOrbit_bijective ι H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have hq : e q = Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out) := by
    show doubleCosetToOrbit ι H K q = _
    conv_lhs => rw [← DoubleCoset.out_eq' q]
    rfl
  rw [hq]
  obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq
    (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out)))
  rw [← hh]
  exact (hg h h.2 _).symm

end GlobalTheory.LKCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormEqMulInner
section
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.ConjLiftUnique

private lemma exists_linearMap_sesqForm_eq_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) : ∃ A : E →ₗ[ℂ] E, ∀ x y, b x y = ⟪A x, y⟫_ℂ := by
  let f : E → E := fun x => (InnerProductSpace.toDual ℂ E).symm (LinearMap.toContinuousLinearMap (b x))
  have hf : ∀ x y, ⟪f x, y⟫_ℂ = b x y := by
    intro x y
    simp only [f, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, fun x y => (hf x y).symm⟩
  · intro x x'
    apply ext_inner_right ℂ
    intro y
    simp [hf, inner_add_left]
  · intro c x
    apply ext_inner_right ℂ
    intro y
    simp [hf, inner_smul_left]

theorem form_eq_mul_inner {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (g : I → E →ₗ[ℂ] E) (hu : ∀ k x y, ⟪g k x, g k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ E, (∀ k, ∀ x ∈ U, g k x ∈ U) → U = ⊥ ∨ U = ⊤)
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (hb : ∀ k x y, b (g k x) (g k y) = b x y) : ∃ c : ℂ, ∀ x y, b x y = c * ⟪x, y⟫_ℂ := by
  obtain ⟨A, hA⟩ := exists_linearMap_sesqForm_eq_inner b
  have hinj : ∀ k, Function.Injective (g k) := by
    intro k
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h0 : ⟪x, x⟫_ℂ = 0 := by rw [← hu k x x, LinearMap.mem_ker.mp hx, inner_zero_left]
    exact inner_self_eq_zero.mp h0
  have hsurj : ∀ k, Function.Surjective (g k) := fun k => LinearMap.injective_iff_surjective.mp (hinj k)
  have hcomm : ∀ k x, A (g k x) = g k (A x) := by
    intro k x
    apply ext_inner_right ℂ
    intro y
    obtain ⟨z, rfl⟩ := hsurj k y
    rw [← hA, hb, hu, hA]
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨0, fun x y => by simp [Subsingleton.elim x 0]⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  have hinv : ∀ k, ∀ x ∈ Module.End.eigenspace A c, g k x ∈ Module.End.eigenspace A c := by
    intro k x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hcomm, hx, map_smul]
  rcases hirr _ hinv with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.mp hc)
  · refine ⟨conj c, fun x y => ?_⟩
    have hx : x ∈ Module.End.eigenspace A c := h ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [hA, hx, inner_smul_left]

private lemma inner_self_eq_one_of_norm_eq_one' {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {u : F}
    (hu : ‖u‖ = 1) : ⟪u, u⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hu]; simp

variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem exists_const (B : (∀ i, E i) → W → (∀ i, E i) → W → ℂ) (w₀ : W) (h₀ : ‖w₀‖ = 1)
    (h1 : ∀ w w' i v v', ∃ c : ℂ, ∀ a a' : E i,
      B (Function.update v i a) w (Function.update v' i a') w' = c * ⟪a, a'⟫_ℂ)
    (h2 : ∀ v v', ∃ c : ℂ, ∀ w w', B v w v' w' = c * ⟪w, w'⟫_ℂ) :
    ∃ c : ℂ, ∀ v w v' w', B v w v' w' = c * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ) := by
  by_cases hall : ∀ i, Nontrivial (E i)
  · have he : ∀ i, ∃ e : E i, ‖e‖ = 1 := fun i => by
      haveI := hall i
      exact exists_norm_eq (E i) zero_le_one
    choose e he using he
    have hee : ∀ i, ⟪e i, e i⟫_ℂ = 1 := fun i => inner_self_eq_one_of_norm_eq_one' (he i)
    have hw : ∀ v v' w w', B v w v' w' = B v w₀ v' w₀ * ⟪w, w'⟫_ℂ := by
      intro v v' w w'
      obtain ⟨c, hc⟩ := h2 v v'
      rw [hc, hc w₀ w₀, inner_self_eq_one_of_norm_eq_one' h₀, mul_one]
    have hs : ∀ s : Finset ι, ∀ v v' : ∀ i, E i, (∀ i ∉ s, v i = e i) → (∀ i ∉ s, v' i = e i) →
        B v w₀ v' w₀ = B e w₀ e w₀ * ∏ i ∈ s, ⟪v i, v' i⟫_ℂ := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro v v' hv hv'
        have e1 : v = e := funext fun i => hv i (by simp)
        have e2 : v' = e := funext fun i => hv' i (by simp)
        subst e1 e2
        simp
      | insert j s hj ih =>
        intro v v' hv hv'
        obtain ⟨c, hc⟩ := h1 w₀ w₀ j v v'
        have k1 := hc (v j) (v' j)
        have k2 := hc (e j) (e j)
        rw [Function.update_eq_self, Function.update_eq_self] at k1
        rw [hee, mul_one] at k2
        have ih' := ih (Function.update v j (e j)) (Function.update v' j (e j)) ?_ ?_
        · rw [k1, ← k2, ih', Finset.prod_insert hj]
          have hcg : ∀ i ∈ s, ⟪Function.update v j (e j) i, Function.update v' j (e j) i⟫_ℂ = ⟪v i, v' i⟫_ℂ := by
            intro i hi
            have hij : i ≠ j := fun h => hj (h ▸ hi)
            rw [Function.update_of_ne hij, Function.update_of_ne hij]
          rw [Finset.prod_congr rfl hcg]
          ring
        · intro i hi
          by_cases hij : i = j
          · subst hij
            simp
          · rw [Function.update_of_ne hij]
            exact hv i (by simp [hij, hi])
        · intro i hi
          by_cases hij : i = j
          · subst hij
            simp
          · rw [Function.update_of_ne hij]
            exact hv' i (by simp [hij, hi])
    refine ⟨B e w₀ e w₀, fun v w v' w' => ?_⟩
    rw [hw, hs Finset.univ v v' (by simp) (by simp)]
    ring
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    haveI : Subsingleton (E i) := not_nontrivial_iff_subsingleton.mp hi
    refine ⟨0, fun v w v' w' => ?_⟩
    obtain ⟨c, hc⟩ := h1 w w' i v v'
    have k := hc (v i) (v' i)
    rw [Function.update_eq_self, Function.update_eq_self, Subsingleton.elim (v i) 0, inner_zero_left,
      mul_zero] at k
    rw [k, zero_mul]

private lemma inner_self_eq_one_of_unit_norm {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {u : F}
    (hu : ‖u‖ = 1) : ⟪u, u⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hu]; simp

private lemma eq_smul_of_form_eq_of_unit_modulus {Y : Type} [AddCommGroup Y] [Module ℂ Y] (b : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ)
    (hs : ∀ x y, b y x = conj (b x y)) (hd : ∀ x, b x x = 0 → x = 0)
    {x y : Y} {κ : ℂ} (hk : conj κ * κ = 1) (hyy : b y y = b x x) (hxy : b x y = κ * b x x) :
    y = κ • x := by
  have hyx : b y x = conj κ * b x x := by
    rw [hs x y, hxy, map_mul, ← hs x x]
  rw [← sub_eq_zero]
  apply hd
  simp only [map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
  linear_combination hyy - κ * hyx - conj κ * hxy - b x x * hk

theorem exists_phase {Y : Type} [AddCommGroup Y] [Module ℂ Y] (b : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ)
    (hs : ∀ x y, b y x = conj (b x y)) (hp : ∀ x, 0 ≤ (b x x).re) (hd : ∀ x, b x x = 0 → x = 0)
    (F F' : (∀ i, E i) → W → Y) {c₁ c₂ c₃ : ℂ}
    (h1 : ∀ v w v' w', b (F v w) (F v' w') = c₁ * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ))
    (h2 : ∀ v w v' w', b (F' v w) (F' v' w') = c₂ * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ))
    (h3 : ∀ v w v' w', b (F v w) (F' v' w') = c₃ * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ))
    {v₀ v₀' : ∀ i, E i} {w₀ w₀' : W} (n1 : ∀ i, ‖v₀ i‖ = 1) (n2 : ∀ i, ‖v₀' i‖ = 1) (n3 : ‖w₀‖ = 1) (n4 : ‖w₀'‖ = 1)
    {l : ℂ} (hl : ‖l‖ = 1) (hm : F v₀ w₀ = l • F' v₀' w₀') :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ v w, F' v w = κ • F v w := by
  have P1 : (∏ i, ⟪v₀ i, v₀ i⟫_ℂ) * ⟪w₀, w₀⟫_ℂ = 1 := by
    rw [Finset.prod_eq_one (fun i _ => inner_self_eq_one_of_unit_norm (n1 i)), inner_self_eq_one_of_unit_norm n3, one_mul]
  have P2 : (∏ i, ⟪v₀' i, v₀' i⟫_ℂ) * ⟪w₀', w₀'⟫_ℂ = 1 := by
    rw [Finset.prod_eq_one (fun i _ => inner_self_eq_one_of_unit_norm (n2 i)), inner_self_eq_one_of_unit_norm n4, one_mul]
  have hl1 : conj l * l = 1 := by
    rw [Complex.conj_mul', hl]
    simp
  have e1 : b (F v₀ w₀) (F v₀ w₀) = c₁ := by rw [h1, P1, mul_one]
  have e2 : b (F' v₀' w₀') (F' v₀' w₀') = c₂ := by rw [h2, P2, mul_one]
  have hc : c₁ = c₂ := by
    rw [← e1, ← e2, hm]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul]
    linear_combination b (F' v₀' w₀') (F' v₀' w₀') * hl1
  have hA : c₃ * ((∏ i, ⟪v₀ i, v₀' i⟫_ℂ) * ⟪w₀, w₀'⟫_ℂ) = conj l * c₁ := by
    have t := h3 v₀ w₀ v₀' w₀'
    rw [hm] at t
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at t
    rw [e2, ← hc] at t
    exact t.symm
  have hB : c₃ = conj l * c₁ * ((∏ i, ⟪v₀' i, v₀ i⟫_ℂ) * ⟪w₀', w₀⟫_ℂ) := by
    have t1 := h3 v₀ w₀ v₀ w₀
    have t2 := h2 v₀' w₀' v₀ w₀
    rw [P1, mul_one, hm] at t1
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at t1
    rw [t2] at t1
    rw [← t1, hc]
    ring
  by_cases h0 : c₁ = 0
  · refine ⟨1, by simp, fun v w => ?_⟩
    have a1 : F v w = 0 := hd _ (by rw [h1, h0, zero_mul])
    have a2 : F' v w = 0 := hd _ (by rw [h2, ← hc, h0, zero_mul])
    rw [a1, a2, smul_zero]
  · set p := (∏ i, ⟪v₀ i, v₀' i⟫_ℂ) * ⟪w₀, w₀'⟫_ℂ with hp
    set q := (∏ i, ⟪v₀' i, v₀ i⟫_ℂ) * ⟪w₀', w₀⟫_ℂ with hq
    have hqp : q = conj p := by
      rw [hp, hq]
      simp [map_prod]
    have hl0 : conj l ≠ 0 := by
      intro h
      rw [map_eq_zero] at h
      rw [h, norm_zero] at hl
      exact zero_ne_one hl
    have hqp1 : q * p = 1 := by
      have hz : conj l * c₁ * (q * p - 1) = 0 := by linear_combination hA - p * hB
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (mul_ne_zero hl0 h0)
      · exact sub_eq_zero.mp h
    have hq1 : ‖q‖ = 1 := by
      have h := congrArg norm hqp1
      rw [norm_mul, norm_one] at h
      have e : ‖p‖ = ‖q‖ := by rw [hqp, Complex.norm_conj]
      rw [e] at h
      rcases mul_self_eq_one_iff.mp h with h | h
      · exact h
      · linarith [norm_nonneg q]
    have hκ : ‖conj l * q‖ = 1 := by rw [norm_mul, Complex.norm_conj, hl, hq1, one_mul]
    refine ⟨conj l * q, hκ, fun v w => ?_⟩
    apply eq_smul_of_form_eq_of_unit_modulus b hs hd
    · rw [Complex.conj_mul', hκ]
      simp
    · rw [h2, h1, hc]
    · rw [h3, h1, hB]
      ring

end GlobalTheory.ConjLiftUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralDiagonalHermitianFormMatrices
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_diag_norm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : α → ν → Fˣ, HasGauss μ (fun x => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (x i j))) (g * ∏ i, ∏ j, (sgn E (t i j) * ((nabs F (t i j))⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ ψ hψ hn h1 _ _ μ _
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  haveI : FiniteDimensional F E := hfd
  have hGE : Good E := _root_.GlobalTheory.KSp.good_of_finiteDimensional F E
  haveI := hGE.grp; haveI := hGE.lc; haveI := hGE.sc; haveI := hGE.t2
  let μE : Measure E := Measure.addHaar
  obtain ⟨g₁, hg₁⟩ := _root_.GlobalTheory.KSp.hasGauss_norm_mul F E c δ hE ψ hψ hn h1 μE
  have hGM : Good (Matrix α ν E) := (hmat α ν).2
  haveI := hGM.grp; haveI := hGM.lc; haveI := hGM.sc
  let T : Matrix α ν E ≃ₜ+ (α × ν → E) :=
    { toFun := fun x p => x p.1 p.2
      invFun := fun y i j => y (i, j)
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
      continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j) }
  haveI : BorelSpace (α × ν → E) := Pi.borelSpace
  haveI : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hr : μ.map T = (μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) •
      Measure.pi fun _ : α × ν => μE := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(((μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) : ℝ) : ℂ) *
    g₁ ^ Fintype.card (α × ν), fun t => ?_⟩
  have hpi := _root_.GlobalTheory.KSp.hasGauss_pi E hGE μE (α × ν) (fun p z => ψ ((t p.1 p.2 : F) * Algebra.norm F z))
    (fun p => g₁ * (sgn E (t p.1 p.2) * ((nabs F (t p.1 p.2))⁻¹ : ℝ))) (fun p => hg₁ _)
  have hm := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale _ _ μ _ T _ _ _ hr hpi
  have hsum : ∀ (s : Finset (α × ν)) (f : α × ν → F), ψ (∑ p ∈ s, f p) = ∏ p ∈ s, ψ (f p) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  convert (preTransparency := .reducible) hm using 1
  · funext x
    rw [← Fintype.sum_prod_type', hsum]
    rfl
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_prod_type, mul_assoc]

end GlobalTheory.KSp
end

