module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftReductionStandardFacts
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem abelianLift_facts : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → AllPrim (dp0 R) (𝟙 _) A' ∧ AllPrim (dp0 R₀) (𝟙 _) A₀ ∧ AllPrim (divided₂ hI) (spMap π) A₀ ∧ Function.Bijective (liftMor (divided₂ hI) h').pull ∧ Module.Finite R (Cr hI π A₀.hom) ∧ Module.Projective R (Cr hI π A₀.hom) ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  have F : AbelianDeRham.Free :=
    GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.Proof.abelianDeRhamFree_of_hodge H1 H2)
  have C : CrystallineDeRham := H1.toCrystallineDeRham
  have Rg : AbelianDeRham.Rigid := AbelianDeRham.rigid_of_free_of_crystallineDeRham F C
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h'
  have hg₀ : SmoothOfRelativeDimension g A₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h'.1 hg
  have p' : AllPrim (dp0 R) (𝟙 _) A' := (F R A' g hA hg).1
  have p₀ : AllPrim (dp0 R₀) (𝟙 _) A₀ := (F R₀ A₀ g hA₀ hg₀).1
  have hκ : IsNilDP (divided₂ hI) := isDPNilpotent_squareZero hI
  have bij := Rg R A' g hA hg I (divided₂ hI) hκ R₀ π hπ hk A₀ i' h'
  have := hA.smooth
  have := hA.proper
  obtain ⟨b₁, -⟩ := C R I (divided₂ hI) hκ R₀ π hπ hk A'.left A₀.left (A'.hom ≫ 𝟙 _) A₀.hom i' inferInstance
    inferInstance inferInstance (by rw [Category.comp_id]; exact h'.1) (liftMor (divided₂ hI) h').isMor
  have pc : AllPrim (divided₂ hI) (spMap π) A₀ := by
    refine Submodule.eq_top_iff'.2 fun c ↦ ?_
    obtain ⟨c', rfl⟩ := b₁.2 c
    have hc' : c' ∈ prim (dp0 R) (𝟙 _) A' := by rw [show prim (dp0 R) (𝟙 _) A' = ⊤ from p']; trivial
    exact (liftMor (divided₂ hI) h').pullback_mem_primitive hc'
  let e := LinearEquiv.ofBijective (liftMor (divided₂ hI) h').isMor.pull1 b₁
  have fin : Module.Finite R (FirstDeRham (A'.hom ≫ 𝟙 _)) := (F R A' g hA hg).2.1
  have proj : Module.Projective R (FirstDeRham (A'.hom ≫ 𝟙 _)) := (F R A' g hA hg).2.2.1
  exact ⟨p', p₀, pc, bij, Module.Finite.equiv e, Module.Projective.of_equiv e, hA₀, hg₀⟩

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHodgeFiltrationFunctionalExtends
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem exists_extend_hodgeFiltration_functional_split {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hO : Function.Injective (cmpO s)) (h1 : Function.Surjective (cmp1 s))
    (hsurj : Function.Surjective (toHO1 s)) [Module.Projective R (HO1 s)]
    (ψ : F1 s →ₗ[R] R) : ∃ H : FirstDeRham s →ₗ[R] R, ∀ c : F1 s, H c = ψ c := by
  let f : FirstDeRham s →ₗ[R] HO1 s := (toHO1 s).comp (cmp1 s)
  have hf : Function.Surjective f := hsurj.comp h1
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hker : ∀ c : FirstDeRham s, f c = 0 ↔ c ∈ F1 s := fun c ↦ by
    change toHO1 s (cmp1 s c) = 0 ↔ toH1O s c = 0
    rw [structureSheaf_comparison_comm]
    exact ⟨fun h ↦ hO (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
  let p : FirstDeRham s →ₗ[R] F1 s := LinearMap.codRestrict (F1 s) (LinearMap.id - σ.comp f) fun c ↦ by
    rw [← hker]
    have : f (σ (f c)) = f c := LinearMap.congr_fun hσ (f c)
    simp [this]
  refine ⟨ψ.comp p, fun c ↦ ?_⟩
  have hc : f c = 0 := (hker c).2 c.2
  have : p c = c := Subtype.ext (by simp [p, hc])
  simp [this]

end GlobalTheory.CechDR

namespace GlobalTheory.AbelianExtend

open GlobalTheory.CechDR

theorem abelianScheme_hodgeFiltration_functional_extends' : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∃ H : FirstDeRham (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R,
      ∀ c : F1 (A.hom ≫ 𝟙 (Sp R)), H c = ψ c := by
  intro hC hH R _ A _ g hab hdim ψ
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hsurj⟩, -⟩ := hH R A g hab hdim
  haveI := hab.smooth
  haveI := hab.proper
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have h1 := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left (A.hom ≫ 𝟙 (Sp R)) hsm hsep hqc).1.2
  have hO := _root_.GlobalTheory.CechDR.cmpO_injective R A.left (A.hom ≫ 𝟙 (Sp R))
  have hs' : Function.Surjective (toHO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hsurj
  haveI : Module.Projective R (HO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hproj
  exact GlobalTheory.CechDR.exists_extend_hodgeFiltration_functional_split _ hO h1 hs' ψ

end GlobalTheory.AbelianExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfKerLeOfNilpotentReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.QuotEq

theorem eq_of_ker_le_of_reduction : ∀ (A κ : Type) [CommRing A] [CommRing κ] (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (G B : Over (Sp A)) [GrpObj G] [GrpObj B], IsAbelianScheme B → ∀ (q₁ q₂ : G ⟶ B), IsMonHom q₁ → IsMonHom q₂ → Flat q₁.left → Surjective q₁.left → QuasiCompact q₁.left → (∀ (T : Over (Sp A)) (x : T ⟶ G), x ≫ q₁ = 1 → x ≫ q₂ = 1) → pullback.fst G.hom (spMap π) ≫ q₁.left = pullback.fst G.hom (spMap π) ≫ q₂.left → q₁ = q₂ := by
  intro A κ _ _ π hπ hnil G B _ _ hB q₁ q₂ h₁ h₂ hfl hsu hqc hker hκ
  haveI := h₁; haveI := h₂; haveI := hfl; haveI := hsu; haveI := hqc
  obtain ⟨d, hd⟩ := GlobalTheory.ExtensionRigidity.exists_factor q₁ q₂ (fun W a b h => by
    have e : (a * b⁻¹) ≫ q₁ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, h, mul_inv_cancel]
    have e₂ := hker W (a * b⁻¹) e
    rw [MonObj.mul_comp, GrpObj.inv_comp] at e₂
    exact mul_inv_eq_one.1 e₂)
  have hη : η[B] ≫ d = η[B] := by
    calc η[B] ≫ d = (η[G] ≫ q₁) ≫ d := by rw [IsMonHom.one_hom q₁]
      _ = η[B] := by rw [Category.assoc, hd, IsMonHom.one_hom q₂]
  haveI hdm : IsMonHom d := GlobalTheory.rigidity_holds (Sp A) B B hB hB d hη
  let qκ : pullback G.hom (spMap π) ⟶ pullback B.hom (spMap π) :=
    pullback.lift (pullback.fst G.hom (spMap π) ≫ q₁.left) (pullback.snd G.hom (spMap π))
      (by rw [Category.assoc, Over.w, pullback.condition])
  have hq₁ : qκ ≫ pullback.fst B.hom (spMap π) = pullback.fst G.hom (spMap π) ≫ q₁.left :=
    pullback.lift_fst _ _ _
  have hsq : IsPullback (pullback.fst G.hom (spMap π)) qκ q₁.left (pullback.fst B.hom (spMap π)) := by
    refine IsPullback.of_bot ?_ hq₁.symm (IsPullback.of_hasPullback B.hom (spMap π))
    rw [pullback.lift_snd, Over.w]
    exact IsPullback.of_hasPullback G.hom (spMap π)
  haveI : Flat qκ := MorphismProperty.of_isPullback hsq hfl
  haveI : Surjective qκ := MorphismProperty.of_isPullback hsq hsu
  haveI : QuasiCompact qκ := MorphismProperty.of_isPullback hsq hqc
  have hfib : pullback.fst B.hom (spMap π) ≫ d.left = pullback.fst B.hom (spMap π) := by
    rw [← cancel_epi qκ, reassoc_of% hq₁, ← Over.comp_left, hd, ← hκ, hq₁]
  have hP := isGrpPullback_pullback B (spMap π)
  have hu := GlobalTheory.HomLift.existsUnique_isMonHom_lift A κ π hπ hnil _ _ B B _ _ hP hP hB hB
    (𝟙 ((Over.pullback (spMap π)).obj B)) (𝟙 B) (by simp)
  have hd1 : d = 𝟙 B := hu.unique ⟨hdm, by simpa using hfib⟩ ⟨inferInstance, by simp⟩
  rw [← hd, hd1, Category.comp_id]

end GlobalTheory.Mum.QuotEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfConstantDimension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DimRed

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

abbrev qmap (π : R →+* R₀) (f : R) : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f} :=
  Ideal.quotientMap _ π (Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    rw [SetLike.mem_coe, Ideal.mem_comap]; exact Ideal.mem_span_singleton_self _)))

theorem qmap_facts (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) (f : R) :
    Function.Surjective (qmap π f) ∧ RingHom.ker (qmap π f) = I.map (Ideal.Quotient.mk _) ∧
      (I.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ 2 = 0 ∧
      (qmap π f).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π := by
  refine ⟨Ideal.quotientMap_surjective hπ, ?_, ?_, Ideal.quotientMap_comp_mk _⟩
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
      obtain ⟨r, rfl⟩ := hπ c
      refine ⟨x - r * f, ?_, ?_⟩
      · rw [← hk, RingHom.mem_ker, map_sub, map_mul, hc, sub_self]
      · rw [Ideal.Quotient.eq]
        simpa using Ideal.mul_mem_left _ r (Ideal.mem_span_singleton_self f)
    · rintro ⟨y, hy, hyx⟩
      rw [Ideal.Quotient.eq] at hyx
      have h1 : π (y - x) ∈ Ideal.span {π f} := by
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyx
        rw [← hc, map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      have h2 : π y = 0 := by rw [← RingHom.mem_ker, hk]; exact hy
      rw [map_sub, h2, zero_sub] at h1
      simpa using (Ideal.span {π f}).neg_mem h1
  · rw [← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot]; exact Ideal.zero_eq_bot.symm

theorem smooth_paste {X Y Z S T : Scheme.{0}} (p : X ⟶ S) (u : Y ⟶ S) (v : Z ⟶ Y) (w : T ⟶ S) (d : Z ⟶ T)
    (hw : d ≫ w = v ≫ u) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd p w)) :
    SmoothOfRelativeDimension g (pullback.snd (pullback.snd p u) v) := by
  have outer := (IsPullback.of_hasPullback (pullback.snd p u) v).paste_horiz (IsPullback.of_hasPullback p u)
  rw [← hw] at outer
  have sq := IsPullback.of_right
    (h₁₁ := pullback.lift (pullback.fst (pullback.snd p u) v ≫ pullback.fst p u)
      (pullback.snd (pullback.snd p u) v ≫ d) (by rw [Category.assoc]; exact outer.w))
    (by rw [pullback.lift_fst]; exact outer) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p w)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h

theorem smooth_zero_of_subsingleton [Subsingleton R₀] {X : Scheme.{0}} (p : X ⟶ Sp R₀) :
    SmoothOfRelativeDimension 0 p :=
  ⟨fun x ↦ absurd (Subsingleton.elim (⊤ : Ideal R₀) (p x).asIdeal) (p x).isPrime.ne_top.symm⟩

theorem lift_of_split (hU : UnobDim) (n : ℕ) : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ e : Fin n → R₀, CompleteOrthogonalIdempotents e →
    (∀ k, ∃ g : ℕ, SmoothOfRelativeDimension g
      (pullback.snd A₀.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k}))))) →
    ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  induction n with
  | zero =>
    intro R _ I hI R₀ _ π hπ hk A₀ _ hA e he _
    have h01 : (0 : R₀) = 1 := by simpa using he.complete
    haveI : Subsingleton R₀ := subsingleton_of_zero_eq_one h01
    exact hU R I hI R₀ π hπ hk A₀ 0 hA (smooth_zero_of_subsingleton _)
  | succ n ih =>
    intro R _ I hI R₀ _ π hπ hk A₀ _ hA e he hsm
    have hnil : ∀ x ∈ RingHom.ker π, IsNilpotent x := fun x hx ↦ ⟨2, by
      rw [hk] at hx
      have h2 := Ideal.pow_mem_pow hx 2
      rw [hI] at h2
      simpa using h2⟩
    obtain ⟨ε, hε, hπε⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent π hnil (e 0) (hπ _) (he.idem 0)
    refine _root_.GlobalTheory.AbLiftGlue.exists_lift_of_split R R₀ I hI π hπ hk ε hε A₀ hA ?_
    intro f hf
    obtain ⟨hρs, hρk, hρ2, hρc⟩ := qmap_facts I hI π hπ hk f
    let B : Over (Sp (R₀ ⧸ Ideal.span {π f})) := (Over.pullback (spMap (Ideal.Quotient.mk _))).obj A₀
    letI : GrpObj B := Functor.grpObjObj
    have hB : IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) (pullback.fst _ _) := isGrpPullback_pullback A₀ _
    have hBa : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hB
    suffices H : ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (i : B.left ⟶ A.left),
        IsGrpPullback B A (spMap (qmap π f)) i ∧ IsAbelianScheme A by
      obtain ⟨A, _, i, h1, h2⟩ := H
      exact ⟨A, _, B, _, i, pullback.fst _ _, qmap π f, hρc, h1, hB, h2⟩
    rcases hf with rfl | rfl
    · have hm := he.map (Ideal.Quotient.mk (Ideal.span {π f}))
      refine ih (R ⧸ Ideal.span {f}) (I.map (Ideal.Quotient.mk _)) hρ2 (R₀ ⧸ Ideal.span {π f}) (qmap π f) hρs hρk
        B hBa (fun k ↦ Ideal.Quotient.mk _ (e k.succ)) ⟨⟨fun k ↦ hm.idem k.succ,
          fun i j hij ↦ hm.ortho ((Fin.succ_injective _).ne hij)⟩, ?_⟩ ?_
      · have hc := hm.complete
        rw [Fin.sum_univ_succ] at hc
        have h0 : Ideal.Quotient.mk (Ideal.span {π f}) (e 0) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, ← hπε]; exact Ideal.mem_span_singleton_self _
        simpa [h0] using hc
      · intro k
        obtain ⟨g, hg⟩ := hsm k.succ
        refine ⟨g, smooth_paste A₀.hom _ _ _
          (spMap (Ideal.Quotient.lift (Ideal.span {1 - e k.succ})
            ((Ideal.Quotient.mk (Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {π f}) (e k.succ)})).comp
              (Ideal.Quotient.mk (Ideal.span {π f}))) ?_)) ?_ g hg⟩
        · intro a ha
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
          have h0 : (Ideal.Quotient.mk (Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {π f}) (e k.succ)}))
              (Ideal.Quotient.mk (Ideal.span {π f}) (1 - e k.succ)) = 0 := by
            rw [Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]; exact Ideal.mem_span_singleton_self _
          rw [RingHom.comp_apply, map_mul, map_mul, h0, mul_zero]
        · rw [← Spec.map_comp, ← Spec.map_comp]
          congr 1
    · obtain ⟨g, hg⟩ := hsm 0
      have h1 : π (1 - ε) = 1 - e 0 := by rw [map_sub, map_one, hπε]
      rw [← h1] at hg
      exact hU _ _ hρ2 _ _ hρs hρk B g hBa hg

theorem abelianUnobstructed_of_unobDim : UnobDim → GlobalTheory.Published.AbelianUnobstructed := by
  intro hU R _ I hI R₀ _ π hπ hk A₀ _ hA
  obtain ⟨n, e, he, hsm⟩ := _root_.GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension R₀ A₀ hA
  exact lift_of_split hU n R I hI R₀ π hπ hk A₀ hA e he hsm

end GlobalTheory.DimRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareGlobalOneFormEqZeroOfAxes
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh.AxesForm

open GlobalTheory.AbCoh.PrimForm

theorem eq_zero_of_axes : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ y : GlobForm (A ⊗ A).hom, GlobalTheory.AbCoh.pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 → GlobalTheory.AbCoh.pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0 := by
  intro R _ A _ g hA hg y h₁ h₂
  obtain ⟨hA2, hg2⟩ := (_root_.GlobalTheory.Obs.sq_abelian_and_affine_H1 R).1 A g hA hg
  obtain ⟨f1, p1, r1⟩ := _root_.GlobalTheory.AbCoh.globForm_FP R A g hA hg
  obtain ⟨f2, p2, r2⟩ := _root_.GlobalTheory.AbCoh.globForm_FP R (A ⊗ A) (g + g) hA2 hg2
  let N : GlobForm (A ⊗ A).hom →ₗ[R] GlobForm A.hom × GlobForm A.hom :=
    LinearMap.prod (pF (lift (𝟙 A) (toUnit A ≫ η[A]))) (pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
  let P : GlobForm A.hom × GlobForm A.hom →ₗ[R] GlobForm (A ⊗ A).hom :=
    LinearMap.coprod (pF (fst A A)) (pF (snd A A))
  have hNP : N ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · show pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.1
      rw [map_add (f := _), pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, add_zero]
    · show pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.2
      rw [map_add (f := _), pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, zero_add]
  have hinj := GlobalTheory.Obs.Axes.injective_of_section N P hNP (fun p ↦ by
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2])
  refine hinj (?_ : N y = N 0)
  rw [map_zero]
  exact Prod.ext h₁ h₂

end GlobalTheory.AbCoh.AxesForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoVanishAffineBases
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

def pairFun (φ : X' ⟶ X) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) : T ⥤ (Pair φ)ᵒᵖ where
  obj t := Opposite.op ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩
  map {t t'} a := (homOfLE (show (⟨((H.obj t').unop, (G.obj (K.obj t')).unop), le t'⟩ : Pair φ) ≤
      ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩ from
    ⟨leOfHom (H.map a).unop, leOfHom (G.map (K.map a)).unop⟩)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def pairTo {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (G : D ⥤ AffOp X) (H : T ⥤ AffOp X')
    (K : T ⥤ D) (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) :
    CoefMap (RingHom.id R') (OPair φ s') (H ⋙ OAff s') where
  G := pairFun φ G H K le
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

end GlobalTheory.PrimBasis

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

theorem pairTo_pairRes (φ : X' ⟶ X) (s' : X' ⟶ Sp R) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) (c : H2 (ext R₁ (OAff s'))) :
    (extMap R₁ (pairTo φ s' G H K le)).pull2 ((extMap R₁ (pairRes φ s')).pull2 c) =
      (extMap R₁ (CoefMap.restrict (OAff s') H)).pull2 c := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 H) (fun t b ↦ ?_) c
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem pairTo_pairPull {φ : X' ⟶ X} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} (w : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) (c : H2 (ext R₁ (OAff s))) :
    (extMap R₁ (pairTo φ s' G H K le)).pull2 ((extMap R₁ (pairPull w)).pull2 c) =
      (extMap R₁ (pullMap w G H K le)).pull2 ((extMap R₁ (CoefMap.restrict (OAff s) G)).pull2 c) := by
  rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
  refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 (K ⋙ G)) (fun t b ↦ ?_) c
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end GlobalTheory.PrimBasis

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

theorem pairTo_injective (φ : X' ⟶ X) (s' : X' ⟶ Sp R) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1)
    (hr : Function.Surjective (extMap R₁ (pairRes φ s')).pull2)
    (hH : Function.Injective (extMap R₁ (CoefMap.restrict (OAff s') H)).pull2) :
    Function.Injective (extMap R₁ (pairTo φ s' G H K le)).pull2 := by
  intro x y e
  obtain ⟨x, rfl⟩ := hr x
  obtain ⟨y, rfl⟩ := hr y
  rw [pairTo_pairRes, pairTo_pairRes] at e
  rw [hH e]

end GlobalTheory.PrimBasis


open GlobalTheory.PrimBasis in
theorem GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases : PrimitiveExtendedDegTwoVanish → ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] [Quiver.IsThin D] [Quiver.IsThin T] (G : D ⥤ AffOp A.left) (H : T ⥤ AffOp (A ⊗ A).left) (K₀ K₁ K₂ : T ⥤ D) (le₀ : ∀ t, (H.obj t).unop.1 ≤ (μ[A]).left ⁻¹ᵁ (G.obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ (fst A A).left ⁻¹ᵁ (G.obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ (snd A A).left ⁻¹ᵁ (G.obj (K₂.obj t)).unop.1), IsBasis G → IsBasis H → ∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ (G ⋙ OAff A.hom)), (extMap R₁ (pullMap (overW μ[A]) G H K₀ le₀)).pull2 c = (extMap R₁ (pullMap (overW (fst A A)) G H K₁ le₁)).pull2 c + (extMap R₁ (pullMap (overW (snd A A)) G H K₂ le₂)).pull2 c → c = 0 := by
  intro hP R R₁ _ _ _ q hq A _ g hA hg D T _ _ _ _ G H K₀ K₁ K₂ le₀ le₁ le₂ hGb hHb c hc
  have hG := (GlobalTheory.Obs.BasisExt.restrict_ext_bijective R R₁ A.left A.hom D G hGb.cover hGb.dir).2
  have hH := (GlobalTheory.Obs.BasisExt.restrict_ext_bijective R R₁ (A ⊗ A).left (A ⊗ A).hom T H hHb.cover hHb.dir).2
  have hr : ∀ φ : (A ⊗ A).left ⟶ A.left, Function.Bijective (extMap R₁ (pairRes φ (A ⊗ A).hom)).pull2 :=
    fun φ ↦ (_root_.GlobalTheory.Obs.PairExt.pairRes_ext_bijective R R₁ A.left (A ⊗ A).left (A ⊗ A).hom φ).1.2
  obtain ⟨c', rfl⟩ := hG.2 c
  obtain ⟨c₁, hc₁⟩ := (hr (fst A A).left).2 ((extMap R₁ (pairPull (overW (fst A A)))).pull2 c')
  obtain ⟨c₂, hc₂⟩ := (hr (snd A A).left).2 ((extMap R₁ (pairPull (overW (snd A A)))).pull2 c')
  suffices h : c' = 0 by rw [h, map_zero]
  refine hP R R₁ q hq A g hA hg c' c₁ c₂ ?_ hc₁.symm hc₂.symm
  refine pairTo_injective R₁ _ _ G H K₀ le₀ (hr _).2 hH.1 ?_
  rw [pairTo_pairPull, pairTo_pairRes, map_add (f := _), hc, ← pairTo_pairPull R₁ (overW (fst A A)) G H K₁ le₁,
    ← pairTo_pairPull R₁ (overW (snd A A)) G H K₂ le₂, ← hc₁, ← hc₂, pairTo_pairRes, pairTo_pairRes]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveAffineOpenFlatBaseChangeProperStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_injective_affineOpen_flat_baseChange_proper : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → Function.Injective π.appTop.hom → ∀ V : Y.Opens, IsAffineOpen V → Function.Injective (p.app V).hom := by
  first | exact @GlobalTheory.AffInj.app_injective_of_isPullback | exact GlobalTheory.AffInj.app_injective_of_isPullback | (intros; apply GlobalTheory.AffInj.app_injective_of_isPullback <;> assumption)
end

