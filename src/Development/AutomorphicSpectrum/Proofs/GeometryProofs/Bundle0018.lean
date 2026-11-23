module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LatticeSectionAlgebra

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinitePointExtendsSection
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem spec_gamma_isoSpec_inv (S : CommRingCat.{0}) :
    Spec.map (Scheme.ΓSpecIso S).hom ≫ (Spec S).isoSpec.inv = 𝟙 _ := by
  simp [Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

theorem exists_section_of_isFinite (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsFinite f]
    (p : Spec (CommRingCat.of (FractionRing R)) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ s = p := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop
  let φ : Γ(X, ⊤) ⟶ CommRingCat.of (FractionRing R) :=
    p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom
  have hφψ : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    have h1 : f.appTop ≫ p.appTop = (p ≫ f).appTop := by simp
    simp only [ψ, φ, Category.assoc]
    rw [reassoc_of% h1, hp, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have hfin : ψ.hom.Finite := by
    have h2 : f.appTop.hom.Finite := IsFinite.finite_app f ⊤ (isAffineOpen_top _)
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
    simpa [ψ] using RingHom.Finite.comp h2 h3
  have hint : ∀ a : Γ(X, ⊤), ∃ y : R, algebraMap R (FractionRing R) y = φ.hom a := by
    intro a
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    obtain ⟨P, hm, hP⟩ := hfin.to_isIntegral a
    refine ⟨P, hm, ?_⟩
    have h4 : φ.hom.comp ψ.hom = algebraMap R (FractionRing R) := by
      rw [← CommRingCat.hom_comp, hφψ]; rfl
    have := Polynomial.hom_eval₂ P ψ.hom φ.hom a
    rw [hP, map_zero, h4] at this
    exact this.symm
  have hinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  let e : R ≃+* (algebraMap R (FractionRing R)).range :=
    RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let θ₀ : Γ(X, ⊤) →+* R :=
    e.symm.toRingHom.comp (φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a))
  have hθ₀ : ∀ a, algebraMap R (FractionRing R) (θ₀ a) = φ.hom a := by
    intro a
    have h5 : e (θ₀ a) = φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a) a := by
      simp [θ₀]
    exact congrArg Subtype.val h5
  let θ : Γ(X, ⊤) ⟶ CommRingCat.of R := CommRingCat.ofHom θ₀
  have hθφ : θ ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = φ := by
    ext a; exact hθ₀ a
  have hψθ : ψ ≫ θ = 𝟙 _ := by
    ext r
    apply hinj
    have h6 := congrArg (fun g => g.hom r) hφψ
    have h7 := hθ₀ (ψ.hom r)
    exact h7.trans h6
  have hfθ : f.appTop ≫ θ = (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id, ← hψθ]
    simp [ψ]
  refine ⟨Spec.map θ ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, hfθ]
    exact spec_gamma_isoSpec_inv _
  · rw [← Spec.map_comp_assoc, hθφ]
    simp only [φ, Spec.map_comp, Category.assoc]
    rw [Scheme.isoSpec_inv_naturality, reassoc_of% spec_gamma_isoSpec_inv]

theorem exists_section_of_generic_point (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens)
    (hU : IsFinite (U.ι ≫ Γ.G.hom)) (t : T) (ht : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) :
    ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, (∀ z, σ.left z ∈ U) ∧
      toUnit (genPt R) ≫ σ = Γ.pt t := by
  have hr : Set.range (Γ.pt t).left ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ht (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  let p := IsOpenImmersion.lift U.ι (Γ.pt t).left hr
  have hpι : p ≫ U.ι = (Γ.pt t).left := IsOpenImmersion.lift_fac _ _ _
  have hp : p ≫ U.ι ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [reassoc_of% hpι]; exact Over.w (Γ.pt t)
  obtain ⟨s, hs, hsp⟩ := exists_section_of_isFinite R (U.ι ≫ Γ.G.hom) p hp
  refine ⟨Over.homMk (s ≫ U.ι) (by simpa using hs), ?_, ?_⟩
  · intro z
    have h8 : U.ι (s z) ∈ Set.range U.ι := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at h8
    simpa using h8
  · apply Over.OverMorphism.ext
    change (genPt R).hom ≫ s ≫ U.ι = (Γ.pt t).left
    rw [← hpι, ← hsp]
    simp

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAdjoinVarsField
section
namespace GlobalTheory.CompanionTheory.FieldDeg

open ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension

theorem finrank_fraction_over_adjoin_X_eq (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    [FiniteDimensional Ω₀ Ω] (I : Type)
    [Algebra Ω₀ (FractionRing (MvPolynomial I Ω))]
    (hF : algebraMap Ω₀ (FractionRing (MvPolynomial I Ω)) =
      (algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp (algebraMap Ω₀ Ω)) :
    Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
      (FractionRing (MvPolynomial I Ω)) = Module.finrank Ω₀ Ω := by
  classical
  let φ : FractionRing (MvPolynomial I Ω₀) →+* FractionRing (MvPolynomial I Ω) :=
    liftY (L := Ω₀) (E := Ω) (σ := I)
  let : Algebra (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) :=
    φ.toAlgebra
  have hφ : ∀ a : MvPolynomial I Ω₀, φ (algebraMap _ _ a) =
      algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
        (MvPolynomial.map (algebraMap Ω₀ Ω) a) := fun a => by
    simp only [φ, liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  have h1 : Module.finrank (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) =
      Module.finrank Ω₀ Ω := by
    let : Algebra (MvPolynomial I Ω₀) (MvPolynomial I Ω) := MvPolynomial.algebraMvPolynomial
    let b := Module.finBasis Ω₀ Ω
    let j := algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
    let v := fun i => j (MvPolynomial.C (b i))
    let S := Submodule.span (FractionRing (MvPolynomial I Ω₀)) (Set.range v)
    have hsmul (q : MvPolynomial I Ω₀) (p : MvPolynomial I Ω) :
        j (q • p) =
          (algebraMap (MvPolynomial I Ω₀) (FractionRing (MvPolynomial I Ω₀)) q) • j p := by
      rw [Algebra.smul_def, Algebra.smul_def]
      change j (_ * p) = φ (algebraMap _ _ q) * j p
      rw [map_mul, hφ]
      rfl
    have hj (p : MvPolynomial I Ω) : j p ∈ S := by
      rw [ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis.eq_sum_crd b p, map_sum]
      simp only [hsmul]
      exact Submodule.sum_mem S fun i _ => S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    have hli : LinearIndependent (FractionRing (MvPolynomial I Ω₀)) v := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples
        (nonZeroDivisors (MvPolynomial I Ω₀)) Finset.univ g
      choose q hq using fun k => ha k (Finset.mem_univ k)
      have hsum : ∑ k, q k • (MvPolynomial.C (b k) : MvPolynomial I Ω) = 0 := by
        apply IsFractionRing.injective (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
        change j (∑ k, q k • MvPolynomial.C (b k)) = j 0
        rw [map_sum, map_zero]
        simp only [hsmul]
        change ∑ k, (algebraMap (MvPolynomial I Ω₀) (FractionRing (MvPolynomial I Ω₀)) (q k)) •
          v k = 0
        simp_rw [hq, Algebra.smul_def (a : MvPolynomial I Ω₀), mul_smul, ← Finset.smul_sum,
          hg, smul_zero]
      have hqi := (Fintype.linearIndependent_iff.mp
        (ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis.linearIndependent_C
          (σ := I) b)) q hsum i
      have hzero : (a : MvPolynomial I Ω₀) • g i = 0 := by
        rw [← hq i, hqi, map_zero]
      rw [Algebra.smul_def] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2)
    have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
      intro x hx y hy
      have hxy := Submodule.mul_mem_mul hx hy
      change x * y ∈ Submodule.span _ (Set.range v) * Submodule.span _ (Set.range v) at hxy
      rw [Submodule.span_mul_span] at hxy
      refine (Submodule.span_le.mpr ?_) hxy
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
      change j _ * j _ ∈ S
      rw [← map_mul]
      exact hj _
    have hone : 1 ∈ S := by simpa using hj 1
    let A := S.toSubalgebra hone fun x y hx hy => hmul x hx y hy
    have hfg : A.toSubmodule.FG := by
      rw [Submodule.toSubalgebra_toSubmodule]
      exact Submodule.fg_span (Set.finite_range v)
    have htop : ⊤ ≤ S := by
      intro x _
      obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial I Ω) x
      have hint := IsIntegral.of_mem_of_fg _ hfg (j q) (hj q)
      have hinv := A.inv_mem_of_algebraic (x := ⟨j q, hj q⟩) hint.isAlgebraic
      rw [div_eq_mul_inv]
      exact hmul _ (hj p) _ hinv
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli htop)]
    simp
  let K := IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
    algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q))
  have hpoly : ∀ a : MvPolynomial I Ω₀, algebraMap (MvPolynomial I Ω)
      (FractionRing (MvPolynomial I Ω)) (MvPolynomial.map (algebraMap Ω₀ Ω) a) ∈ K := fun a => by
    induction a using MvPolynomial.induction_on with
    | C r =>
      have := K.algebraMap_mem r
      rw [hF] at this
      simpa [MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))] using this
    | add p q hp hq => simpa using K.add_mem hp hq
    | mul_X p i hp =>
      have hX : algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X i) ∈ K :=
        IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
      simpa using K.mul_mem hp hX
  have hmem : ∀ x, φ x ∈ K := fun x => by
    obtain ⟨a, c, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I Ω₀) x
    rw [map_div₀, hφ, hφ]
    exact K.div_mem (hpoly a) (hpoly c)
  have hle : K ≤ Subfield.toIntermediateField φ.fieldRange (fun r => by
      refine ⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.C r), ?_⟩
      rw [hφ, hF]
      simp [MvPolynomial.map_C, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    refine ⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.X q), ?_⟩
    rw [hφ]; simp
  let ψ : FractionRing (MvPolynomial I Ω₀) →+* K := φ.codRestrict K hmem
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y h => φ.injective (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hle y.2
    exact ⟨x, Subtype.ext hx⟩
  rw [← h1]
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective ψ hψ) (RingEquiv.refl _)
    (by ext x; rfl)).symm

theorem finrank_adjoin_vars :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (I : Type) (d : ℕ),
      0 < d →
      (letI : Algebra Ω₀ Ω := fn.toAlgebra;
       Module.finrank Ω₀ Ω = d) →
      letI : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
        ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra;
      Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
        (FractionRing (MvPolynomial I Ω)) = d := by
  intro Ω₀ Ω _ _ fn I d hd hfin
  let : Algebra Ω₀ Ω := fn.toAlgebra
  have : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  let : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
    ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
  exact (finrank_fraction_over_adjoin_X_eq Ω₀ Ω I rfl).trans hfin

end GlobalTheory.CompanionTheory.FieldDeg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubBaseChange
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.PullSub

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {R' : Type} [CommRing R'] [IsDomain R'] (Γ' : QFGroup R' T) (φ : R →+* R')
  (F : Γ'.G.left ⟶ Γ.G.left)

def pushPt (hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G :=
  Over.homMk (x.left ≫ F) (by
    have hx : x.left ≫ Γ'.G.hom = S.hom := Over.w x
    simp only [Over.mk_hom, Category.assoc, hw]
    rw [← Category.assoc, hx])

variable {Γ Γ' φ F}

theorem pushPt_left (hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    (pushPt Γ Γ' φ F hw x).left = x.left ≫ F := rfl

theorem pushPt_mul (h : Γ'.IsBaseChange Γ φ F)
    {S : Over (Spec (CommRingCat.of R'))} (x y : S ⟶ Γ'.G) :
    pushPt Γ Γ' φ F h.cart.w (x * y) = pushPt Γ Γ' φ F h.cart.w x * pushPt Γ Γ' φ F h.cart.w y := by
  apply Over.OverMorphism.ext
  rw [pushPt_left]
  exact (h.mul S x y _ _ (pushPt_left h.cart.w x) (pushPt_left h.cart.w y)).symm

theorem pushPt_one (h : Γ'.IsBaseChange Γ φ F) (S : Over (Spec (CommRingCat.of R'))) :
    pushPt Γ Γ' φ F h.cart.w (1 : S ⟶ Γ'.G) = 1 := by
  have h1 := pushPt_mul h (1 : S ⟶ Γ'.G) 1
  rw [_root_.mul_one] at h1
  exact _root_.mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)

theorem pushPt_inv (h : Γ'.IsBaseChange Γ φ F)
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    pushPt Γ Γ' φ F h.cart.w x⁻¹ = (pushPt Γ Γ' φ F h.cart.w x)⁻¹ := by
  have h2 := pushPt_mul h x⁻¹ x
  rw [_root_.inv_mul_cancel, pushPt_one h S] at h2
  exact eq_inv_of_mul_eq_one_left h2.symm

end GlobalTheory.CompanionTheory.Ar.BT.PullSub

open GlobalTheory.CompanionTheory.Ar.BT.PullSub

open GlobalTheory.CompanionTheory.Ar.BT.PullSub in
theorem GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ U : Γ.G.left.Opens, Γ.IsFinOpenSub U → Γ'.IsFinOpenSub (F ⁻¹ᵁ U) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F h U hU
  have hpb := (isPullback_morphismRestrict F U).paste_vert h.cart
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) hpb hU.finite, ?_, ?_, ?_⟩
  · intro x
    have e1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G) = MonObj.one := by
      change SemiCartesianMonoidalCategory.toUnit _ ≫ MonObj.one = MonObj.one
      rw [SemiCartesianMonoidalCategory.toUnit_unique (SemiCartesianMonoidalCategory.toUnit _) (𝟙 _),
        Category.id_comp]
    have e2 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G).left ≫ F =
        (1 : Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R'))) ⟶ Γ.G).left := by
      rw [← pushPt_left h.cart.w, pushPt_one h]
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← e1, e2]
    change (Over.Hom.left (SemiCartesianMonoidalCategory.toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (MonObj.one : 𝟙_ _ ⟶ Γ.G))) x ∈ U
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hU.one _
  · intro S x y hx hy z
    have hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hx w)
    have hy' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w y).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hy w)
    have hxy := hU.mul _ _ _ hx' hy' z
    rw [← pushPt_mul h, pushPt_left, Scheme.Hom.comp_apply] at hxy
    exact (Scheme.Hom.mem_preimage F).mpr hxy
  · intro S x hx z
    have hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hx w)
    have hxi := hU.inv _ _ hx' z
    rw [← pushPt_inv h, pushPt_left, Scheme.Hom.comp_apply] at hxi
    exact (Scheme.Hom.mem_preimage F).mpr hxi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ValHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

def stalkEquiv {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩

theorem stalkEquiv_coe {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    ((stalkEquiv ξ hξ p s : regAt ξ p) : Ω) = genMap ξ p s := rfl

theorem isUnit_iff_unitAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · intro hs
    obtain ⟨u, rfl⟩ := hs
    refine ⟨((u.isUnit).map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : _ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  · rintro ⟨h0, -, ⟨t, ht⟩⟩
    refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
    rw [map_mul, map_one, ht, mul_inv_cancel₀ h0]

theorem exists_valAt_hom (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) (hξ : IsCptGen ξ) :
    ∃ φ : regAt ξ ⟨centre z, h⟩ →+* R,
      (∀ (a : Ω) (r : R), ValAt ξ z a r ↔ ∃ ha : a ∈ regAt ξ ⟨centre z, h⟩, φ ⟨a, ha⟩ = r) ∧
      ∀ a : regAt ξ ⟨centre z, h⟩, IsUnit (φ a) ↔ unitAt ξ ⟨centre z, h⟩ (a : Ω) := by
  let p : Cpt ξ := ⟨centre z, h⟩
  let e := stalkEquiv ξ hξ p
  let v : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  have hv : IsLocalHom v := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have key : ∀ s, e.symm (e s) = s := e.symm_apply_apply
  refine ⟨v.comp (e.symm : regAt ξ p →+* X.presheaf.stalk p.1), ?_, ?_⟩
  · intro a r
    constructor
    · rintro ⟨h', s, hs, hr⟩
      have hs' : genMap ξ p s = a := hs
      refine ⟨⟨s, hs'⟩, ?_⟩
      have : (⟨a, ⟨s, hs'⟩⟩ : regAt ξ p) = e s := Subtype.ext hs'.symm
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [this, key]
      exact hr
    · rintro ⟨ha, hr⟩
      refine ⟨h, e.symm ⟨a, ha⟩, ?_, hr⟩
      have := stalkEquiv_coe ξ hξ p (e.symm ⟨a, ha⟩)
      rw [RingEquiv.apply_symm_apply] at this
      exact this.symm
  · intro a
    obtain ⟨s, rfl⟩ := e.surjective a
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [key]
    have : IsUnit (v s) ↔ IsUnit s := isUnit_map_iff v s
    exact this.trans (isUnit_iff_unitAt ξ hξ p s)

end GlobalTheory.CompanionTheory.Ar.ValHom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitNatCastStalk
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem isUnit_natCast_stalk (X : Scheme.{0}) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ X) (n : ℕ) (hn : n ≠ 0) :
    IsUnit ((n : X.presheaf.stalk (centre z))) := by
  set x := IsLocalRing.closedPoint L
  have hL : IsUnit (n : L) := (Nat.cast_ne_zero.mpr hn).isUnit
  let φ : L →+* (Sp L).presheaf.stalk x :=
    ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (Sp L).presheaf.germ ⊤ x trivial).hom
  have h2 : IsUnit (n : (Sp L).presheaf.stalk x) := by
    simpa using hL.map φ
  have h3 : IsUnit ((z.stalkMap x).hom (n : X.presheaf.stalk (z x))) := by
    simpa using h2
  haveI : IsLocalHom (z.stalkMap x).hom := z.prop x
  exact (isUnit_map_iff (z.stalkMap x).hom _).mp h3

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankTranscendenceDegree
section
namespace GlobalTheory.CompanionTheory.Kaehler

theorem finrank_kaehlerDifferential_of_adjoin_eq_top (K L : Type) [Field K] [Field L] [Algebra K L]
    (I : Type) [Fintype I] (u : I → L) (hu : AlgebraicIndependent K u)
    (hadj : IntermediateField.adjoin K (Set.range u) = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  classical
  letI : Algebra (MvPolynomial I K) L := (MvPolynomial.aeval u).toRingHom.toAlgebra
  have hmap : ∀ q : MvPolynomial I K, algebraMap (MvPolynomial I K) L q = MvPolynomial.aeval u q :=
    fun _ => rfl
  have : IsScalarTower K (MvPolynomial I K) L :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [hmap, AlgHom.commutes]
  have : FaithfulSMul (MvPolynomial I K) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hu
  have : IsFractionRing (MvPolynomial I K) L := IsFractionRing.of_field (MvPolynomial I K) L fun z => by
    have hz : z ∈ IntermediateField.adjoin K (Set.range u) := by rw [hadj]; trivial
    obtain ⟨r, s, h⟩ := (IntermediateField.mem_adjoin_range_iff K u z).1 hz
    exact ⟨r, s, h⟩
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors (MvPolynomial I K))
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale K (MvPolynomial I K) L
  rw [Module.finrank_eq_card_basis (hbc.basis (KaehlerDifferential.mvPolynomialBasis K I))]

end GlobalTheory.CompanionTheory.Kaehler
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLatticeLocalFree
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.SecAlg

theorem locFree_and_extend : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type) (reg : Q → Subring Ω) (r : ℕ) (Λ : Q → AddSubgroup (Fin r → Ω)), (∀ q, IsLocalRing (reg q)) → (∀ q, ∀ a ∈ R, a ∈ reg q) → (∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q)) → (∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R) → (∀ q, ∃ g ∈ R, g ≠ 0 ∧ g⁻¹ ∈ reg q ∧ ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q', g⁻¹ ∈ reg q' → ∀ e, e ∈ Λ q' ↔ ∃ a : Fin r → Ω, (∀ i, a i ∈ reg q') ∧ e = ∑ i, a i • f i) → LocFree R r (⨅ q, Λ q) ∧ ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) → ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q :=
  @PositivityTheory.Xgn.lattice_section_algebra

end GlobalTheory.CompanionTheory.Ar.Num.SecAlg
end

