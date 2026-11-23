module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Formalism.PairingDivisors.StatementN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAbelianSchemeAlongSquareZeroFactorization
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem corr_crysToDR_step_iff {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I : Ideal R}
    {I₁ : Ideal R₁} {κ : DividedPowers I} {κ₁ : DividedPowers I₁} {π : R →+* R₀} {ρ : R →+* R₁}
    {π₁ : R₁ →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {X₁ : Over (Sp R₁)} [GrpObj X₁] {X : Over (Sp R)}
    [GrpObj X] {i₁ : A₀.left ⟶ X₁.left} {i₂ : X₁.left ⟶ X.left} {i : A₀.left ⟶ X.left}
    (h₁ : IsGrpPullback A₀ X₁ (spMap π₁) i₁) (h₂ : IsGrpPullback X₁ X (spMap ρ) i₂)
    (h : IsGrpPullback A₀ X (spMap π) i) (e : i₁ ≫ i₂ = i)
    (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _))
    (hs : Function.Surjective (liftMor κ h).pull) (d : Crys κ (spMap π) A₀) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
  have k : GrpMor (dp0 R) (𝟙 _) X κ₁ (spMap π₁) A₀
      (ρ.comp (RingHom.id R)) ((𝟙 _) ≫ spMap π) ((𝟙 _) ≫ i) := by
    apply GrpMor.of_isGrpPullback
    · exact IsDPMorphism.comp _ M.dp (liftMor κ h).dp
    · simpa using M.base
    · simpa using h
  have e1 : ∀ c, (liftMor κ₁ h₁).pull ((redMor h₂).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) (by rw [Category.id_comp, e]) c
  have e2 : ∀ c, M.pull ((liftMor κ h).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c
  constructor
  · intro H c
    obtain ⟨c, rfl⟩ := hs c
    have := H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2] at this
    exact this
  · intro H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2]
    exact H _

theorem liftObj_step : AbelianDeRham → AbelianUnobstructed → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁]
    [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftObj (divided₂ hJ) ρ → LiftObj κ₁ π₁ → LiftObj κ π := by
  intro P U R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ S L₂ L₁
  intro g A₀ _ A' _ i' h' hA' hg F hF
  have hπ : Function.Surjective π := S.comp ▸ S.surj₁.comp S.surj
  have hrig := P.2.2.2.1
  have hsp : spMap π = spMap π₁ ≫ spMap ρ := by rw [← S.comp, Cris.spMap_comp]
  have M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) := by
    refine ⟨S.dp, ?_, ?_, ?_⟩
    · simpa using hsp
    · simp
    · intro T x y x₀ y₀ hx hy
      have mul_left {U : Over (Sp R₀)} (a b : U ⟶ A₀) :
          (a * b).left = CategoryTheory.Limits.pullback.lift a.left b.left ((Over.w a).trans (Over.w b).symm) ≫ μ[A₀].left := by
        rw [Hom.mul_def, Over.comp_left, Over.lift_left]
      rw [mul_left, mul_left]
      congr 1
      apply CategoryTheory.Limits.pullback.hom_ext
      · simpa using hx
      · simpa using hy

  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, e₁₂, hA₁, hg₁⟩ :=
    _root_.GlobalTheory.SqLift.exists_intermediate_grpPullback R R₁ R₀ ρ π₁ g A₀ A' i' (by rw [S.comp]; exact h') hA' hg
  obtain ⟨F₁, hF₁, hF₁F⟩ :=
    _root_.GlobalTheory.SqLift.isAdmissible_reduce P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ A₁ A' i₁ i₂ i' h₁ h₂ h' e₁₂ hA' hg F hF

  obtain ⟨B₁, _, j₁, k₁, hB₁, hgB₁, hfB₁⟩ := L₁ g A₀ A₁ i₁ h₁ hA₁ hg₁ F₁ hF₁
  obtain ⟨C, _, j₂, k₂, hC⟩ := U R J hJ R₁ ρ S.surj S.kerJ B₁ hB₁
  have hgC : SmoothOfRelativeDimension g C.hom :=
    _root_.GlobalTheory.LiftDim.smoothOfRelativeDimension_of_reduction R R₁ ρ S.surj (by rw [S.kerJ]; exact ⟨2, hJ⟩) g C B₁ j₂ k₂.1 hC.smooth hgB₁
  have kC : IsGrpPullback A₀ C (spMap π) (j₁ ≫ j₂) := (k₁.comp k₂).congr hsp.symm rfl
  have b' : Function.Bijective (crysToDR κ h') :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hA' hg S.nil hπ S.ker h'
  have bC : Function.Bijective (crysToDR κ kC) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hC hgC S.nil hπ S.ker kC
  have bB₁ : Function.Bijective (crysToDR κ₁ k₁) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hB₁ hgB₁ S.nil₁ S.surj₁ S.ker₁ k₁
  have s' := (hrig R A' g hA' hg I κ S.nil R₀ π hπ S.ker A₀ i' h').2
  have sC := (hrig R C g hC hgC I κ S.nil R₀ π hπ S.ker A₀ _ kC).2

  set E := F.comap (crysToDR κ h') with hE
  set FC := E.map (crysToDR κ kC) with hFC
  have hFCa : IsAdmissible k₂ FC := by
    obtain ⟨N, hN⟩ := hF.1
    refine ⟨⟨(N.comap (crysToDR κ h')).map (crysToDR κ kC), ?_⟩, fun y ↦ ?_⟩
    · exact (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ bC)).isCompl
        ((Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ b')).symm.isCompl hN)
    obtain ⟨d₁, rfl⟩ := bB₁.2 y
    have l1 : crysToDR κ₁ k₁ d₁ ∈ Fil B₁ ↔ ∃ d ∈ E, M.Corr d d₁ := by
      change d₁ ∈ liftFil κ₁ k₁ ↔ _
      rw [hfB₁, Submodule.mem_comap, hF₁F]
      constructor
      · rintro ⟨x, hx, ex⟩
        obtain ⟨d, rfl⟩ := b'.2 x
        exact ⟨d, hx, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).1 ex⟩
      · rintro ⟨d, hd, ed⟩
        exact ⟨_, hd, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).2 ed⟩
    rw [l1]
    constructor
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).2 ed⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, ex⟩
      exact ⟨d, hd, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).1 ex⟩

  obtain ⟨A, _, j₃, k₃, hA, hgA, hfA⟩ := L₂ g B₁ C j₂ k₂ hC hgC FC hFCa
  have kA : IsGrpPullback A₀ A (spMap π) (j₁ ≫ j₃) := (k₁.comp k₃).congr hsp.symm rfl
  refine ⟨A, inferInstance, j₁ ≫ j₃, kA, hA, hgA, ?_⟩
  obtain ⟨N, -, hNC⟩ :=
    _root_.GlobalTheory.SqLift.crys_two_reductions P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ C j₁ j₂ (j₁ ≫ j₂) k₁ k₂ kC rfl hC hgC
  obtain ⟨N', -, hNA⟩ :=
    _root_.GlobalTheory.SqLift.crys_two_reductions P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ A j₁ j₃ (j₁ ≫ j₃) k₁ k₃ kA rfl hA hgA
  obtain rfl : N' = N := rfl
  ext d
  change crysToDR κ kA d ∈ Fil A ↔ d ∈ E
  rw [hNA d]
  change _ ∈ liftFil (divided₂ hJ) k₃ ↔ _
  rw [hfA, Submodule.mem_comap, ← hNC d]
  exact ⟨fun ⟨d', hd', e⟩ ↦ bC.1 e ▸ hd', fun hd ↦ ⟨d, hd, rfl⟩⟩

end GlobalTheory.SqLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfIsStep
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

section Step

variable {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I J : Ideal R} {I₁ : Ideal R₁}
  {κ : DividedPowers I} {π : R →+* R₀} {hJ : J ^ 2 = 0} {ρ : R →+* R₁} {κ₁ : DividedPowers I₁}
  {π₁ : R₁ →+* R₀}

theorem IsStep.spMap_eq (st : IsStep κ π hJ ρ κ₁ π₁) : spMap π = spMap π₁ ≫ spMap ρ := by
  rw [← st.comp, Cris.spMap_comp]

theorem IsStep.idMor (st : IsStep κ π hJ ρ κ₁ π₁) (A₀ : Over (Sp R₀)) [GrpObj A₀] :
    GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) :=
  ⟨st.dp, by simpa using st.spMap_eq, by simp, by
    intro T x y x₀ y₀ hx hy
    have ex : x₀ = x := Over.OverMorphism.ext (by simpa using hx)
    have ey : y₀ = y := Over.OverMorphism.ext (by simpa using hy)
    subst x₀; subst y₀
    exact Category.comp_id _ |>.symm⟩

def redSub (hρ : Function.Surjective ρ) {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A]
    {i₂ : A₁.left ⟶ A.left} (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (F : Submodule R (HdR A)) :
    Submodule R₁ (HdR A₁) where
  carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
  add_mem' := by
    rintro y y' ⟨x, hx, e⟩ ⟨x', hx', e'⟩
    exact ⟨x + x', F.add_mem hx hx', fun c ↦ by
      rw [LinearMap.add_apply, LinearMap.add_apply, e, e', map_add (f := _)]⟩
  zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
  smul_mem' := by
    rintro r₁ y ⟨x, hx, e⟩
    obtain ⟨r, rfl⟩ := hρ r₁
    exact ⟨r • x, F.smul_mem r hx, fun c ↦ by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, e, map_mul]⟩

theorem mem_liftFil_iff (P : AbelianDeRham) (st : IsStep κ π hJ ρ κ₁ π₁) {g : ℕ} {A₀ : Over (Sp R₀)}
    [GrpObj A₀] {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A] {i₁ : A₀.left ⟶ A₁.left}
    {i₂ : A₁.left ⟶ A.left} {i : A₀.left ⟶ A.left} (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁)
    (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i) (ei : i₁ ≫ i₂ = i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    d₁ ∈ liftFil κ₁ h₁ ↔ ∃ d ∈ liftFil κ h, (st.idMor A₀).Corr d d₁ := by
  have T := _root_.GlobalTheory.FilRed.filtration_reduction P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
    (st.idMor A₀) (Fil A) (redSub st.surj h₂ (Fil A)) (fun _ ↦ Iff.rfl)
  have e : Fil A₁ = redSub st.surj h₂ (Fil A) := Submodule.ext T.2
  rw [liftFil, Submodule.mem_comap, e, T.1 d₁]
  exact Iff.rfl

theorem dualMap_push {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀] {A₁ B₁ : Over (Sp R₁)} [GrpObj A₁]
    [GrpObj B₁] {i₁ : A₀.left ⟶ A₁.left} {j₁ : B₀.left ⟶ B₁.left}
    (NA : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁)
    (NB : GrpMor (divided₂ hJ) (spMap ρ) B₁ κ (spMap π) B₀ (RingHom.id R) (spMap π₁) j₁)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) [IsMonHom f₀] [IsMonHom f₁] (e : i₁ ≫ f₁.left = f₀.left ≫ j₁)
    (d : Crys κ (spMap π) A₀) :
    (NB.pull : prim (divided₂ hJ) (spMap ρ) B₁ →ₗ[R] prim κ (spMap π) B₀).dualMap (push κ (spMap π) f₀ d) =
      push (divided₂ hJ) (spMap ρ) f₁
        ((NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  refine LinearMap.ext fun c ↦ ?_
  let m : GrpMor (divided₂ hJ) (spMap ρ) B₁ κ (spMap π) A₀
      (RingHom.id R) (spMap π₁ ≫ 𝟙 _) (i₁ ≫ f₁.left) := by
    refine ⟨NA.dp, ?_, ?_, ?_⟩
    · simpa using NA.base
    · simpa only [Category.comp_id, Category.assoc, Over.w f₁] using NA.w
    · intro T x y x₀ y₀ hx hy
      let x₁ : Over.mk (T.hom ≫ spMap π₁) ⟶ A₁ :=
        Over.homMk (x.left ≫ i₁) (by simp only [Over.mk_hom, Category.assoc, NA.w, reassoc_of% (Over.w x)])
      let y₁ : Over.mk (T.hom ≫ spMap π₁) ⟶ A₁ :=
        Over.homMk (y.left ≫ i₁) (by simp only [Over.mk_hom, Category.assoc, NA.w, reassoc_of% (Over.w y)])
      let x₂ : Over.mk ((Over.mk (T.hom ≫ spMap π₁)).hom ≫ 𝟙 _) ⟶ B₁ :=
        Over.homMk x₀.left (by simpa using Over.w x₀)
      let y₂ : Over.mk ((Over.mk (T.hom ≫ spMap π₁)).hom ≫ 𝟙 _) ⟶ B₁ :=
        Over.homMk y₀.left (by simpa using Over.w y₀)
      have h₁ := NA.mul T x y x₁ y₁ rfl rfl
      have h₂ := (homMor (divided₂ hJ) (spMap ρ) f₁).mul _ x₁ y₁ x₂ y₂
        (by simpa [x₂, x₁, Category.assoc] using hx)
        (by simpa [y₂, y₁, Category.assoc] using hy)
      have h₃ : (x₀ * y₀).left = (x₂ * y₂).left := by
        simp [Hom.mul_def, Over.comp_left, Over.lift_left, x₂, y₂]
      rw [h₃, h₂, h₁, Category.assoc]
  have e1 : (homMor κ (spMap π) f₀).pull (NB.pull c) = m.pull c :=
    GrpMor.pull_pull NB (homMor κ (spMap π) f₀) m (fun _ ↦ rfl) e.symm c
  have e2 : NA.pull ((homMor (divided₂ hJ) (spMap ρ) f₁).pull c) = m.pull c :=
    GrpMor.pull_pull (homMor (divided₂ hJ) (spMap ρ) f₁) NA m (fun _ ↦ rfl) rfl c
  exact congrArg d (e1.trans e2.symm)

end Step

theorem liftHom_of_isStep : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftHom (divided₂ hJ) ρ → LiftHom κ₁ π₁ → LiftHom κ π := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ st H₂ H₁
  intro g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have hc : spMap (π₁.comp ρ) = spMap π := by rw [st.comp]
  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, ei, hA₁, hgA⟩ :=
    _root_.GlobalTheory.SqLift.exists_intermediate_grpPullback R R₁ R₀ ρ π₁ g A₀ A i (by rw [hc]; exact h) hA hg
  obtain ⟨B₁, _, j₁, j₂, k₁, k₂, ej, hB₁, hgB⟩ :=
    _root_.GlobalTheory.SqLift.exists_intermediate_grpPullback R R₁ R₀ ρ π₁ g' B₀ B j (by rw [hc]; exact k) hB hg'

  have hf₁ : ∀ d₁ ∈ liftFil κ₁ h₁, push κ₁ (spMap π₁) f₀ d₁ ∈ liftFil κ₁ k₁ := by
    intro d₁ hd₁
    obtain ⟨d, hd, e⟩ := (mem_liftFil_iff P st h₁ h₂ h ei hA hg d₁).1 hd₁
    exact (mem_liftFil_iff P st k₁ k₂ k ej hB hg' _).2
      ⟨_, hf d hd, GrpMor.Corr.push (st.idMor B₀) f₀ f₀ (by simp) e⟩
  obtain ⟨f₁, ⟨_, ef₁⟩, uf₁⟩ := H₁ g A₀ A₁ i₁ h₁ hA₁ hgA g' B₀ B₁ j₁ k₁ hB₁ hgB f₀ hf₁

  obtain ⟨NA, bA, cA⟩ := _root_.GlobalTheory.SqLift.crys_two_reductions P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
  obtain ⟨NB, -, cB⟩ := _root_.GlobalTheory.SqLift.crys_two_reductions P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g' B₀ B₁ B j₁ j₂ j k₁ k₂ k ej hB hg'
  have sA : Function.Surjective
      (NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap :=
    (LinearEquiv.ofBijective _ bA).dualMap.surjective
  have hf₂ : ∀ e ∈ liftFil (divided₂ hJ) h₂, push (divided₂ hJ) (spMap ρ) f₁ e ∈ liftFil (divided₂ hJ) k₂ := by
    intro e he
    obtain ⟨d, rfl⟩ := sA e
    have hd : d ∈ liftFil κ h := by
      rw [liftFil, Submodule.mem_comap, cA]; exact he
    have hk := hf d hd
    rw [liftFil, Submodule.mem_comap, cB] at hk
    rw [liftFil, Submodule.mem_comap, ← dualMap_push NA NB f₀ f₁ ef₁ d]
    exact hk
  obtain ⟨f, ⟨_, ef⟩, uf⟩ := H₂ g A₁ A i₂ h₂ hA hg g' B₁ B j₂ k₂ hB hg' f₁ hf₂
  refine ⟨f, ⟨inferInstance, ?_⟩, ?_⟩
  · rw [← ei, ← ej, Category.assoc, ef, ← Category.assoc, ef₁, Category.assoc]
  · rintro f' ⟨_, ef'⟩
    let f₁' : A₁ ⟶ B₁ := Over.homMk (k₂.1.lift (i₂ ≫ f'.left) A₁.hom
      (by rw [Category.assoc, Over.w f', h₂.1.w])) (k₂.1.lift_snd _ _ _)
    have e₁ : f₁'.left ≫ j₂ = i₂ ≫ f'.left := k₂.1.lift_fst _ _ _
    haveI := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback h₂ k₂ f' f₁' e₁
    have e₂ : i₁ ≫ f₁'.left = f₀.left ≫ j₁ := by
      refine k₂.1.hom_ext ?_ ?_
      · rw [Category.assoc, e₁, ← Category.assoc, ei, ef', Category.assoc, ej]
      · rw [Category.assoc, Category.assoc, Over.w f₁', h₁.1.w, k₁.1.w, ← Category.assoc, Over.w f₀]
    have e₃ : f₁' = f₁ := uf₁ f₁' ⟨inferInstance, e₂⟩
    exact uf f' ⟨inferInstance, by rw [← e₁, e₃]⟩

end GlobalTheory.SqLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDel
section
noncomputable section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom

theorem eulerStep {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)) (hmax : 𝔭.IsMaximal) (hp : 𝔭 ≠ ⊥) (hcop : 𝔭 ⊔ 𝔪 = ⊤)
    (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ) (hZ : IsRayL 𝔪 (wideInd C) Z) (hZ' : IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z') :
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) :=
  GlobalTheory.T.isNarrowRayClassLFunction_mul_prime_wideIndicator 𝔪 𝔭 hmax hp hcop C Z Z' hZ hZ'

theorem isRayL_top_iff {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) :
    IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z :=
  _root_.GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff C Z

theorem primesOver_exists {F : Type} [Field F] [NumberField F] (l : ℕ) (hl : l.Prime) :
    ∃ P : Finset (Ideal (𝓞 F)), (∀ 𝔭 ∈ P, 𝔭.IsMaximal ∧ 𝔭 ≠ ⊥ ∧ l ∣ Ideal.absNorm 𝔭) ∧
      ∀ I : Ideal (𝓞 F), CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔ CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I :=
  _root_.GlobalTheory.PrimesOverL.primes_over_l l hl

theorem inZl_of_shift {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime] (g : G) (q : ℕ) (hq : l ∣ q)
    (x : G → ℚ) (h : ∀ C, InZl l (x C - (q : ℚ) * x (C * g))) (C : G) : InZl l (x C) :=
  GlobalTheory.T.isRatInPadicIntegers_of_twisted_difference l g q hq x h C

theorem cE_le_of_inZl {F : Type} [Field F] [NumberField F] (z : ClassGroup (𝓞 F) → ℚ) (l a n : ℕ) [Fact l.Prime]
    (ha : 2 ≤ a) (hn : 1 ≤ n) (h : ∀ C, InZl l (((a ^ n - 1 : ℕ) : ℚ) * z C)) :
    cE z l ≤ finrank ℚ F * padicValNat l 2 + padicValNat l (a ^ n - 1) :=
  _root_.GlobalTheory.DenomBound.cE_le_of_inZl z l a n ha hn h

theorem mMin_eq_mE (hmin : Formalism.PairingDivisionLocalBalance.MinVal) (l n : ℕ) (hl : l.Prime) (hn : 2 ≤ n) (he : Even n) :
    mMin l n = Formalism.PairingDivisionLocalBalance.mE l n :=
  _root_.GlobalTheory.MinValClosed.mMin_eq_mE hmin l n hl hn he

theorem sumBound_of_local {F : Type} [Field F] [NumberField F] (hsum : Formalism.PairingDivisionLocalBalance.CESum) (k : ℕ)
    (z : ClassGroup (𝓞 F) → ℚ) (hk : 2 ≤ k) (h16 : 16 ≤ finrank ℚ F * k)
    (h : ∀ l : ℕ, l.Prime → cE z l ≤ finrank ℚ F * padicValNat l 2 + Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k)) : SumBound k z :=
  _root_.GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds.sumBound_of_local hsum k z hk h16 h

theorem isRayL_of_coprime_iff {F : Type} [Field F] [NumberField F] {𝔣 𝔤 : Ideal (𝓞 F)}
    (h : ∀ I, CoprimeTo F 𝔣 I ↔ CoprimeTo F 𝔤 I) {ε : Ideal (𝓞 F) → ℚ} {L : ℂ → ℂ} (hL : IsRayL 𝔣 ε L) : IsRayL 𝔤 ε L :=
  ⟨hL.1, fun s hs => (Equiv.subtypeEquivRight fun I => (h I).symm).hasSum_iff
    (f := fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} => (ε I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) |>.2 (hL.2 s hs)⟩

theorem exists_isZetaValues (h : GlobalTheory.Published.SiegelKlingen) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ)
    (hk : 1 ≤ k) : ∃ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z := by
  have : ∀ C : ClassGroup (𝓞 F), ∃ r : ℚ, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (r : ℂ) := by
    intro C
    obtain ⟨L, hL, hv⟩ := h F ⊤ top_ne_bot (wideInd C) (isRayFun_wideInd _ C)
    obtain ⟨r, hr⟩ := hv k hk
    exact ⟨r, L, (isRayL_top_iff C L).1 hL, hr⟩
  choose z hz using this
  exact ⟨z, hz⟩

theorem inZl_mul_zeta (h : GlobalTheory.Published.DeligneRibet) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (l : ℕ) [hl : Fact l.Prime] (a k : ℕ) (ha : 2 ≤ a) (hac : a.Coprime l) (hk : 2 ≤ k)
    (z : ClassGroup (𝓞 F) → ℚ) (hz : IsZetaValues k z) (C : ClassGroup (𝓞 F)) :
    InZl l (((a ^ (finrank ℚ F * k) - 1 : ℕ) : ℚ) * z C) := by
  classical
  obtain ⟨P, hP, hPc⟩ := primesOver_exists (F := F) l hl.out
  set c : ℚ := ((a ^ (finrank ℚ F * k) - 1 : ℕ) : ℚ) with hcdef
  let St : Finset (Ideal (𝓞 F)) → Prop := fun T => ∀ x : ClassGroup (𝓞 F) → ℚ,
    (∀ C, ∃ Z : ℂ → ℂ, IsRayL (∏ 𝔭 ∈ T, 𝔭) (wideInd C) Z ∧ Z (1 - (k : ℂ)) = (x C : ℂ)) → ∀ C, InZl l (c * x C)

  have hfull : St P := by
    intro x hx C
    obtain ⟨Z, hZ, e⟩ := hx C
    have hZ1 : IsRayL (powMod F l 1) (wideInd C) Z :=
      isRayL_of_coprime_iff (fun I => by rw [hPc, coprimeTo_powMod_iff le_rfl]) hZ
    have ha0 : (a : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hcop : CoprimeTo F (powMod F l 1) (Ideal.span {(a : 𝓞 F)}) := by
      rw [coprimeTo_powMod_iff le_rfl]
      refine ⟨by simpa using ha0, ?_⟩
      rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
      simpa using (Nat.isCoprime_iff_coprime.2 hac).map (Int.castRingHom (𝓞 F))
    have hv : IsRayValue (powMod F l 1) (wideInd C) k (x C) := ⟨Z, hZ1, e⟩
    have hv' : IsRayValue (powMod F l 1) (translate (Ideal.span {(a : 𝓞 F)}) (wideInd C)) k (x C) := by
      rw [translate_wideInd ha0]; exact hv
    have hint : ∀ I, CoprimeTo F (powMod F l 1) I → InZl l (wideInd C I) := fun I _ => by
      unfold wideInd; split_ifs <;> simp [InZl]
    have := h F l 1 le_rfl (wideInd C) (isRayFun_wideInd _ C) hint _ hcop k (by omega) (x C) (x C) hv hv'
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at this
    have e2 : c * x C = -(x C - (((a ^ finrank ℚ F : ℕ) : ℚ)) ^ k * x C) := by
      rw [hcdef, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]; push_cast; ring
    rw [e2, inZl_iff, padicValRat.neg, ← inZl_iff]; exact this

  have step : ∀ (T : Finset (Ideal (𝓞 F))) (𝔭 : Ideal (𝓞 F)), 𝔭 ∉ T → 𝔭 ∈ P → T ⊆ P → St (insert 𝔭 T) → St T := by
    intro T 𝔭 h𝔭T h𝔭P hTP hSt x hx
    choose Zf hZf eZ using hx
    obtain ⟨hmax, hne, hdvd⟩ := hP 𝔭 h𝔭P
    have hcopT : 𝔭 ⊔ ∏ 𝔮 ∈ T, 𝔮 = ⊤ := by
      rw [← Ideal.isCoprime_iff_sup_eq]
      refine IsCoprime.prod_right fun 𝔮 h𝔮 => Ideal.isCoprime_iff_sup_eq.2 ?_
      exact Ideal.IsMaximal.coprime_of_ne hmax (hP 𝔮 (hTP h𝔮)).1 (fun e => h𝔭T (e ▸ h𝔮))
    set q : ℕ := Ideal.absNorm 𝔭 ^ (k - 1) with hqdef
    have hy : ∀ C, ∃ Z : ℂ → ℂ, IsRayL (∏ 𝔮 ∈ insert 𝔭 T, 𝔮) (wideInd C) Z ∧
        Z (1 - (k : ℂ)) = ((x C - (q : ℚ) * x (C * (cls 𝔭)⁻¹) : ℚ) : ℂ) := by
      intro C
      refine ⟨fun s => Zf C s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Zf (C * (cls 𝔭)⁻¹) s, ?_, ?_⟩
      · rw [Finset.prod_insert h𝔭T, mul_comm]
        exact eulerStep _ 𝔭 hmax hne hcopT C _ _ (hZf C) (hZf _)
      · have e1 : -(1 - (k : ℂ)) = ((k - 1 : ℕ) : ℂ) := by rw [Nat.cast_sub (by omega)]; push_cast; ring
        simp only [e1, Complex.cpow_natCast, eZ, hqdef]
        push_cast; ring
    have := hSt _ hy
    intro C
    have hmul := inZl_of_shift l ((cls 𝔭)⁻¹) q (dvd_pow hdvd (by omega)) (fun C => c * x C)
      (fun C => by have := this C; rwa [mul_sub, mul_left_comm] at this) C
    exact hmul
  have key : ∀ U : Finset (Ideal (𝓞 F)), U ⊆ P → St (P \ U) := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro _; simpa using hfull
    | insert 𝔭 U h𝔭U ih =>
      intro hU
      have h𝔭P : 𝔭 ∈ P := hU (Finset.mem_insert_self _ _)
      have ih := ih ((Finset.subset_insert _ _).trans hU)
      have e : P \ U = insert 𝔭 (P \ insert 𝔭 U) := by
        ext 𝔮; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩; by_cases h : 𝔮 = 𝔭 <;> simp_all
        · rintro (h | ⟨h1, h2⟩)
          · subst h; exact ⟨h𝔭P, h𝔭U⟩
          · exact ⟨h1, fun h => h2 (Or.inr h)⟩
      rw [e] at ih
      exact step _ 𝔭 (by simp) h𝔭P Finset.sdiff_subset ih
  have h0 := key P subset_rfl
  rw [Finset.sdiff_self] at h0
  refine h0 z (fun C => ?_) C
  obtain ⟨Z, hZ, e⟩ := hz C
  exact ⟨Z, by rw [Finset.prod_empty, Ideal.one_eq_top]; exact (isRayL_top_iff C Z).2 hZ, e⟩

theorem zetaDenominators (h : GlobalTheory.Published.SiegelKlingenDeligneRibet) : ZetaDenominators := by
  apply ZetaDenominatorsReal.cm
  intro F _ _ _ s hs
  have hf : 1 ≤ finrank ℚ F := (Module.finrank_pos : 0 < finrank ℚ F)
  have hn2 : 2 ≤ finrank ℚ F * (2 * s) := by nlinarith
  have hev : Even (finrank ℚ F * (2 * s)) := ⟨finrank ℚ F * s, by ring⟩
  have hloc : ∀ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues (2 * s) z → ∀ l : ℕ, l.Prime → LocalBound (2 * s) z l := by
    intro z hz l hl
    haveI := Fact.mk hl
    have hm := mMin_eq_mE _root_.GlobalTheory.cmValues_minPadicVal_bound l _ hl hn2 hev
    obtain ⟨a, ha2, hac, hv⟩ := _root_.GlobalTheory.cmValues_minPadicVal_bound l _ hl hn2 hev
    have hc := cE_le_of_inZl (F := F) z l a _ ha2 (by omega) (inZl_mul_zeta h.2 F l a (2 * s) ha2 hac (by omega) z hz)
    rw [hv] at hc
    refine ⟨by rw [hm]; exact hc, fun h2 hd => ?_, fun h2 hd => ?_, fun h2 => ?_⟩ <;> rw [hm] <;> simp [Formalism.PairingDivisionLocalBalance.mE, *]
  refine ⟨exists_isZetaValues h.1 F (2 * s) (by omega), fun z hz => ⟨hloc z hz, fun h16 =>
    sumBound_of_local _root_.GlobalTheory.dividedPowerValuations_cESum (2 * s) z (by omega) h16 fun l hl => ?_⟩⟩
  have h1 := hloc z hz l hl
  have h2 := h1.1
  rwa [h1.mMin_eq] at h2

end GlobalTheory.ZetaDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceBound
section
namespace GlobalTheory.FinGL.MultSharpObj

open GlobalTheory.FinGL Formalism.L2.DIV

theorem placeBound : MultSharpPf.PlaceBound := by
  intro F _ _ ψ hψ r V _ _ _ b σ hσ ρ k hk hr hq
  rw [GlobalTheory.T.symmetricPositionCharMultiplicity_parabolicInduction F ψ hψ r V b σ hσ ρ k hr]
  exact sum_numBlockSets_mul_gamma_two_sided_bounds r k (Fintype.card F) b hk (by omega) hq Fintype.one_lt_card

theorem multSharp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.MultSharp := MultSharpPf.multSharp_of_placeBound placeBound

end GlobalTheory.FinGL.MultSharpObj
end

