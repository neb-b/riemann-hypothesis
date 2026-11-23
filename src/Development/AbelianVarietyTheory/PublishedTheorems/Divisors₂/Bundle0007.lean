module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianDeRhamFree : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    Module.Finite R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧ Module.Projective R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham (A.hom ≫ 𝟙 _)) p = 2 * g) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham (A.hom ≫ 𝟙 _)) ≃ₗ[R] SecondDeRham (A.hom ≫ 𝟙 _),
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b

def AbelianDeRhamStructure : Prop :=
  AbelianDeRhamFree ∧ AbelianDeRham.Hodge ∧ AbelianDeRham.BaseChange

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDieudonne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianDieudonne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : ∀ (A : Over (Sp k)) [GrpObj A], ModuleCat.{0} (WittVector p k))
      (map : ∀ {A B : Over (Sp k)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f],
        M A →ₗ[WittVector p k] M B)
      (F : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] M A)
      (V : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] M A)
      (red : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] HdR A),
      (∀ (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
        SmoothOfRelativeDimension g A.hom →
        Module.Free (WittVector p k) (M A) ∧ Module.Finite (WittVector p k) (M A) ∧
        Module.finrank (WittVector p k) (M A) = 2 * g ∧
        (∀ m, F A (V A m) = p • m) ∧ (∀ m, V A (F A m) = p • m) ∧
        Function.Surjective (red A) ∧ (∀ m, red A m = 0 ↔ ∃ n, m = p • n) ∧
        (∀ h, h ∈ Fil A ↔ ∃ m, h = red A (V A m)) ∧
        map (𝟙 A) = LinearMap.id) ∧
      (∀ (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B →
        (∀ (f : A ⟶ B) [IsMonHom f] (m : M A),
          map f (F A m) = F B (map f m) ∧ map f (V A m) = V B (map f m) ∧
          red B (map f m) = push (dp0 k) (𝟙 _) f (red A m)) ∧
        ∀ (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)],
          map (f * g) = map f + map g) ∧
      ∀ (A B C : Over (Sp k)) [GrpObj A] [GrpObj B] [GrpObj C], IsAbelianScheme A →
        IsAbelianScheme B → IsAbelianScheme C →
        ∀ (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g], map (f ≫ g) = map g ∘ₗ map f

namespace AbelianDieudonne

end AbelianDieudonne

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace GrothendieckMessing

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R}

theorem redMor {π : R →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap π) i) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R₀) (𝟙 _) A₀ π (spMap π) i :=
  GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) h

def IsAdmissible {π : R →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap π) i) (F : Submodule R (HdR A)) : Prop :=
  (∃ N : Submodule R (HdR A), IsCompl F N) ∧
    ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ x ∈ F, (redMor h).Corr x y

variable (κ : DividedPowers I) (π : R →+* R₀)

def Canonical : Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    Function.Bijective (liftMor κ h).pull ∧ IsAdmissible h (Fil A)

def LiftObj : Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left)
    (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom →
    ∀ F : Submodule R (HdR A'), IsAdmissible h' F →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left)
        (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A ∧
        SmoothOfRelativeDimension g A.hom ∧ liftFil κ h = F.comap (crysToDR κ h')

def LiftHom : Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (k : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil κ h, push κ (spMap π) f₀ d ∈ liftFil κ k) →
    ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j

def At : Prop := Canonical κ π ∧ LiftObj κ π ∧ LiftHom κ π

end GrothendieckMessing

def GrothendieckMessing : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (R : Type) [CommRing R], IsNilpotent (p : R) →
    ∀ (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
      GrothendieckMessing.At κ π

namespace GrothendieckMessing

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I}
  {π : R →+* R₀} {g g' : ℕ} {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀]
  {A A' B : Over (Sp R)} [GrpObj A] [GrpObj A'] [GrpObj B]
  {i : A₀.left ⟶ A.left} {i' : A₀.left ⟶ A'.left} {j : B₀.left ⟶ B.left}

theorem Canonical.crysToDR_bijective (H : Canonical κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Bijective (crysToDR κ h) :=
  (LinearEquiv.ofBijective _ (H g A₀ A i h hA hg).1).dualMap.bijective

theorem LiftHom.exists_iff (H : LiftHom κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (k : IsGrpPullback B₀ B (spMap π) j) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] :
    (∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j) ↔
      ∀ d ∈ liftFil κ h, push κ (spMap π) f₀ d ∈ liftFil κ k :=
  ⟨fun ⟨f, _, e⟩ _ hd ↦ push_mem_liftFil κ h k f₀ f e hd,
    fun e ↦ (H g A₀ A i h hA hg g' B₀ B j k hB hg' f₀ e).exists⟩

theorem LiftHom.unique (H : LiftHom κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (k : IsGrpPullback B₀ B (spMap π) j) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] {f f' : A ⟶ B}
    [IsMonHom f] [IsMonHom f'] (e : i ≫ f.left = f₀.left ≫ j) (e' : i ≫ f'.left = f₀.left ≫ j) :
    f = f' :=
  (H g A₀ A i h hA hg g' B₀ B j k hB hg' f₀ fun _ hd ↦ push_mem_liftFil κ h k f₀ f e hd).unique
    ⟨inferInstance, e⟩ ⟨inferInstance, e'⟩

theorem LiftHom.exists_iso_iff (H : LiftHom κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (h' : IsGrpPullback A₀ A' (spMap π) i') (hA' : IsAbelianScheme A')
    (hg' : SmoothOfRelativeDimension g' A'.hom) :
    (∃ e : A ≅ A', IsMonHom e.hom ∧ i ≫ e.hom.left = i') ↔ liftFil κ h = liftFil κ h' := by
  have hid : ∀ d : Crys κ (spMap π) A₀, push κ (spMap π) (𝟙 A₀) d = d := fun d ↦ by
    rw [push_id]; rfl
  constructor
  · rintro ⟨e, _, he⟩
    have he' : i' ≫ e.inv.left = i := by
      rw [← he, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]
    refine le_antisymm (fun d hd ↦ ?_) fun d hd ↦ ?_
    · exact hid d ▸ push_mem_liftFil κ h h' (𝟙 A₀) e.hom (by simpa using he) hd
    · exact hid d ▸ push_mem_liftFil κ h' h (𝟙 A₀) e.inv (by simpa using he') hd
  · intro e
    obtain ⟨f, _, ef⟩ := (H.exists_iff h hA hg h' hA' hg' (𝟙 A₀)).2 fun d hd ↦ by
      rw [hid, ← e]; exact hd
    obtain ⟨f', _, ef'⟩ := (H.exists_iff h' hA' hg' h hA hg (𝟙 A₀)).2 fun d hd ↦ by
      rw [hid, e]; exact hd
    rw [Over.id_left, Category.id_comp] at ef ef'
    refine ⟨⟨f, f', H.unique h hA hg h hA hg (𝟙 A₀) ?_ (by simp),
      H.unique h' hA' hg' h' hA' hg' (𝟙 A₀) ?_ (by simp)⟩, inferInstance, ef⟩
    · rw [Over.comp_left, ← Category.assoc, ef, ef', Over.id_left, Category.id_comp]
    · rw [Over.comp_left, ← Category.assoc, ef', ef, Over.id_left, Category.id_comp]

theorem crysRedMor (κ : DividedPowers I) (hI : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] :
    GrpMor κ (spMap π) A₀ (dp0 R₀) (𝟙 _) A₀ π (𝟙 _) (Over.Hom.left (𝟙 A₀)) := by
  apply GrpMor.of_hom _ (Category.id_comp _).symm (𝟙 A₀)
  have z : ∀ a ∈ I, π a = 0 := fun a ha ↦ RingHom.mem_ker.1 (hI ▸ ha)
  refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ z a ha, fun n hn a ha ↦ ?_⟩
  rw [z a ha, z _ (κ.dpow_mem hn ha), dpow_eval_zero _ hn]

theorem corr_crysToDR_iff (hI : RingHom.ker π = I) (h : IsGrpPullback A₀ A (spMap π) i)
    (hs : Function.Surjective (liftMor κ h).pull) (d : Crys κ (spMap π) A₀) (y : HdR A₀) :
    (redMor h).Corr (crysToDR κ h d) y ↔ (crysRedMor κ hI A₀).Corr d y := by
  have e : ∀ c, (crysRedMor κ hI A₀).pull ((liftMor κ h).pull c) = (redMor h).pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) (by simp) c
  refine ⟨fun H c ↦ ?_, fun H c ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := hs c
    rw [e]; exact H c
  · rw [← e]; exact H _

theorem canonical_of_abelianDeRham (P : AbelianDeRham) (hκ : IsNilDP κ)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) : Canonical κ π := by
  intro g A₀ _ A _ i h hA hg
  obtain ⟨PF, PH, PB, PR, -⟩ := P
  letI : Algebra R R₀ := π.toAlgebra
  obtain ⟨-, ⟨N, hN⟩, -⟩ := PH R A g hA hg
  have hF : PrimitiveSubmodule A₀ = Submodule.span R₀ ((redMor h).pull '' (PrimitiveSubmodule A)) :=
    (PB R A g hA hg R₀ A₀ i h).2
  have := (PF.prim hA hg).2.1
  refine ⟨PR R A g hA hg I κ hκ R₀ π hπ hI A₀ i h, ⟨N.dualAnnihilator, ?_, ?_⟩, fun y ↦ ⟨?_, ?_⟩⟩
  · rw [disjoint_iff, Fil, ← Submodule.dualAnnihilator_sup_eq, hN.sup_eq_top,
      Submodule.dualAnnihilator_top]
  · refine codisjoint_iff_le_sup.2 fun x _ ↦ Submodule.mem_sup.2
      ⟨x ∘ₗ Submodule.projection _ _ hN.symm, ?_, x ∘ₗ Submodule.projection _ _ hN, ?_, ?_⟩
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero]
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN).2 hc, map_zero]
    · ext c
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add (f := _), add_comm,
        Submodule.projection_add_projection_eq_self hN]
  · intro hy
    let l : primDR A →ₗ[R] R₀ :=
      { toFun c := y ((redMor h).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₀) l hπ
    refine ⟨x ∘ₗ Submodule.projection _ _ hN.symm, (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero], fun c ↦ ?_⟩
    have z : l (Submodule.projection _ _ hN c) = 0 := (Submodule.mem_dualAnnihilator _).1 hy _
      (hF ▸ Submodule.subset_span ⟨_, Submodule.projection_apply_mem hN c, rfl⟩)
    change l c = π (x _)
    conv_lhs => rw [← Submodule.projection_add_projection_eq_self hN c, map_add (f := _), z, zero_add, ← hx]
    rfl
  · rintro ⟨x, hx, e⟩
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker y)).2 (fun c hc ↦ ?_) hc
    obtain ⟨c, hc, rfl⟩ := hc
    exact (e c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hx c hc, map_zero])

end GrothendieckMessing

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DeRhamVectorExtension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace DeRhamVectorExtension

abbrev Family (p : ℕ) : Type 1 :=
  ∀ ⦃R : Type⦄ [CommRing R], IsNilpotent (p : R) → ∀ ⦃A : Over (Sp R)⦄ [GrpObj A],
    IsAbelianScheme A → ∀ ⦃G : PDivGroup p R⦄, G.TorsionTower A → (primDR A ≃ₗ[R] G.RigExt)

variable {p : ℕ} (e : Family p)

def Family.Natural : Prop :=
  ∀ ⦃R R' : Type⦄ [CommRing R] [CommRing R'] (hR : IsNilpotent (p : R)) (hR' : IsNilpotent (p : R'))
    ⦃A : Over (Sp R)⦄ [GrpObj A] ⦃A' : Over (Sp R')⦄ [GrpObj A']
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    ⦃G : PDivGroup p R⦄ ⦃G' : PDivGroup p R'⦄ (t : G.TorsionTower A) (t' : G'.TorsionTower A')
    ⦃σ : R →+* R'⦄ ⦃φ : A'.left ⟶ A.left⦄
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) (c : primDR A),
    e hR' hA' t' (m.pull c) = (t'.semiHom t m).rig (e hR hA t c)

def Family.Filtered : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
    (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A),
    (PrimitiveSubmodule A).map (e hR hA t).toLinearMap = LinearMap.range G.rigOfOmega

def Family.Tangent : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
    (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A)
    (h : HdR A) (v : epsR R ⟶ A),
    IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie ((e hR hA t).symm.dualMap h)) v

end DeRhamVectorExtension

def DeRhamVectorExtension : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ e : DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent

namespace DeRhamVectorExtension

variable {p : ℕ} {e : Family p} {R : Type} [CommRing R] (hR : IsNilpotent (p : R))
  {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
  {G H : PDivGroup p R} (t : G.TorsionTower A) (u : H.TorsionTower B)


variable [Fact p.Prime]

theorem Family.Natural.primPull (he : e.Natural) (f : A ⟶ B) [IsMonHom f] (c : primDR B) :
    e hR hA t (primPull (dp0 R) (𝟙 _) f c) = PDivGroup.rigExtMap (t.map u f) (e hR hB u c) := by
  have k := he hR hR hB hA u t (PDiv.grpMor_of_hom f) c
  rw [← PDivGroup.SemiHom.ofHom_rig]
  exact k

end DeRhamVectorExtension

end GlobalTheory.Published
end
end

