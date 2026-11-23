module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM.SFamModel
open Out.Inh GlobalTheory.ZM.Model GlobalTheory.ZM.DimZero

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {k : ℕ}

theorem isIso_of_points [IsReduced S] (A : Over S) [GrpObj A] (h : IsAbelianScheme A)
    (hp : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y = 1) : IsIso A.hom := by
  haveI := h.proper
  haveI := h.smooth
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ A.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.hom
  haveI : Surjective e := ⟨fun a => by
    let K := AlgebraicClosure (A.left.residueField a)
    let y : Sp K ⟶ A.left := spMap (algebraMap (A.left.residueField a) K) ≫ A.left.fromSpecResidueField a
    have h1 := hp K (y ≫ A.hom) (Over.homMk y rfl)
    have h2 : y = (y ≫ A.hom) ≫ e := by
      have := congrArg (·.left) h1
      simpa [Hom.one_def, e, eSec] using this
    have h3 : y default = a := by
      simp only [y, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    exact ⟨(y ≫ A.hom) default, by rw [← Scheme.Hom.comp_apply, ← h2, h3]⟩⟩
  haveI : IsIso e := isIso_of_isClosedImmersion_of_surjective e
  haveI : IsIso (e ≫ A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e _

theorem siegPB_zero {B : Type} [CommRing B] {ζ' : B} {s' : S' ⟶ Sp B} (c : SiegPre 0 k ζ' s') [IsIso c.A.hom]
    (ζ : o) (s : S ⟶ Sp o) (f : S' ⟶ S) : SiegPB c (zeroSieg k ζ s) f := by
  have uniq : ∀ {T : Over S'} (x y : T ⟶ c.A), x = y := fun x y =>
    Over.OverMorphism.ext (by rw [← cancel_mono c.A.hom, Over.w x, Over.w y])
  have aux : ∀ {X Y Z : Scheme.{0}} (u : X ⟶ S') (d : S ⟶ Z) (p : Z ⟶ S) (q : X ⟶ Y) (a : Y ⟶ S') (f : S' ⟶ S),
      d ≫ p = 𝟙 S → q ≫ a = u → (u ≫ f ≫ d) ≫ p = q ≫ a ≫ f := by
    rintro X Y Z _ d p q a f h rfl
    simp [h]
  obtain ⟨r, hr⟩ := c.rig₁
  have hF : (fst c.A c.A).left ≫ (lift (1 : c.A ⟶ c.A) (𝟙 c.A)).left = 𝟙 _ := by
    have : fst c.A c.A ≫ lift (1 : c.A ⟶ c.A) (𝟙 c.A) = 𝟙 _ :=
      CartesianMonoidalCategory.hom_ext _ _ (uniq _ _) (uniq _ _)
    exact congrArg (·.left) this
  let d : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ 𝟙_ (Over S) := lift (𝟙 _) (𝟙 _)
  have d1 : d.left ≫ (fst _ _ : 𝟙_ (Over S) ⊗ 𝟙_ (Over S) ⟶ _).left = 𝟙 S := by
    rw [← Over.comp_left, lift_fst]; rfl
  have d2 : d.left ≫ (snd _ _ : 𝟙_ (Over S) ⊗ 𝟙_ (Over S) ⟶ _).left = 𝟙 S := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨c.A.hom ≫ f, (c.A ⊗ c.A).hom ≫ f ≫ d.left, ⟨?_, fun T x y x₀ y₀ _ _ => ?_⟩, ⟨?_, ?_⟩,
    lbIso_of_gen _ _ _ hF _ (DVR.pullGen_isGen _ _ _ r hr (fst c.A c.A).left) (linComb_triv_g _ _), fun a => ?_⟩
  · show IsPullback (c.A.hom ≫ f) c.A.hom (𝟙 S) f
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  · have h1 : (x₀ * y₀).left ≫ 𝟙 S = T.hom ≫ f := Over.w (x₀ * y₀)
    exact ((Category.comp_id _).symm.trans h1).trans
      ((congrArg (· ≫ f) (Over.w (x * y))).symm.trans (Category.assoc _ _ _))
  · exact aux _ _ _ _ _ _ d1 (Over.w (fst c.A c.A))
  · exact aux _ _ _ _ _ _ d2 (Over.w (snd c.A c.A))
  · have h1 : (c.lev a).left ≫ c.A.hom = 𝟙 S' := Over.w (c.lev a)
    have h2 : ((zeroSieg k ζ s).lev a).left ≫ 𝟙 S = 𝟙 S := Over.w ((zeroSieg k ζ s).lev a)
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) h1).trans (Category.id_comp _))).trans
      ((congrArg (f ≫ ·) ((Category.comp_id _).symm.trans h2)).trans (Category.comp_id _)).symm

def zeroFam (k : ℕ) (ζ : o)
    (hz : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre 0 k ζ s'), IsReduced S → IsIso c.A.hom) : SFam 0 k ζ where
  X := Sp o
  s := 𝟙 _
  smooth := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 _))
  qproj := OnePoint.isQProjOver_id o
  univ := zeroSieg k ζ _
  princ := principal_zeroSieg k ζ _
  rep := fun S s' c hS _ _ => by
    haveI := hz S s' c hS
    exact ⟨s', Category.comp_id _, siegPB_zero c ζ _ s'⟩
  inj := fun _ _ _ _ _ _ _ h _ _ => by simpa using h

theorem tors_eq_one {ζ : o} (hζ : IsUnit ζ) {s' : S ⟶ Sp o} (c : SiegPre 0 k ζ s') (K : Type) [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ c.A) (hy : y ^ k = 1) : y = 1 := by
  let β : o →+* K := (Spec.preimage (x ≫ s')).hom
  have hβ : x ≫ s' = spMap β := by simp [β, spMap]
  obtain ⟨h1, h2, -⟩ := c.geom K x β (hζ.map β).unit hβ rfl
  obtain ⟨a, rfl⟩ := h2 y hy
  exact (h1 a).2 ⟨0, Subsingleton.elim _ _⟩

def zeroFamLevelZero {ζ : o} (hζ : IsUnit ζ) : SFam 0 0 ζ :=
  zeroFam 0 ζ fun _ _ c _ => isIso_of_points c.A c.ab fun K _ _ x y => tors_eq_one hζ c K x y (pow_zero y)

theorem isIso_of_count
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (g n : ℕ), IsAbelianScheme B →
      SmoothOfRelativeDimension g B.hom → (n : K) ≠ 0 →
      Nat.card {x : (𝟙_ (Over (Sp K)) ⟶ B) // x ^ n = 1} = n ^ (2 * g))
    {ζ : o} (hζ : IsUnit ζ) (hku : IsUnit (k : o)) (hk : 2 ≤ k) {s' : S ⟶ Sp o} (c : SiegPre 0 k ζ s') [IsReduced S] :
    IsIso c.A.hom :=
  isIso_of_points c.A c.ab fun K _ _ t y => by
    have hB' : IsAbelianScheme ((Over.pullback t).obj c.A) :=
      { comm := by have := c.ab.comm; infer_instance
        smooth := by have := c.ab.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := c.ab.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := c.ab.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
    obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K _ hB'
    have hn : (k : K) ≠ 0 := by
      have := hku.map (Spec.preimage (t ≫ s')).hom
      rw [map_natCast] at this
      exact this.ne_zero
    have h := H K _ g k hB' hg hn
    have hp := isGrpPullback_pullback c.A t
    have hinj : Function.Injective (pushHom hp (𝟙_ (Over (Sp K)))) := by
      intro x y hxy
      have e : x.left ≫ pullback.fst c.A.hom t = y.left ≫ pullback.fst c.A.hom t := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    have h1 : Nat.card {x : (𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj c.A) // x ^ k = 1} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, one_pow k⟩, fun x => Subtype.ext (hinj ?_)⟩
      rw [map_one]
      exact tors_eq_one hζ c K _ _ (by rw [← map_pow, x.2, map_one])
    rw [h1] at h
    obtain rfl : g = 0 := by
      rcases (Nat.pow_eq_one.1 h.symm) with h | h <;> omega
    haveI : IsIso (pullback.snd c.A.hom t) := isIso_of_dim_zero _ hB' hg
    have u : ∀ z z' : Over.mk t ⟶ c.A, z = z' := fun z z' => by
      have e : pullback.lift z.left (𝟙 _) ((Over.w z).trans (Category.id_comp t).symm) =
          pullback.lift z'.left (𝟙 _) ((Over.w z').trans (Category.id_comp t).symm) := by
        rw [← cancel_mono (pullback.snd c.A.hom t), pullback.lift_snd, pullback.lift_snd]
      have := congrArg (· ≫ pullback.fst c.A.hom t) e
      simp only [pullback.lift_fst] at this
      exact Over.OverMorphism.ext this
    exact u _ _

theorem hom_ext {h : ℕ} {ζ : o} (F : SFam h k ζ) {s' : S ⟶ Sp o} (c : SiegPre h k ζ s') (f f' : S ⟶ F.X)
    (hs : f ≫ F.s = f' ≫ F.s) (h₁ : SiegPB c F.univ f) (h₂ : SiegPB c F.univ f') : f = f' := by
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  obtain ⟨c', hc'⟩ := (GlobalTheory.siegPre_pullback h k o ζ S (Sp (S.presheaf.stalk x)) s' _ (S.fromSpecStalk x) c rfl).1
  exact F.inj (S.presheaf.stalk x) _ _ _ c'
    ((Category.assoc _ _ _).trans ((congrArg (S.fromSpecStalk x ≫ ·) hs).trans (Category.assoc _ _ _).symm))
    (GlobalTheory.SiegelPullComp.pb_comp h₁ hc') (GlobalTheory.SiegelPullComp.pb_comp h₂ hc')

def zeroFamLevel {ζ : o} (hζ : IsUnit ζ) (hku : IsUnit (k : o)) (hk : 2 ≤ k) : SFam 0 k ζ :=
  zeroFam k ζ fun _ _ c _ => isIso_of_count GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional hζ hku hk c

end GlobalTheory.ZM.SFamModel
end
