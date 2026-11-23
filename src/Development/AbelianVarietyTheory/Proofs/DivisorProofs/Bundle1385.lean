module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalQuotientTransitionIsomorphisms
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace QuotTransition

section

variable {S U V : Scheme.{0}} (fU : U ⟶ S) (fV : V ⟶ S) (A : Over S)
  (BU : Over U) (BV : Over V) (qU : (Over.pullback fU).obj A ⟶ BU) (qV : (Over.pullback fV).obj A ⟶ BV)

lemma w_left : qU.left ≫ BU.hom = pullback.snd A.hom fU := Over.w qU

noncomputable abbrev src : Scheme.{0} := pullback qU.left (pullback.fst (BU.hom ≫ fU) fV)

noncomputable def toV : src fU fV A BU qU ⟶ pullback A.hom fV :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst A.hom fU) (pullback.snd _ _ ≫ pullback.snd _ _) (by
    have h1 := pullback.condition (f := A.hom) (g := fU)
    have h2 := pullback.condition (f := qU.left) (g := pullback.fst (BU.hom ≫ fU) fV)
    have h3 := pullback.condition (f := BU.hom ≫ fU) (g := fV)
    have h4 := w_left fU A BU qU
    simp only [Category.assoc] at h1 h2 h3 ⊢
    rw [h1, ← h4, Category.assoc, reassoc_of% h2, h3])

lemma toV_fst : toV fU fV A BU qU ≫ pullback.fst A.hom fV =
    pullback.fst _ _ ≫ pullback.fst A.hom fU := pullback.lift_fst _ _ _

lemma toV_snd : toV fU fV A BU qU ≫ pullback.snd A.hom fV =
    pullback.snd _ _ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _

variable (H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)

lemma map_left_fst {T : Scheme.{0}} (f : T ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

lemma toV_comp_eq [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    (hU : IsPullback ((fst ((Over.pullback fU).obj H) ((Over.pullback fU).obj A) ≫ (Over.pullback fU).map i) *
      snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A))
      (snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A)) qU qU)
    (hV : IsPullback ((fst ((Over.pullback fV).obj H) ((Over.pullback fV).obj A) ≫ (Over.pullback fV).map i) *
      snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A))
      (snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A)) qV qV)
    {T : Scheme.{0}} (u v : T ⟶ src fU fV A BU qU)
    (huv : u ≫ pullback.snd _ _ = v ≫ pullback.snd _ _) :
    u ≫ toV fU fV A BU qU ≫ qV.left = v ≫ toV fU fV A BU qU ≫ qV.left := by
  obtain ⟨yu, hyu_def⟩ : ∃ y, y = u ≫ pullback.fst qU.left (pullback.fst (BU.hom ≫ fU) fV) := ⟨_, rfl⟩
  obtain ⟨yv, hyv_def⟩ : ∃ y, y = v ≫ pullback.fst qU.left (pullback.fst (BU.hom ≫ fU) fV) := ⟨_, rfl⟩
  have hq : yu ≫ qU.left = yv ≫ qU.left := by
    simp only [hyu_def, hyv_def, Category.assoc, pullback.condition, reassoc_of% huv]
  have hs : yu ≫ pullback.snd A.hom fU = yv ≫ pullback.snd A.hom fU := by
    rw [← w_left fU A BU qU, reassoc_of% hq]
  let Tj : Over U := Over.mk (yv ≫ pullback.snd A.hom fU)
  let yu' : Tj ⟶ (Over.pullback fU).obj A := Over.homMk yu hs
  let yv' : Tj ⟶ (Over.pullback fU).obj A := Over.homMk yv rfl
  have hq' : yu' ≫ qU = yv' ≫ qU := Over.OverMorphism.ext hq
  let s := hU.lift yu' yv' hq' ≫ fst _ _
  have hyu : yu' = (s ≫ (Over.pullback fU).map i) * yv' := by
    have h1 := hU.lift_fst yu' yv' hq'
    rw [comp_mul, hU.lift_snd] at h1
    rw [Category.assoc, h1]
  have e1 : yv ≫ pullback.snd A.hom fU ≫ fU =
      u ≫ pullback.snd _ _ ≫ pullback.snd (BU.hom ≫ fU) fV ≫ fV := by
    rw [← w_left fU A BU qU, hyv_def]
    simp only [Category.assoc]
    rw [reassoc_of% (pullback.condition (f := qU.left) (g := pullback.fst (BU.hom ≫ fU) fV)),
      pullback.condition, reassoc_of% huv]
  have hsw : s.left ≫ pullback.snd H.hom fU = yv ≫ pullback.snd A.hom fU := Over.w s
  have hc1 : (s.left ≫ pullback.fst H.hom fU) ≫ H.hom =
      (u ≫ pullback.snd _ _ ≫ pullback.snd (BU.hom ≫ fU) fV) ≫ fV := by
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% hsw, e1]
  let Tk : Over V := Over.mk (u ≫ pullback.snd _ _ ≫ pullback.snd (BU.hom ≫ fU) fV)
  let s' : Tk ⟶ (Over.pullback fV).obj H :=
    Over.homMk (pullback.lift (s.left ≫ pullback.fst H.hom fU) (u ≫ pullback.snd _ _ ≫ pullback.snd _ _) hc1)
      (pullback.lift_snd _ _ _)
  let zu : Tk ⟶ (Over.pullback fV).obj A :=
    Over.homMk (u ≫ toV fU fV A BU qU) (by simp [Tk, Category.assoc, toV_snd])
  let zv : Tk ⟶ (Over.pullback fV).obj A :=
    Over.homMk (v ≫ toV fU fV A BU qU) (by simp [Tk, Category.assoc, toV_snd, reassoc_of% huv])
  have hc0 : (s.left ≫ pullback.fst H.hom fU ≫ i.left) ≫ A.hom = yv ≫ pullback.fst A.hom fU ≫ A.hom := by
    rw [Category.assoc, Category.assoc, Over.w i, pullback.condition, reassoc_of% hsw, pullback.condition]
  let x0 : Over.mk (yv ≫ pullback.fst A.hom fU ≫ A.hom) ⟶ A :=
    Over.homMk (s.left ≫ pullback.fst H.hom fU ≫ i.left) hc0
  let y0 : Over.mk (yv ≫ pullback.fst A.hom fU ≫ A.hom) ⟶ A :=
    Over.homMk (yv ≫ pullback.fst A.hom fU) (Category.assoc _ _ _)
  have mU := GlobalTheory.TorusToProper.mul_left_fst fU A (s ≫ (Over.pullback fU).map i) yv' x0 y0
    (by rw [Over.comp_left, Category.assoc, map_left_fst]; rfl) rfl
  have mV := GlobalTheory.TorusToProper.mul_left_fst fV A (s' ≫ (Over.pullback fV).map i) zv x0 y0
    (by rw [Over.comp_left, Category.assoc, map_left_fst]; simp only [x0, s', Over.homMk_left]; rw [pullback.lift_fst_assoc, Category.assoc]) (by simp [y0, zv, hyv_def, Category.assoc, toV_fst])
  have key : zu = (s' ≫ (Over.pullback fV).map i) * zv := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [mV, ← mU, ← hyu]
      simp [zu, yu', hyu_def, Category.assoc, toV_fst]
    · exact (Over.w zu).trans (Over.w ((s' ≫ (Over.pullback fV).map i) * zv)).symm
  have hk : zu ≫ qV = zv ≫ qV := by
    rw [key]
    have := lift s' zv ≫= hV.w
    simpa [comp_mul, ← Category.assoc] using this
  have := congrArg CommaMorphism.left hk
  simpa [zu, zv] using this

theorem exists_trans [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    (hU : IsPullback ((fst ((Over.pullback fU).obj H) ((Over.pullback fU).obj A) ≫ (Over.pullback fU).map i) *
      snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A))
      (snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A)) qU qU)
    (hV : IsPullback ((fst ((Over.pullback fV).obj H) ((Over.pullback fV).obj A) ≫ (Over.pullback fV).map i) *
      snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A))
      (snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A)) qV qV) :
    ∃ b : pullback (BU.hom ≫ fU) fV ⟶ BV.left, b ≫ BV.hom = pullback.snd _ _ ∧
      ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fU) (z : T ⟶ pullback A.hom fV)
        (w : T ⟶ pullback (BU.hom ≫ fU) fV), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qU.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ qV.left := by
  have hc : ∀ {T : Scheme.{0}} (u v : T ⟶ src fU fV A BU qU),
      u ≫ pullback.snd _ _ = v ≫ pullback.snd _ _ →
      u ≫ (toV fU fV A BU qU ≫ qV.left) = v ≫ (toV fU fV A BU qU ≫ qV.left) :=
    fun u v huv => toV_comp_eq fU fV A BU BV qU qV H i hU hV u v huv
  have fac := EffectiveEpi.fac (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV))
    (toV fU fV A BU qU ≫ qV.left) hc
  refine ⟨EffectiveEpi.desc (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV))
    (toV fU fV A BU qU ≫ qV.left) hc, ?_, ?_⟩
  · rw [← cancel_epi (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV)), reassoc_of% fac,
      w_left fV A BV qV, toV_snd]
  · intro T y z w h1 h2 h3
    have hw : w = pullback.lift y w h2.symm ≫ pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV) :=
      (pullback.lift_snd _ _ _).symm
    have hz : pullback.lift y w h2.symm ≫ toV fU fV A BU qU = z := by
      apply pullback.hom_ext
      · rw [Category.assoc, toV_fst, pullback.lift_fst_assoc, h1]
      · rw [Category.assoc, toV_snd, pullback.lift_snd_assoc, h3]
    rw [hw, Category.assoc, fac, ← Category.assoc, hz]

end

lemma lift_comp_lift {S U V : Scheme.{0}} (fU : U ⟶ S) (fV : V ⟶ S) (A : Over S)
    (BU : Over U) (BV : Over V) (qU : (Over.pullback fU).obj A ⟶ BU) (qV : (Over.pullback fV).obj A ⟶ BV)
    [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    (b : pullback (BU.hom ≫ fU) fV ⟶ BV.left) (b' : pullback (BV.hom ≫ fV) fU ⟶ BU.left)
    (hb : b ≫ BV.hom = pullback.snd _ _)
    (cb : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fU) (z : T ⟶ pullback A.hom fV)
        (w : T ⟶ pullback (BU.hom ≫ fU) fV), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qU.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ qV.left)
    (cb' : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fV) (z : T ⟶ pullback A.hom fU)
        (w : T ⟶ pullback (BV.hom ≫ fV) fU), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qV.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b' = z ≫ qU.left)
    (h₁ : b ≫ BV.hom ≫ fV = (pullback.fst _ _ ≫ BU.hom) ≫ fU)
    (h₂ : b' ≫ BU.hom ≫ fU = (pullback.fst _ _ ≫ BV.hom) ≫ fV) :
    pullback.lift b (pullback.fst _ _ ≫ BU.hom) h₁ ≫ pullback.lift b' (pullback.fst _ _ ≫ BV.hom) h₂ =
      𝟙 _ := by
  rw [← cancel_epi (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV)), Category.comp_id]
  have k1 : pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV) ≫ b = toV fU fV A BU qU ≫ qV.left :=
    cb _ (pullback.fst _ _) (toV fU fV A BU qU) _ (toV_fst fU fV A BU qU).symm pullback.condition.symm
      (toV_snd fU fV A BU qU).symm
  have k2 := cb' _ (toV fU fV A BU qU) (pullback.fst _ _)
    (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV) ≫ pullback.lift b (pullback.fst _ _ ≫ BU.hom) h₁)
    (toV_fst fU fV A BU qU) (by rw [Category.assoc, pullback.lift_fst, k1])
    (by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← pullback.condition, Category.assoc,
      w_left fU A BU qU])
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc, k2, pullback.condition]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc (pullback.lift b _ _),
      pullback.lift_fst, hb]

theorem isPullback_trans {S U V : Scheme.{0}} (fU : U ⟶ S) (fV : V ⟶ S) (A : Over S)
    (BU : Over U) (BV : Over V) (qU : (Over.pullback fU).obj A ⟶ BU) (qV : (Over.pullback fV).obj A ⟶ BV)
    [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    [Flat qV.left] [Surjective qV.left] [QuasiCompact qV.left]
    (b : pullback (BU.hom ≫ fU) fV ⟶ BV.left) (b' : pullback (BV.hom ≫ fV) fU ⟶ BU.left)
    (hb : b ≫ BV.hom = pullback.snd _ _) (hb' : b' ≫ BU.hom = pullback.snd _ _)
    (cb : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fU) (z : T ⟶ pullback A.hom fV)
        (w : T ⟶ pullback (BU.hom ≫ fU) fV), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qU.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ qV.left)
    (cb' : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fV) (z : T ⟶ pullback A.hom fU)
        (w : T ⟶ pullback (BV.hom ≫ fV) fU), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qV.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b' = z ≫ qU.left) :
    IsPullback b (pullback.fst _ _ ≫ BU.hom) (BV.hom ≫ fV) fU := by
  have h₁ : b ≫ BV.hom ≫ fV = (pullback.fst _ _ ≫ BU.hom) ≫ fU := by
    rw [reassoc_of% hb, Category.assoc]; exact pullback.condition.symm
  have h₂ : b' ≫ BU.hom ≫ fU = (pullback.fst _ _ ≫ BV.hom) ≫ fV := by
    rw [reassoc_of% hb', Category.assoc]; exact pullback.condition.symm
  let e : pullback (BU.hom ≫ fU) fV ≅ pullback (BV.hom ≫ fV) fU :=
    { hom := pullback.lift b (pullback.fst _ _ ≫ BU.hom) h₁
      inv := pullback.lift b' (pullback.fst _ _ ≫ BV.hom) h₂
      hom_inv_id := lift_comp_lift fU fV A BU BV qU qV b b' hb cb cb' h₁ h₂
      inv_hom_id := lift_comp_lift fV fU A BV BU qV qU b' b hb' cb' cb h₂ h₁ }
  exact IsPullback.of_iso_pullback ⟨h₁⟩ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem exists_transition : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) →
    ∃ b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left,
      (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) ∧
      (∀ j k, IsPullback (b j k) (pullback.fst _ _ ≫ (B j).hom) ((B k).hom ≫ 𝒰.f k) (𝒰.f j)) ∧
      ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left := by
  intro S 𝒰 A H _ _ i B q hf hs hqc hpb
  have key : ∀ j k, ∃ b : pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left,
      b ≫ (B k).hom = pullback.snd _ _ ∧
      ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ (q k).left := fun j k => by
    haveI := hf j; haveI := hs j; haveI := hqc j
    exact exists_trans (𝒰.f j) (𝒰.f k) A (B j) (B k) (q j) (q k) H i (hpb j) (hpb k)
  choose b hb1 hb3 using key
  refine ⟨b, hb1, fun j k => ?_, hb3⟩
  haveI := hf j; haveI := hs j; haveI := hqc j
  haveI := hf k; haveI := hs k; haveI := hqc k
  exact isPullback_trans (𝒰.f j) (𝒰.f k) A (B j) (B k) (q j) (q k) (b j k) (b k j) (hb1 j k) (hb1 k j)
    (hb3 j k) (hb3 k j)

end QuotTransition
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensEtaleGenericallyFiniteDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GenEtale

theorem exists_opens_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hd
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have : IsProper π := IsProper.of_comp π p
  have := hp.isLocallyNoetherian
  have := hp.charZero
  obtain ⟨U, -, hU, hxU, hW, -, hE, -⟩ :=
    GlobalTheory.GenFiniteEtale.exists_finite_etale_of_isProper π hη hd ⊤ (Opens.mem_top _)
  refine ⟨π ⁻¹ᵁ U, ⟨genericPoint Y, show π _ ∈ U from hη ▸ hxU⟩, ?_⟩
  have : IsAffine U := hU
  have : IsAffine (π ⁻¹ᵁ U) := hW
  have hE' : ∀ U' : X.Opens, U' = U → (π.app U').hom.Etale := by
    rintro _ rfl
    exact hE
  have e : U.ι ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have h1 : Etale (π ∣_ U) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
    exact (RingHom.Etale.respectsIso).cancel_right_isIso _ _ |>.2 (hE' _ e)
  rw [← morphismRestrict_ι]
  infer_instance

end GlobalTheory.GenEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductSchwartzGlue
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

namespace GlobalTheory.ThK.EvAt0.SchwartzProd


open scoped Classical in
theorem exists_prod : ∀ {F : Type} [Field F] [NumberField F] {n d d₁ : ℕ} (h : d = d₁ + 2) (G : SInf F (Fin n × Fin 2))
    (f : SInf F (Fin n × Fin d₁)), ∃ g : SInf F (Fin n × Fin d), ∀ y,
      g y = G (fun p => y ((idx h).symm (Sum.inr p))) * f (fun q => y ((idx h).symm (Sum.inl q))) := by
  intro F _ _ n d d₁ h G f
  obtain ⟨b, hb⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box f G
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n × Fin d => mixedEmbedding.mixedSpace F)
      (idx h).symm).symm b, fun y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hb, mul_comm]
  rfl

end GlobalTheory.ThK.EvAt0.SchwartzProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPtOfMemConeOfIsAlgClosed
section
set_option autoImplicit false
noncomputable section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
open GlobalTheory.CompHt

namespace GlobalTheory.ConeOnto

theorem exists_pt_of_mem_cone_of_isAlgClosed : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosed K] (y : Fin S.N → K), y ≠ 0 → (∀ g ∈ S.imageIdeal, aeval y g = 0) → ∃ (x : S.Pt K) (c : K), c ≠ 0 ∧ S.coords x.1 = c • y := by
  intro F _ S hS hb K _ _ _ y hy hI
  classical
  by_contra hno
  push_neg at hno
  have hT : (S.baseChange K).IsVariety := hS.baseChange K
  have hbT : (S.baseChange K).BasePointFree := hb.baseChange K
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hy
  change y i₀ ≠ 0 at hi₀
  let u : Fin S.N → Fin S.N → K := fun j => y i₀ • Pi.single j 1 - y j • Pi.single i₀ 1
  have hu : ∀ (j : Fin S.N) (c : Fin S.N → K), ∑ l, u j l * c l = y i₀ * c j - y j * c i₀ := fun j c => by
    simp [u, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, mul_assoc]

  have hcov : ∀ z : (S.baseChange K).Y, ∃ j, z ∈ nonzeroLocus ((S.baseChange K).comb (u j)) := by
    by_contra hc
    push_neg at hc
    obtain ⟨z, hz⟩ := hc
    have := hT.smooth
    have : Smooth (S.baseChange K).str := SmoothOfRelativeDimension.smooth (S.baseChange K).D _
    have hZ : IsClosed (⋂ j, ((nonzeroLocus ((S.baseChange K).comb (u j)) : Set (S.baseChange K).Y)ᶜ)) :=
      isClosed_iInter fun j => (nonzeroLocus ((S.baseChange K).comb (u j))).isOpen.isClosed_compl
    obtain ⟨a, ha, haZ⟩ := GlobalTheory.ConeOnto.exists_rat_pt (S.baseChange K).str hZ.isLocallyClosed
      (x := z) (Set.mem_iInter.2 hz)
    let xa : (S.baseChange K).Pt K := ⟨a, ha.trans (Spec.map_id _).symm⟩
    have hbase : (S.baseChange K).baseHom a = RingHom.id K := LinSys.baseHom_ptOver xa
    have hv : ∀ j, y i₀ * (S.baseChange K).coords a j - y j * (S.baseChange K).coords a i₀ = 0 := fun j => by
      have h0 := Set.mem_iInter.1 (haZ (IsLocalRing.closedPoint K)) j
      have h1 : (S.baseChange K).val a ((S.baseChange K).comb (u j)) = 0 :=
        not_not.1 fun h => h0 (((S.baseChange K).val_ne_zero_iff a _).1 h)
      have h2 := ((S.baseChange K).val_comb a (u j)).symm.trans h1
      rw [hbase] at h2
      simp only [RingHom.id_apply] at h2
      exact (hu j ((S.baseChange K).coords a)).symm.trans h2
    have hc0 : (S.baseChange K).coords a i₀ ≠ 0 := fun h0 => hbT.coords_ne_zero a (funext fun j => by
      have := hv j
      rw [h0, mul_zero, sub_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hi₀)
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange K a
    refine hno (LinSys.toBase xa) (c⁻¹ * ((S.baseChange K).coords a i₀ / y i₀))
      (mul_ne_zero (inv_ne_zero hc) (div_ne_zero hc0 hi₀)) (funext fun j => ?_)
    have ej := congrFun e j
    have hvj := hv j
    change S.coords (a ≫ S.bcFst K) j = _
    simp only [Pi.smul_apply, smul_eq_mul] at ej ⊢
    have e1 : S.coords (a ≫ S.bcFst K) j = c⁻¹ * (S.baseChange K).coords a j := by
      rw [ej, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have e2 : (S.baseChange K).coords a j = (S.baseChange K).coords a i₀ / y i₀ * y j := by
      field_simp
      linear_combination hvj
    rw [e1, e2]
    ring

  have hX : (X i₀ : MvPolynomial (Fin (S.baseChange K).N) K).IsHomogeneous 1 := isHomogeneous_X K i₀
  obtain ⟨m, A, hA, hrel⟩ := GlobalTheory.SecIntegral.exists_integral_relation K (S.baseChange K) hT S.N 1 u
    ((S.baseChange K).form hX) hcov
  let σ : Fin S.N → MvPolynomial (Fin S.N) K := fun i => ∑ j, C (u i j) * X j
  have hσ : ∀ i, (σ i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_C (Fin S.N) (u i j)).mul (isHomogeneous_X K j)
  let G : MvPolynomial (Fin S.N) K := X i₀ ^ m + ∑ k : Fin m, bind₁ σ (A k) * X i₀ ^ (k : ℕ)
  have hG : G.IsHomogeneous m := by
    refine (isHomogeneous_X_pow i₀ m).add (IsHomogeneous.sum _ _ _ fun k _ => ?_)
    have h1 : (bind₁ σ (A k)).IsHomogeneous (1 * (1 * (m - k))) :=
      (hA k).eval₂ C σ (fun r => isHomogeneous_C _ r) hσ
    have h2 := h1.mul (isHomogeneous_X_pow i₀ (k : ℕ))
    have e : 1 * (1 * (m - (k : ℕ))) + k = m := by omega
    rwa [e] at h2

  haveI := HeightExists.isIntegral hT
  obtain ⟨Ω, _, _, xg, hxg, -⟩ := HeightExists.exists_generic hT
  have hmem : G ∈ (S.baseChange K).imageIdeal := by
    rw [imageIdeal_eq_coneIdeal_of_generic K Ω _ xg hxg 1 _ one_ne_zero (one_smul _ _).symm]
    refine (mem_coneIdeal_of_isHomogeneous (K := K) (N := S.N) _ hG).2 ?_
    have h := hrel Ω xg
    rw [LinSys.powVal_form, LinSys.baseHom_ptOver] at h
    erw [eval₂_X] at h
    let cg : Fin S.N → Ω := (S.baseChange K).coords xg.1
    have h' : cg i₀ ^ m + ∑ k : Fin m, aeval (fun i : Fin S.N => ∑ j : Fin S.N, algebraMap K Ω (u i j) * cg j) (A k) *
        cg i₀ ^ (k : ℕ) = 0 := h
    show aeval cg G = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, σ, map_add (f := _), map_pow, map_sum, map_mul, aeval_X, aeval_bind₁, aeval_C]
    exact h'

  rw [← HeightExists.map_imageIdeal hS K] at hmem
  have hker : S.imageIdeal.map (MvPolynomial.map (algebraMap F K)) ≤ RingHom.ker (eval y) :=
    Ideal.map_le_iff_le_comap.2 fun g hg => by
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.eval_map, ← aeval_def]
      exact hI g hg
  have h0 : eval y G = 0 := hker hmem
  have hA0 : ∀ k : Fin m, eval y (bind₁ σ (A k)) = 0 := fun k => by
    show aeval y (bind₁ σ (A k)) = 0
    rw [aeval_bind₁]
    have e : (fun i => aeval y (σ i)) = 0 := funext fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [σ, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, Pi.zero_apply]
      rw [hu i y]
      ring
    rw [e, aeval_zero, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
    exact (hA k).coeff_eq_zero (d := 0) (by simp; omega)
  have h3 : eval y G = y i₀ ^ m := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, map_add (f := _), map_pow, map_sum, map_mul, eval_X, hA0, zero_mul, Finset.sum_const_zero, add_zero]
  exact pow_ne_zero m hi₀ (h3.symm.trans h0)

end GlobalTheory.ConeOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RegCoverExists

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
private theorem isSeparated_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c) := by
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
    show IsAffine (Spec (CommRingCat.of R)); infer_instance
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') := by
    show IsAffine (Spec (CommRingCat.of R')); infer_instance
  infer_instance


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
theorem _root_.GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    {Y : Scheme.{0}} {f : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (f ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f := by
  obtain ⟨N, i, hi, hif⟩ := h
  have hP := _root_.GlobalTheory.ProjSpace.isPullback_baseChange N c
  haveI := isSeparated_spMap c
  haveI : IsSeparated (_root_.GlobalTheory.ProjSpace.baseChange N c) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  refine ⟨N, hP.lift i f hif, ?_, hP.lift_snd _ _ _⟩
  haveI : IsClosedImmersion (hP.lift i f hif ≫ _root_.GlobalTheory.ProjSpace.baseChange N c) := by
    rw [hP.lift_fst]; exact hi
  exact IsClosedImmersion.of_comp _ (_root_.GlobalTheory.ProjSpace.baseChange N c)

end GlobalTheory.RegCoverExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureChangeFramedGeometricPointUniqueStatement
section
open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelStructureChange_framedGeometricPoint_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k) (γ γ' : Gam Dw l), levR (lift γ, LinearMap.id) y y' → levR (lift γ', LinearMap.id) y y' → γ = γ' := by
  first | exact @GlobalTheory.LevelFree.move_unique | exact GlobalTheory.LevelFree.move_unique | (intros; apply GlobalTheory.LevelFree.move_unique <;> assumption)
end

