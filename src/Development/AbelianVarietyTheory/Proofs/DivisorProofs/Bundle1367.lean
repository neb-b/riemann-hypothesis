module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffOneRealOfIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismFiniteOfGeometricFibres
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbEnd

theorem isFinite_of_isFinite_geomFibres :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  intro S A _ hA φ hgeo
  haveI : IsProper A.hom := hA.proper
  haveI : IsProper (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  haveI : IsProper φ.left := IsProper.of_comp φ.left A.hom
  haveI : LocallyQuasiFinite φ.left := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton φ.left fun y => ?_
    let K := AlgebraicClosure (A.left.residueField y)
    let u : Spec (CommRingCat.of K) ⟶ A.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (A.left.residueField y) K)) ≫
        A.left.fromSpecResidueField y
    let t := u ≫ A.hom
    haveI := hgeo K t
    let φ' := ((Over.pullback t).map φ).left
    let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
    have hup : u p = y := Scheme.fromSpecResidueField_apply y _
    let v : Spec (CommRingCat.of K) ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
    refine ((φ'.finite_preimage_singleton (v p)).image (pullback.fst A.hom t)).subset fun x hx => ?_
    have hx' : φ.left x = u p := by rw [hup]; exact hx
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := u) x p hx'
    let m : pullback φ.left u ⟶ pullback A.hom t :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
        rw [← Over.w φ, ← Category.assoc, pullback.condition, Category.assoc])
    have hm1 : m ≫ pullback.fst A.hom t = pullback.fst _ _ := pullback.lift_fst _ _ _
    have hφ1 : φ' ≫ pullback.fst A.hom t = pullback.fst A.hom t ≫ φ.left :=
      (GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ).w.symm
    have hφ2 : φ' ≫ pullback.snd A.hom t = pullback.snd A.hom t := pullback.lift_snd _ _ _
    have hmv : m ≫ φ' = pullback.snd φ.left u ≫ v := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφ1, ← Category.assoc, hm1, Category.assoc, pullback.lift_fst, pullback.condition]
      · rw [Category.assoc, hφ2, pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    refine ⟨m w, ?_, ?_⟩
    · change φ' (m w) = v p
      rw [← Scheme.Hom.comp_apply, hmv, Scheme.Hom.comp_apply, hw2]
    · rw [← Scheme.Hom.comp_apply, hm1, hw1]
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ.left

end GlobalTheory.AbEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem smoothOfRelativeDimension_sq {R : Type} [CommRing R] {A : Over (Sp R)} {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom A.hom).flip hg
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g g _ _

theorem basic_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ CohomZeroIsConstants (OAff A.hom) ∧
      IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  intro R _ A _ g hA hg
  have hs : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  refine ⟨_root_.GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj R A hs, ?_, AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA, smoothOfRelativeDimension_sq hg⟩
  have hsq : IsPullback (𝟙 A.left) A.hom A.hom (spMap (algebraMap R R)) := by
    rw [Algebra.algebraMap_self, spMap_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact _root_.GlobalTheory.AbCoh.uConst_of_isAbelianScheme R A hA R A.left A.hom (𝟙 _) hsq

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometric
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRigid

theorem eq_one_of_geometric (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (T : Over S) (x : T ⟶ A) (c : ℕ) (hc : IsUnit (c : Γ(T.left, ⊤)))
    (hx : x ^ c = 1)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S)
      (g : Over.mk z ⟶ T), g ≫ x = 1) : x = 1 := by
  have := hA.smooth
  let AT := (Over.pullback T.hom).obj A
  have hft : LocallyOfFiniteType AT.hom := by
    change LocallyOfFiniteType (pullback.snd A.hom T.hom); infer_instance
  let f := ((Over.pullback T.hom).map (mulN A c)).left
  have hfu : FormallyUnramified f := by
    have h := GlobalTheory.GrpTangent.formallyUnramified_mulN AT hc
    rw [← GlobalTheory.GrpTangent.pullback_map_mulN] at h
    exact h
  have hff : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ AT.hom) := by
      rw [show f ≫ AT.hom = AT.hom from Over.w ((Over.pullback T.hom).map (mulN A c))]
      infer_instance
    exact locallyOfFiniteType_of_comp f AT.hom
  let sec : (T ⟶ A) → (T.left ⟶ AT.left) := fun y =>
    pullback.lift y.left (𝟙 T.left) (by rw [Over.w y, Category.id_comp])
  have sec_fst : ∀ y : T ⟶ A, sec y ≫ pullback.fst A.hom T.hom = y.left := fun y =>
    pullback.lift_fst _ _ _
  have sec_snd : ∀ y : T ⟶ A, sec y ≫ pullback.snd A.hom T.hom = 𝟙 _ := fun y =>
    pullback.lift_snd _ _ _
  have f_fst : f ≫ pullback.fst A.hom T.hom = pullback.fst A.hom T.hom ≫ (mulN A c).left :=
    pullback.lift_fst _ _ _
  have f_snd : f ≫ pullback.snd A.hom T.hom = pullback.snd A.hom T.hom :=
    pullback.lift_snd _ _ _
  have sec_f : ∀ y : T ⟶ A, sec y ≫ f = sec (y ^ c) := by
    intro y
    apply pullback.hom_ext
    · rw [Category.assoc, f_fst, ← Category.assoc, sec_fst, sec_fst,
        ← GlobalTheory.GrpTangent.comp_mulN]
      rfl
    · rw [Category.assoc, f_snd, sec_snd, sec_snd]
  have key : sec x ≫ f = sec 1 ≫ f := by rw [sec_f, sec_f, hx, one_pow]
  let Y : Over AT.left := Over.mk f
  let X : Over AT.left := Over.mk (sec 1 ≫ f)
  let fx : X ⟶ Y := Over.homMk (sec x) key
  let f1 : X ⟶ Y := Over.homMk (sec 1) rfl
  haveI : LocallyOfFiniteType Y.hom := hff
  haveI : FormallyUnramified Y.hom := hfu
  have hpt : ∀ t : T.left, t ∈ Set.range (GlobalTheory.FinEt.agreeι fx f1) := by
    intro t
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point T.left t
    have hk : (c : k) ≠ 0 := (GlobalTheory.GrpTangent.isUnit_natCast_of_point hc a).ne_zero
    have h1 := H k hk (a ≫ T.hom) (Over.homMk a rfl)
    have h2 : a ≫ x.left = a ≫ (1 : T ⟶ A).left := by
      have := congrArg CommaMorphism.left
        (h1.trans (comp_one (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)).symm)
      exact this
    have h3 : a ≫ fx.left = a ≫ f1.left := by
      change a ≫ sec x = a ≫ sec 1
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, sec_fst, sec_fst, h2]
      · rw [Category.assoc, Category.assoc, sec_snd, sec_snd]
    have h4 := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 a).mp h3
    apply h4
    rw [ha]; rfl
  have hsec : sec x = sec 1 := by
    have := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 (𝟙 _)).mpr (by
      rintro _ ⟨t, rfl⟩; exact hpt _)
    simpa [fx, f1] using this
  ext1
  rw [← sec_fst x, hsec, sec_fst]

end GlobalTheory.TorsionRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblBox

open Formalism.IndefR.Datum

variable {D : D7} {S T : HSp D}

def top (w : WO S (GlobalTheory.Doubling.dblSp T)) : WO S T := w.submatrix (finSumFinEquiv ∘ Sum.inl) id

def bot (w : WO S (GlobalTheory.Doubling.dblSp T)) : WO S T := w.submatrix (finSumFinEquiv ∘ Sum.inr) id

def join (u v : WO S T) : WO S (GlobalTheory.Doubling.dblSp T) := (Matrix.fromRows u v).submatrix finSumFinEquiv.symm id

@[simp] theorem top_join (u v : WO S T) : top (join u v) = u := by
  ext i j
  simp only [top, join, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, id]

@[simp] theorem bot_join (u v : WO S T) : bot (join u v) = v := by
  ext i j
  simp only [bot, join, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr, id]

theorem join_top_bot (w : WO S (GlobalTheory.Doubling.dblSp T)) : join (top w) (bot w) = w := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp only [top, bot, join, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, id]

@[simp] theorem top_add (x y : WO S (GlobalTheory.Doubling.dblSp T)) : top (x + y) = top x + top y := rfl
@[simp] theorem bot_add (x y : WO S (GlobalTheory.Doubling.dblSp T)) : bot (x + y) = bot x + bot y := rfl

def box (f₁ f₂ : WO S T → ℂ) : WO S (GlobalTheory.Doubling.dblSp T) → ℂ := fun w => f₁ (top w) * star (f₂ (bot w))

theorem hO_dbl (x y : WO S (GlobalTheory.Doubling.dblSp T)) :
    hO S (GlobalTheory.Doubling.dblSp T) x y = hO S T (top x) (top y) - hO S T (bot x) (bot y) := by
  simp only [hO, GlobalTheory.Doubling.gram_hdbl, GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, map_zero, map_neg, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    top, bot, Function.comp_apply, id]
  simp only [neg_mul, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem symplO_dbl (x y : WO S (GlobalTheory.Doubling.dblSp T)) :
    symplO S (GlobalTheory.Doubling.dblSp T) x y = symplO S T (top x) (top y) - symplO S T (bot x) (bot y) := by
  simp only [symplO, hO_dbl, mul_sub, map_sub]

theorem symplOH_dbl (x y : WO S (GlobalTheory.Doubling.dblSp T)) :
    symplOH S (GlobalTheory.Doubling.dblSp T) x y = symplOH S T (top x) (top y) - symplOH S T (bot x) (bot y) := by
  simp only [symplOH, symplO_dbl, mul_sub]

def IsTopDiag (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)) : Prop :=
  Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1)

theorem top_actO {h : GA D T} {hd : GA D (GlobalTheory.Doubling.dblSp T)} (hh : IsTopDiag h hd) (g : GA D S)
    (w : WO S (GlobalTheory.Doubling.dblSp T)) : top (actO S (GlobalTheory.Doubling.dblSp T) g hd w) = actO S T g h (top w) := by
  ext i j
  simp only [top, actO, IsTopDiag] at hh ⊢
  rw [hh]
  simp only [Matrix.submatrix_apply, Function.comp_apply, id, Matrix.mul_apply, Matrix.reindex_apply,
    ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

theorem bot_actO {h : GA D T} {hd : GA D (GlobalTheory.Doubling.dblSp T)} (hh : IsTopDiag h hd) (g : GA D S)
    (w : WO S (GlobalTheory.Doubling.dblSp T)) : bot (actO S (GlobalTheory.Doubling.dblSp T) g hd w) = actO S T g 1 (bot w) := by
  ext i j
  simp only [bot, actO, IsTopDiag] at hh ⊢
  rw [hh]
  simp only [Matrix.submatrix_apply, Function.comp_apply, id, Matrix.mul_apply, Matrix.reindex_apply,
    ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  rw [show Formalism.L2.Theta.mt T 1 = 1 from rfl]

theorem actO_one_one (w : WO S T) : actO S T 1 1 w = w := by
  simp only [actO, inv_one, show Formalism.L2.Theta.mt T 1 = 1 from rfl, show Formalism.L2.Theta.mt S 1 = 1 from rfl,
    Matrix.one_mul, Matrix.mul_one]

theorem psi_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (b : AF D.host.F) : ψ (-b) = star (ψ b) := by
  have h1 : ψ (-b) * ψ b = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 := GlobalTheory.ThetaSchur.mul_star_psi hψ b
  linear_combination (-ψ (-b)) * h2 + star (ψ b) * h1

theorem heisO_box {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (w : WO S (GlobalTheory.Doubling.dblSp T))
    (f₁ f₂ : WO S T → ℂ) :
    heisO ψ S (GlobalTheory.Doubling.dblSp T) w (box f₁ f₂) = box (heisO ψ S T (top w) f₁) (heisO ψ S T (bot w) f₂) := by
  funext x
  simp only [heisO, box, symplOH_dbl, top_add, bot_add, sub_eq_add_neg, AddChar.map_add_eq_mul, psi_neg hψ, star_mul']
  ring

end GlobalTheory.DblBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivMapsOpenFiniteSubgroupToOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.WeilAdm

theorem fintrans_cont (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) :
    Continuous B :=
  IsModuleTopology.continuous_of_linearMap B.toLinearMap

def finIdem (F : Type) [Field F] [NumberField F] : AdeleRing (𝓞 F) F := (0, 1)

theorem finIdem_mul (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) :
    finIdem F * a = (0, a.2) := by
  change ((0 : InfiniteAdeleRing F) * a.1, (1 : FiniteAdeleRing (𝓞 F) F) * a.2) = _
  rw [zero_mul, one_mul]

theorem finiteAdelesVecPairAsAdeles_eq_idempotent_smul (F : Type) [Field F] [NumberField F] (κ : Type)
    (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    finE2 F m = finIdem F • finE2 F m := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change _ = finIdem F * (show AdeleRing (𝓞 F) F from (0, m.1 i)); rw [finIdem_mul]; rfl
  · change _ = finIdem F * (show AdeleRing (𝓞 F) F from (0, m.2 i)); rw [finIdem_mul]; rfl

theorem finiteAdeleIdempotent_smul_eq_finiteAdelesVecPair (F : Type) [Field F] [NumberField F] (κ : Type)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    finIdem F • w = finE2 F (fun i => (w.1 i).2, fun i => (w.2 i).2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change finIdem F * w.1 i = _; rw [finIdem_mul]; rfl
  · change finIdem F * w.2 i = _; rw [finIdem_mul]; rfl

theorem finiteAdelesVecPairAsAdeles_add (F : Type) [Field F] [NumberField F] (κ : Type)
    (a b : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    finE2 F (a + b) = finE2 F a + finE2 F b := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change ((0 : InfiniteAdeleRing F), a.1 i + b.1 i) = ((0 : InfiniteAdeleRing F) + 0, a.1 i + b.1 i)
    rw [add_zero]
  · change ((0 : InfiniteAdeleRing F), a.2 i + b.2 i) = ((0 : InfiniteAdeleRing F) + 0, a.2 i + b.2 i)
    rw [add_zero]

theorem finiteAdelesVecPairAsAdeles_zero (F : Type) [Field F] [NumberField F] (κ : Type) :
    finE2 F (0 : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rfl

theorem fintrans : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) →
      ∃ M' : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M' : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m' ∈ M', ∃ m ∈ M, B (GlobalTheory.WeilAdm.finE2 F m) = GlobalTheory.WeilAdm.finE2 F m' := by
  intro F _ _ κ _ B M hM
  let g : ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) →+
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
    { toFun := fun m' => (fun i => ((B.symm (finE2 F m')).1 i).2, fun i => ((B.symm (finE2 F m')).2 i).2)
      map_zero' := by
        simp only [finiteAdelesVecPairAsAdeles_zero, map_zero]; rfl
      map_add' := fun a b => by
        simp only [finiteAdelesVecPairAsAdeles_add, map_add (f := _)]; rfl }
  have hg : ∀ m', finE2 F (g m') = B.symm (finE2 F m') := by
    intro m'
    rw [finiteAdelesVecPairAsAdeles_eq_idempotent_smul F κ m', map_smul, finiteAdeleIdempotent_smul_eq_finiteAdelesVecPair]
    rfl
  have hgc : Continuous g := by
    have h1 : Continuous fun m' : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) => B.symm (finE2 F m') := by
      refine (fintrans_cont F κ B.symm).comp ?_
      refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
      · exact continuous_const.prodMk ((continuous_apply i).comp continuous_fst)
      · exact continuous_const.prodMk ((continuous_apply i).comp continuous_snd)
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
    · exact continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp h1))
    · exact continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp h1))
  refine ⟨M.comap g, hM.preimage hgc, fun m' hm' => ⟨g m', hm', ?_⟩⟩
  rw [hg, LinearEquiv.apply_symm_apply]

end GlobalTheory.WeilAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSetStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_quotient_compact_fundamental_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : Set (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsCompact K ∧ ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  first | exact @GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | exact GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | (intros; apply GlobalTheory.AdeleCocompactExt.exists_compact_adeleE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesRationalSurjectiveOfCM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
    ∀ y z : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  intro F E _ _ _ _ _ nS nT N e hrat y z
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  let I : Matrix (Fin nT) (Fin nS) E →ₗ[F] Formalism.IndefR.DatumF.WOF F E nS nT :=
    (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
  have hI : ∀ x, I x = Formalism.IndefR.DatumF.ratWF x := fun x => rfl
  let L : Matrix (Fin nT) (Fin nS) E →ₗ[F] GlobalTheory.ThetaTransform.VA F N := (e.toLinearMap.restrictScalars F).comp I
  have hL : ∀ x, L x = e (Formalism.IndefR.DatumF.ratWF x) := fun x => by rw [← hI]; rfl
  let r : (Fin N → F) →ₗ[F] (Fin N → AF F) :=
    LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
  let R : ((Fin N → F) × (Fin N → F)) →ₗ[F] GlobalTheory.ThetaTransform.VA F N := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin nT) * Fintype.card (Fin nS) * Module.finrank F E = N + N := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h1
    exact h1
  have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fin_fun, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittaker
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem bad_part_le_locShare : ∀ (D : D7) (Γ V : Type) [Group Γ] [Finite Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G0g D.nd) (ι : G0g D.nd →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D P lam ψ → ∀ (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup (G0g D.nd)), (∀ k, IsHalf D k (H k)) → ∀ (n : Fin 2 → ℕ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → ∀ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) → ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) : ℝ) ≤ c * (locShare D (fun k _ => eUk D k (ψ₀ k)) 0 (S 0) + locShare D (fun k _ => eUk D k (ψ₀ k)) 1 (S 1)) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  intro D Γ V _ _ _ _ _ π ι hs ρ P lam ψ hW lamb hlamb H hH n c hemb hn ψ₀ hψ₀
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  haveI : Finite (G0g D.nd) := Finite.of_injective ι (fun a b h => by
    have := congrArg π h; rwa [hs.1, hs.1] at this)
  letI : Fintype (G0g D.nd) := Fintype.ofFinite _
  obtain ⟨S, hbad, hsplit⟩ := GlobalTheory.T.one_sub_goodIdempotent_eq_badTupleSums D
  have hloc : ∀ k, locShare D (fun k' v => eUk D k' (ψ ⟨k', v⟩)) k (S k) =
      locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k) := by
    intro k
    unfold locShare
    refine Finset.sum_congr rfl fun t _ => Finset.prod_congr rfl fun v _ => ?_
    exact _root_.GlobalTheory.BadCount.wtOf_eUk_indep D k _ _ (hW.1 ⟨k, v⟩) (hψ₀ k) (t v)
  refine ⟨S, hbad, ?_⟩
  have key := _root_.GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit (G0g D.nd) Γ V π ι hs ρ P lam lamb hlamb H n D.ntypes.e0
    (fun k => badElt D k (S k)) (fun k => locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k)) c hemb hn
    (fun k => (GlobalTheory.BadCount.IdemCen.badElt_idem_central D k (S k)).1)
    (fun k a => (GlobalTheory.BadCount.IdemCen.badElt_idem_central D k (S k)).2 a)
    (by simpa using hsplit)
    (fun k g hg => (GlobalTheory.BadCount.badElt_mul_lvlIdem D P lam ψ hW k (S k) (H k) (hH k)).1 g hg)
    (fun k => by rw [← hloc k]; exact (GlobalTheory.BadCount.badElt_mul_lvlIdem D P lam ψ hW k (S k) (H k) (hH k)).2)
  simpa using key

end GlobalTheory.BadCount
end

