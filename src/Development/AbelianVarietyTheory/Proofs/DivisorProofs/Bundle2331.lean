module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealMulConjEqGramDetSelfDual
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDefiniteLieIndexIdealEqNormIdeal
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCM.IdealZero

theorem idealSt_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det} ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          GlobalTheory.FlatCM.idx K p (FB.eigLat X.B.t.act τ) (GlobalTheory.FlatCM.subP FP FB MP τ) = 𝔫.map τ := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hg
  obtain ⟨Λ, hfg, hstd, hdual, hdesc⟩ := _root_.GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan E H hH K ρ σ₁ p X gP gQ hg
  have hbinj : Function.Injective ((algebraMap (𝓞 E) E).comp (H.bar : 𝓞 E →+* 𝓞 E)) :=
    (RingOfIntegers.coe_injective (K := E)).comp (GlobalTheory.CM.ringOfIntegers_hom_injective _)
  let barE : E →+* E := IsFractionRing.lift hbinj
  have hbarE : ∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E) := fun x => IsFractionRing.lift_algebraMap hbinj x
  refine ⟨_, _root_.GlobalTheory.SelfDualIndex.idx_mul_map_bar_eq E _ barE hbarE p gP Λ hfg hstd (hdual barE hbarE), ?_⟩
  intro FP FB MP hMP τ hτ
  have hτinj : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective (K := K)).comp (GlobalTheory.CM.ringOfIntegers_hom_injective _)
  let τE : E →+* K := IsFractionRing.lift hτinj
  have hτE : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K) := fun x => IsFractionRing.lift_algebraMap hτinj x
  classical
  let FA : ∀ b, GenFib (X.A b).pol := fun b => match b with
    | true => FP
    | false => (GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K (X.A false).pol).some
  let M : ∀ k : Fin p ⊕ Fin 0, (Fin (FA k.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K) := fun k => match k with
    | .inl a => MP a
    | .inr a => a.elim0
  obtain ⟨-, -, hinj, hind, -⟩ :=
    GlobalTheory.CM.Indep.letters_independent GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 E H K ρ σ₁ p 0 X FA FB M
      (fun k => match k with
        | .inl a => hMP a
        | .inr a => a.elim0)
  have hfgA : (FP.eigLat (X.A true).t.act τ).FG :=
    Submodule.FG.of_le (LieLattice.lieLat_fg_and_span_eq_top K _ FP).1
      (Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩)
  have hrk : latRank K (FP.eigLat (X.A true).t.act τ) = 1 := by
    rw [(GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ (X.A true) FP 1 0 X.split X.typeP X.ρ_sq).1 τ, if_pos hτ]
  rw [subP, hdesc FP FB MP hMP τ hτ τE hτE]
  exact _root_.GlobalTheory.IdxTensor.idx_image_eq_map E K τ τE hτE p _ _ _ MP Λ hfgA hrk (fun a => hinj (.inl a))
    (iSupIndep.comp hind (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin 0), τ)) fun a b e => by simpa using e)
    hfg hstd

end GlobalTheory.FlatCM.IdealZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpFormEqZeroOfPullbackVanishing
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.CechDR KaehlerDifferential
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtVanish

section Affine

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
variable {A R' : Type} [CommRing A] [Algebra R A] [CommRing R'] [Algebra R R'] [Algebra A R']
  [IsScalarTower R A R']

def nbdMap (l : Ω[A⁄R] →ₗ[A] R') : TrivSqZeroExt A Ω[A⁄R] →ₐ[R] TrivSqZeroExt R' R' :=
  { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap A R' c.fst) + TrivSqZeroExt.inr (l c.snd)
    map_one' := by ext <;> simp
    map_zero' := by ext <;> simp
    map_add' := fun a b ↦ by ext <;> simp <;> ring
    map_mul' := fun a b ↦ by
      have hop : ∀ (b : A) (ω : Ω[A⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, hop, map_add (f := _), map_smul, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul, Algebra.smul_def]
        simp [MulOpposite.smul_eq_mul_unop]
        ring
    commutes' := fun r ↦ by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply] }

theorem snd_nbdMap (l : Ω[A⁄R] →ₗ[A] R') (c : TrivSqZeroExt A Ω[A⁄R]) :
    (nbdMap l c).snd = l c.snd := by
  simp [nbdMap]

theorem fst_nbdMap (l : Ω[A⁄R] →ₗ[A] R') (c : TrivSqZeroExt A Ω[A⁄R]) :
    (nbdMap l c).fst = algebraMap A R' c.fst := by
  simp [nbdMap]

theorem snd_val_affine_eq (U : X.affineOpens) [Algebra (Sec s U.1) R'] [IsScalarTower R (Sec s U.1) R']
    (l : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] R') (y : Sp (TrivSqZeroExt R' R') ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : spMap ((nbdMap l).comp (diagSec R (Sec s U.1)) : Sec s U.1 →+* TrivSqZeroExt R' R') ≫
      affPt s U = y) (f : Form s) :
    TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) =
      l (connForm f.1 (affPt s U) (affPt_w s U)) := by
  have hx := affPt_w s U
  let Φ := nbdMap (R := R) l
  let α : Sec s U.1 →ₐ[R] TrivSqZeroExt R' R' := Φ.comp (diagSec R (Sec s U.1))
  let α₀ : Sec s U.1 →ₐ[R] R' := (TrivSqZeroExt.fstHom R R' R').comp α
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R R' R').π (Φ c) := fun c ↦ by
    change (Φ (diagSec R (Sec s U.1) c.fst)).fst = (Φ c).fst
    rw [fst_nbdMap, fst_nbdMap, fst_derSec]
  have e₀ : spMap (α₀ : Sec s U.1 →+* R') ≫ affPt s U =
      spMap ((SqExt.ofModule R R' R').π : TrivSqZeroExt R' R' →+* R') ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]; rfl
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R R' R') Φ α₀ hπ hx
    ((SqExt.ofModule R R' R').red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv R' _ ((SqExt.ofModule R R' R').red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt R' R') y hy :=
    Thick.trivHom α e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R R' R').secHom ((SqExt.ofModule R R' R').red_w hy)
    (SqExt.ofModule R R' R').i (SqExt.ofModule R R' R').π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext
      · change (Φ (diagSec R (Sec s U.1) c)).fst = (Φ (TrivSqZeroExt.inl c)).fst
        rw [fst_nbdMap, fst_nbdMap, fst_derSec, TrivSqZeroExt.fst_inl]
      · rw [TrivSqZeroExt.snd_inl, snd_nbdMap, TrivSqZeroExt.snd_inl, map_zero]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R R' R').idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl
    fun _ ↦ rfl
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = _
  rw [← map_sub, snd_nbdMap]
  rfl

end Affine

theorem tanVal_pull_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)}
    {B : Over (Sp R')} {φ : B.left ⟶ A.left}
    (m : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R') (B.hom ≫ 𝟙 _) (algebraMap R R') φ) (v' : epsR R' ⟶ B)
    (y : Sp (TrivSqZeroExt R' R') ⟶ A.left)
    (hy : y ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : v'.left ≫ φ = y) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v' (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) := by
  subst e
  let E := SqExt.ofModule R R' R'
  let E' := SqExt.dual R'
  have hy' := pt_w v'
  have hc : ∀ r : R, algebraMap R E.C r = algebraMap R' E'.C (algebraMap R R' r) := fun r ↦ by
    ext <;> simp [E, E', TrivSqZeroExt.algebraMap_eq_inl']
  have e₀ : spMap (RingHom.id R') ≫ spMap (E.π : E.C →+* E.B) ≫ v'.left ≫ φ =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v'.left) ≫ φ := by
    rw [Cris.spMap_id, Category.id_comp, Category.assoc]; rfl
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { RingHom.id E.C with commutes' := hc }
      φ₀ := RingHom.id R'
      comm := fun _ ↦ rfl
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun _ ha ↦ ha
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { RingHom.id E.C with commutes' := hc } (by
      change spMap (RingHom.id E.C) ≫ v'.left ≫ φ = v'.left ≫ φ
      rw [Cris.spMap_id, Category.id_comp])
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { RingHom.id R' with commutes' := fun _ ↦ rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ ↦ rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun _ ↦ rfl
  have k : E'.val v'.left hy' (m.pullForm f).1 = E.val (v'.left ≫ φ) hy f.1 :=
    (congrArg₂ (fun u v : E'.C ↦ u - v) k2 k1).trans (add_sub_add_right_eq_sub (G := E'.C) _ _ _)
  rw [tanVal_apply]
  exact congrArg (TrivSqZeroExt.snd (R := R')) k

theorem sec_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s)
    (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom :=
    HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h2 : RingHom.Smooth (secMap s U.1).hom :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact h2

end GlobalTheory.PtVanish

namespace GlobalTheory.PtVanish

theorem connForm_eq_zero {K : Type} [Field K] {X : Over (Sp K)} (hX : Smooth X.hom)
    (f : Form (X.hom ≫ 𝟙 (Sp K)))
    (H : ∀ (L : Type) [Field L] (σ : K →+* L), ∃ (X' : Over (Sp L)) (φ : X'.left ⟶ X.left)
      (m : IsMor (dp0 K) (X.hom ≫ 𝟙 (Sp K)) (dp0 L) (X'.hom ≫ 𝟙 (Sp L)) σ φ),
      IsPullback φ X'.hom X.hom (spMap σ) ∧ ∀ u : epsR L ⟶ X', tanVal u (m.pullForm f) = 0)
    (U : X.left.affineOpens) :
    connForm f.1 (affPt (X.hom ≫ 𝟙 (Sp K)) U) (affPt_w (X.hom ≫ 𝟙 (Sp K)) U) = 0 := by
  have hsm : Smooth (X.hom ≫ 𝟙 (Sp K)) := by rw [Category.comp_id]; exact hX
  haveI : Algebra.Smooth K (Sec (X.hom ≫ 𝟙 (Sp K)) U.1) := sec_smooth _ hsm U
  haveI : _root_.IsReduced (Sec (X.hom ≫ 𝟙 (Sp K)) U.1) :=
    _root_.GlobalTheory.isReduced_of_smooth_over_field K (Sec (X.hom ≫ 𝟙 (Sp K)) U.1)
  refine GlobalTheory.T.eq_zero_of_forall_residueField_functional' (Sec (X.hom ≫ 𝟙 (Sp K)) U.1) Ω[Sec (X.hom ≫ 𝟙 (Sp K)) U.1⁄K] _ ?_
  intro p _ l
  obtain ⟨X', φ, m, hpb, hv⟩ := H p.ResidueField (algebraMap K p.ResidueField)
  let α : Sec (X.hom ≫ 𝟙 (Sp K)) U.1 →ₐ[K] TrivSqZeroExt p.ResidueField p.ResidueField :=
    (nbdMap l).comp (diagSec K (Sec (X.hom ≫ 𝟙 (Sp K)) U.1))
  let y := spMap (α : Sec (X.hom ≫ 𝟙 (Sp K)) U.1 →+* TrivSqZeroExt p.ResidueField p.ResidueField) ≫
    affPt (X.hom ≫ 𝟙 (Sp K)) U
  have hy : y ≫ X.hom ≫ 𝟙 (Sp K) =
      spMap (algebraMap K (TrivSqZeroExt p.ResidueField p.ResidueField)) := by
    simp only [y, Category.assoc, affPt_w, ← Cris.spMap_comp, α.comp_algebraMap]
  have hcomp : (algebraMap p.ResidueField (DualNumber p.ResidueField)).comp
      (algebraMap K p.ResidueField) =
      algebraMap K (TrivSqZeroExt p.ResidueField p.ResidueField) :=
    RingHom.ext fun r ↦ by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']
  have w : y ≫ X.hom = spMap (algebraMap p.ResidueField (DualNumber p.ResidueField)) ≫
      spMap (algebraMap K p.ResidueField) := by
    rw [← Cris.spMap_comp, hcomp, ← hy, Category.comp_id]
  let u : epsR p.ResidueField ⟶ X' :=
    Over.homMk (hpb.lift y (spMap (algebraMap p.ResidueField (DualNumber p.ResidueField))) w)
      (hpb.lift_snd _ _ _)
  have e : u.left ≫ φ = y := hpb.lift_fst _ _ _
  have h := hv u
  rw [tanVal_pull_eq m u y hy e f, snd_val_affine_eq U l y hy rfl f] at h
  exact h

theorem cmpForm_eq_zero_of_tanVal : ∀ (K : Type) [Field K] (X : Over (Sp K)), Smooth X.hom → ∀ f : Form (X.hom ≫ 𝟙 (Sp K)), (∀ (L : Type) [Field L] (σ : K →+* L), ∃ (X' : Over (Sp L)) (φ : X'.left ⟶ X.left) (m : IsMor (dp0 K) (X.hom ≫ 𝟙 (Sp K)) (dp0 L) (X'.hom ≫ 𝟙 (Sp L)) σ φ), IsPullback φ X'.hom X.hom (spMap σ) ∧ ∀ u : epsR L ⟶ X', tanVal u (m.pullForm f) = 0) → GlobalTheory.CechDR.cmpForm (X.hom ≫ 𝟙 (Sp K)) f = 0 := by
  intro K _ X hX f H
  refine Subtype.ext (Subtype.ext (funext fun U ↦ ?_))
  exact (cmpForm_apply _ f U).trans (connForm_eq_zero hX f H U.unop)

end GlobalTheory.PtVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleDescends
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatDescent

def restrictR {R D A E : Type} [CommRing R] [CommRing D] [CommRing A] [CommRing E]
    [Algebra R D] [Algebra R A] [Algebra R E] [Algebra D A] [Algebra D E]
    (hA : ∀ r, algebraMap D A (algebraMap R D r) = algebraMap R A r)
    (hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r)
    (f : A →ₐ[D] E) : A →ₐ[R] E :=
  ⟨f.toRingHom, fun r => by
    show f (algebraMap R A r) = algebraMap R E r
    rw [← hA r, ← hE r]; exact f.commutes _⟩

theorem cocycle_descends : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D'), (ψ : D →+* D').FaithfullyFlat → ∀ (c : ∀ (E : Type) [CommRing E] [Algebra R E], (D' →ₐ[R] E) → (D' →ₐ[R] E) → E), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (α β : D' →ₐ[R] E) (ρ : E →ₐ[R] E'), α.comp ψ = β.comp ψ → c E' (ρ.comp α) (ρ.comp β) = ρ (c E α β)) → (∀ (E : Type) [CommRing E] [Algebra R E] (f₁ f₂ f₃ : D' →ₐ[R] E), f₁.comp ψ = f₂.comp ψ → f₂.comp ψ = f₃.comp ψ → c E f₁ f₃ = c E f₁ f₂ + c E f₂ f₃) → ∃ a : D', ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → c E α β = β a - α a := by
  intro R _ D D' _ _ _ _ ψ hψ c hnat hcoc
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  letI instRT : Algebra R (D' ⊗[D] D') :=
    ((algebraMap D (D' ⊗[D] D')).comp (algebraMap R D)).toAlgebra
  have h' : ∀ r, algebraMap D D' (algebraMap R D r) = algebraMap R D' r := fun r => ψ.commutes r
  have hT : ∀ r, algebraMap D (D' ⊗[D] D') (algebraMap R D r) = algebraMap R (D' ⊗[D] D') r :=
    fun _ => rfl
  let i₁ : D' →ₐ[R] D' ⊗[D] D' := restrictR h' hT Algebra.TensorProduct.includeLeft
  let i₂ : D' →ₐ[R] D' ⊗[D] D' := restrictR h' hT Algebra.TensorProduct.includeRight
  have h12 : i₁.comp ψ = i₂.comp ψ := by
    ext d
    exact ((Algebra.TensorProduct.includeLeft (R := D) (S := D) (A := D') (B := D')).commutes d).trans
      ((Algebra.TensorProduct.includeRight (R := D) (A := D') (B := D')).commutes d).symm
  obtain ⟨a, ha⟩ := GlobalTheory.AmitsurCohomologyH1.cocycle_is_coboundary D D' (c (D' ⊗[D] D') i₁ i₂) (by
    intro E _ _ f₁ f₂ f₃
    letI : Algebra R E := ((algebraMap D E).comp (algebraMap R D)).toAlgebra
    have hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r := fun _ => rfl
    have key : ∀ f g : D' →ₐ[D] E,
        Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _) (c (D' ⊗[D] D') i₁ i₂) =
          c E (restrictR h' hE f) (restrictR h' hE g) := by
      intro f g
      let ρ : D' ⊗[D] D' →ₐ[R] E :=
        restrictR hT hE (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _))
      have hn := hnat (D' ⊗[D] D') E i₁ i₂ ρ h12
      have e1 : ρ.comp i₁ = restrictR h' hE f := by
        ext x; simp [ρ, i₁, restrictR]
      have e2 : ρ.comp i₂ = restrictR h' hE g := by
        ext x; simp [ρ, i₂, restrictR]
      rw [e1, e2] at hn
      exact hn.symm
    have hc : ∀ f g : D' →ₐ[D] E, (restrictR h' hE f).comp ψ = (restrictR h' hE g).comp ψ := by
      intro f g; ext d
      exact (f.commutes d).trans (g.commutes d).symm
    rw [key, key, key]
    exact hcoc E _ _ _ (hc _ _) (hc _ _))
  refine ⟨a, ?_⟩
  intro E _ _ α β hαβ
  letI : Algebra D E := ((α.comp ψ : D →ₐ[R] E) : D →+* E).toAlgebra
  let α' : D' →ₐ[D] E := ⟨α.toRingHom, fun _ => rfl⟩
  let β' : D' →ₐ[D] E := ⟨β.toRingHom, fun d => by
    show β (ψ d) = α (ψ d)
    exact (DFunLike.congr_fun hαβ d).symm⟩
  have hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r := fun r => by
    show α (ψ _) = _
    rw [ψ.commutes, α.commutes]
  let ρ : D' ⊗[D] D' →ₐ[R] E :=
    restrictR hT hE (Algebra.TensorProduct.lift α' β' (fun _ _ ↦ Commute.all _ _))
  have hn := hnat (D' ⊗[D] D') E i₁ i₂ ρ h12
  have e1 : ρ.comp i₁ = α := by
    ext x; simp [ρ, i₁, α', restrictR]
  have e2 : ρ.comp i₂ = β := by
    ext x; simp [ρ, i₂, β', restrictR]
  rw [e1, e2] at hn
  rw [hn]
  show Algebra.TensorProduct.lift α' β' (fun _ _ ↦ Commute.all _ _) (c (D' ⊗[D] D') i₁ i₂) = _
  rw [ha]
  simp [α', β']

end GlobalTheory.FlatDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfIsPullDeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullUnif

theorem coordMap_of_isPullDeg {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V]
    [IsLocalRing V] {g : R →+* V} {D : DegPre R} {D' : DegPre V} (hD : IsPullDeg g D D') :
    CoordMap D D' g hD.xe.symm.toAddMonoidHom := by
  intro y r r' hr hr'
  have hr2 : PsiCoord D (hD.xe (hD.xe.symm y)) r := by rwa [AddEquiv.apply_symm_apply]
  obtain ⟨u, hu⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (hD.xe.symm y) r hr2
  have h1 : Associated (u * g r) r' := GlobalTheory.TorRef.psiCoord_associated hu hr'
  exact Associated.trans ⟨u, mul_comm _ _⟩ h1


set_option maxHeartbeats 1600000 in
theorem gtTorus_pull {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
    {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']
    {U : Unif (maximalIdeal R) D A G} {U' : Unif (maximalIdeal V) D' A' G'} {g : R →+* V}
    {bc : G' ≅ (Over.pullback (specOf g)).obj G} {hD : IsPullDeg g D.toPre D'.toPre}
    (H : IsPullUnif g hD bc U U')
    {κ : Type} [Field κ] {b : V →+* κ} (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0)
    (hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), (b.comp g) x = 0)
    {G₀ : Over (Sp κ)} [GrpObj G₀] {φ' : G₀.left ⟶ G'.left}
    (hp' : IsGrpPullback G₀ G' (spMap b) φ')
    (hp : IsGrpPullback G₀ G (spMap (b.comp g)) (φ' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g))) :
    GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hp' =
      GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb' hp := by
  obtain ⟨wL, -, he, -, Hs⟩ := (isPullUnif_iff_stalks R V _ _ g D D' hD A A' G G' bc U U').1 H
  obtain ⟨h, hf, ⟨hpG, hψ⟩, -⟩ := Hs 0
  obtain ⟨s, τ, hτ⟩ := GlobalTheory.PullLinear.exists_point (U.gt 0) (U'.gt 0) hpG (hψ 0).1 (𝟙 _)
  have : IsClosedImmersion (thick R (maximalIdeal R) 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have C1 : GlobalTheory.TorusPart.thickLift hb' hp = GlobalTheory.TorusPart.thickLift hb hp' ≫ h := by
    rw [← cancel_mono (pullback.fst G.hom (thick R (maximalIdeal R) 0)), GlobalTheory.TorusPart.thickLift_fst,
      Category.assoc]
    erw [hf]
    erw [← Category.assoc (GlobalTheory.TorusPart.thickLift hb hp'), GlobalTheory.TorusPart.thickLift_fst hb hp']
  have hτ' : (U'.gt 0).i.left ≫ h = τ.left ≫ (U.gt 0).i.left := by
    rw [← Over.comp_left, hτ, Category.id_comp]
  have key : GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left =
      (GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X := by
    have wA : (GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, ← Over.w (U.gt 0).i, ← Category.assoc τ.left, ← hτ', Category.assoc,
        ← Category.assoc _ (U'.gt 0).i.left]
      erw [← GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
      rw [Category.assoc, ← Category.assoc _ h, ← C1, (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp).1.w,
        ← Category.assoc, Over.w]
    have wB : ((GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w]
    have hchar : ∀ x' : D'.toPre.X, τ.left.appTop.hom (Rosenlicht.chi D.toPre.X (hD.xe x')) =
        Rosenlicht.chi D'.toPre.X x' := by
      intro x'
      apply TopCat.Presheaf.section_ext (splitTorus _ D'.toPre.X).left.sheaf ⊤
      intro z hz
      have e := congrArg Units.val
        (GlobalTheory.PullLinear.char_eq (U.gt 0) (U'.gt 0) hD.w (hψ x').1 (hψ x').2 (𝟙 _) τ hτ z)
      rw [gm_val τ.left z ⊤ trivial, gm_val (Over.Hom.left (𝟙 (WeightPf.Te D'.toPre (maximalIdeal V) 0))) z ⊤ trivial, GlobalTheory.SplitTorus.charUnit_val,
        GlobalTheory.SplitTorus.charUnit_val] at e
      exact e
    have e := GlobalTheory.SplitTorus.hom_ext (T := Over.mk ((splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb'))
      (g := Over.homMk _ wA) (g' := Over.homMk _ wB) (fun a => by
        rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq]
        simp only [Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
        rw [GlobalTheory.SplitTorus.bcMap_appTop_chi, GlobalTheory.SplitTorus.torusMap_appTop_chi,
          ← AddEquiv.apply_symm_apply hD.xe a, hchar, GlobalTheory.SplitTorus.bcMap_appTop_chi,
          AddEquiv.apply_symm_apply]
        rfl)
    exact congrArg (·.left) e
  apply GlobalTheory.TorusPart.hom_ext_of_pullback (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp)
  rw [Over.comp_left, Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp) (U.gt 0).i]
  rw [C1, ← Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
  rw [Category.assoc, hτ', ← Category.assoc, key, Category.assoc]


set_option maxHeartbeats 800000 in
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsLocalHom g → ∀ (bc : G' ≅ (Over.pullback (specOf g)).obj G), IsMonHom bc.hom → β = bc.hom.left ≫ pullback.fst G.hom (specOf g) → ∀ hD : IsPullDeg g D.toPre D'.toPre, IsPullUnif g hD bc U U' → LBIso U'.LG.L (U.LG.L.pull β) ∧ CoordMap D.toPre D'.toPre g hD.xe.symm.toAddMonoidHom ∧ EquivMap U U' β hD.xe.symm.toAddMonoidHom := by
  intro R _ _ _ _ G _ _ _ D A U V _ _ _ _ G' _ _ _ D' A' U' g β hloc bc hbc hβ hD H
  subst hβ
  refine ⟨?_, coordMap_of_isPullDeg hD, ?_⟩
  · obtain ⟨wL, hwL, -⟩ := H.lg
    exact ⟨wL, hwL⟩
  intro f f' _ _ hcomm m m' hm hm' y
  have hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), residue V x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), ((residue V).comp g) x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 ((map_mem_nonunits_iff g x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx))
  have hp' := isGrpPullback_pullback G' (spMap (residue V))
  have hβ : IsGrpPullback G' G (spMap g) (bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf g))).congr (Category.id_comp _) rfl
  have hp : IsGrpPullback ((Over.pullback (spMap (residue V))).obj G') G (spMap ((residue V).comp g))
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    (hp'.comp hβ).congr (Spec.map_comp (CommRingCat.ofHom g) (CommRingCat.ofHom (residue V))).symm rfl
  have e' : ((Over.pullback (spMap (residue V))).map f').left ≫ pullback.fst G'.hom (spMap (residue V)) =
      pullback.fst G'.hom (spMap (residue V)) ≫ f'.left := pullback.lift_fst _ _ _
  have e : ((Over.pullback (spMap (residue V))).map f').left ≫
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) =
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) ≫ f.left := by
    rw [← Category.assoc, e', Category.assoc, hcomm]
    simp only [Category.assoc]
  have k' := hm' _ _ hb _ _ hp' _ e'
  have k := hm _ _ hb' _ _ hp _ e
  have K := gtTorus_pull H hb hb' hp' hp
  have hmono := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hb' hp).1
  have k2 := (Category.assoc _ _ _).trans ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V))
    hD.xe.symm.toAddMonoidHom ≫ ·) k.symm).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Over.pullback (spMap (residue V))).map f') K.symm).trans (k'.trans
    ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V)) m' ≫ ·) K).trans (Category.assoc _ _ _).symm)))))
  have k3 := (cancel_mono _).1 k2
  rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp] at k3
  exact congrArg (fun φ : D.toPre.X →+ D'.toPre.X => φ y) (GlobalTheory.SplitTorus.torusMap_injective k3)

end GlobalTheory.Poinc.Eq8.PullUnif
end
end

