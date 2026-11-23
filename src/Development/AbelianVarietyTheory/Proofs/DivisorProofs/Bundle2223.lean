module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointLocallyConstantComplexAbelian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionLocal

lemma comp_pow_overScheme_grpObj {A T : Over (Sp ℂ)} [GrpObj A] (f : T ⟶ A) (g : A ⟶ A) :
    ∀ n : ℕ, f ≫ g ^ n = (f ≫ g) ^ n
  | 0 => by simp [MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj f g n]

theorem locally_eq_const_of_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (N : ℕ), 1 ≤ N →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 →
    ∀ t : T.left, ∃ (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A), t ∈ U ∧ U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left := by
  intro A _ hA N hN T x hx t
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have h : IsUnit ((N : ℂ)) := (Nat.cast_ne_zero.mpr (by omega)).isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨-, hfin, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective (Sp ℂ) A N hA hunit
  set f : A ⟶ A := (𝟙 A) ^ N with hf
  have hTu : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  have hxf : x.left ≫ f.left = T.hom ≫ η[A].left := by
    have h1 : x ≫ f = toUnit T ≫ η[A] := by
      rw [hf, comp_pow_overScheme_grpObj, Category.comp_id, hx]; rfl
    have h2 := congrArg (fun h => h.left) h1
    simpa [hTu] using h2
  haveI : IsFinite f.left := hfin
  haveI : Etale f.left := het
  haveI := hA.smooth
  have hη : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  have hfw : f.left ≫ A.hom = A.hom := Over.w f
  have hpt : T.hom t = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  set a := x.left t with ha_def
  have hfa : f.left a = η[A].left (IsLocalRing.closedPoint ℂ) := by
    rw [ha_def, ← Scheme.Hom.comp_apply, hxf, Scheme.Hom.comp_apply, hpt]
  have he : IsClosed ({η[A].left (IsLocalRing.closedPoint ℂ)} : Set A.left) :=
    ((pointEquivClosedPoint A.hom) ⟨η[A].left, hη⟩).2
  haveI : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have ha : IsClosed ({a} : Set A.left) := by
    rw [isClosed_singleton_iff_locallyOfFiniteType]
    have h1 : LocallyOfFiniteType (A.left.fromSpecResidueField (f.left a)) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp (hfa ▸ he)
    have h2 : LocallyOfFiniteType (Spec.map (f.left.residueFieldMap a)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.FiniteType.of_finite (residueFieldMap_finite_of_locallyQuasiFinite f.left a)
    have h3 : LocallyOfFiniteType (A.left.fromSpecResidueField a ≫ f.left) := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; infer_instance
    exact locallyOfFiniteType_of_comp _ f.left
  let y0 : Sp ℂ ⟶ A.left := pointOfClosedPoint A.hom a ha
  have hy0 : y0 ≫ A.hom = 𝟙 _ := pointOfClosedPoint_comp A.hom a ha
  let y : 𝟙_ (Over (Sp ℂ)) ⟶ A := Over.homMk y0 (by simpa using hy0)
  have hy0f : y0 ≫ f.left = η[A].left := by
    refine ext_of_apply_closedPoint_eq A.hom ?_ hη ?_
    · rw [Category.assoc, hfw, hy0]
    · show f.left (pointOfClosedPoint A.hom a ha (IsLocalRing.closedPoint ℂ)) = _
      exact (congrArg f.left (pointOfClosedPoint_apply A.hom a ha _)).trans hfa
  have hg : x.left ≫ f.left = (T.hom ≫ y0) ≫ f.left := by
    rw [hxf, Category.assoc, hy0f]
  have hψ := Spec.map_preimage (T.left.fromSpecResidueField t ≫ T.hom)
  set ψ := Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)
  have hr : (residueFieldIsoBase A.hom a ha).inv ≫ x.left.residueFieldMap t = ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, SpecMap_residueFieldIsoBase_inv]
    erw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
    rw [Over.w x]
  have k : T.left.fromSpecResidueField t ≫ x.left = T.left.fromSpecResidueField t ≫ T.hom ≫ y0 := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← hψ]
    simp only [y0, pointOfClosedPoint, ← Category.assoc, ← Spec.map_comp]
    rw [← hr, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let g : T.left ⟶ pullback f.left f.left := pullback.lift x.left (T.hom ≫ y0) hg
  have kg : T.left.fromSpecResidueField t ≫ g =
      (T.left.fromSpecResidueField t ≫ x.left) ≫ pullback.diagonal f.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, k]
  refine ⟨g ⁻¹ᵁ (pullback.diagonal f.left).opensRange, y, ?_, ?_⟩
  · show g t ∈ Set.range (pullback.diagonal f.left)
    have hk := congrArg (fun h => h (IsLocalRing.closedPoint (T.left.residueField t))) kg
    refine ⟨_, ((Scheme.Hom.comp_apply _ _ _).symm.trans hk.symm).trans
      ((Scheme.Hom.comp_apply _ _ _).trans ?_)⟩
    exact congrArg g (Scheme.fromSpecResidueField_apply t _)
  · set U := g ⁻¹ᵁ (pullback.diagonal f.left).opensRange
    have hle : Set.range (U.ι ≫ g) ⊆ Set.range (pullback.diagonal f.left) := by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact u.2
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f.left) (U.ι ≫ g) hle
    have h1 := congrArg (· ≫ pullback.fst f.left f.left) hl
    have h2 := congrArg (· ≫ pullback.snd f.left f.left) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, g,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    show U.ι ≫ x.left = U.ι ≫ T.hom ≫ y0
    rw [← h1, h2]

end GlobalTheory.TorsionLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtTrans

theorem ptTrans : ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (K : Type) [Field K] [Algebra (FractionRing V) K] [Algebra (FractionRing V') K] (A : PolAV (Sp (FractionRing V))) (A' : PolAV (Sp (FractionRing V'))) (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ A.A.left) (a' : P₀.A.left ⟶ A'.A.left), IsGrpPullback P₀.A A.A (spMap (algebraMap (FractionRing V) K)) a → IsGrpPullback P₀.A A'.A (spMap (algebraMap (FractionRing V') K)) a' → ∀ (m : ℕ) (x : TFK (R := V) K ⟶ A.A), x ^ m = 1 → ∃ (w : Sp K ⟶ P₀.A.left) (x' : TFK (R := V') K ⟶ A'.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x' ^ m = 1 := by
  intro V V' _ _ _ _ K _ _ _ A A' P₀ a a' h h' m x hx
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let e : TFK (R := V) K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V) K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let e' : TFK (R := V') K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V') K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let Φ : (T ⟶ P₀.A) →* (TFK (R := V) K ⟶ A.A) := (preHom e).comp (pushHom h T)
  let Φ' : (T ⟶ P₀.A) →* (TFK (R := V') K ⟶ A'.A) := (preHom e').comp (pushHom h' T)
  have hΦ : ∀ u : T ⟶ P₀.A, (Φ u).left = u.left ≫ a := fun u => by
    simp [Φ, e, preHom, pushHom, pushPt]
  have hΦ' : ∀ u : T ⟶ P₀.A, (Φ' u).left = u.left ≫ a' := fun u => by
    simp [Φ', e', preHom, pushHom, pushPt]
  have inj : Function.Injective Φ := fun u v huv => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← hΦ, ← hΦ, huv]
    · rw [Over.w u, Over.w v]
  have hsq : x.left ≫ A.A.hom = 𝟙 (Sp K) ≫ spMap (algebraMap (FractionRing V) K) := by
    rw [Over.w x, Category.id_comp]; rfl
  let w : T ⟶ P₀.A := Over.homMk (h.1.lift x.left (𝟙 _) hsq) (by simp [T])
  have hw : Φ w = x := by
    apply Over.OverMorphism.ext
    rw [hΦ]
    simp [w]
  have hwm : w ^ m = 1 := by
    apply inj
    rw [map_pow, hw, hx, map_one]
  refine ⟨w.left, Φ' w, ?_, ?_, ?_, ?_⟩
  · simpa [T] using Over.w w
  · rw [← hΦ, hw]
  · rw [hΦ']
  · rw [← map_pow, hwm, map_one]

end GlobalTheory.PtTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.OmRes

variable {R : Type} [CommRing R]

theorem val_map_coc {X : Scheme.{0}} {s : X ⟶ Sp R} (E E' : SqExt R) (φ : E.C →ₐ[R] E'.C) (φ₀ : E.B →ₐ[R] E'.B)
    (hπ : ∀ c, φ₀ (E.π c) = E'.π (φ c))
    (hi : ∀ b, φ (E.i b) = E'.i (φ₀ b)) (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (y' : Sp E'.C ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R E'.C))
    (a : Thick.triv E.C y hy ⟶ Thick.triv E'.C y' hy') (ha : ∀ c, a.φ c = φ c)
    (e : spMap (φ : E.C →+* E'.C) ≫ y = y') (f : Z1 (O (dp0 R) s)) :
    ∃ b : E'.B, E'.val y' hy' f = φ (E.val y hy f) + (ev f a : E'.C) - E'.i b := by
  have e₀ : spMap (φ₀ : E.B →+* E'.B) ≫ spMap (E.π : E.C →+* E.B) ≫ y =
      spMap (E'.π : E'.C →+* E'.B) ≫ y' := by
    rw [← e, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext hπ
  let Φ := E.thickHom E' φ φ₀ hπ (E.red_w hy) (E'.red_w hy') e₀
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ Thick.triv E'.B _ (E'.red_w hy') := Thick.trivHom φ₀ e₀
  have k1 := ev_sq f a (E'.idHom hy') (E.idHom hy) Φ ha
  have k2 := ev_sq f b (E'.secHom (E'.red_w hy') E'.i E'.π_i) (E.secHom (E.red_w hy) E.i E.π_i)
    Φ fun c ↦ (hi c).symm
  refine ⟨ev f b, ?_⟩
  rw [SqExt.val_apply, SqExt.val_apply, map_sub]
  have k1' : (ev f a : E'.C) + (ev f (E'.idHom hy') : E'.C) = φ (ev f (E.idHom hy)) + (ev f Φ : E'.C) := k1
  have k2' : E'.i (ev f b) + (ev f (E'.secHom (E'.red_w hy') E'.i E'.π_i) : E'.C) =
    φ (ev f (E.secHom (E.red_w hy) E.i E.π_i)) + (ev f Φ : E'.C) := k2
  linear_combination k2' - k1'

attribute [local instance] cotOp cotCentral cotTower

variable {D D' : Type} [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R D']

def rho (φ : D →ₐc[R] D') : (cotExt R D).C →ₐ[R] (cotExt R D').C := TrivSqZeroExt.map (cotMap φ)

theorem cotSnd_cotPt (a : D) : cotSnd R D (cotPt R D a) = dUnit (R := R) a := by
  simp [cotSnd, cotPt, TrivSqZeroExt.algebraMap_eq_inl, dUnit]

theorem cotSnd_rho (φ : D →ₐc[R] D') (c : (cotExt R D).C) : cotSnd R D' (rho φ c) = cotMap φ (cotSnd R D c) :=
  TrivSqZeroExt.snd_map _ _

theorem rho_cotPt (φ : D →ₐc[R] D') (a : D) : rho φ (cotPt R D a) = cotPt R D' (φ a) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine (TrivSqZeroExt.fst_map _ _).trans ?_
    simp [cotPt, TrivSqZeroExt.algebraMap_eq_inl]
  · exact (cotSnd_rho φ _).trans (by rw [cotSnd_cotPt, cotMap_d]; exact (cotSnd_cotPt _).symm)

theorem cotVal_map {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (φ : D →ₐc[R] D') (y : Pt X D) :
    cotVal f (spOver (φ : D →ₐ[R] D') ≫ y) =
      cotMap φ (cotVal f y) + dUnit (R := R) (fv f D D' (φ : D →ₐ[R] D') y) := by
  let z : Pt X (cotExt R D).C := spOver (cotPt R D) ≫ y
  let z' : Pt X (cotExt R D').C := spOver (cotPt R D') ≫ spOver (φ : D →ₐ[R] D') ≫ y
  have e : spMap (rho φ : (cotExt R D).C →+* (cotExt R D').C) ≫ z.left = z'.left := by
    change spMap _ ≫ spMap _ ≫ y.left = spMap _ ≫ spMap _ ≫ y.left
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext (rho_cotPt φ)
  let a : trivAt z ⟶ trivAt z' := Thick.trivHom (rho φ) e
  obtain ⟨b, hb⟩ := val_map_coc (cotExt R D) (cotExt R D') (rho φ) (AlgHom.id R R)
    (fun c ↦ (TrivSqZeroExt.fst_map _ _).symm) (fun r ↦ TrivSqZeroExt.map_inl _ _) z.left z.w z'.left z'.w a
    (fun _ ↦ rfl) e f
  have k : rho φ (fv f D _ (cotPt R D) y) + (ev f a : (cotExt R D').C) =
      cotPt R D' (fv f D D' (φ : D →ₐ[R] D') y) + fv f D' _ (cotPt R D') (spOver (φ : D →ₐ[R] D') ≫ y) :=
    ev_sq f (trivMap (cotPt R D) y) a (trivMap (φ : D →ₐ[R] D') y) (trivMap (cotPt R D') _) (rho_cotPt φ)
  have h0 : cotSnd R D' ((cotExt R D').i b) = 0 := rfl
  change cotSnd R D' ((cotExt R D').val z'.left z'.w f - _) =
    cotMap φ (cotSnd R D ((cotExt R D).val z.left z.w f - _)) + _
  rw [← cotSnd_rho, ← cotSnd_cotPt, ← map_add (f := _), ← sub_zero (cotSnd R D' (_ + _)), ← h0, ← map_sub, hb, map_sub (rho φ)]
  congr 1
  linear_combination k

theorem cotMap_res_om (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    cotMap (G.res n) (d.om (n + 1)) = d.om n := by
  have h := cotVal_map d.f (G.res n) (t.y (n + 1))
  rw [t.res n, d.res n] at h
  rw [Dat.om, Dat.om, h, map_sub, cotMap_d]
  simp only [dUnit, map_sub]
  abel

end GlobalTheory.PtExt.OmRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def ActsAs {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g : G ⟶ G) : Prop :=
  ∀ e : ℕ, (Over.pullback (thick R I e)).map g ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map b ∧
    ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X,
      TorusEndOf D.toPre.X h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map g = t ≫ (U.gt e).i

theorem pull_padd {S S' : Scheme.{0}} (f : S' ⟶ S) {T G : Over S} [GrpObj G] (a b : T ⟶ G) :
    (Over.pullback f).map (padd G a b) = padd _ ((Over.pullback f).map a) ((Over.pullback f).map b) := by
  simp [padd, Functor.Monoidal.lift_μ_assoc]

theorem comp_padd' {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (x : T ⟶ T') (a b : T' ⟶ G) :
    x ≫ padd G a b = padd G (x ≫ a) (x ≫ b) := by
  rw [padd, padd, comp_lift_assoc]

theorem padd_comp_hom {S : Scheme.{0}} {X Y T : Over S} [GrpObj X] [GrpObj Y] (f f' : T ⟶ X) (h : X ⟶ Y) [IsMonHom h] :
    padd X f f' ≫ h = padd Y (f ≫ h) (f' ≫ h) := by
  rw [padd, padd, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem torusEndOf_padd {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h h' : X → X}
    {t t' : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X h t) (ht' : TorusEndOf X h' t') :
    TorusEndOf X (h + h') (padd _ t t') := by
  rw [GlobalTheory.LinearUnifCheck.torusEndOf_iff] at ht ht' ⊢
  intro χ
  have hc : ∀ x, (charUnit S X x).val =
      (GlobalTheory.splitTorusPointsEquiv S X (splitTorus S X) (𝟙 _) (Multiplicative.ofAdd x)).val := fun x =>
    ((GlobalTheory.splitTorusPointsEquiv_val S X _ (𝟙 _) x).trans (SplitTorusHom.appTop_id _)).symm
  have hp : padd (splitTorus S X) t t' = t * t' := rfl
  rw [hp, ← GlobalTheory.splitTorusPointsEquiv_val, map_mul, MonoidHom.mul_apply, Units.val_mul,
    GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val, ht, ht', hc, hc, hc, Pi.add_apply, ofAdd_add,
    map_mul, Units.val_mul]

theorem actsAs_padd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A} {h h' : D.toPre.X → D.toPre.X} {g g' : G ⟶ G}
    (hg : ActsAs U b h g) (hg' : ActsAs U b' h' g') : ActsAs U (padd _ b b') (h + h') (padd G g g') := by
  intro e
  obtain ⟨q1, t, ht, i1⟩ := hg e
  obtain ⟨q2, t', ht', i2⟩ := hg' e
  have := (U.gt e).q_hom
  have := (U.gt e).i_hom
  refine ⟨?_, padd _ t t', torusEndOf_padd ht ht', ?_⟩
  · rw [pull_padd, pull_padd, padd_comp_hom, q1, q2, comp_padd']
  · rw [pull_padd, comp_padd', i1, i2, padd_comp_hom]

theorem actsAs_comp {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A} {h h' : D.toPre.X → D.toPre.X} {g g' : G ⟶ G}
    (hg : ActsAs U b h g) (hg' : ActsAs U b' h' g') : ActsAs U (b ≫ b') (h ∘ h') (g ≫ g') := by
  intro e
  obtain ⟨q1, t, ht, i1⟩ := hg e
  obtain ⟨q2, t', ht', i2⟩ := hg' e
  refine ⟨?_, t ≫ t', GlobalTheory.LinearUnifCheck.torusEndOf_comp ht ht', ?_⟩
  · rw [Functor.map_comp, Category.assoc, q2, ← Category.assoc, q1, Category.assoc, ← Functor.map_comp]
  · rw [Functor.map_comp, ← Category.assoc, i1, Category.assoc, i2, Category.assoc]

theorem actsAs_id {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) : ActsAs U (𝟙 _) id (𝟙 G) := by
  intro e
  refine ⟨by simp, 𝟙 _, ?_, by simp⟩
  rw [GlobalTheory.LinearUnifCheck.torusEndOf_iff]; intro χ; simp

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointCharacterValuesFixedLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CharValsFixed

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∀ (σ : F →+* F), (∀ t ∈ T, σ t = t) → ∀ (g : GtPtF D F) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ (S : Set D.X), AddSubgroup.closure S = ⊤ → (∀ χ ∈ S, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → ∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) := by
  intro R _ _ D F _ _ T _ φ₁ hφ₁ J₀ h₀ J hJ eJ σ hσ g b hb hbA S hS hSfix
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ₁) := Over.homMk (spMap T.subtype) (by
    show spMap T.subtype ≫ spMap φ₁ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ₁)
  let w : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ →* Fˣ :=
    (Units.map σ.toMonoidHom).comp (sig F) * (sig F)⁻¹
  have hwv : ∀ u, ((w u : Fˣ) : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) := fun u => rfl
  have hw1 : ∀ u, w u = 1 ↔ σ (sig F u : F) = (sig F u : F) := fun u => by
    constructor
    · intro h
      have e := congrArg Units.val h
      rw [hwv, Units.val_one] at e
      calc σ (sig F u : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) * (sig F u : F) := by
            rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]
        _ = (sig F u : F) := by rw [e, _root_.one_mul]
    · intro h
      apply Units.ext
      rw [hwv, h, Units.mul_inv, Units.val_one]
  have hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (Over.mk (spMap φ₁)).left ⟶ Y),
      w (val t (ρ.left ≫ r) (closedPoint F) J) = 1 := by
    intro Y K _ φ ε t r
    obtain ⟨u, hu⟩ := val_integral T.subtype h₀ eJ t r
    refine (hw1 _).2 ?_
    have hu' : (sig F (val t (ρ.left ≫ r) (closedPoint F) J) : F) = T.subtype u := hu
    rw [hu']
    exact hσ _ (u : T).2
  let b' : Over.mk (spMap φ₁) ⟶ D.P.A := Over.homMk b hbA
  have hgb : g.b = ρ ≫ b' := by
    ext1
    exact hb.symm
  have hth : ∀ χ χ', w (th D (closedPoint F) J (cP D _ χ) (cP D _ χ') g.b) = 1 := fun χ χ' => by
    rw [hgb, ← comp_cP D ρ χ, ← comp_cP D ρ χ']
    exact w_th ρ w hw _ _ _
  let H : AddSubgroup D.X :=
    { carrier := {χ | w (charVal g χ (closedPoint F) J) = 1}
      zero_mem' := by
        show w _ = 1
        rw [charVal_zero g hJ, map_one]
      add_mem' := fun {χ χ'} (h : w _ = 1) (h' : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ χ')
        rw [map_mul, map_mul, hth, h, h', _root_.mul_one, _root_.mul_one] at e
        exact e
      neg_mem' := fun {χ} (h : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ (-χ))
        rw [map_mul, map_mul, hth, h, _root_.mul_one, _root_.one_mul, add_neg_cancel, charVal_zero g hJ,
          map_one] at e
        exact e.symm }
  have hSH : S ⊆ H := fun χ hχ => (hw1 _).2 (hSfix χ hχ)
  have hH : H = ⊤ := eq_top_iff.2 (hS ▸ (AddSubgroup.closure_le H).2 hSH)
  intro χ
  exact (hw1 _).1 (show χ ∈ H by rw [hH]; trivial)

end GlobalTheory.CharValsFixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorusExt

open GlobalTheory.BXOf ReciprocityTheory.ChartRestriction.G.DVR

theorem gtExt_eq_self_of_charVal_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F) (g : GtPtF D F), spMap σ ≫ g.b.left = g.b.left → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → GlobalTheory.TorusExt.gtExt D σ hσ g = g := by
  intro R _ _ D F _ _ σ hσ g hb J hJ hfix
  have hb' : extMap σ hσ ≫ g.b = g.b := Over.OverMorphism.ext hb
  have hφ0 : ∀ χ k, Spec.map (CommRingCat.ofHom σ) ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k := by
    intro χ k
    show (extMap σ hσ).left ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k
    fin_cases k
    · show (extMap σ hσ ≫ (cP D _ χ * g.b)).left = (cP D _ χ * g.b).left
      rw [MonObj.comp_mul, comp_cP, hb']
    · show (extMap σ hσ ≫ cP D _ χ).left = (cP D _ χ).left
      rw [comp_cP]
    · show (extMap σ hσ ≫ g.b).left = g.b.left
      rw [hb']
    · show (extMap σ hσ ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
      rw [MonObj.comp_one]
  refine gt_ext_val ((gtExt_b σ hσ g).trans hb') fun χ y J' hJ' => ?_
  obtain rfl : y = closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hdel : ∀ ψ : Spec (CommRingCat.of F) ⟶ D.P.A.left, Spec.map (CommRingCat.ofHom σ) ≫ ψ = ψ →
      del D.P.L σ J J' ψ = del D.P.L (RingHom.id F) J J' ψ := by
    intro ψ h
    unfold del
    rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have e₁ := val_nat (g.isGen χ) σ hJ hJ' (𝟙 _)
  have e₂ := val_nat (g.isGen χ) (RingHom.id F) hJ hJ' (𝟙 _)
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at e₂
  have hu : Units.map σ.toMonoidHom (sig F (charVal g χ (closedPoint F) J)) = sig F (charVal g χ (closedPoint F) J) :=
    Units.ext (hfix χ)
  have hu' : Units.map (RingHom.id F).toMonoidHom (sig F (charVal g χ (closedPoint F) J)) =
      sig F (charVal g χ (closedPoint F) J) := Units.ext rfl
  have key : sig F (charVal (gtExt D σ hσ g) χ (closedPoint F) J') = sig F (charVal g χ (closedPoint F) J') := by
    rw [gtExt_val σ hσ g χ hJ', extMap_left, ← Category.comp_id (spMap σ)]
    refine e₁.trans (Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ DegPre.gtε k)
      (hdel _ ((congrArg _ (Category.id_comp _)).trans ((hφ0 χ k).trans (Category.id_comp _).symm))))
      (hu.trans hu'.symm)) e₂.symm)
  exact Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of F)).hom.hom.toMonoidHom)
    (stalkClosedPointIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective key

end GlobalTheory.TorusExt
end

