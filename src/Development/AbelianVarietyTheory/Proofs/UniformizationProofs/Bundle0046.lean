module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPsiOnBasicOpen
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcPsiOn

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull

theorem genRel_iff_val {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) {pt : PUnit → (Sp F ⟶ B)} {pt₀ : PUnit → (Sp F ⟶ B₀)} {ε : PUnit → ℤ}
    (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) (z : Sp F) :
    GenRel w t t₀ x ↔ pt PUnit.unit ≫ φ = pt₀ PUnit.unit ∧ ∀ J₀ J, Good M₀ z J₀ → Good M z J →
      (om w z J₀ J (pt PUnit.unit) ^ ε PUnit.unit * val t (𝟙 _) z J).val = toStk z x * (val t₀ (𝟙 _) z J₀).val := by
  rw [genRel_iff w t t₀ x z]
  constructor
  · rintro ⟨hp, H⟩
    refine ⟨hp _, fun J₀ J hJ₀ hJ => ?_⟩
    have e := H (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ)) (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
    rw [Fintype.prod_unique] at e
    rw [val_of t _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
      val_of t₀ _ z J₀ (fun k => J₀ (pt k ≫ φ)) (fun k => by rw [Category.id_comp, hp])]
    exact e
  · rintro ⟨hp, H⟩
    refine ⟨fun _ => hp, fun j j₀ h₀ h₁ => ?_⟩
    obtain ⟨J, hJ, eJ⟩ := exists_good M hM z pt j (fun _ _ _ => rfl) h₁
    obtain ⟨J₀, hJ₀, eJ₀⟩ := exists_good M₀ hM₀ z (fun k => pt k ≫ φ) j₀ (fun _ _ _ => rfl) h₀
    have e := H J₀ J hJ₀ hJ
    rw [val_of t _ z J j (fun k => by rw [Category.id_comp]; exact eJ k),
      val_of t₀ _ z J₀ j₀ (fun k => by rw [Category.id_comp, ← eJ₀ k]; exact congrArg J₀ hp.symm), om, eJ,
      eJ₀ PUnit.unit] at e
    rw [Fintype.prod_unique]
    exact e

theorem exists_unit_basicOpen {R : Type} [CommRing R] (u : R) :
    ∃ c : Γ((TW (R := R) (PrimeSpectrum.basicOpen u)).left, ⊤)ˣ, ∀ (F : Type) [Field F] (r : R →+* F)
      (z : Sp F ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left),
      z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → ∀ (p : Sp F) (n : ℤ),
      (gm z p ⊤ (c ^ n)).val = toStk p (r u ^ n) := by
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen u
  let s : Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u
  have hc : IsUnit ((U.ι.app ⊤).hom s) := by
    apply U.toScheme.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    have : y ∈ U.toScheme.basicOpen ((U.ι.app ⊤).hom s) := by
      rw [← Scheme.preimage_basicOpen]
      show U.ι y ∈ (Spec (CommRingCat.of R)).basicOpen s
      rw [basicOpen_eq_of_affine]
      exact y.2
    exact (Scheme.mem_basicOpen _ _ y hy).1 this
  refine ⟨hc.unit, fun F _ r z hz p n => ?_⟩
  have e : (gm z p ⊤ hc.unit).val = toStk p (r u) := by
    have e₁ : (gm z p ⊤ hc.unit).val = gs (z ≫ U.ι) p ⊤ s :=
      (gs_unit z p ⊤ trivial hc.unit).symm.trans (gs_pull z U.ι p ⊤ trivial s)
    have hz' : z ≫ U.ι = specOf r := hz
    rw [e₁, hz', gs_eq _ p ⊤ trivial]
    have nat := congrArg (fun q => q.hom u) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r))
    exact congrArg ((Sp F).presheaf.germ ⊤ p trivial).hom nat.symm
  have h0 : r u ≠ 0 := fun h => by
    rw [h, map_zero] at e
    exact (gm z p ⊤ hc.unit).ne_zero e
  have e' : Units.map (toStk p).toMonoidHom (Units.mk0 _ h0) = gm z p ⊤ hc.unit := Units.ext e.symm
  refine (congrArg Units.val ((map_zpow (gm z p ⊤) hc.unit n).trans ((congrArg (· ^ n) e'.symm).trans
    (map_zpow _ _ n).symm))).trans ?_
  show toStk p _ = _
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem val_scale' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem φ r) _) rfl)

variable {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] {D₀ : DegPre O'} {D : DegPre R}

theorem exists_gen_on (f : O' →+* R) (u : R) {φ : D.P.A.left ⟶ D₀.P.A.left} (w : LB.Iso D.P.L (D₀.P.L.pull φ))
    (hw : w.IsGen) (y : D₀.X) (x : D.X) (hc : (D.c x).left ≫ φ = spMap f ≫ (D₀.c y).left)
    (hy : PsiUnitOn D₀ y Set.univ) (n : ℤ) :
    ∃ s : LB.Gen (LB.LinComb D.P.L (K := PUnit)
        (fun _ => (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left) (fun _ => -1)), s.IsGen ∧
      ∀ (F : Type) [Field F] (r : R →+* F) (z : Sp F ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left),
        z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → ∀ j : Sp F ⟶ (TK O').left,
        j ≫ jK O' = specOf r ≫ spMap f →
        GenRel w (LB.pullGen _ _ _ s z) (LB.pullGen _ _ _ (D₀.psi y) j) (r u ^ n) := by
  obtain ⟨t, ht, H⟩ := (psiUnitOn_univ_iff D₀ y).1 hy
  obtain ⟨c, hcu⟩ := exists_unit_basicOpen u
  have hψ : (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left ≫ φ =
      ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f) ≫ (D₀.c y).left := by
    show ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ (D.c x).left) ≫ φ = _
    rw [Category.assoc, hc, Category.assoc]
  obtain ⟨a, ha, va⟩ := exists_down_om hw D₀.P.isLB D.P.isLB (K := PUnit)
    (φ' := fun _ => (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left)
    ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f) (fun _ => hψ) t ht
  refine ⟨scaleGen (c ^ n) a, scaleGen_isGen _ _ ha, fun F _ r z hz j hj => ?_⟩
  have p : Sp F := (default : PrimeSpectrum F)
  have hzj : z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f = j ≫ jK O' := by
    rw [← Category.assoc, hz, hj]
  refine (genRel_iff_val D.P.isLB D₀.P.isLB w _ _ _ p).2 ⟨?_, fun J₀ J hJ₀ hJ => ?_⟩
  · show (z ≫ (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left) ≫ φ = j ≫ jK O' ≫ (D₀.c y).left
    rw [Category.assoc, hψ, ← Category.assoc, hzj, Category.assoc]
  · have e := va _ z p J₀ J hJ₀ hJ
    rw [Fintype.prod_unique, hzj, ← val_pull hJ₀, val_corr hJ₀ H] at e
    rw [val_pull hJ, val_pull hJ₀, Category.id_comp, Category.id_comp, val_scale' _ _ _ hJ, e, ← hcu F r z hz p n,
      ← Units.val_mul, mul_left_comm]

theorem val_eq_of_genRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {pt pt' : PUnit → (Sp F ⟶ B)} {pt₀ : PUnit → (Sp F ⟶ B₀)} {ε : PUnit → ℤ}
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F}
    (hp : pt PUnit.unit = pt' PUnit.unit) (h : GenRel w t t₀ x) (h' : GenRel w t' t₀ x) (z : Sp F) {J} (hJ : Good M z J) :
    val t (𝟙 _) z J = val t' (𝟙 _) z J := by
  obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' hM₀ z
  have e := ((genRel_iff_val hM hM₀ w _ _ _ z).1 h).2 J₀ J hJ₀ hJ
  have e' := ((genRel_iff_val hM hM₀ w _ _ _ z).1 h').2 J₀ J hJ₀ hJ
  rw [hp, ← e'] at e
  exact mul_left_cancel (Units.ext e)

theorem corr_of_geom (U : (Spec (CommRingCat.of R)).Opens) (hU : (U : Set (Spec (CommRingCat.of R))).Nonempty)
    (x : D.X) (s : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (toUnit (TW U) ≫ D.c x).left) (fun _ => -1)))
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (H : ∀ z : Sp F ⟶ (TW U).left, z ≫ (TW U).hom = jFK (R := R) F ≫ jK R → ∀ p J, Good D.P.L p J →
      val s z p J = val (D.psi x) (jFK (R := R) F) p J) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ s (jK R ∣_ U)) (LB.pullGen D.P.L _ _ (D.psi x) (jK R ⁻¹ᵁ U).ι) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : Sp F ⟶ (jK R ⁻¹ᵁ U).toScheme, lam ≫ (jK R ⁻¹ᵁ U).ι = jFK (R := R) F :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem _ U hU), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ U) ≫ U.ι = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl]
  have p : Sp F := (default : PrimeSpectrum F)
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  refine TauPull.corr_of_dense D.P.isLB lam p (fun V ⟨y, hy⟩ => ?_) fun J hJ => ?_
  · rw [show lam p = y from Subtype.ext (Subsingleton.elim _ _)]
    exact hy
  · rw [val_pull hJ, val_pull hJ, hl]
    exact H _ hκ p J hJ

end GlobalTheory.ArcPsiOn


open GlobalTheory.ArcPsiOn GlobalTheory.ArcPull ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem GlobalTheory.arcWit_psiOn_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : Geo.Tor.ArcIn Dm l β O' b) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (f : O' →+* R), Function.Injective f → ∀ (u : R), u ≠ 0 → ∀ (χ : Geo.Tor.Sp R ⟶ Y.X) (W : Geo.Tor.ArcWit Y a I f u χ), ∃ ψW : PsiOn W.P.D.toPre (PrimeSpectrum.basicOpen u), ∀ (F : Type) [Field F] [Algebra (FractionRing O') F] (r : R →+* F) (z : Spec (CommRingCat.of F) ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left), z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = r (f x)) → ∀ y, Geo.Tor.GenRel W.w (LB.pullGen _ _ _ (ψW.psi (W.e y)) z) (LB.pullGen _ _ _ (a.D₀.psi y) (jFK (R := O') F)) (r u ^ (a.be y y / 2)) := by
  intro E _ _ _ H Dm l Xo c O _ β Y O' _ _ b a R _ _ I f hf u hu χ W
  obtain ⟨-, s2, -, -, s5, s6⟩ := W.spec
  choose s hs H using fun x : W.P.D.toPre.X => exists_gen_on f u W.w s2 (W.e.symm x) x
    (by simpa only [LinearEquiv.apply_symm_apply] using s5 (W.e.symm x)) (a.gen _)
    (a.be (W.e.symm x) (W.e.symm x) / 2)
  refine ⟨⟨s, hs, fun x => ?_⟩, fun F _ _ r z hz hr y => ?_⟩
  · let F := AlgebraicClosure (FractionRing R)
    letI : Algebra (FractionRing O') F := ((algebraMap (FractionRing R) F).comp (fracMap hf)).toAlgebra
    have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x =>
      congrArg (algebraMap (FractionRing R) F) (fracMap_algebraMap hf x)
    refine corr_of_geom _ ⟨⟨⊥, Ideal.isPrime_bot⟩, hu⟩ x (s x) F fun z hz p J hJ => ?_
    have hj : jFK (R := R) F ≫ jK R = specOf ((algebraMap (FractionRing R) F).comp (algebraMap R _)) :=
      (spMap_comp _ _).symm
    have k := H x F _ z (hz.trans hj) (jFK (R := O') F) ((spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext hF)).trans (spMap_comp f _)))
    have k' := (s6 F _ hF rfl).1 (W.e.symm x)
    rw [LinearEquiv.apply_symm_apply] at k'
    have e := val_eq_of_genRel W.P.D.toPre.P.isLB a.D₀.P.isLB (by
      show z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ (W.P.D.toPre.c x).left =
        jFK (R := R) F ≫ jK R ≫ (W.P.D.toPre.c x).left
      rw [← Category.assoc, hz, Category.assoc]) k k' p hJ
    rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at e
  · have k := H (W.e y) F r z hz (jFK (R := O') F) ((spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext hr)).trans (spMap_comp f r)))
    rw [LinearEquiv.symm_apply_apply] at k
    exact k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivTransport
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiTransport

variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}

theorem lift_lam {G H T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G) (t : T ⟶ H) (x : T ⟶ G)
    (k : Fin 4) : (lift t x).left ≫ lamφ i k = (![(t ≫ i) * x, t ≫ i, x, 1] k : T ⟶ G).left := by
  fin_cases k
  · exact congrArg (fun q => q.left) (show lift t x ≫ ((fst H G ≫ i) * snd H G) = (t ≫ i) * x by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd])
  · exact congrArg (fun q => q.left) (lift_fst_assoc t x i)
  · exact congrArg (fun q => q.left) (lift_snd t x)
  · exact congrArg (fun q => q.left) (show lift t x ≫ (1 : H ⊗ G ⟶ G) = 1 from MonObj.comp_one _)

theorem prod_lam {G H T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G) (t : T ⟶ H) (x : T ⟶ G)
    {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k, h ((lift t x).left ≫ lamφ i k) ^ Oε k =
      h ((t ≫ i) * x).left * (h (t ≫ i).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left := by
  simp only [lift_lam, Fin.prod_univ_four]
  show h ((t ≫ i) * x).left ^ (1 : ℤ) * h (t ≫ i).left ^ (-1 : ℤ) * h x.left ^ (-1 : ℤ) *
    h (1 : T ⟶ G).left ^ (1 : ℤ) = _
  simp only [zpow_one, zpow_neg]

theorem toBase_surj {A : Over S} {A₀ : Over S₀} {E : A₀.left ⟶ A.left} (hE : IsPullback E A₀.hom A.hom ρ)
    (hw : E ≫ A.hom = A₀.hom ≫ ρ) {T : Over S₀} (x : Over.mk (T.hom ≫ ρ) ⟶ A) : ∃ x₀ : T ⟶ A₀, toBase hw x₀ = x :=
  ⟨Over.homMk (hE.lift x.left T.hom (Over.w x)) (hE.lift_snd _ _ _), Over.OverMorphism.ext (hE.lift_fst _ _ _)⟩

theorem exists_over {Z : Over S} (r : Z.left ⟶ S₀) (h : r ≫ ρ = Z.hom) : ∃ T : Over S₀, Z = Over.mk (T.hom ≫ ρ) := by
  obtain ⟨Z, ⟨⟨⟩⟩, f⟩ := Z
  change Z ⟶ S₀ at r
  change Z ⟶ S at f
  obtain rfl : r ≫ ρ = f := h
  exact ⟨Over.mk r, rfl⟩

section
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G₀ H₀ : Over S₀} [GrpObj G₀] [IsCommMonObj G₀]
  [GrpObj H₀] {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ ρ} {E : H₀.left ⟶ H.left}
  {P : CP G} {P₀ : CP G₀} {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : H ⟶ G} {i₀ : H₀ ⟶ G₀}


omit [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj G₀] [IsCommMonObj G₀] [GrpObj H₀] in
theorem toBase_comp (hE : E ≫ H.hom = H₀.hom ≫ ρ) (hi : E ≫ i.left = i₀.left ≫ F) {T : Over S₀} (t : T ⟶ H₀) :
    toBase hE t ≫ i = toBase hw (t ≫ i₀) := Over.OverMorphism.ext (by
  show (t.left ≫ E) ≫ i.left = (t.left ≫ i₀.left) ≫ F
  rw [Category.assoc, hi, Category.assoc])

theorem exists_gen_val [Mono ρ] (hF : IsPullback F G₀.hom G.hom ρ) (hE : IsPullback E H₀.hom H.hom ρ)
    (hP : IsCPMap P₀ P ρ F hw w) (hi : E ≫ i.left = i₀.left ≫ F)
    (σ : LB.Gen (LB.LinComb P₀.L.L (lamφ i₀) Oε)) (hσ : σ.IsGen) :
    ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧
      ∀ (T : Over S₀) (t : T ⟶ H₀) (x : T ⟶ G₀) (a : T.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift (toBase hE.w t) (toBase hw x)).left →
        ∀ (z : T.left) (J' J), Good P₀.L.L z J' → Good P.L.L z J →
        ∀ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ, (∀ y, W y = gw w y.left z (J (y.left ≫ F)) (J' y.left)) →
          val s a z J = W ((t ≫ i₀) * x) * (W (t ≫ i₀))⁻¹ * (W x)⁻¹ * W 1 * val σ (lift t x).left z J' := by
  let Y : Over S₀ := Over.mk (pullback.snd (H ⊗ G).hom ρ)
  let j : Over.mk (Y.hom ≫ ρ) ⟶ H ⊗ G := Over.homMk (pullback.fst (H ⊗ G).hom ρ) pullback.condition
  obtain ⟨t₀, ht₀⟩ := toBase_surj hE hE.w (j ≫ fst H G)
  obtain ⟨x₀, hx₀⟩ := toBase_surj hF hw (j ≫ snd H G)
  have hj : pullback.fst (H ⊗ G).hom ρ = (lift (toBase hE.w t₀) (toBase hw x₀)).left := by
    rw [ht₀, hx₀, ← comp_lift, lift_fst_snd, Category.comp_id]; rfl
  have hφ : (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) = fun k => ((lift t₀ x₀).left ≫ lamφ i₀ k) ≫ F := by
    funext k
    refine ((congrArg (· ≫ lamφ i k) hj).trans (lift_lam i _ _ k)).trans
      (Eq.trans ?_ (congrArg (· ≫ F) (lift_lam i₀ t₀ x₀ k)).symm)
    rw [toBase_comp (hw := hw) hE.w hi]
    fin_cases k
    · exact (congrArg (fun q => q.left) (hP.mul Y (t₀ ≫ i₀) x₀)).symm
    · rfl
    · rfl
    · exact (congrArg (fun q => q.left) (map_one (toBaseHom hP.mul Y))).symm
  obtain ⟨s, hs, hv⟩ := exists_up ((isGen_iff w).1 hP.gen) P.L.isLB P₀.L.isLB
    (LB.pullGen P₀.L.L (lamφ i₀) Oε σ (lift t₀ x₀).left) (DVR.pullGen_isGen _ _ _ _ hσ _)
  rw [hφ]
  refine ⟨s, hs, fun T t x a ha z J' J hJ' hJ W hW => ?_⟩
  have e₀ : a ≫ pullback.snd (H ⊗ G).hom ρ = T.hom := by
    rw [← cancel_mono ρ, Category.assoc, ← pullback.condition, ← Category.assoc, ha]
    exact Over.w _
  let a' : T ⟶ Y := Over.homMk a e₀
  have e₁ : a' ≫ t₀ = t := Over.OverMorphism.ext (hE.hom_ext (by
    have := congrArg (fun q => a ≫ q.left) ht₀
    refine ((Category.assoc _ _ _).trans this).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fst H G).left) ha)).trans ?_
    exact congrArg (fun q => q.left) (lift_fst (toBase hE.w t) (toBase hw x))) ((Over.w _).trans (Over.w _).symm))
  have e₂ : a' ≫ x₀ = x := Over.OverMorphism.ext (hF.hom_ext (by
    have := congrArg (fun q => a ≫ q.left) hx₀
    refine ((Category.assoc _ _ _).trans this).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (snd H G).left) ha)).trans ?_
    exact congrArg (fun q => q.left) (lift_snd (toBase hE.w t) (toBase hw x))) ((Over.w _).trans (Over.w _).symm))
  have e₃ : a ≫ (lift t₀ x₀).left = (lift t x).left :=
    congrArg (fun q => q.left) (show a' ≫ lift t₀ x₀ = lift t x by rw [comp_lift, e₁, e₂])
  have v := hv _ a z _ _ (hJ.mem (fun k => ((lift t₀ x₀).left ≫ lamφ i₀ k) ≫ F) a)
    (hJ'.mem (fun k => (lift t₀ x₀).left ≫ lamφ i₀ k) a)
  refine v.trans (congrArg₂ (· * ·) ?_ ((val_pull hJ' σ _ a).trans (congrArg (fun q => val σ q z J') e₃)))
  simp only [hW]
  refine Eq.trans ?_ (prod_lam i₀ t x (fun q => gw w q z (J (q ≫ F)) (J' q)))
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← e₃]
  simp only [Category.assoc]

theorem exists_transport [Mono ρ] (hF : IsPullback F G₀.hom G.hom ρ) (hE : IsGrpPullback H₀ H ρ E)
    (hP : IsCPMap P₀ P ρ F hw w) (hi : E ≫ i.left = i₀.left ≫ F) [IsMonHom i₀] (σ : BiTriv P₀.c i₀) :
    ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧
      (∀ (Z : Over S) (t t' : Z ⟶ H) (x : Z ⟶ G) (a b d : Z.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift (t * t') x).left → b ≫ pullback.fst _ _ = (lift t x).left →
        d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I), Good P.L.L z I →
        val s a z I = cubV P.c z I (t ≫ i) (t' ≫ i) x * val s b z I * val s d z I) ∧
      (∀ (Z : Over S) (t : Z ⟶ H) (x x' : Z ⟶ G) (a b d : Z.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift t (x * x')).left → b ≫ pullback.fst _ _ = (lift t x).left →
        d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I), Good P.L.L z I →
        val s a z I = cubV P.c z I (t ≫ i) x x' * val s b z I * val s d z I) := by
  obtain ⟨s, hs, hv⟩ := exists_gen_val hF hE.1 hP hi σ.s σ.gen
  have ov : ∀ (Z : Over S) (a : Z.left ⟶ pullback (H ⊗ G).hom ρ) (p : Z ⟶ H ⊗ G), a ≫ pullback.fst _ _ = p.left →
      ∃ T : Over S₀, Z = Over.mk (T.hom ≫ ρ) := fun Z a p ha => exists_over (a ≫ pullback.snd _ _) (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha]; exact Over.w p)
  refine ⟨s, hs, fun Z t t' x a b d ha hb hd z I hI => ?_, fun Z t x x' a b d ha hb hd z I hI => ?_⟩
  · obtain ⟨T, rfl⟩ := ov Z a _ ha
    obtain ⟨t, rfl⟩ := toBase_surj hE.1 hE.1.w t
    obtain ⟨t', rfl⟩ := toBase_surj hE.1 hE.1.w t'
    obtain ⟨x, rfl⟩ := toBase_surj hF hw x
    obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB (Z := T.left) z
    have m : toBase hE.1.w t * toBase hE.1.w t' = toBase hE.1.w (t * t') :=
      Over.OverMorphism.ext (hE.2 T t t' _ _ rfl rfl)
    rw [m] at ha
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ y, W y = gw w y.left z (I (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    have c := (hP.vals T z J' I hJ' hI W hW).2.2 (t ≫ i₀) (t' ≫ i₀) x
    have l := σ.law1 T t t' x z J' hJ'
    have va := hv T _ _ a ha z J' I hJ' hI W hW
    have vb := hv T _ _ b hb z J' I hJ' hI W hW
    have vd := hv T _ _ d hd z J' I hJ' hI W hW
    rw [MonObj.mul_comp] at va
    rw [toBase_comp (hw := hw) hE.1.w hi, toBase_comp (hw := hw) hE.1.w hi]
    show @id (T.left.presheaf.stalk z)ˣ (val s a z I) = @id (T.left.presheaf.stalk z)ˣ
      (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀)) (toBase hw (t' ≫ i₀)) (toBase hw x)) *
        @id (T.left.presheaf.stalk z)ˣ (val s b z I) * @id (T.left.presheaf.stalk z)ˣ (val s d z I)
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀))
      (toBase hw (t' ≫ i₀)) (toBase hw x)) = C at c ⊢
    refine va.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (C * ·) vb) vd).symm)
    rw [l]
    apply Additive.ofMul.injective
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv] at c' ⊢
    linear_combination (norm := abel) -c'
  · obtain ⟨T, rfl⟩ := ov Z a _ ha
    obtain ⟨t, rfl⟩ := toBase_surj hE.1 hE.1.w t
    obtain ⟨x, rfl⟩ := toBase_surj hF hw x
    obtain ⟨x', rfl⟩ := toBase_surj hF hw x'
    obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB (Z := T.left) z
    rw [← hP.mul] at ha
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ y, W y = gw w y.left z (I (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    have c := (hP.vals T z J' I hJ' hI W hW).2.2 (t ≫ i₀) x x'
    have l := σ.law2 T t x x' z J' hJ'
    have va := hv T _ _ a ha z J' I hJ' hI W hW
    have vb := hv T _ _ b hb z J' I hJ' hI W hW
    have vd := hv T _ _ d hd z J' I hJ' hI W hW
    rw [← _root_.mul_assoc (t ≫ i₀)] at va
    rw [toBase_comp (hw := hw) hE.1.w hi]
    show @id (T.left.presheaf.stalk z)ˣ (val s a z I) = @id (T.left.presheaf.stalk z)ˣ
      (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀)) (toBase hw x) (toBase hw x')) *
        @id (T.left.presheaf.stalk z)ˣ (val s b z I) * @id (T.left.presheaf.stalk z)ˣ (val s d z I)
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀))
      (toBase hw x) (toBase hw x')) = C at c ⊢
    refine va.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (C * ·) vb) vd).symm)
    rw [l]
    apply Additive.ofMul.injective
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv] at c' ⊢
    linear_combination (norm := abel) -c'

end

theorem biTriv_transport : ∀ (S S₀ : Scheme.{0}) (ρ : S₀ ⟶ S) [Mono ρ] (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G ρ F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P ρ F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat ρ F i₀ i → BiTriv P₀.c i₀ → ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (splitTorus S X ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧ (∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (x : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift (t * t') x).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) (t' ≫ i) x * val s b z I * val s d z I) ∧ (∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x x' : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift t (x * x')).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) x x' * val s b z I * val s d z I) := by
  intro S S₀ ρ _ X _ G _ _ G₀ _ _ F hw hF P P₀ w hP i i₀ _ _ hi σ
  exact exists_transport hF.1 (SplitTorus.isGrpPullback_bcMap ρ X) hP (torusCompat_iff.1 hi) σ

end GlobalTheory.UU.BiTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConvTermFe
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ConvTermFE
open ReciprocityTheory.ChartRestriction.G.DVR

theorem famFE_val (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s : Raw D F k) (hs : DegPre.FamFE D F k s) (mu β : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    sval (s (β + k • mu)) r.left z J = sval (s β) (r ≫ DegPre.trF D F mu).left z J *
      (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu β
  rw [← hv u hu hc Z r z J hJ]
  exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hs mu β u hu hc) _ r.left z J hJ

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

theorem units_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k l : ℕ) (mu β ga : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J) *
      (uVal D F l ga (cP D _ mu) r z J * val (DegPre.famMult D F l mu ga) (r ≫ fst _ _).left z J) *
      th D z J (cP D Z (β + k • mu)) (cP D Z (ga + l • mu)) (r ≫ DegPre.prB D F) =
    th D z J (cP D Z β) (cP D Z ga) ((r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F) *
      (uVal D F (k + l) (β + ga) (cP D _ mu) r z J *
        val (DegPre.famMult D F (k + l) mu (β + ga)) (r ≫ fst _ _).left z J) := by
  have C : IsCub (th D (T := Z) z J) := isCub_cubV D.cub hJ
  have hm : r ≫ fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D Z mu := by rw [comp_cP, comp_cP]
  have hy : (r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = (r ≫ DegPre.prB D F) * cP D Z mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, hm]
  have t := tau_mul (r ≫ fst (TF (R := R) F) D.P.A) hJ hB β ga mu
  rw [tau_symm _ hJ (β + ga), tau_symm _ hJ β, tau_symm _ hJ ga] at t
  have key := GlobalTheory.translationUnit_mul _ _ _ C k l (cP D Z β) (cP D Z ga) (cP D Z mu) (r ≫ DegPre.prB D F)
  rw [hy, uVal, uVal, uVal, hm, val_famMult _ hJ, val_famMult _ hJ, val_famMult _ hJ, cPoint_add, cPoint_add, cPoint_add,
    cPoint_nsmul, cPoint_nsmul]
  simp only [val_powGen, pow_add]
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  have t' := congrArg Additive.ofMul t
  simp only [ofMul_mul, ofMul_inv] at key' t' ⊢
  linear_combination (norm := abel) key' - t'

theorem conv_term_fe : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k l : ℕ) (s : Raw D F k) (s' : Raw D F l), DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ∀ (mu α β ga β' ga' : D.X), β + ga = α → β' = β + k • mu → ga' = ga + l • mu → ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α) → ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J), Good D.P.L z J → sval (s β') r.left z J * sval (s' ga') r.left z J * (cubV D.cub z J (toUnit Z ≫ D.c β') (toUnit Z ≫ D.c ga') (r ≫ snd _ _)).val = sval (s β) (r ≫ DegPre.trF D F mu).left z J * sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) ((r ≫ DegPre.trF D F mu) ≫ snd _ _)).val * (val u r.left z J).val := by
  rintro hG R _ _ D hB F _ _ k l s s' hs hs' mu _ β ga _ _ rfl rfl rfl u hu hc Z r z J hJ
  have e := congrArg Units.val (units_mul hB k l mu β ga Z r z J hJ)
  rw [famFE_val hG k s hs mu β Z r z J hJ, famFE_val hG l s' hs' mu ga Z r z J hJ,
    (gen_fe hG (k + l) mu (β + ga)).2 u hu hc Z r z J hJ]
  rw [Units.val_mul, Units.val_mul, Units.val_mul (th D z J _ _ _)] at e
  refine Eq.trans ?_ ((congrArg (sval (s β) (r ≫ DegPre.trF D F mu).left z J *
    sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * ·) e).trans (_root_.mul_assoc _ _ _).symm)
  rw [_root_.mul_mul_mul_comm, _root_.mul_assoc]
  rfl

end GlobalTheory.ConvTermFE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisTwistField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_basis_twist_field : Laws → Laws2 → (∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)), ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)), ∃! c : Fin (k ^ D.P.g) → F, ∀ j, s.f j = ∑ i, DegPre.constBF D F (c i) _ * (b i).f j) :=
  fun _ h₂ _ _ _ D F _ _ _ hk α =>
    GlobalTheory.FamDimension.exists_basis_famSec (D := D) (F := F) h₂.secTwist hk α

end GlobalTheory.UU
end

