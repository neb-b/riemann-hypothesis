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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordAdditive
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CoordAdd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusCoord

theorem corr_of_thick {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤)
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z J, Good L z J → val u (thick R I e) z J = val u' (thick R I e) z J) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := exists_ratio hL h u hu u' hu'
  have h2 : a = 1 := by
    refine Units.ext (AbelianPartIso.fn_eq_of_thickenings hI ⊤ rfl _ _ fun e z => ?_)
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := ha _ (thick R I e) z J hJ
    rw [hv e z J hJ] at this
    rw [gs_unit _ z ⊤ trivial, gs_unit _ z ⊤ trivial, map_one, mul_eq_right.1 this.symm]
  exact corr_of_val hL fun y J hJ => by rw [ha _ _ y J hJ, h2, map_one, _root_.one_mul]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]


variable (I) in
abbrev lev (e : ℕ) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (𝟙 _)


variable (I) in
abbrev levι (e : ℕ) : (Over.map (thick R I e)).obj (lev I e) ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))) := toUnit _

omit [IsDomain R] in
theorem levι_left (e : ℕ) : (levι I e).left = thick R I e :=
  (Category.comp_id _).symm.trans ((Over.w (levι I e)).trans (Category.id_comp _))

omit [IsDomain R] in
theorem toUnit_left (e : ℕ) : (toUnit (Over.mk (thick R I e))).left = thick R I e :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (thick R I e))))

def Lifts {e : ℕ} (g : GtCoord I D e G) (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G)
    (gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) (a : lev I e ⟶ thickObj R I e G) : Prop :=
  pushHom (isGrpPullback_pullback G (thick R I e)) (lev I e) a = levι I e ≫ x ∧ im g a = levι I e ≫ gp.b ∧
    ∀ χ z J, Good D.P.L z J → val (g.t χ) a.left z J = val (gp.s χ) (levι I e).left z J

theorem exists_lifts {e : ℕ} (g : GtCoord I D e G) {x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G}
    {gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G),
      xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ g.pG = toUnit _ ≫ gp.b ∧
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) xe.left)
        (LB.pullGen D.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) :
    ∃ a, Lifts g x gp a := by
  obtain ⟨xe, h₁, h₂, h₃⟩ := h
  have hw : xe.left ≫ (thickObj R I e G).hom = 𝟙 _ := by
    rw [← cancel_mono (thick R I e), Category.assoc]
    exact (Over.w xe).trans (Category.id_comp _).symm
  have hu : (toUnit (Over.mk (thick R I e))).left = (levι I e).left := (toUnit_left e).trans (levι_left e).symm
  refine ⟨Over.homMk xe.left hw, Over.OverMorphism.ext ?_, Over.OverMorphism.ext ?_, fun χ z J hJ => ?_⟩
  · exact (congrArg (·.left) h₁).trans (congrArg (· ≫ x.left) hu)
  · exact (congrArg (·.left) h₂).trans (congrArg (· ≫ gp.b.left) hu)
  · have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h₃ χ) (𝟙 _)).trans (val_pull hJ _ _ _))
    rw [Category.id_comp, Category.id_comp, hu] at this
    exact this

omit [IsDomain R] [IsCommMonObj G] in
theorem push_injective {e : ℕ} {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    Function.Injective (pushHom (isGrpPullback_pullback G (thick R I e)) T) := fun a b h =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (·.left) h) ((Over.w a).trans (Over.w b).symm))


omit [IsDomain R] in
theorem pt_ext [IsLocalRing R] [IsHausdorff I R] {B : Over (Spec (CommRingCat.of R))}
    {b b' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B} (h : ∀ e, levι I e ≫ b = levι I e ≫ b') : b = b' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e =>
    (congrArg (· ≫ b.left) (levι_left e)).symm.trans
      ((congrArg (·.left) (h e)).trans (congrArg (· ≫ b'.left) (levι_left e))))

theorem prod_gtφT {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h (DegPre.cT D T χ * b).left)⁻¹ * h (DegPre.cT D T χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h _ ^ (-1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (-1 : ℤ) = _
  rw [zpow_neg_one, zpow_neg_one, zpow_one, zpow_one]
  rfl

variable [IsLocalRing R] [IsNoetherianRing R] [IsHausdorff I R]

theorem isAdd_of_lifts (hGF : GlobalFnsSt) (hI : I ≠ ⊤) (g : ∀ e, GtCoord I D e G)
    {x x' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G} {gp gp' gp'' : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∀ e, ∃ a, Lifts (g e) x gp a) (h' : ∀ e, ∃ a, Lifts (g e) x' gp' a)
    (h'' : ∀ e, ∃ a, Lifts (g e) (x * x') gp'' a) : GtPt.IsAdd gp gp' gp'' := by
  choose a ha using h
  choose a' ha' using h'
  choose a'' ha'' using h''
  have hm : ∀ e, a'' e = a e * a' e := fun e => push_injective (by
    rw [map_mul, (ha e).1, (ha' e).1, (ha'' e).1]
    exact MonObj.comp_mul _ _ _)
  have hb : gp''.b = gp.b * gp'.b := pt_ext (I := I) fun e => by
    rw [MonObj.comp_mul, ← (ha e).2.1, ← (ha' e).2.1, ← (ha'' e).2.1, hm, im_mul]
  refine ⟨hb, fun χ => corr_of_thick hI D.P.isLB (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp''.isGen χ) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp.isGen χ) (gp'.isGen χ)) fun e z J hJ => ?_⟩
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    refine (congrArg₂ (· * ·) (prod_gtφT gp''.b χ h) (prod_cub (DegPre.cT D _ χ) gp.b gp'.b h)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (prod_gtφT gp.b χ h) (prod_gtφT gp'.b χ h)).symm)
    rw [hb, _root_.mul_assoc (DegPre.cT D _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have k := val_t_mul_points (g e) hGF χ (a e) (a' e) z J hJ
    have c : cubeVal (g e) χ z J (a e) (a' e) =
        cubV D.cub z J (levι I e ≫ DegPre.cT D _ χ) (levι I e ≫ gp.b) (levι I e ≫ gp'.b) := by
      unfold cubeVal
      rw [(ha e).2.1, (ha' e).2.1, comp_toUnit_assoc]
    rw [← hm, (ha e).2.2 χ z J hJ, (ha' e).2.2 χ z J hJ, (ha'' e).2.2 χ z J hJ, c] at k
    have := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (levι I e) hJ _ _ _))).trans
      (k.trans (val_mul hJ _ _ _).symm)
    rw [levι_left] at this
    exact this

theorem isZero_of_lifts (hI : I ≠ ⊤) (g : ∀ e, GtCoord I D e G)
    {gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∀ e, ∃ a, Lifts (g e) 1 gp a) : gp.IsZero := by
  choose a ha using h
  have hm : ∀ e, a e = 1 := fun e => push_injective (by
    rw [map_one, (ha e).1]
    exact MonObj.comp_one _)
  have hb : gp.b = 1 := pt_ext (I := I) fun e => by
    rw [MonObj.comp_one, ← (ha e).2.1, hm, im_one]
  refine ⟨hb, fun χ => corr_of_thick hI D.P.isLB (fun U _ h => ?_) (gp.isGen χ)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm) fun e z J hJ => ?_⟩
  · refine (prod_gtφT gp.b χ h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
  · have k := (ha e).2.2 χ z J hJ
    rw [hm, val_unit (g e) χ hJ, levι_left] at k
    exact k.symm.trans (val_one _).symm

end GlobalTheory.CoordAdd

namespace GlobalTheory


open CoordAdd in
theorem gtCoord_additive : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), (∀ (x x' : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp gp' gp'' : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x' ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp'.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp'.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (x * x') ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp''.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp''.s χ) (toUnit (Over.mk (thick R I e))).left)) → GtPt.IsAdd gp gp' gp'') ∧ ∀ gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (1 : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.IsZero := by
  intro hGF R _ _ _ I hR hI D A G _ _ U
  obtain ⟨_, -, -, _⟩ := hR
  exact ⟨fun x x' gp gp' gp'' h h' h'' => isAdd_of_lifts hGF hI U.gt (fun e => exists_lifts _ (h e))
    (fun e => exists_lifts _ (h' e)) (fun e => exists_lifts _ (h'' e)),
    fun gp h => isZero_of_lifts hI U.gt fun e => exists_lifts _ (h e)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyLinearEquivOfRel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamDimension

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem nonempty_linearEquiv_of_rel {F M N : Type*} [Semiring F] [AddCommMonoid M] [AddCommMonoid N] [Module F M]
    [Module F N] (P : M → N → Prop) (h₁ : ∀ m, ∃! n, P m n) (h₂ : ∀ n, ∃! m, P m n)
    (ha : ∀ m n m' n', P m n → P m' n' → P (m + m') (n + n')) (hs : ∀ (c : F) m n, P m n → P (c • m) (c • n)) :
    Nonempty (M ≃ₗ[F] N) := by
  choose f hf hf' using h₁
  let g : M →ₗ[F] N :=
    { toFun := f
      map_add' := fun m m' => (hf' _ _ (ha _ _ _ _ (hf m) (hf m'))).symm
      map_smul' := fun c m => (hf' _ _ (hs c _ _ (hf m))).symm }
  refine ⟨LinearEquiv.ofBijective g ⟨fun m m' e => ?_, fun n => ?_⟩⟩
  · have e' : f m = f m' := e
    exact (h₂ (f m')).unique (e' ▸ hf m) (hf m')
  · obtain ⟨m, hm, -⟩ := h₂ n
    exact ⟨m, (hf' _ _ hm).symm⟩

section Comb

variable {X Y : Scheme.{0}} {n : ℕ}

def IsComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, resTop _ (a i) * (b i).f j

theorem exists_isComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) : ∃ s, IsComb b a s :=
  ⟨⟨fun j => ∑ i, resTop _ (a i) * (b i).f j, fun j j' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (b i)).compat j j'⟩, fun _ => rfl⟩

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem isComb_iff_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) :
    IsComb b a s ↔ ∀ y J, Good L y J →
      sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (a i) * sval (b i) (𝟙 Y) y J := by
  refine ⟨fun h y J hJ => SectionScalarValuation.sval_lin a b h _ y hJ, fun h j => ?_⟩
  obtain ⟨t, ht⟩ := exists_isComb b a
  rw [← ht j]
  exact sec_ext_val hL (fun y J hJ => (h y J hJ).trans (SectionScalarValuation.sval_lin a b ht _ y hJ).symm) j

theorem exists_basis_of_gen (hL : L.IsLB) {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ k) φ₃) (Sum.elim ε ε₃) φ' ε')
    {A : Type} (g : A → Γ(Y, ⊤)) (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s, ∃! c : Fin n → A, IsComb b (fun i => g (c i)) s) :
    ∃ b' : Fin n → LB.Sec (LB.LinComb L φ' ε'), ∀ s, ∃! c : Fin n → A, IsComb b' (fun i => g (c i)) s := by
  have h' : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ' k) φ₃) (Sum.elim ε' fun k => -ε₃ k) φ ε := fun U _ w => by
    have := h U w
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp] at this ⊢
    rw [← this]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  choose b' hb' using fun i => exists_sec hL h (pullMulSec (b i) (𝟙 Y) u hu)
  refine ⟨b', fun s => ?_⟩
  have hu' := invGen_isGen L _ _ u hu
  obtain ⟨t, ht⟩ := exists_sec hL h' (pullMulSec s (𝟙 Y) (LB.invGen L _ _ u) hu')
  refine (existsUnique_congr fun c => ?_).1 (hb t)
  rw [isComb_iff_sval hL, isComb_iff_sval hL]
  refine forall₃_congr fun y J hJ => ?_
  rw [ht _ _ y J hJ, sval_pullMulSec _ _ _ hu' _ y hJ, val_inv, Category.id_comp, Units.mul_inv_eq_iff_eq_mul,
    Finset.sum_mul]
  refine Eq.congr_right (Finset.sum_congr rfl fun i _ => ?_)
  rw [hb' i _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ, Category.id_comp, _root_.mul_assoc]

end Comb

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_basis_famSec (hT : SecTwistSt) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ b : Fin (k ^ D.P.g) → FamFree.FamSec D F k α,
      ∀ s, ∃! c : Fin (k ^ D.P.g) → F, IsComb b (fun i => gF D F (c i)) s := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk F (jFK (R := R) F ≫ jK R) (cP D (TF (R := R) F) α)
  let q : (DegPre.BF D F).left ⟶ (TK R).left := (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F
  let u := LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi α) D.rigK) q
  have hu : u.IsGen := pullGen_isGen _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen α) (pullGen_isGen _ _ _ _ D.rig_gen _)) _
  refine exists_basis_of_gen D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k) u hu (fun U _ h => by
      have p := prod_fam D F (𝟙 _) α k h
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₁ : q ≫ D.xK α = (cP D (DegPre.BF D F) α).left :=
        congrArg (fun x => x.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have a₂ : q ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun x : DegPre.BF D F ⟶ D.P.A => x.left)
          (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have a₃ : translPt D.P.A (cP D (TF (R := R) F) α) = cP D (DegPre.BF D F) α * DegPre.prB D F := by
        rw [translPt, comp_cP]; rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Category.id_comp, a₁, a₂, a₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one]
      rw [← _root_.mul_assoc]) (gF D F) b (fun s => ?_)
  exact (Equiv.existsUnique_congr (Equiv.piCongrRight fun _ : Fin (k ^ D.P.g) =>
      (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.toEquiv) fun _ => Iff.rfl).2 (hb s)

theorem nonempty_fam_equiv (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Nonempty (Fam D F k ≃ₗ[F] (D.X ⧸ FamFree.multiples D k → Fin (k ^ D.P.g) → F)) := by
  let rep : D.X ⧸ FamFree.multiples D k → D.X := Quotient.out
  have hrep : ∀ c, QuotientAddGroup.mk (rep c) = c := fun c => Quotient.out_eq c
  choose b hb using fun c => exists_basis_famSec (D := D) (F := F) hT hk (rep c)
  refine nonempty_linearEquiv_of_rel
    (fun s z => ∀ c, IsComb (b c) (fun i => gF D F (z c i)) (s.s (rep c))) (fun s => ?_) (fun z => ?_) ?_ ?_
  · choose z hz hz' using fun c => hb c (s.s (rep c))
    exact ⟨z, hz, fun z' h => funext fun c => hz' c _ (h c)⟩
  · choose σ hσ using fun c => exists_isComb (b c) (fun i => gF D F (z c i))
    refine (existsUnique_congr fun s => forall_congr' fun c => ?_).1
      (FamFree.existsUnique_fam hG hB hk rep hrep σ)
    exact ⟨fun h => h ▸ hσ c, fun h => SecOps.sec_ext fun j => (h j).trans (hσ c j).symm⟩
  · intro s z s' z' h h' c j
    rw [add_f, h c j, h' c j, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, map_add (f := _), resTop, add_mul]
  · intro a s z h c j
    rw [smul_f, h c j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, resTop, _root_.mul_assoc]

theorem finrank_fam (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.rank + D.P.g) := by
  obtain ⟨e⟩ := nonempty_fam_equiv (D := D) (F := F) hG hT hB hk
  have hc : Nat.card (D.X ⧸ FamFree.multiples D k) = k ^ D.rank := AddSubgroup.index_range_nsmul D.X k
  have : Finite (D.X ⧸ FamFree.multiples D k) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite (D.X ⧸ FamFree.multiples D k)
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Module.finrank_fin_fun, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hc, smul_eq_mul, pow_add]

theorem main : GlobalFnsSt → CubeSt → SquareSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D.toPre F k) ∧ Module.finrank F (Fam D.toPre F k) = k ^ (D.toPre.rank + D.toPre.P.g) :=
  fun hG _ _ hT _ _ _ _ D _ _ _ _ hk => finrank_fam hG hT D.tau_bimult hk

end GlobalTheory.FamDimension
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameOfOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TorusWeight

theorem gs_map {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) :
    gs r z U f = (r.stalkMap z).hom (gs (𝟙 X) (r z) U f) := by
  rw [gs_eq r z U h, gs_eq (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h f).symm

theorem val_const {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (a : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → (val t (𝟙 _) y J).val = gs (𝟙 _) y ⊤ a) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    (val t r z J).val = gs r z ⊤ a := by
  have hJ' : Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ (r ≫ ψ)
  have e := h (r z) _ hJ'
  rw [val_of t (𝟙 _) (r z) _ (fun k => J (r ≫ φ k)) (fun k => by rw [Category.id_comp])] at e
  have hm := hJ.mem φ r
  refine (gs_unit r z _ hm _).symm.trans ((gs_map r z _ hm _).trans (Eq.trans ?_ (gs_map r z ⊤ trivial a).symm))
  exact congrArg _ ((gs_unit (𝟙 Y) (r z) _ hm _).trans e)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem normd_one {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    {u : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    val u (1 : TF (R := R) F ⟶ D.P.A).left z J = 1 :=
  (val_pull hJ u (eSec D.P.A) (toUnit (TF (R := R) F)).left).symm.trans ((val_corr hJ hu.2 _).trans (val_one _))

theorem psi_zero (hB : D.TauBimult) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi 0) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J = 1 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have z0 : (0 : D.X) + 0 = 0 := add_zero 0
  have hpt : ∀ a b c : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _),
      val (D.tau a c) r z J = val (D.tau b c) r z J := by rintro a b c rfl r; rfl
  have hpp : ∀ a b : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _), val (D.psi a) r z J = val (D.psi b) r z J := by
    rintro a b rfl r; rfl
  have hτ0 := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 0
  rw [hpt _ _ _ z0, cPoint_zero, C.face] at hτ0
  have t00 := (mul_left_cancel hτ0).symm
  have hψ := UUA.psi_add (𝟙 (TF (R := R) F)) hJ (0 : D.X) 0
  rw [hpp _ _ z0, t00, _root_.one_mul, _root_.mul_assoc] at hψ
  have h1 := left_eq_mul.1 hψ
  rw [Over.id_left, Category.id_comp] at h1
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) h1
  exact (val_pull hJ (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (toUnit (TK R)).left (jFK (R := R) F)).symm

theorem txFrame_of_one (hB : D.TauBimult) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) : TXFrame N p w := by
  refine ⟨hw.1, fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
  · have e : val (p.g.s p.y) (𝟙 _) z J = 1 := Units.ext (by
      rw [hτ.2 _ z J hJ, hy, ofAdd_zero, map_one, CoefBasic.cst_eq]; exact map_one _)
    rw [hw.2 z J hJ, e, hτ.1, normd_one hν z hJ, one_pow, _root_.one_mul]
  · rw [hw.2 z J hJ, hτ.1, normd_one hκ z hJ, one_pow, _root_.one_mul, hy, psi_zero hB z hJ]

theorem sval_const {k : ℕ} (α : D.X) (ζ : F) (s s' : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    (∀ j, s'.f j = DegPre.constBF D F ζ _ * s.f j) ↔
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        sval s' ρ.left z J = sval s ρ.left z J *
          gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) j, r z ∈ LB.wchart D.P.L (DegPre.famφ D F α) j →
      gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (DegPre.constBF D F ζ _ * s.f j) =
        gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (s.f j) *
          gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
    fun Z r z j hm => (gs_mul r z _ hm _ _).trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl
      ((gs_res r z le_top hm _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _))))
  constructor
  · intro h T ρ z J hJ
    exact (congrArg (gs ρ.left z _) (h _)).trans (key _ ρ.left z _ (hJ.mem _ _))
  · intro h j
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB y
    have e := h _ (𝟙 _) y J hJ
    refine Eq.trans ?_ (key _ (𝟙 _) y j hy).symm
    refine (sec_trans s' (𝟙 _) y hy (hJ.mem _ (𝟙 _))).trans ?_
    rw [sec_trans s (𝟙 _) y hy (hJ.mem _ (𝟙 _)), _root_.mul_assoc]
    exact congrArg _ e

theorem phiRel_tor (hG : GlobalFnsSt) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) (s s' : Fam D F N) :
    PhiRel D F N p w s s' ↔
      ∀ α j, (s'.s α).f j = DegPre.constBF D F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  have tr : DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]; exact tr_fst D F _
    · rw [Category.id_comp]
      refine (tr_pr D F _).trans ?_
      rw [hτ.1, MonObj.comp_one, _root_.mul_one]
  have v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      (uVal D F N α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd α)).val) := by
    intro α T ρ z J hJ
    have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have hu : uVal D F N α p.g.b ρ z J = 1 := by
      rw [uVal, hτ.1]
      simp only [MonObj.comp_one]
      unfold cubN
      simp only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]
    have h₁ := val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ
    have h₂ := val_const w 1 (fun y J hJ => by
      rw [hw.2 y J hJ, gs_eq _ _ ⊤ trivial, map_one, map_one]; rfl) (ρ ≫ fst _ _).left z hJ
    rw [gs_eq _ _ ⊤ trivial, map_one, map_one] at h₂
    rw [hu, _root_.one_mul, val_mul hJ, Units.val_mul, h₁, h₂, _root_.mul_one]
  rw [phiRel_iff hG p w hw.1]
  constructor
  · intro H α
    refine (sval_const α _ _ _).2 fun T ρ z J hJ => ?_
    have := H α α (by rw [hy, add_zero]) T ρ z J hJ
    rwa [v α T ρ z J hJ, tr, Category.comp_id] at this
  · intro H α β h T ρ z J hJ
    obtain rfl : α = β := by rw [← h, hy, add_zero]
    rw [v α T ρ z J hJ, tr, Category.comp_id]
    exact (sval_const α _ _ _).1 (H α) T ρ z J hJ

theorem torus_weight : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) τ, p.y = 0 → IsTor τ p.g → ∀ w, TXFrame N p w → FrmOne w ∧ ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N p w s s' ↔ ∀ α j, (s'.s α).f j = DegPre.constBF D.toPre F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  intro hL R _ _ _ I hI D A G _ _ _ U F _ _ _ N hN p τ hy hτ w hw
  obtain ⟨w₀, hw₀⟩ := (CoefBasic.coef_basic R D.toPre F N p.g).2.1 hτ.1
  have h₁ : FrmOne w := ⟨hw.1, fun z J hJ =>
    ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p).2 w w₀ hw (txFrame_of_one D.tau_bimult p hy hτ hw₀) z J hJ).trans (hw₀.2 z J hJ)⟩
  exact ⟨h₁, phiRel_tor hL.1.globalFns p hy hτ h₁⟩

end GlobalTheory.UT.TorusWeight
end
end

