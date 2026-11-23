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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalAdd
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalAdd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

theorem val₂_one (f g : A ⟶ A) (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε))
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good Lr.L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ h₀ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this

omit [IsCommMonObj A] in
theorem val_pull₂ (f g : A ⟶ A) (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good Lr.L z J) (a b : T ⟶ A) :
    val (LB.pullGen Lr.L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl

theorem ros_sum (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g f' g' : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    (u' : LB.Gen (LB.LinComb Lr.L (rosatiφ A f' g') rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u' (zero2 A)) (LB.oneGen Lr.L))
    (w : LB.Gen (LB.LinComb Lr.L (rosatiφ A (f * f') (g * g')) rosatiε)) (hw : w.IsGen)
    (w₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ w (zero2 A)) (LB.oneGen Lr.L))
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (x y : T ⟶ A) :
    val₂ w z J x y * cubV c z J x (y ≫ g) (y ≫ g') =
      cubV c z J (x ≫ f) (x ≫ f') y * (val₂ u z J x y * val₂ u' z J x y) := by
  let p : A ⊗ A ⟶ A := fst A A
  let q : A ⊗ A ⟶ A := snd A A
  let e : 𝟙_ (Over S) ⟶ A ⊗ A := lift 1 1
  have e₀ : e ≫ p = 1 := lift_fst _ _
  have e₁ : e ≫ q = 1 := lift_snd _ _
  have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (hG _ _ hA).2
  have he : e.left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  have ev : ∀ {T' : Over S} (σ : T' ⟶ A ⊗ A) {z : T'.left} {J}, Good Lr.L z J →
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ w (lift p q).left)
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift p (lift (q ≫ g) (q ≫ g'))).left)) σ.left z J =
        val₂ w z J (σ ≫ p) (σ ≫ q) * cubV c z J (σ ≫ p) (σ ≫ q ≫ g) (σ ≫ q ≫ g') ∧
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (p ≫ f) (lift (p ≫ f') q)).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift p q).left) (LB.pullGen Lr.L _ _ u' (lift p q).left)))
        σ.left z J = cubV c z J (σ ≫ p ≫ f) (σ ≫ p ≫ f') (σ ≫ q) *
          (val₂ u z J (σ ≫ p) (σ ≫ q) * val₂ u' z J (σ ≫ p) (σ ≫ q)) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ _ _ w σ hJ _ _) (val_cub c σ hJ _ _ _)),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ _ _ u σ hJ _ _) (val_pull₂ _ _ u' σ hJ _ _))))⟩
  have key := (ev (lift x y) hJ).1.symm.trans (Eq.trans (gen_unique' Lr.isLB (fun V _ k => by
      refine (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := V) _ (prod_cub (p ≫ f) (p ≫ f') q k)
        (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _ (prod_ros f g p q k) (prod_ros f' g' p q k))).trans
        (Eq.trans ?_ (prod_sum₂ (K := Fin 6) (K' := thK) (U := V) _ (prod_ros (f * f') (g * g') p q k)
          (prod_cub p (q ≫ g) (q ≫ g') k)).symm)
      rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc p]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) _ e.left he sj
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hw _) (pullGen_isGen _ _ _ _ c.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _) (mulGen_isGen _ _ _ _ _ _ _
        (pullGen_isGen _ _ _ _ hu _) (pullGen_isGen _ _ _ _ hu' _))) (fun y I hI => by
      have C : IsCub (cubV c y I) := isCub_cubV c hI
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁, val₂_one _ _ w w₀ hI, val₂_one _ _ u h₀ hI, val₂_one _ _ u' h₀' hI, C.face, C.face₃]
      simp) _ (lift x y).left z J hJ) (ev (lift x y) hJ).2)
  have r₀ : lift x y ≫ p = x := lift_fst _ _
  have r₁ : lift x y ≫ q = y := lift_snd _ _
  simp only [← Category.assoc, r₀, r₁] at key
  exact key

end GlobalTheory.TauBalAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorPointZeroOfPowerEigen
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaEigen

theorem gs_pow {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem sval_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (pr : Y ⟶ X) (a b : ℤ) (l : ℕ)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => a)))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => b)))
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) : sval t r z J = sval th r z J ^ l := by
  have key : ∀ j : L.ι, (t.f (fun _ => j) : Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j))) =
      (show Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) from th.f (fun _ => j)) ^ l := fun j =>
    fn_ext (V := LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) fun y hy => by
      obtain ⟨I, hI, e⟩ := exists_good L hL y (K := PUnit) (fun _ => 𝟙 Y ≫ pr) (fun _ => j) (fun _ _ _ => rfl)
        (fun _ => Set.mem_iInter.1 hy 0)
      have := hp y I hI
      rw [sval_of t _ y I (fun _ => j) (fun _ => e PUnit.unit),
        sval_of th _ y I (fun _ => j) (fun _ => e PUnit.unit)] at this
      exact this.trans (gs_pow _ y _ hy _ l).symm
  exact (congrArg (gs r z _) (key _)).trans (gs_pow r z _ (hJ.mem (fun _ : Fin 1 => pr) r) _ l)

theorem exists_gen_of_eigen {X Y : Scheme.{0}} [IsIntegral Y] (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {L : LB X} (hL : L.IsLB) (pr m : Y ⟶ X) (τ : Y ⟶ Y) (hm : τ ≫ pr = m) (l : ℕ) (hl : 1 ≤ l)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => ((1 : ℕ) : ℤ))))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => (l : ℤ)))) (h0 : ∃ j, th.f j ≠ 0)
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l) (c : Γ(Y, ⊤)ˣ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![(l : ℤ), -(l : ℤ)])) (hα : α.IsGen)
    (H : ∀ y J, Good L y J →
      gs (𝟙 Y) y ⊤ c.val * sval t (𝟙 Y) y J = (val α (𝟙 Y) y J).val * sval t (𝟙 Y ≫ τ) y J) :
    ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![m, pr] ![1, -1]), r.IsGen := by
  obtain ⟨s₁, h₁⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => m) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, hm, Nat.cast_one])
    (DVR.pullSec L _ _ th τ)
  obtain ⟨s₂, h₂⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => pr) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, Nat.cast_one]) th
  obtain ⟨u, hu, h₃⟩ := exists_gen hL (K' := Fin 2) (φ' := ![m, pr]) (ε' := ![(l : ℤ), -(l : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv]
      exact _root_.mul_comm _ _)
    (DVR.scaleGen c (LB.invGen L _ _ α)) (DVR.scaleGen_isGen _ _ (DVR.invGen_isGen _ _ _ _ hα))
  have h₄ : ∀ y J, Good L y J → val u (𝟙 Y) y J = gm (𝟙 Y) y ⊤ c * (val α (𝟙 Y) y J)⁻¹ := fun y J hJ =>
    (h₃ _ _ y J hJ).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res _ y le_top (hJ.mem ![pr, m] (𝟙 Y)) c) (val_inv α (𝟙 Y))))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow X Y hN L hL m pr l hl s₁ s₂ u hu
    (by
      obtain ⟨y⟩ : Nonempty Y := inferInstance
      choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hJ' : Good L y J := hJ
      refine ⟨fun _ => J (𝟙 Y ≫ pr), fun e => ?_⟩
      refine RootUnit.sec_gs_ne_zero th h0 y _ (hJ'.mem (fun _ : Fin 1 => pr) (𝟙 Y)) ?_
      refine (h₂ _ _ y J hJ').symm.trans ((congrArg (gs (𝟙 Y) y _) e).trans ?_)
      exact (RootUnit.gs_id y _ (hJ'.mem (fun _ : PUnit => pr) (𝟙 Y)) _).trans (map_zero _))
    (fun y J hJ => by
      have e₁ := (h₁ _ (𝟙 Y) y J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ th τ _ y hJ)
      have e₂ := h₂ _ (𝟙 Y) y J hJ
      have e := H y J hJ
      rw [hp y J hJ, sval_pow hL pr _ _ l th t hp _ y J hJ, gs_unit _ y ⊤ (by trivial)] at e
      refine (congrArg (· ^ l) e₁).trans (Eq.trans ?_ (congrArg₂ (fun a b => Units.val a * b ^ l) (h₄ y J hJ) e₂).symm)
      change _ = Units.val (_ * _) * _
      rw [Units.val_mul, mul_right_comm, e, mul_right_comm, Units.mul_inv, _root_.one_mul])
  exact ⟨r, hr⟩

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (l : ℕ), 1 ≤ l → ∀ (th : EA P p 1) (t : EA P p l) (θ : ThetaGrp P.A P.L (l : ℤ) (Over.mk p)) (c : Fˣ), th ≠ 0 → (∀ z J, Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((l : ℕ) : ℤ)) t.sec (𝟙 _) z J = sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th.sec (𝟙 _) z J ^ l) → IsActOf P.A P.L (l : ℤ) θ t.sec (c.val • t).sec → θ.pt = 1 := by
  intro S P F _ p l hl th t θ c h0 hp hθ
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  haveI : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  haveI := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  have hs : Smooth (fst (Over.mk p) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst p P.A.hom))
  have hN := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hs).2.1
  let φ : F →+* Γ((Over.mk p ⊗ P.A).left, ⊤) :=
    (fst (Over.mk p) P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  obtain ⟨r, hr⟩ := exists_gen_of_eigen (fun y => (hN y).2) P.isLB (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (by rw [← Over.comp_left, translT, lift_snd]) l hl th.sec t.sec
    (not_forall.1 fun h => h0 ((SecMod.eq_zero_iff th).2 h)) hp (Units.map φ.toMonoidHom c) θ.φ θ.isGen
    (fun y J hJ => (SecMod.sval_smul hJ (𝟙 _) c.val t).symm.trans (ThetaLin.sval_of_isTwistPull P.A hθ (𝟙 _) y hJ))
  exact P.ktriv F p θ.pt fun _ => ⟨⊤, trivial, exists_isGen_pull (translDiff P.A P.L θ.pt) r hr _⟩

end GlobalTheory.ThetaEigen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueExpansionOfChartExpansion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))))

theorem scal_specMap {A C : Type} [CommRing A] [CommRing C] (φ : A →+* C) {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (a : A) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) a = scal p (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact congrArg p.appTop.hom e.symm

theorem gs_scal_inv_mul {R : Type} [CommRing R] [IsDomain R] {Y₁ Y₂ Z : Scheme.{0}}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of (FractionRing R))) (p₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂) (h : r₂ ≫ p₂ = ((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) (z : Z)
    {a : R} (ha : a ≠ 0) :
    gs r₁ z ⊤ (scal p₁ (algebraMap R (FractionRing R) a)⁻¹) * gs r₂ z ⊤ (scal p₂ a) = 1 := by
  have k : ∀ {S : Type} [CommRing S] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of S)) (r : Z ⟶ Y) (c : S),
      gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
    intro S _ Y p r c
    calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
      _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
      _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl
  have e : scal (((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) a =
      scal (r₁ ≫ p₁) (algebraMap R (FractionRing R) a) :=
    (scal_specMap _ _ a).trans (scal_specMap _ _ _)
  have ha' : algebraMap R (FractionRing R) a ≠ 0 := fun h0 =>
    ha (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
  rw [k p₁, k p₂, h, e, ← gs_mul _ z ⊤ trivial, scal, scal, ← map_mul, ← map_mul, inv_mul_cancel₀ ha', map_one, map_one,
    gs_eq _ z ⊤ trivial, map_one, map_one]

theorem expF_of_expands : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ t s hσ hK hE
  obtain ⟨r, hr, τ, f, hτ, hf, hE⟩ := hE
  have hL := hM.LG
  have hX := fun τ₀ τ' f' h₁ h₂ h₃ => expT_of_expandsAt R I D A G U U' hM k τ τ₀ τ' f f' h₁ h₂ h₃ hE
  clear hE hM
  cases U'
  dsimp only at hL
  subst hL
  cases hσ
  obtain ⟨e₁, -, e₃, -⟩ := GlobalTheory.UnitSec.same_exists R D.toPre G U.P.L.L U.P.L.isLB k
  obtain ⟨τ', hτ'⟩ := e₁ τ
  obtain ⟨f', hf'⟩ := e₃ f
  refine ⟨1, fun _ => (algebraMap R (FractionRing R) r)⁻¹, fun _ => τ', fun _ => f',
    fun _ => hX τ τ' f' HEq.rfl hτ' hf', ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    refine (hK Z rA y h₁ z JA JG hJA hJG).trans ?_
    rw [Fin.sum_univ_one, hτ' Z rG z JG hJG, h₂]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal hτ y z hJG)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rA y ?_ z hr).symm)
    have w₁ := Over.w (fst (TFK (R := R) (FractionRing R)) A.A)
    have w₂ := Over.w (snd (TFK (R := R) (FractionRing R)) A.A)
    have w₃ := Over.w U.gen.hom
    have w₄ : (rA ≫ (fst (TFK (R := R) (FractionRing R)) A.A).left) ≫ jFK (R := R) (FractionRing R) =
        y ≫ pullback.snd G.hom (jK R) :=
      (Category.assoc _ _ _).trans ((congrArg (rA ≫ ·) (w₁.trans w₂.symm)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ A.A.hom) h₁).trans ((Category.assoc _ _ _).trans (congrArg (y ≫ ·) w₃)))))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) w₄.symm)
  · intro α Z rF rB h₁ z J hJ
    rw [Fin.sum_univ_one, hf' α Z rB z J hJ, h₁]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal (hf α) rF z hJ)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rF rF ?_ z hr).symm)
    have w₁ := Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)
    exact (congrArg (rF ≫ ·) w₁.symm).trans ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm)

end GlobalTheory.UU
end

