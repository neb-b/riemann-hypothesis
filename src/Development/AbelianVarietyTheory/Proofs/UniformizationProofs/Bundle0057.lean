module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAdditionFactorGeneratorTransported
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddGeneric

theorem exists_additionFactor_generator_value {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {T : Over S}
    (x y : T ⟶ G) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![x.left, y.left, (x * y).left, (x * y⁻¹).left] ![2, 2, -1, -1]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P.L.L z J →
        val t ρ.left z J = kap0 P.c P.sym z J (ρ ≫ x) (ρ ≫ y) := by
  let r₀ := LB.pullGen P.L.L (fun _ : PUnit => eSec G) (fun _ => 1) P.L.rig T.hom
  have hr₀ : r₀.IsGen := DVR.pullGen_isGen _ _ _ _ P.L.rigGen _
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := ![x.left, y.left, (x * y).left, (x * y⁻¹).left])
    (ε' := ![2, 2, -1, -1]) (fun U _ h => by
      have o : ∏ _k : PUnit, h (T.hom ≫ eSec G) ^ (1 : ℤ) = h (1 : T ⟶ G).left := by
        rw [Fintype.prod_unique, zpow_one, one_left]
      refine (DVR.prod_sum₂ (U := U) (K := thK ⊕ Fin 2) (K' := PUnit ⊕ PUnit) _
        (DVR.prod_sum₂ (U := U) (K := thK) (K' := Fin 2) _ (prod_cub x y y⁻¹ h) (DVR.prod_neg _ _ (prod_sym y h)))
        (DVR.prod_sum₂ (U := U) (K := PUnit) (K' := PUnit) _ o o)).trans ?_
      rw [mul_inv_cancel_right, mul_inv_cancel]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen P.L.L _ _ _ _
      (LB.mulGen P.L.L _ _ _ _ (LB.pullGen P.L.L (thφ G (x3 G)) thε P.c.t (lift x (lift y y⁻¹)).left)
        (LB.invGen P.L.L _ _ (LB.pullGen P.L.L _ _ P.sym y.left)))
      (LB.mulGen P.L.L _ _ _ _ r₀ r₀))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.c.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _))) (DVR.mulGen_isGen _ _ _ _ _ _ _ hr₀ hr₀))
  refine ⟨t, ht, fun T' ρ z J hJ => ?_⟩
  have e₀ : val r₀ ρ.left z J =
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T'.hom z J :=
    (val_pull hJ _ _ _).trans (by rw [Over.w ρ])
  refine ((hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub P.c ρ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ e₀))))).trans ?_
  rw [kap0, sq, GrpObj.comp_inv, Over.comp_left]

theorem exists_additionFactor_generator_transported {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G)
    {A : Over S'} [GrpObj A] [IsCommMonObj A] {Φ : A.left ⟶ G.left} (hw : Φ ≫ G.hom = A.hom ≫ f)
    (mul : ∀ (T : Over S') (x y : T ⟶ A), toBase hw (x * y) = toBase hw x * toBase hw y)
    {L' : LB A.left} (hL' : L'.IsLB) (u : LB.Iso L' (P.L.L.pull Φ)) (hu : PGen u) {Y : Over S'} (p q s d : Y ⟶ A)
    (hs : s = p * q) (hd : d = p * q⁻¹) :
    ∃ a : LB.Gen (LB.LinComb L' (K := Fin 4) ![p.left, q.left, s.left, d.left] ![2, 2, -1, -1]), a.IsGen ∧
      ∀ (T : Over S') (ρ : T ⟶ Y) (z : T.left) (J J'), Good P.L.L z J → Good L' z J' →
        ∀ W : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw u x.left z (J (x.left ≫ Φ)) (J' x.left)) →
        @id (T.left.presheaf.stalk z)ˣ (kap0 P.c P.sym (T := Over.mk (T.hom ≫ f)) z J (toBase hw (ρ ≫ p)) (toBase hw (ρ ≫ q))) =
          W (ρ ≫ p) ^ 2 * W (ρ ≫ q) ^ 2 * (W ((ρ ≫ p) * (ρ ≫ q)))⁻¹ * (W ((ρ ≫ p) * (ρ ≫ q)⁻¹))⁻¹ *
            val a ρ.left z J' := by
  subst hs hd
  obtain ⟨t, ht, hv⟩ := exists_additionFactor_generator_value P (toBase hw p) (toBase hw q)
  have hψ : ∀ k : Fin 4, ![p.left, q.left, (p * q).left, (p * q⁻¹).left] k ≫ Φ = 𝟙 Y.left ≫
      ![(toBase hw p).left, (toBase hw q).left, (toBase hw p * toBase hw q).left,
        (toBase hw p * (toBase hw q)⁻¹).left] k := by
    intro k
    rw [Category.id_comp]
    have e : toBase hw (p * q⁻¹) = toBase hw p * (toBase hw q)⁻¹ :=
      (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul Y) q))
    rw [← e, ← mul]
    fin_cases k <;> rfl
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps hu P.L.isLB hL' (𝟙 Y.left) hψ t ht
  refine ⟨a, ha, fun T ρ z J J' hJ hJ' W hW => ?_⟩
  have e₁ := DegPull.pmaps_val hψ H ρ.left z hJ hJ'
  let ρ' : Over.mk (T.hom ≫ f) ⟶ Over.mk (Y.hom ≫ f) := Over.homMk ρ.left (by
    show ρ.left ≫ Y.hom ≫ f = T.hom ≫ f
    rw [← Category.assoc, Over.w ρ])
  have e₂ := hv _ ρ' z J hJ
  have e₃ : ∀ x : Y ⟶ A, ρ' ≫ toBase hw x = toBase hw (ρ ≫ x) := fun x =>
    Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [e₃, e₃] at e₂
  rw [Category.comp_id] at e₁
  refine e₂.symm.trans (e₁.trans (congrArg (· * val a ρ.left z J') ?_))
  rw [← GrpObj.comp_inv, ← MonObj.comp_mul, ← MonObj.comp_mul, ← zpow_neg_one (W _), ← zpow_neg_one (W _),
    ← zpow_natCast (W _), ← zpow_natCast (W _), hW, hW, hW, hW, Fin.prod_univ_four]
  rfl

theorem cancel_alg {B : Type} [CommRing B] {n : ℕ} (a b c d k k' : Bˣ) (r s s' : B) (t t' : Fin n → B)
    (hk : k = a ^ 2 * b ^ 2 * c⁻¹ * d⁻¹ * k')
    (h : ∑ i, (a.val ^ 2 * t i) * (b.val ^ 2 * t' i) = r * k.val * ((c.val ^ 1 * s) * (d.val ^ 1 * s'))) :
    ∑ i, t i * t' i = r * k'.val * (s * s') := by
  apply (a ^ 2 * b ^ 2).isUnit.mul_left_cancel
  rw [Finset.mul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h.trans ?_)
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
  · have hc := c.inv_mul
    have hd := d.inv_mul
    rw [hk]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (r * a.val ^ 2 * b.val ^ 2 * k'.val * s * s' * (d⁻¹).val * d.val) * hc +
      (r * a.val ^ 2 * b.val ^ 2 * k'.val * s * s') * hd

theorem isUnit_scal {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of (FractionRing R))) {r : R} (hr : r ≠ 0) : IsUnit (scal (p ≫ jK R) r) := by
  have e : scal (jK R) r = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) :=
    (congrArg (fun q => q.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm
  have h : IsUnit (algebraMap R (FractionRing R) r) :=
    IsUnit.mk0 _ fun h => hr ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
  have : IsUnit (scal (jK R) r) := e ▸ h.map _
  exact this.map p.appTop.hom

theorem addA_of_addG : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (θ : U.SecGT (𝟙_ _) 1) (r : R) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := R) F))) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := R) F))), r ≠ 0 → U.AddG θ r σ σ' → U.PullG F (toUnit _) 1 θ th → (∀ i, U.PullG F (toUnit _) 2 (σ i) (t i) ∧ U.PullG F (toUnit _) 2 (σ' i) (t' i)) → AddA A (TFK (R := R) F) th t t' := by
  intro R _ _ D I A G _ _ U F _ _ θ r n σ σ' th t t' hr hadd hθ hσ
  have := U.gen_hom
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  obtain ⟨u, hu, huv⟩ := ThetaBaseChange.exists_unpull U.wA_gen U.gen.inv.left hi rfl
  have hw : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ G.hom = A.A.hom ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ jK R) (Over.w U.gen.inv)
  have tb : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), toBase hw x =
      toBase (A := G) (A' := (Over.pullback (jK R)).obj G) (g := pullback.fst G.hom (jK R)) pullback.condition
        (x ≫ U.gen.inv) := fun T x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
  have mul : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x y : T ⟶ A.A),
      toBase hw (x * y) = toBase hw x * toBase hw y := fun T x y => by
    rw [tb, tb, tb, MonObj.mul_comp, toBase_mul_pullback]
  obtain ⟨a, ha, hv⟩ := exists_additionFactor_generator_transported U.P hw mul A.isLB u hu (Y := TFK (R := R) F ⊗ (A.A ⊗ A.A))
    (snd _ _ ≫ fst A.A A.A) (snd _ _ ≫ snd A.A A.A) (snd _ _ ≫ (fst A.A A.A * snd A.A A.A))
    (snd _ _ ≫ (fst A.A A.A * (snd A.A A.A)⁻¹)) (MonObj.comp_mul _ _ _)
    ((MonObj.comp_mul _ _ _).trans (by rw [GrpObj.comp_inv]))
  have hun := isUnit_scal (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom hr
  refine ⟨scaleGen hun.unit a, scaleGen_isGen _ ha, fun T ρ x y z J hJ => ?_⟩
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let W : (T ⟶ A.A) → (T.left.presheaf.stalk z)ˣ := fun p =>
    gw u p.left z (JG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (J p.left)
  have k₀ := hv T (lift ρ (lift x y)) z JG J hJG hJ W (fun _ => rfl)
  have ex : lift ρ (lift x y) ≫ snd _ _ ≫ fst A.A A.A = x := by simp
  have ey : lift ρ (lift x y) ≫ snd _ _ ≫ snd A.A A.A = y := by simp
  rw [ex, ey] at k₀
  have pull : ∀ (k : ℕ) (s : U.SecGT (𝟙_ _) k) (s' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))),
      U.PullG F (toUnit _) k s s' → ∀ p : T ⟶ A.A,
      (W p).val ^ k * sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ))
        s' (lift ρ p).left z J =
      @id (T.left.presheaf.stalk z) (sval s (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left z JG) := by
    intro k s s' h p
    have e₁ : (p.left ≫ U.gen.inv.left) ≫ U.gen.hom.left = p.left := by rw [Category.assoc, hi, Category.comp_id]
    have e := h T.left (lift ρ p).left (p.left ≫ U.gen.inv.left)
      (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left
      ((congrArg (fun q => q.left) (lift_snd ρ p)).trans e₁.symm)
      ((congrArg (fun q => q.left) (lift_snd _ (toBase hw p))).trans (Category.assoc _ _ _).symm)
      (by
        rw [← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Rosenlicht.toUnit_left, Rosenlicht.toUnit_left]
        show T.hom ≫ jK R = ρ.left ≫ jFK (R := R) F ≫ jK R
        rw [← Category.assoc]
        exact congrArg (· ≫ jK R) (Over.w ρ).symm) z J JG hJ hJG
    rw [e₁, Category.assoc] at e
    refine Eq.trans (congrArg (fun q : (T.left.presheaf.stalk z)ˣ => q.val ^ k * _) ?_) e
    exact huv _ p.left z _ _ (hJG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (hJ p.left)
  have add := hadd (Over.mk (T.hom ≫ jK R)) (toBase hw x) (toBase hw y) z JG hJG
  have e : toBase hw (x * y⁻¹) = toBase hw x * (toBase hw y)⁻¹ :=
    (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul T) y))
  rw [← e, ← mul] at add
  have key := cancel_alg (W x) (W y) (W (x * y)) (W (x * y⁻¹)) _ _ _ _ _ _ _ k₀
    ((Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (pull 2 _ _ (hσ i).1 x) (pull 2 _ _ (hσ i).2 y)).trans
      (add.trans (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (pull 1 _ _ hθ _).symm (pull 1 _ _ hθ _).symm))))
  refine key.trans (congrArg (· * _) ?_)
  rw [val_scaleGen _ _ _ hJ, Units.val_mul]
  refine congrArg (· * _) (Eq.trans ?_ (gs_unit _ z ⊤ trivial _))
  refine Eq.trans ?_ ((gs_pull (𝟙 _) (lift ρ (lift x y)).left z ⊤ trivial _).trans (by rw [Category.id_comp]))
  refine congrArg (gs (𝟙 T.left) z ⊤) ?_
  show scal (T.hom ≫ jK R) r = scal ((lift ρ (lift x y)).left ≫ (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom ≫ jK R) r
  rw [← Category.assoc, Over.w]

end GlobalTheory.AddGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalAdditionFactorGenerator
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU

theorem exists_cubical_addition_factor_generator {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {Y : Over S}
    (a b : Y ⟶ G) :
    ∃ κ : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![a.left, b.left, (a * b).left, (a * b⁻¹).left] ![2, 2, -1, -1]),
      κ.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ Y) (z : T.left) (J), Good P.L.L z J →
        val κ ρ.left z J = kap0 P.c P.sym z J (ρ ≫ a) (ρ ≫ b) := by
  let cu := LB.pullGen P.L.L (thφ G (x3 G)) thε P.c.t (lift a (lift b b⁻¹)).left
  let sy := LB.invGen P.L.L _ _ (LB.pullGen P.L.L _ _ P.sym b.left)
  let rg := LB.pullGen P.L.L (fun _ : PUnit => eSec G) (fun _ => 1) P.L.rig Y.hom
  have gc : cu.IsGen := DVR.pullGen_isGen _ _ _ _ P.c.isGen _
  have gy : sy.IsGen := DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _)
  have gr : rg.IsGen := DVR.pullGen_isGen _ _ _ _ P.L.rigGen _
  obtain ⟨κ, hκ, hv⟩ := exists_gen P.L.isLB (K' := Fin 4)
    (φ' := ![a.left, b.left, (a * b).left, (a * b⁻¹).left]) (ε' := ![2, 2, -1, -1]) (fun U _ h => by
      have e₂ : ∏ k : Fin 2, h (b.left ≫ ![(ι[G]).left, 𝟙 G.left] k) ^ (-(![1, -1] : Fin 2 → ℤ) k) =
          (h (b⁻¹).left * (h b.left)⁻¹)⁻¹ := by
        rw [← prod_sym b h]; simp only [zpow_neg, Finset.prod_inv_distrib]
      have e₃ : ∏ _k : PUnit, h (Y.hom ≫ eSec G) ^ (1 : ℤ) = h (1 : Y ⟶ G).left := by
        rw [Fintype.prod_unique, zpow_one, one_left]
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (prod_cub a b b⁻¹ h) e₂)) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) e₃ e₃)))).trans ?_
      rw [mul_inv_cancel_right, mul_inv_cancel b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen P.L.L _ _ _ _ (LB.mulGen P.L.L _ _ _ _ cu sy) (LB.mulGen P.L.L _ _ _ _ rg rg))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ gc gy) (DVR.mulGen_isGen _ _ _ _ _ _ _ gr gr))
  refine ⟨κ, hκ, fun T ρ z J hJ => (hv _ _ z J hJ).trans ?_⟩
  have vr : val rg ρ.left z J =
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T.hom z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Over.w ρ]
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    (val_cub P.c ρ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) vr vr)))).trans ?_
  rw [kap0, GrpObj.comp_inv, pow_two]
  rfl

theorem exists_addSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : CP G) (T₀ : Over S) (θ : LB.Sec (LB.LinComb P.L.L (K := Fin 1) (fun _ => (snd T₀ G).left) (fun _ => ((1 : ℕ) : ℤ)))) (ρ₀ : G ⊗ G ⟶ T₀), ∃ v : LB.Sec (LB.LinComb P.L.L (K := Fin 1 ⊕ Fin 1) (Sum.elim (fun _ => (fst G G).left) (fun _ => (snd G G).left)) (Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ)))), ∀ (T : Over S) (x y : T ⟶ G) (z : T.left) (J), Good P.L.L z J → sval v (lift x y).left z J = (kap0 P.c P.sym z J x y).val * (sval θ (lift (lift x y ≫ ρ₀) (x * y)).left z J * sval θ (lift (lift x y ≫ ρ₀) (x * y⁻¹)).left z J) := by
  intro S G _ _ P T₀ θ ρ₀
  obtain ⟨κ, hκ, hv⟩ := exists_cubical_addition_factor_generator P (fst G G) (snd G G)
  obtain ⟨v, hs⟩ := exists_sec P.L.isLB (K' := Fin 1 ⊕ Fin 1)
    (φ' := Sum.elim (fun _ => (fst G G).left) (fun _ => (snd G G).left))
    (ε' := Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ))) (fun U _ h => by
      have e : ∀ p : G ⊗ G ⟶ G, ∏ _k : Fin 1, h ((lift ρ₀ p).left ≫ (snd T₀ G).left) ^ ((1 : ℕ) : ℤ) = h p.left :=
        fun p => by rw [Fintype.prod_unique, ← Over.comp_left, lift_snd, Nat.cast_one, zpow_one]
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (e _) (e _))))).trans ?_
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (H1.SectionArithmetic.mulSec (genSec κ hκ) (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec θ (lift ρ₀ (fst G G * snd G G)).left)
      (H1.SectionArithmetic.pullSec θ (lift ρ₀ (fst G G * (snd G G)⁻¹)).left)))
  refine ⟨v, fun T x y z J hJ => (hs _ _ z J hJ).trans ?_⟩
  rw [H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ,
    H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, sval_genSec _ _ _ z hJ, hv T _ z J hJ, ← Over.comp_left, ← Over.comp_left,
    comp_lift, comp_lift, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtPtOfCharacter
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_gtPt_of_character : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (χ₀ : Multiplicative D.X →* Fˣ), ∃ g : GtPtF D F, g.b = DegPre.zeroF D F ∧ (∀ α z J, Good D.P.L z J → (val (g.s α) (𝟙 _) z J).val = gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of F))) (χ₀ (Multiplicative.ofAdd α)).val)) ∧ (∀ N : ℕ, χ₀ ^ N = 1 → GtTors D N g) ∧ (g.IsZero ↔ χ₀ = 1) := by
  intro R _ _ D F _ _ χ₀
  refine ⟨TorusExt.torusPt D F (Additive.ofMul χ₀), TorusExt.torusPt_b _, fun α z J hJ => ?_, fun N hN => ?_, ?_⟩
  · refine (congrArg Units.val (TorusExt.torusPt_val χ₀ α hJ)).trans ?_
    exact (gs_eq (𝟙 _) z ⊤ trivial _).symm
  · refine ⟨_, (TorusExt.isNsmul_iff_eq N _ _).2 rfl, (TorusExt.isZero_iff_eq _).2 ?_⟩
    rw [← map_nsmul, ← ofMul_pow, hN, ofMul_one, map_zero]
  · rw [TorusExt.isZero_iff_eq, map_eq_zero_iff _ TorusExt.torusPt_injective]
    exact ofMul_eq_zero
end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanGenerateValuationRingsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_integral_families_span_generate_valuationRings : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F₁ : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F₁ i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F₁) = ⊤ ∧ (∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ s : Fam D.toPre F k, (∃ g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1)) → ∃ c : Fin n → S, ∀ α, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (ιF (c i)))) := by
  first | exact @GlobalTheory.FamGen.exists_span_generate | exact GlobalTheory.FamGen.exists_span_generate | (intros; apply GlobalTheory.FamGen.exists_span_generate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftUnitTensor
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU

theorem exists_lift_unit_tensor {S Z : Scheme.{0}} (X : Over S) (q : Z ⟶ X.left) :
    ∃ r : Z ⟶ (𝟙_ (Over S) ⊗ X).left, r ≫ (snd _ X).left = q ∧ r ≫ (fst _ X).left = q ≫ X.hom := by
  refine ⟨q ≫ (λ_ X).inv.left, ?_, ?_⟩
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_snd, Over.id_left, Category.comp_id]
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_fst]
    rfl

theorem expandsAt_of_expT : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → U.ExpT (𝟙_ _) k σ' f' → ∀ e, U'.ExpandsAt e k σ f := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U
  cases P
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  dsimp only at hL hgt hw
  subst hL hgt
  obtain rfl := eq_of_heq hw
  obtain rfl := eq_of_heq hσ
  obtain ⟨S, hS⟩ := hE e
  refine DVR.expandsAt_of_val U' e k σ f S fun y J hJ => ?_
  obtain ⟨rG, hG₁, hG₂⟩ := exists_lift_unit_tensor G (fstG I e G).left
  obtain ⟨rB, hB₁, hB₂⟩ := exists_lift_unit_tensor D.toPre.P.A (U'.gt e).pG.left
  have hc : (U'.gt e).pG.left ≫ D.toPre.P.A.hom = (fstG I e G).left ≫ G.hom :=
    (Over.w (U'.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H := hS _ (𝟙 _) rG rB (hG₁.trans (Category.id_comp _).symm) (hB₁.trans (Category.id_comp _).symm)
    (hB₂.trans (hc.trans hG₂.symm)) y
  have hf : ∀ α, sval (f' α) rB y J = sval (f α) (DVR.pGl U' e) y J := fun α => by
    rw [hB α _ rB y J hJ, hB₁]
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · choose JG hJG using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U'.LG.isLB (ψ y)
    exact (hf α).symm.trans ((H JG J hJG hJ).1 α hα)
  · obtain ⟨JG, hJG, eJ⟩ := exists_good U'.LG.L U'.LG.isLB y (fun _ : PUnit => (fstG I e G).left) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    have e₀ : JG (fstG I e G).left = jL := eJ PUnit.unit
    have H₂ := (H JG J hJG hJ).2
    have hs : sval σ' rG y JG = DVR.sv U' k σ (DVR.fGl I G e) y jL := by
      rw [hG _ rG y JG hJG, hG₁]
      exact sval_of σ _ y JG (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact e₀)
    simp only [Category.id_comp, e₀, hs, hf] at H₂
    rw [Units.val_pow_eq_pow_val]
    exact H₂

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsOrderTranslates
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem stalkMap_mem_map_base {R : Type} [CommRing R] (I : Ideal R) {Z Z' : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of R)) (p' : Z' ⟶ Spec (CommRingCat.of R)) (ρ : Z' ⟶ Z) (h : ρ ≫ p = p') (z : Z')
    (a : Z.presheaf.stalk (ρ z))
    (ha : a ∈ I.map ((Z.presheaf.germ ⊤ (ρ z) trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))) :
    (ρ.stalkMap z).hom a ∈ I.map ((Z'.presheaf.germ ⊤ z trivial).hom.comp
      (p'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  subst h
  have := Ideal.mem_map_of_mem (ρ.stalkMap z).hom ha
  rw [Ideal.map_map] at this
  convert this using 2
  ext r
  exact (Scheme.Hom.germ_stalkMap_apply ρ ⊤ z trivial _).symm

theorem map_base_eq_bot {R : Type} [CommRing R] (I : Ideal R) {Z : Scheme.{0}}
    (ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I))) (z : Z) :
    I.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
      ((ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro r hr
  have e := congrArg (fun q => q.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero] at e
  rw [RingHom.mem_ker, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  erw [← e]
  simp only [map_zero]

theorem exists_order_translates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f₀ : SecBT D (𝟙_ _) k 0), (∃ j, f₀.f j ≠ 0) → ∃ m : ℕ, ∀ χ : D.X, ∃ (z : (𝟙_ _ ⊗ D.P.A).left) (J : _), Good D.P.L z J ∧ sval f₀ (lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * cT D _ χ)).left z J ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)) := by
  intro V _ _ _ hV D k f₀ ⟨j, hj⟩
  haveI := hV.1
  haveI := D.P.isAb.smooth
  haveI := D.P.isAb.geomConnected
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  haveI : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    isNoetherianRing_of_ringEquiv V (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
  obtain ⟨m, z₀, J₀, hJ₀, h₀⟩ : ∃ (m : ℕ) (z : (𝟙_ _ ⊗ D.P.A).left) (J : _), Good D.P.L z J ∧
      sval f₀ (𝟙 _) z J ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)) := by
    by_contra hc
    push Not at hc
    refine hj (sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A ?_ _ D.P.L D.P.isLB
      _ _ _ f₀ ?_ j)
    · intro r hr
      let e : V ≃+* Γ(Spec (CommRingCat.of V), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
      have h1 : r ∈ Ideal.jacobson (⊥ : Ideal V) := by
        rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      have h2 := Ideal.mem_map_of_mem e.toRingHom h1
      rw [Ideal.map_jacobson_of_bijective (f := e.toRingHom) e.bijective, Ideal.map_bot] at h2
      exact h2
    · rintro e Z r ⟨ρ, hρ⟩ z J hJ
      obtain ⟨g, hs, -⟩ := values_natural _ _ _ _ D.P.L _ (famφT D (𝟙_ _) 0) (DegPre.famε k) (𝟙 _) r z J hJ
      have h1 := stalkMap_mem_map_base _ _ _ r hρ.symm z _ (hc e _ _ g)
      rw [← hs f₀, Category.comp_id, map_base_eq_bot] at h1
      exact h1
  refine ⟨m, fun χ => ?_⟩
  let σ : 𝟙_ _ ⊗ D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * (cT D _ χ)⁻¹)
  let τ : 𝟙_ _ ⊗ D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * cT D _ χ)
  have hστ : σ ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · have : σ ≫ cT D _ χ = cT D _ χ := by
        rw [cT, ← Category.assoc, toUnit_unique (σ ≫ toUnit _) (toUnit _)]
      rw [Category.assoc, lift_snd, MonObj.comp_mul, this, lift_snd, inv_mul_cancel_right, Category.id_comp]
  obtain ⟨g, hs, -⟩ := values_natural _ _ _ _ D.P.L _ (famφT D (𝟙_ _) 0) (DegPre.famε k) τ.left σ.left z₀ J₀ hJ₀
  refine ⟨_, _, g, fun hm => h₀ ?_⟩
  have h1 := stalkMap_mem_map_base _ _ _ σ.left (Over.w σ) z₀ _ hm
  have h2 : σ.left ≫ τ.left = 𝟙 _ := congrArg CommaMorphism.left hστ
  rw [← hs f₀, h2] at h1
  exact h1

end GlobalTheory
end

