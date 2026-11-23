module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsShiftGen
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QkShift

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem cubN_one_mul (k : ℕ) (b m x : A) :
    cubN θ k 1 (b * m) x * θ m b x ^ k = θ (m ^ k) (b ^ k) x * cubN θ k 1 b x * cubN θ k 1 m x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c₁ := h.coc (b ^ k * m ^ k) m b x
    have c₂ := h.coc (b ^ k) (m ^ k) m x
    have c₃ := h.coc (m ^ k * m) (b ^ k) b x
    rw [mul_comm m b] at c₁
    rw [h.s01 (b ^ k) (m ^ k), h.s01 (b ^ k) (m ^ k * m)] at c₂
    rw [mul_comm (m ^ k * m) (b ^ k), ← _root_.mul_assoc] at c₃
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [mul_pow b m k, pow_succ m, pow_succ b, pow_succ (θ m b x)]
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₀ := E ih; have a₁ := E c₁; have a₂ := E c₂; have a₃ := E c₃
    simp only [ofMul_mul] at a₀ a₁ a₂ a₃ ⊢
    linear_combination (norm := abel) a₀ - a₁ + a₂ + a₃

theorem cub_shift (k : ℕ) (a m b x : A) (Sa Sm Sam Sq τ P w : U) (h₁ : Sam * cubN θ k a m b = Sa * Sm ^ k)
    (h₂ : Sq * θ a b m = Sa * τ) :
    cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * (τ * P) *
        (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * (Sam * w)) =
      cubN θ k a (b * m) x * (θ a x (b * m))⁻¹ * (Sq * (w * P * Sm ^ k)) := by
  have e₁ := h.N_add k a m x b
  have e₂ := cubN_one_mul h k b m x
  have e₃ := h.N_split k (a * m ^ k) b x
  have e₄ := h.N_split k a (b * m) x
  have e₅ := h.N_split k a m x
  have e₆ := h.coc a (m ^ k) (b ^ k) x
  have e₇ := h.coc x b m a
  rw [h.s12 m x b] at e₁
  rw [← mul_pow, mul_comm m b] at e₆
  rw [h.s12 (x * b), h.s01 (x * b), h.s12 x b a, h.s01 x a b, h.s12 x (b * m), h.s01 x a, h.s12 b m a,
    h.s01 b a m] at e₇
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have c₁ := E h₁; have c₂ := E h₂
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ - a₄ + a₅ + a₆ - a₇ + c₁ - c₂

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_comp (m m' : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.trPt D F m' = DegPre.trPt D F (m * m') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, tr_fst]
  · refine Eq.trans ?_ (tr_pr D F (m * m')).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D F m')).trans ?_)
    rw [MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, MonObj.comp_mul, _root_.mul_assoc]

theorem exists_shift_gen (n : ℕ) (g : GtPtF D F) (z : D.X) (b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = g.b * cP D _ z)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε n))) (hw : w.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε n)), w₂.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (y : Z) (J), Good D.P.L y J →
        val w₂ r y J = val w r y J *
          (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (r ≫ jFK (R := R) F) y J *
            val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) (r ≫ jFK (R := R) F) y J) * val (g.s z) r y J ^ n := by
  subst hb
  obtain ⟨w₂, h₂, v₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F (g.b * cP D _ z)) (ε' := DegPre.lineε n)
    (fun U _ h => by
      have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h g.b.left ^ (-(n : ℤ)) * _ *
        (h (cP D _ z * g.b).left ^ ((n : ℤ) * -1) * h (cP D _ z).left ^ ((n : ℤ) * 1) * h g.b.left ^ ((n : ℤ) * 1) *
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((n : ℤ) * -1)) =
        h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h (g.b * cP D _ z).left ^ (-(n : ℤ))
      rw [mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ w (LB.pullGen D.P.L _ _
      (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (GeneratorPullback.powGen D.P.L _ _ D.rigK n)) (jFK (R := R) F)))
      (GeneratorPullback.powGen D.P.L _ _ (g.s z) n))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hw (pullGen_isGen _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen z) n)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) n)) _)) (powGen_isGen _ _ _ _ (g.isGen z) n))
  refine ⟨w₂, h₂, fun Z r y J hJ => (v₂ Z r y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (val_mul hJ _ _ _)))) ?_))⟩
  exact map_pow _ _ _

theorem qk_shift : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p q : QkPt D F n) (z : D.X) (h : GtPtF D F), q.y = p.y + n • z → GtPtF.IsIota z h → GtPtF.IsAdd p.g h q.g → ∀ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)), w.IsGen → ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε n)), w₂.IsGen ∧ ∀ s s' : Fam D F n, PhiRel D F n p w s s' → PhiRel D F n q w₂ s s' := by
  intro hG R _ _ D _ F _ _ n _ p q z h hy hι hadd w hw
  have hh : h.b = cP D _ z := hι.1
  have hb : q.g.b = p.g.b * cP D _ z := hadd.1.trans (congrArg (p.g.b * ·) hh)
  obtain ⟨w₂, h₂, v₂⟩ := exists_shift_gen n p.g z q.g.b hb w hw
  refine ⟨w₂, h₂, fun s t H => ?_⟩
  rw [phiRel_iff hG p w hw] at H
  rw [phiRel_iff hG q w₂ h₂]
  intro α β hβ T ρ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  have e₁ := H (α + n • z) β (by rw [← hβ, hy]; abel) T ρ y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F) hG n z α
  have e₄ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (s.fe z α u' hu' hc') _
    (ρ ≫ DegPre.trPt D F p.g.b).left y J hJ
  rw [hv' u' hu' hc' _ (ρ ≫ DegPre.trPt D F p.g.b) y J hJ, trF_eq, ← Over.comp_left, Category.assoc, trPt_comp, ← hb,
    Category.assoc, tr_fst] at e₄
  rw [e₁, e₄, _root_.mul_assoc, ← Units.val_mul]
  congr 2
  have t₁ := gt_nsmul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α z n
  have t₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ _ _ _))).symm.trans
    ((val_corr hJ (hadd.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl ((val_corr hJ (hι.2 α) _).trans (val_pull hJ _ _ _)))))
  have c₁ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ DegPre.cF D F α = cP D T α := comp_cP D _ α
  have c₂ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ cP D _ z = cP D T z := comp_cP D _ z
  rw [hh, c₁, c₂] at t₂
  have key := cub_shift C n _ _ _ (ρ ≫ DegPre.prB D F) _ _ _ _ _
    (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J *
      val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J)
    (val w (ρ ≫ fst (TF (R := R) F) D.P.A).left y J) t₁ t₂
  have d₁ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst _ _ ≫ cP D _ z = cP D T z := by
    rw [← Category.assoc]; exact comp_cP D _ z
  have d₂ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F =
      (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, Category.assoc]
  have d₃ : ρ ≫ fst _ _ ≫ q.g.b = ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) * cP D T z := by
    rw [← Category.assoc, hb, MonObj.comp_mul, c₂]
  rw [val_famMult _ hJ, val_mul hJ, val_mul hJ, v₂ _ _ y J hJ, uVal, uVal, uVal, d₁, d₂, d₃, cPoint_add, cPoint_nsmul,
    ← Category.assoc ρ]
  exact key

end GlobalTheory.QkShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.UT.OLinEnd

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_Oφ (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ p χ i) ^ Oε i =
      h (cP D T χ * p).left * (h (cP D T χ).left)⁻¹ * (h p.left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four, _root_.mul_comm (cP D T χ) p]
  show h (p * cP D _ χ).left ^ (1 : ℤ) * h (cP D _ χ).left ^ (-1 : ℤ) * h p.left ^ (-1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_Oφ_inv (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ p χ i) ^ Oinvε i =
      (h (cP D T χ * p).left)⁻¹ * h (cP D T χ).left * h p.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, _root_.mul_comm (cP D T χ) p]
  show h (p * cP D _ χ).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h p.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem exists_u (hG : GlobalFnsSt) (D : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)
    (a : O) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_Oφ D (𝟙 _) (star a • χ) h)
        (prod_Oφ_inv D (oa.onB.act a) χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k
  refine (val_pull hJ _ _ _).trans (k.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem ros_unique (hG : GlobalFnsSt) (D : DegPre R) {f g : D.P.A ⟶ D.P.A}
    {u u' : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (u₀' : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u' (zero2 D.P.A)) (LB.oneGen D.P.L))
    (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D.P.A).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    val u' r z J = val u r z J := by
  have z2 : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  exact gen_unique D.P.isLB _ (zero2 D.P.A) z2 (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) hu' hu
    (fun y I hI => by
      have a₁ := val_corr hI u₀' (𝟙 _)
      have a₂ := val_corr hI u₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁ a₂
      exact a₁.trans a₂.symm) _ _ z J hJ

theorem main : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → ∀ a : O, ∃ E : EndU U.toUnifPre, E.aG = ιG.act a ∧ E.aA = ιA.act a ∧ E.aB = ιD.onB.act a ∧ (∀ χ, E.h χ = star a • χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ GtAct ιD a g g' := by
  intro hL R _ _ _ I _ D A G _ _ _ U O _ _ _ ιD ιA ιG hO a
  have hG := hL.1.globalFns
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  have hr := ιD.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr
  choose v hv vv using exists_u hG D.toPre ιD a u hu u₀
  refine ⟨{ aG := ιG.act a, aA := ιA.act a, aB := ιD.onB.act a, homG := ιG.hom a, homA := ιA.hom a,
            homB := ιD.onB.hom a, h := DistribSMul.toAddMonoidHom D.toPre.X (star a), ext := hO.ext a,
            q_lin := fun e => hO.q_lin e a, i_lin := fun e => hO.i_lin e a, u := v, u_norm := hv,
            t_lin := fun e χ Z x z J hJ => ?_ }, rfl, rfl, rfl, fun _ => rfl, fun F _ _ g g' => ?_⟩
  · have e₁ := val_corr hJ (hL.2.2.2.1.tLin R I O D A G U.toUnifPre ιD ιA ιG hO e a u hu u₀ χ) x
    refine ((val_pull hJ _ _ _).symm.trans e₁.symm).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
    exact (val_pull hJ _ _ _).trans (vv χ _ (U.gt e).pG Z x z J hJ).symm
  · have k : ∀ χ z J, Good D.toPre.P.L z J →
        val (v χ) g.b.left z J = val u (𝟙 _ ≫ (lift (cP D.toPre _ χ) g.b).left) z J := fun χ z J hJ =>
      (congrArg (fun q => val (v χ) q z J) (Category.id_comp g.b.left).symm).trans (vv χ _ g.b _ (𝟙 _) z J hJ)
    refine and_congr Iff.rfl ⟨fun H u' hu' u₀' χ => corr_of_val D.toPre.P.isLB fun z J hJ => ?_, fun H χ z J hJ => ?_⟩
    · refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (H χ z J hJ).symm)
      exact (val_pull hJ _ _ _).trans ((ros_unique hG D.toPre hu hu' u₀ u₀' _ _ z J hJ).trans (k χ z J hJ).symm)
    · refine (val_corr hJ (H u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      exact (val_pull hJ _ _ _).trans (k χ z J hJ).symm

end GlobalTheory.UT.OLinEnd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecPull

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem mem_wchart_comp {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {h : Y' ⟶ Y}
    (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) {p : K → L.ι} {y : Y'}
    (hy : y ∈ LB.wchart L (fun k => φ' k ≫ F) p) : h y ∈ LB.wchart L φ p :=
  Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    show (h ≫ φ k) y ∈ L.U (p k)
    rw [← hc]; exact this

theorem trF_comp {Z : Scheme.{0}} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {h : Y' ⟶ Y}
    (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (p p' : K → L.ι) :
    trF φ ε (r ≫ h) z p p' = trF (fun k => φ' k ≫ F) ε r z p p' := by
  simp only [trF, hc, Category.assoc]

theorem exists_down_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ)
    (s : LB.Sec (LB.LinComb L φ ε)) : ∃ a : LB.Sec (LB.LinComb L' φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gs r z (LB.wchart L' φ' q) (a.f q) =
          (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ a : Γ(Y', LB.wchart L' φ' q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gs r z _ a = (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) := by
    intro q
    let W : (K → L.ι) → Y'.Opens := fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q
    have le : ∀ p, W p ≤ h ⁻¹ᵁ LB.wchart L φ p := fun p y hy => mem_wchart_comp hc hy.1
    obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(Y', W p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p, r z ∈ W p →
        gs r z (W p) (v p) = (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) :=
      ⟨fun p => (u p q)⁻¹.val * (Y'.presheaf.map (homOfLE (le p)).op).hom ((h.app _).hom (s.f p)),
        fun Z r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q Z r z hz)))))
          ((gs_res r z (le p) hz _).trans (gs_pull r h z _ (le p hz) _)))⟩
    obtain ⟨a, ha, -⟩ := Y'.sheaf.existsUnique_gluing' W (LB.wchart L' φ' q)
      (fun p => homOfLE inf_le_right) (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) v
      (fun p p' => fn_ext (V := W p ⊓ W p') fun y hy => by
        refine (gs_res (𝟙 Y') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y') y inf_le_right hy _).symm)
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, sec_trans s (𝟙 Y' ≫ h) y (le p hy.1) (le p' hy.2), trF_comp hc,
          pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.1.2, trF_self hL' _ ε (𝟙 Y') y hy.1.2, inv_one, mul_one,
          ← mul_assoc, ← Units.val_mul, mul_inv_rev, inv_mul_cancel_right])
    refine ⟨a, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ W p := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz a).symm.trans ((congrArg (gs r z (W p)) (ha p)).trans (hv Z r z p hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => ha q Z r z p⟩
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  have m : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (gs_res (𝟙 Y') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y') y _ hy _).trans (congrArg Units.val (gm_linComb L' φ' ε (𝟙 Y') y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y') y _ hy _))).symm)
  refine (ha j _ (𝟙 Y') y p m hy.1).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y') y p m hy.2)).symm)
  rw [pw_trans hw φ' ε (𝟙 Y') y m m hy.1 hy.2, trF_self hL _ ε (𝟙 Y') y m, one_mul, mul_inv, inv_inv, Units.val_mul,
    mul_assoc]
  rfl

theorem existsUnique_secPull (X X' Y Y' : Scheme.{0}) (L : LB X) (L' : LB X') (F : X' ⟶ X) (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) (K : Type) [Fintype K] (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃! a : LB.Sec (LB.LinComb L' φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  obtain ⟨a, ha⟩ := exists_down_sec ((isGen_iff w).1 hw) hL hL' φ' φ ε h hc s
  refine ⟨a, fun Z r z p q hp hq => ?_, fun b hb => ?_⟩
  · rw [ha Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)]
    exact (Units.mul_inv_cancel_left (pw w φ' ε r z p q) _).symm
  · have e : b.f = a.f := funext fun q => fn_ext fun y hy => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      refine Eq.trans ?_ (ha _ (𝟙 Y') y p q (Set.mem_iInter.2 hp) hy).symm
      rw [hb _ (𝟙 Y') y p q hp (Set.mem_iInter.1 hy)]
      exact (Units.inv_mul_cancel_left (pw w φ' ε (𝟙 Y') y p q) _).symm
    cases a; cases b; cases e; rfl

end GlobalTheory.SecPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem expBijF_and_expandsF_lin : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ExpBijF U.toUnifPre ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (w₀ : W0 U.toUnifPre) (t t' t'' : SecA A F k) (s s' : Fam D.toPre F k) (c : F), U.ExpandsF F k w₀ t s → U.ExpandsF F k w₀ t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → U.ExpandsF F k w₀ t'' (c • s + s') := by
  intro hL R _ _ _ I _ D A G _ _ _ U
  refine ⟨GlobalTheory.expansion_bijective_over_fields hL.1.globalFns R I D A G U, ?_⟩
  intro F _ _ k w₀ t t' t'' s s' c h h' e
  have key := GlobalTheory.FieldBaseChange.expandsF_lin U.toUnifPre F c h h'
  have ext : ∀ a b : SecA A F k, (∀ j, a.f j = b.f j) → a = b := by
    rintro ⟨a, _⟩ ⟨b, _⟩ hab
    obtain rfl : a = b := funext hab
    rfl
  exact (congrArg (fun x : SecA A F k => U.ExpandsF F k w₀ x (c • s + s')) (ext t'' _ fun j => (e j).trans rfl)).mpr key

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionExtensionFieldTotal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem expandsF_total : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → (∀ s : Fam D.toPre F k, ∃ t, U.toUnifPre.ExpandsF F k w t s) ∧ ∀ t, ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s := by
  intro h₁ _ R _ _ I _ D A G _ _ _ U F _ _ k hk w hw
  have h := FieldBaseChange.expandsF_bijective U.toUnifPre F h₁.globalFns hk (U.expand k hk) hw
  exact ⟨fun s => (h.2 s).exists, fun t => (h.1 t).exists⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusHomPullbackLocalTrivial
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

theorem splitTorus_hom_pullback_local_trivial {S : Scheme.{0}} (A : CommRingCat.{0}) [IsLocalRing A]
    [IsNoetherianRing A] (p : Spec A ⟶ S) (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : Over S) [GrpObj B] [IsProper B.hom] (f : splitTorus S X ⟶ B)
    (hf : IsMonHom f) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by
  obtain ⟨A⟩ := A
  refine TorusLocal.pullback_map_eq_one p X B f hf fun g hg ↦ ?_
  have : IsProper ((Over.pullback p).obj B).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  exact splitTorus_hom_proper_trivial_local A X _ g hg

theorem splitTorus_hom_abelian_eq_one : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus S X ⟶ B, IsMonHom f → f = 1 := by
  intro S _ X _ _ _ B _ hB f hf
  have := hB.proper
  refine Over.OverMorphism.ext (hom_ext_of_fromSpecStalk fun t ↦ ?_)
  let p := S.fromSpecStalk ((splitTorus S X).hom t)
  have h : (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) :=
    splitTorus_hom_pullback_local_trivial _ p X B f hf
  have h₁ : ∀ u : splitTorus S X ⟶ B, ((Over.pullback p).map u).left ≫ pullback.fst B.hom p =
      pullback.fst (splitTorus S X).hom p ≫ u.left := fun u ↦ pullback.lift_fst _ _ _
  have h₂ : pullback.fst (splitTorus S X).hom p ≫ f.left =
      pullback.fst (splitTorus S X).hom p ≫ (1 : splitTorus S X ⟶ B).left := by
    rw [← h₁, ← h₁, h, Hom.one_def]
  have h₃ : pullback.lift ((splitTorus S X).left.fromSpecStalk t)
      (Spec.map ((splitTorus S X).hom.stalkMap t)) (Scheme.SpecMap_stalkMap_fromSpecStalk _).symm ≫
      pullback.fst (splitTorus S X).hom p = (splitTorus S X).left.fromSpecStalk t :=
    pullback.lift_fst _ _ _
  rw [← h₃, Category.assoc, Category.assoc, h₂]

end GlobalTheory
end

