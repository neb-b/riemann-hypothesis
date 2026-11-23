module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansionsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionFormula_algClosure_with_expansions : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → ∃ (r : V) (n : ℕ) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s s' : Fin n → Raw D (Kbar V) 2), r ≠ 0 ∧ (∀ i, U.ExpF (Kbar V) 2 (t i) (s i) ∧ U.ExpF (Kbar V) 2 (t' i) (s' i)) ∧ AddA A (TFK (R := V) (Kbar V)) th t t' ∧ AddB D (TF (R := V) (Kbar V)) s₀ r s s') := by
  first | exact @GlobalTheory.AddClosure.main | exact GlobalTheory.AddClosure.main | (intros; apply GlobalTheory.AddClosure.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsActValue
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.EvalLevel
open GlobalTheory.UT.CoefBasic

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem powFrame_isGen (z : T ⟶ A)
    (e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame A L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have v : ∀ i : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k := fun i hi =>
    (map_zpow _ _ _).trans (congrArg (· ^ k) (gm_rp₁ T.hom y _ _ (rigT_le A L i) hi _))
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hy.1) (rigT_le A L (T := T) j hy.2)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  refine ((gm_res (𝟙 _) y _ hy _).trans (v i hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L (fun _ : Fin 1 => T.hom ≫ eSec A) (fun _ => k) (𝟙 _) y i j hy.1 hy.2)
    ((gm_res (𝟙 _) y _ hy _).trans (v j hy.2)))).symm)
  rw [Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_translPt (x : T ⟶ A) : ptSecT A (1 : T ⟶ A) ≫ translPt A x = x := by
  rw [ptSecT, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, ← Hom.mul_def, _root_.mul_one]

theorem ptSec_translT (x : T ⟶ A) : (ptSecT A (1 : T ⟶ A)).left ≫ (translT A x).left = (ptSecT A x).left := by
  rw [← Over.comp_left, translT, comp_lift, ptSec_translPt, ptSecT, lift_fst]; rfl

end

theorem sumV_mul {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s c : F}
    (h : SumV v x s) (hc : c ≠ 0) : SumV v (fun i => c * x i) (c * s) := by
  intro q
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  obtain ⟨S, hS⟩ := h (q - r)
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.mul_sum, ← mul_sub, v.map_mul, ← hr, show q = r + (q - r) by ring, WithTop.coe_add]
  exact add_le_add le_rfl (hS T hT)

theorem sumV_equiv {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix Ix' : Type} (e : Ix' ≃ Ix) {x : Ix → F} {s : F}
    (h : SumV v x s) : SumV v (fun i => x (e i)) s := by
  intro q
  obtain ⟨S, hS⟩ := h q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) fun i hi => by
    simpa using hT (Finset.mem_map_of_mem e.symm.toEmbedding hi)
  rwa [Finset.sum_map] at this

theorem exists_act_value {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) (N : ℕ)
    (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F))
    (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => θ.pt.left) (fun _ => 1)))
    (he : e.IsGen) : ∃ u : F, u ≠ 0 ∧ ∀ (t t' : SecA A F N) (c : F), IsActOf A.A A.L (N : ℤ) θ t t' →
      (∀ z J, Good A.L z J → sA t (ptSecT A.A θ.pt).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z)
        (cst (R := R) F z c) * (val (powFrame A.A A.L θ.pt e N) (𝟙 _) z J).val) →
      ∀ z J, Good A.L z J → sA t' (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z)
        (cst (R := R) F z (u * c)) * (val (rigT A.A A.L ρ (TFK (R := R) F) (N : ℤ)) (𝟙 _) z J).val := by
  have e₀ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
      (TFK (R := R) F).hom ≫ eSec A.A := by
    rw [← Over.comp_left, ptSecT, lift_snd]; rfl
  have e₁ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (translPt A.A θ.pt).left = θ.pt.left := by
    rw [← Over.comp_left, ptSec_translPt]
  obtain ⟨u, hu, hv⟩ := TWM.exists_ratio (F := F) A.isLB
    (LB.mulGen A.L _ _ _ _ (LB.pullGen A.L _ _ θ.φ (ptSecT A.A 1).left) (powFrame A.A A.L θ.pt e N))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _) (powFrame_isGen θ.pt e he N))
    (rigT A.A A.L ρ (TFK (R := R) F) (N : ℤ)) (rigT_isGen hρ N) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
      exact (congrArg₂ (fun a b => h a ^ (N : ℤ) * (h b ^ (N : ℤ))⁻¹ * h θ.pt.left ^ (N : ℤ)) e₀ e₁).trans
        (inv_mul_cancel_right _ _))
  refine ⟨u, hu, fun t t' c ha ht z J hJ => ?_⟩
  have a₁ := GlobalTheory.BoxTheta.act_val θ t t' ha (ptSecT A.A 1).left z hJ
  rw [ptSec_translT] at a₁
  have a₀ := (val_pull (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
    (ε := ![(N : ℤ), -(N : ℤ)]) hJ θ.φ (ptSecT A.A 1).left (𝟙 _)).trans
    (congrArg (fun r => val (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
      (ε := ![(N : ℤ), -(N : ℤ)]) θ.φ r z J) (Category.id_comp _))
  have a₂ := ((Units.val_mul _ _).symm.trans (congrArg Units.val ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₀ rfl)).symm)).trans (hv _ (𝟙 _) z J hJ)
  have a₃ := ht z J hJ
  have a₄ : cst (R := R) F z (u * c) = cst (R := R) F z u * cst (R := R) F z c := by
    rw [cst_eq, cst_eq, cst_eq, map_mul]
  refine a₁.trans ((congrArg _ a₃).trans ?_)
  rw [a₄]
  refine (mul_left_comm _ _ _).trans ((congrArg _ a₂).trans ?_)
  exact (_root_.mul_assoc _ _ _).symm.trans (congrArg₂ (fun a b : (TFK (R := R) F).left.presheaf.stalk z => a * b) (_root_.mul_comm _ _) rfl)

theorem value_at_level : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (N : ℕ), 1 ≤ N → ∀ (q : QkPt D.toPre F N) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F N q x → ∀ e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := V) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), e.IsGen → ∀ w : Frm D.toPre F N q.g.b, w.IsGen → ∃ κ : F, κ ≠ 0 ∧ ∀ (t : SecA A F N) s (c : F), U.ExpandsF F N w₀ t s → (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e N) (𝟙 _) z J).val) → SumV v (coef s q.g w) (κ * c) := by
  intro hL V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN N hN1 q x hx e he w hw
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  haveI : Subsingleton (TFK (R := V) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (TFK (R := V) F).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨hxN, hθ⟩ := hx w₀ hN.1
  obtain ⟨θ, rfl⟩ := GlobalTheory.BoxTheta.exists_theta hL.1.kerPow A hN1 (T := TFK (R := V) F) x hxN
  obtain ⟨w', hw', hΦ⟩ := hθ θ rfl
  obtain ⟨u, hu, hval⟩ := exists_act_value hN.2.1 N θ e he
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F N o).2.1 ho.1
  have hadd : o.IsAdd q.g q.g := by
    rw [GlobalTheory.TorusExt.isZero_unique ho GlobalTheory.TorusExt.isZero_gtZero]
    have := GlobalTheory.TorusExt.isAdd_gtAdd (GlobalTheory.TorusExt.gtZero D.toPre F) q.g
    rwa [GlobalTheory.TorusExt.gtZero_add] at this
  obtain ⟨ω, hω, -, hc⟩ := GlobalTheory.UT.CoefPhi.coef_phi hL V _ hB D F N hN1 q w' hw' o q.g hadd w₁ hw₁.1
  obtain ⟨d, hd, -, hdc⟩ := ((coef_basic V D.toPre F N q.g).2.2 ω hω).2.2.1 w hw
  refine ⟨d * u, mul_ne_zero hd hu, fun t s c hts hc' => ?_⟩
  obtain ⟨t', ht'⟩ := GlobalTheory.VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (m := translPt A.A θ.pt)
    (hm := lift_snd _ _) (a := N) (b := N) (α := θ.φ) A.isLB θ.isGen t
  obtain ⟨s', hs', -⟩ := ((GlobalTheory.UT.expBijF_and_expandsF_lin hL V _ hB D A G hG U).1 F N hN1 w₀ hN.1).1 t'
  have h₁ := (GlobalTheory.UT.EvalZero.value_at_origin hL V _ hB D A G hG U F).2.2 w₀ ρ hN N t' s' hs' o w₁ ho hw₁ (u * c)
    (hval t t' c ht' hc')
  have h₂ := sumV_equiv (Equiv.addRight q.y) (GlobalTheory.UT.AdicValSum.main V ϖ hϖ F v hv _ _ _ h₁).1
  have h₃ := hc 1 N le_rfl (Nat.mul_one N).symm q (one_nsmul _).symm rfl w' w₁ ω ⟨hw', fun _ _ _ => (pow_one _).symm⟩
    ⟨hw₁.1, fun _ _ _ => (pow_one _).symm⟩ ⟨hω, fun _ _ _ => (pow_one _).symm⟩ s s' (hΦ t t' s s' hts hs' ht')
  have h₄ := sumV_mul h₂ hd
  simp only [Equiv.coe_addRight, h₃, ← hdc] at h₄
  rw [_root_.mul_assoc]
  exact h₄

end GlobalTheory.UT.EvalLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolExtension

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CubTransport

theorem isCub_of_surjective {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] {θ : A → A → A → U}
    (β : A' →* A) (hβ : Function.Surjective β) (h : IsCub (fun a b c => θ (β a) (β b) (β c))) : IsCub θ := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨y, rfl⟩ := hβ y
    simpa only [map_one] using h.face x y
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨y, rfl⟩ := hβ y; obtain ⟨z, rfl⟩ := hβ z
    exact h.s01 x y z
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨y, rfl⟩ := hβ y; obtain ⟨z, rfl⟩ := hβ z
    exact h.s12 x y z
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨x', rfl⟩ := hβ x'; obtain ⟨x'', rfl⟩ := hβ x''; obtain ⟨y, rfl⟩ := hβ y
    simpa only [map_mul] using h.coc x x' x'' y

theorem isCub_mul_diff {A U : Type} [CommGroup A] [CommGroup U] {θ θ' : A → A → A → U} (hθ : IsCub θ) (Ω : A → U)
    (h : ∀ a b c, θ' a b c = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
      Ω c * (Ω 1)⁻¹ * θ a b c) : IsCub θ' :=
  isCub_of_twist hθ (MonoidHom.id A) (fun a => (Ω a)⁻¹) fun a b c => by
    rw [h]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, MonoidHom.id_apply]
    abel

section DVR

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]


omit [IsDomain V] [IsDiscreteValuationRing V] [GrpObj G] [IsCommMonObj G] in
theorem corr_of_generic_val [IsSeparated G.hom] (T : Over (Spec (CommRingCat.of V))) [Flat T.hom]
    {L : LB G.left} (hL : L.IsLB) {I I' : Type} [Fintype I] [Fintype I']
    {φ : I → (T.left ⟶ G.left)} {ε : I → ℤ} {φ' : I' → (T.left ⟶ G.left)} {ε' : I' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (H : ∀ (y : (pullback T.hom (etaK V K) :)) J, Good L y J →
      val t (pullback.fst T.hom (etaK V K)) y J = val t' (pullback.fst T.hom (etaK V K)) y J) :
    LB.Gen.Corr L _ _ _ _ t t' :=
  corr_of_generic_of_isSeparated V K G T L φ ε φ' ε' t t' (corr_of_val hL fun y J hJ => by
    rw [val_pull hJ, val_pull hJ, Category.id_comp]
    exact H y J hJ)

theorem nonempty_cubical_of_generic [IsSeparated G.hom] [Flat G.hom] (L : RigLB G) (t : LB.Gen (Theta G L.L))
    (ht : t.IsGen)
    (h : ∀ (T : Over (Spec (CommRingCat.of K))) (z : T.left) (J), Good L.L z J →
      IsCub (thV t (T := Over.mk (T.hom ≫ etaK V K)) z J)) : Nonempty (CubicalStr G L) := by
  have f₂ : Flat (G2 G).hom := by
    show Flat (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have f₃ : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (G2 G).hom ≫ G.hom)
    infer_instance
  have f₄ : Flat (G4 G).hom := by
    show Flat (pullback.fst G.hom (G3 G).hom ≫ G.hom)
    infer_instance
  let ρ : ∀ T : Over (Spec (CommRingCat.of V)), Over.mk (pullback.snd T.hom (etaK V K) ≫ etaK V K) ⟶ T := fun T =>
    Over.homMk (pullback.fst T.hom (etaK V K)) pullback.condition
  have v : ∀ (T : Over (Spec (CommRingCat.of V))) (y : (pullback T.hom (etaK V K) :)) J, Good L.L y J →
      ∀ a b c : T ⟶ G, val (LB.pullGen L.L (thφ G (x3 G)) thε t (lift a (lift b c)).left)
        (pullback.fst T.hom (etaK V K)) y J =
        thV t (T := Over.mk (pullback.snd T.hom (etaK V K) ≫ etaK V K)) y J (ρ T ≫ a) (ρ T ≫ b) (ρ T ≫ c) := by
    intro T y J hJ a b c
    refine (val_pull hJ _ _ _).trans ?_
    rw [thV, ← comp_lift, ← comp_lift]; rfl
  have v' : ∀ (y : (pullback (G3 G).hom (etaK V K) :)) J,
      val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (pullback.fst (G3 G).hom (etaK V K)) y J =
        thV t (T := Over.mk (pullback.snd (G3 G).hom (etaK V K) ≫ etaK V K)) y J
          (ρ _ ≫ x3 G 0) (ρ _ ≫ x3 G 1) (ρ _ ≫ x3 G 2) := by
    intro y J
    have e : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
      ext <;> simp [x3]
    rw [thV, ← comp_lift, ← comp_lift, e, Category.comp_id]; rfl
  refine ⟨⟨t, ht, fun i => corr_of_generic_val (K := K) (G2 G) L.isLB fun y J hJ => ?_,
    corr_of_generic_val (K := K) (G3 G) L.isLB fun y J hJ => ?_,
    corr_of_generic_val (K := K) (G3 G) L.isLB fun y J hJ => ?_,
    corr_of_generic_val (K := K) (G4 G) L.isLB fun y J hJ => ?_⟩⟩
  · refine Eq.trans ?_ (val_one _).symm
    have C := h (Over.mk (pullback.snd (G2 G).hom (etaK V K))) y J hJ
    have o : ρ (G2 G) ≫ pzero G _ = 1 := map_one (preHom (ρ (G2 G)))
    fin_cases i
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face _ _)
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face₂ _ _)
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face₃ _ _)
  · exact (v' y J).trans (((h (Over.mk (pullback.snd (G3 G).hom (etaK V K))) y J hJ).s01 _ _ _).trans
      (v _ y J hJ _ _ _).symm)
  · exact (v' y J).trans (((h (Over.mk (pullback.snd (G3 G).hom (etaK V K))) y J hJ).s12 _ _ _).trans
      (v _ y J hJ _ _ _).symm)
  · have C := h (Over.mk (pullback.snd (G4 G).hom (etaK V K))) y J hJ
    have m : ∀ a b : G4 G ⟶ G, ρ (G4 G) ≫ padd G a b = (ρ (G4 G) ≫ a) * (ρ (G4 G) ≫ b) := fun a b =>
      MonObj.comp_mul _ _ _
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _ y J hJ _ _ _) (v _ y J hJ _ _ _))).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _ y J hJ _ _ _) (v _ y J hJ _ _ _))).symm)
    rw [m, m]
    exact C.coc _ _ _ _

variable [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
  {A : Over (Spec (CommRingCat.of K))} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem nonempty_cubical (hE : cubical_extendsSt.{0}) (gp : IsGrpPullback A G (etaK V K) F) (L : RigLB G)
    {M : RigLB A} (c : CubicalStr A M) (w : LB.Iso M.L (L.L.pull F)) (hw : w.IsGen) :
    Nonempty (CubicalStr G L) := by
  have hp := gp.1
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up ((isGen_iff w).1 hw) L.isLB M.isLB (φ' := thφ A (x3 A)) (ε := thε) c.t c.isGen
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd (G3 G).hom (etaK V K))
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
  have hx : ∀ i, (x i).left ≫ F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
  let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
  have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have hl : l.left ≫ (cubeMapOf gp).F3 = genericFiberCubeInclusion V K G := hom_ext_triple _ fun i => by
    rw [Category.assoc, f3, ← Category.assoc, ← Over.comp_left, lx, hx]
  let κ : (G3 A).left ⟶ pullback (G3 G).hom (etaK V K) := pullback.lift (cubeMapOf gp).F3 (G3 A).hom
    (Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2)))))
  have κ₁ : κ ≫ genericFiberCubeInclusion V K G = (cubeMapOf gp).F3 := pullback.lift_fst _ _ _
  have κ₂ : κ ≫ l.left = 𝟙 _ := hom_ext_triple _ fun i => by
    rw [Category.assoc, ← Over.comp_left, lx, Category.id_comp]
    refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, hx, ← Category.assoc]
      exact (congrArg (· ≫ _) κ₁).trans (f3 i)
    · rw [Category.assoc, Over.w, Over.w]
      exact pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, v₂⟩ := exists_gen L.isLB (φ' := fun I => genericFiberCubeInclusion V K G ≫ thφ G (x3 G) I) (ε' := thε)
    (fun U _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) (by
      show _ = genericFiberCubeInclusion V K G ≫ _
      rw [← hl, Category.assoc]
      exact congrArg (l.left ≫ ·) ((cubeMapOf gp).psum_comm I.down)))
    (LB.pullGen L.L _ _ t₁ l.left) (DVR.pullGen_isGen _ _ _ _ ht₁ _)
  have C : ∀ (T : Over (Spec (CommRingCat.of K))) (z : T.left) (J), Good L.L z J →
      IsCub (fun a b d : T ⟶ A => val t₂ ((lift a (lift b d)).left ≫ κ) z J) := by
    intro T z J hJ
    choose J' hJ' using fun χ : T.left ⟶ A.left => exists_chart M.isLB (χ z)
    refine isCub_mul_diff (isCub_cubV c hJ') (fun q => gw w q.left z (J (q.left ≫ F)) (J' q.left)) fun a b d => ?_
    refine (v₂ _ _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)
    rw [Category.assoc, κ₂, Category.comp_id]
    refine (v₁ _ _ z _ _ (hJ.mem _ _) (Good.mem hJ' _ _)).trans (congrArg₂ (· * ·) (Eq.trans ?_
      (prod_cub a b d (fun q => gw w q z (J (q ≫ F)) (J' q)))) rfl)
    exact Finset.prod_congr rfl fun I _ => by rw [Category.assoc]
  have q : ∀ (T : Over (Spec (CommRingCat.of K))) (a b d : T ⟶ A), (lift a (lift b d)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T a) (lift (pushHom gp T b) (pushHom gp T d))).left := fun T a b d => hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  obtain ⟨t, ⟨ht, htt⟩, -⟩ := hE V K G ((lift (1 : 𝟙_ _ ⟶ A) (lift 1 1)).left ≫ κ) (by
      rw [Category.assoc, κ₁, q, map_one, CubeExtension.eSec_three]
      refine hom_ext_triple _ fun i => ?_
      rw [Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3, Hom.one_def]) L t₂ (corr_of_val L.isLB fun y J hJ => by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
      rw [Category.id_comp]
      exact (C (𝟙_ _) y J hJ).face 1 1) ht₂
  refine nonempty_cubical_of_generic (K := K) L t ht fun T z J hJ => isCub_of_surjective (pushHom gp T) (fun a => ?_) ?_
  · exact ⟨Over.homMk (hp.lift a.left T.hom (Over.w a)) (hp.lift_snd _ _ _), Over.OverMorphism.ext (hp.lift_fst _ _ _)⟩
  · refine (congrArg IsCub (funext fun a => funext fun b => funext fun d => ?_)).mpr (C T z J hJ)
    rw [← htt]
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [Category.assoc, κ₁, q]
    rfl


omit [IsCommMonObj A] [QuasiCompact G.hom] in
theorem exists_symmetry (gp : IsGrpPullback A G (etaK V K) F) {L : LB G.left} (hL : L.IsLB)
    {M : LB A.left} (hM : M.IsLB) (hs : Out.Sym A M) (w : LB.Iso M (L.pull F)) (hw : w.IsGen) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L) := by
  have hp := gp.1
  obtain ⟨U, hU, t, ht⟩ := hs (IsLocalRing.closedPoint K)
  obtain ⟨n, hn⟩ : ∃ n : pullback G.hom (etaK V K) ⟶ (A.hom ⁻¹ᵁ U).toScheme, n ≫ (A.hom ⁻¹ᵁ U).ι = hp.isoPullback.inv :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have : A.hom (hp.isoPullback.inv y) = IsLocalRing.closedPoint K :=
        Subsingleton.elim (α := PrimeSpectrum K) _ _
      exact (congrArg (· ∈ U) this).mpr hU), IsOpenImmersion.lift_fac _ _ _⟩
  have hι : (ι[A]).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp A) (𝟙 A))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  obtain ⟨t₁, ht₁, -⟩ := exists_up ((isGen_iff w).1 hw) hL hM _ (DVR.pullGen_isGen _ _ _ _ ht n)
  obtain ⟨t₂, ht₂, -⟩ := exists_gen hL
    (φ' := fun k : Fin 2 => pullback.fst G.hom (etaK V K) ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun _ _ k => Finset.prod_congr rfl fun i _ => congrArg (fun q => k q ^ (![1, -1] : Fin 2 → ℤ) i) (by
      fin_cases i
      · show (n ≫ _ ≫ (ι[A]).left) ≫ F = _ ≫ (ι[G]).left
        rw [← Category.assoc, hn, Category.assoc, hι, ← Category.assoc, hp.isoPullback_inv_fst]
      · show (n ≫ (A.hom ⁻¹ᵁ U).ι) ≫ F = _ ≫ 𝟙 _
        rw [hn, hp.isoPullback_inv_fst, Category.comp_id])) t₁ ht₁
  have a₁ : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  let e : Spec (CommRingCat.of K) ⟶ pullback G.hom (etaK V K) := pullback.lift (etaK V K ≫ eSec G) (𝟙 _) (by
    rw [Category.assoc, a₁, Category.id_comp]; exact Category.comp_id _)
  have he : e ≫ pullback.fst G.hom (etaK V K) = etaK V K ≫ eSec G := pullback.lift_fst _ _ _
  obtain ⟨u, hu, cu⟩ := DVR.exists_normalized_to hL _ _ t₂ ht₂ (pullback.snd G.hom (etaK V K)) e
    (pullback.lift_snd _ _ _) _ _ (LB.oneGen L) (LB.isGen_oneGen L) (by
      have : e ≫ pullback.fst G.hom (etaK V K) ≫ (ι[G]).left = e ≫ pullback.fst G.hom (etaK V K) := by
        rw [← Category.assoc, he, Category.assoc]
        exact congrArg (etaK V K ≫ ·) e₂
      simp [DVR.fsum, Fin.sum_univ_two, this, Finsupp.single_neg])
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen hL (φ' := fun k : Fin 2 => eSec G ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun U _ k => by simp [Fin.prod_univ_two, e₂]) (LB.oneGen L) (LB.isGen_oneGen L)
  obtain ⟨s, ⟨hs₁, hs₂⟩, -⟩ := GenExtend.existsUnique_gen_extend V K G.left G.left G.hom (eSec G) inferInstance
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance) a₁ e he L hL
    (Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] u ρ hu hρ (corr_of_val hL fun y J hJ =>
      (val_corr hJ cu _).trans ((val_one _).trans
        ((val_pull hJ ρ _ _).trans ((vρ _ _ y J hJ).trans (val_one _))).symm))
  have : Flat (𝟙_ (Over (Spec (CommRingCat.of V)))).hom := inferInstanceAs (Flat (𝟙 _))
  refine ⟨s, hs₁, corr_of_generic_val (K := K) (𝟙_ _) hL fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_corr hJ cu (pullback.snd _ _)).trans
    ((val_one _).trans (val_one _).symm)))
  rw [← hs₂]
  refine Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm
  rw [Category.assoc, he, ← Category.assoc, ← pullback.condition]
  exact congrArg (fun q => val s (q ≫ eSec G) y J) (Category.comp_id _).symm

end DVR

end GlobalTheory.PolExtension
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaIntegral

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem exists_sec_ne_zero (h1 : Laws) (h2 : Laws2) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type)
    [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) :
    ∃ v : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p), v ≠ 0 := by
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep h1 h2 S P F p 1 (by simp)
  have : Nontrivial Γ((Over.mk p).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have : Nontrivial (SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p)) :=
    Module.nontrivial_of_finrank_pos (R := Γ((Over.mk p).left, ⊤)) (by rw [hr]; simp)
  exact exists_ne 0

theorem exists_theta : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ θ f, U.Theta θ f) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U
  obtain ⟨v, hv⟩ := exists_sec_ne_zero h1 h2 _ A (Kbar V) (jFK (R := V) (Kbar V))
  obtain ⟨s, n, c, σ, f, hE, hA, -⟩ := _root_.GlobalTheory.UU.ExpTotal.expF_total h1 h2 V hV D A G U (Kbar V) 1 le_rfl (SecM.toSec A.A v)
  by_contra hn
  have hz : ∀ i j, (σ i).f j = 0 := fun i j => by
    by_contra h
    exact hn ⟨σ i, f i, hE i, j, h⟩
  refine hv (Subtype.ext (funext fun j => ?_))
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) (Kbar V)) A.A).left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) A.isLB (s := SecM.toSec A.A v) (s' := SecM.toSec A.A 0) (fun z JA hJA => ?_) j
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let y := (snd (TFK (R := V) (Kbar V)) A.A).left ≫ U.gen.inv.left
  let T : Over (Spec (CommRingCat.of V)) := Over.mk ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom)
  let x : T ⟶ G := Over.homMk (y ≫ pullback.fst G.hom (jK V)) rfl
  have e := hA _ (𝟙 _) y (lift (toUnit T) x).left
    (by rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id])
    (congrArg (fun q => q.left) (lift_snd (toUnit T) x)) z JA JG hJA hJG
  rw [Finset.sum_eq_zero fun i _ => by rw [sval_eq_zero (σ i) (hz i), mul_zero], ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero] at e
  exact e.trans (sval_eq_zero _ (fun _ => rfl) _ _ _).symm

end GlobalTheory.ThetaIntegral
end

