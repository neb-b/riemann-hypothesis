module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfSval
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullComp

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem sval_of_heq {m n : ℕ} (h : m = n) (s : Fam D.toPre F m) (t : Fam D.toPre F n) (e : HEq s t)
    {α β : D.toPre.X} (hα : α = β) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) :
    sval (t.s α) r z J = sval (s.s β) r z J := by
  subst h hα
  cases e
  rfl

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h (fun k => J (r ≫ φ k)))).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem eq_zero_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j) : s.f j = 0 :=
  sec_ext_val hL (s' := SectionArithmetic.secZero _) (fun y J hJ => (h y J hJ).trans
    (sval_eq_zero _ (fun _ => rfl) _ _ _).symm) j

theorem aF_comp (oa : D.toPre.OAct O) (a a' : O) : aF D F oa a ≫ aF D F oa a' = aF D F oa (a' * a) := by
  have : oa.onB.act (a' * a) = oa.onB.act a ≫ oa.onB.act a' := by
    first
      | exact oa.onB.map_mul _ _
      | (rw [mul_comm]; exact oa.onB.map_mul _ _)
  simp [aF, DegPre.prB, this]

theorem zF_aF (oa : D.toPre.OAct O) (a : O) : DegPre.zF D.toPre F ≫ aF D F oa a = DegPre.zF D.toPre F := by
  have := oa.onB.hom a
  have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  apply CartesianMonoidalCategory.hom_ext
  · rw [aF, Category.assoc, lift_fst]
  · rw [aF, Category.assoc, lift_snd, ← Category.assoc, z₂, MonObj.one_comp]
    first | done | exact z₂.symm

end GlobalTheory.PullComp

namespace GlobalTheory


open PullComp in
theorem pullAl_comp : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a a' : O) (N N' k : ℕ), 1 ≤ N → 1 ≤ N' → 1 ≤ k → a * star a = (N : O) → a' * star a' = (N' : O) → ∀ (s : Fam D.toPre F k) (s₁ : Fam D.toPre F (k * N')) (s₂ : Fam D.toPre F (k * N' * N)) (s₃ : Fam D.toPre F (k * (N' * N))), PullAl D F oa a' k N' s s₁ → PullAl D F oa a (k * N') N s₁ s₂ → HEq s₂ s₃ → PullAl D F oa (a' * a) k (N' * N) s s₃ := by
  intro _ V _ _ _ D F _ _ O _ _ _ oa w0 _ a a' N N' k hN hN' _ _ _ s s₁ s₂ s₃ h₁ h₂ he
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hst : ∀ χ : D.toPre.X, star (a' * a) • χ = star a • star a' • χ := fun χ => by
    rw [star_mul, mul_smul]
  have hcl : (aF D F oa a).left ≫ (aF D F oa a').left = (aF D F oa (a' * a)).left :=
    congrArg (fun q => q.left) (aF_comp D F oa a a')
  have hzl : (DegPre.zF D.toPre F).left ≫ (aF D F oa a).left = (DegPre.zF D.toPre F).left :=
    congrArg (fun q => q.left) (zF_aF D F oa a)
  refine ⟨fun χ => ?_, fun β hβ => ?_⟩
  · obtain ⟨u₁, hu₁, c₁, r₁⟩ := h₁.1 χ
    obtain ⟨u₂, hu₂, c₂, r₂⟩ := h₂.1 (star a' • χ)
    obtain ⟨u, hu, vu⟩ := exists_gen hL (φ' := pullφ D F oa (a' * a) χ) (ε' := pullε k (N' * N)) (fun U _ h => by
        simp only [pullφ, pullε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hst, ← hcl, Category.assoc,
          zpow_neg, Finset.prod_inv_distrib, Nat.mul_assoc]
        group)
      (LB.mulGen D.toPre.P.L _ _ _ _ u₂ (LB.pullGen D.toPre.P.L _ _ u₁ (aF D F oa a).left))
      (mulGen_isGen _ _ _ _ _ _ _ hu₂ (pullGen_isGen _ _ _ _ hu₁ _))
    refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => ?_⟩
    · have e₁ := val_corr hJ c₁ (𝟙 _)
      have e₂ := val_corr hJ c₂ (𝟙 _)
      rw [val_pull hJ, val_pull hJ, val_pow] at e₁ e₂
      rw [val_pull hJ, val_pull hJ, val_pow, vu _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, hzl, e₁, e₂,
        ← pow_add]
      congr 1
      obtain ⟨N, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      obtain ⟨N', rfl⟩ : ∃ n, N' = n + 1 := ⟨N' - 1, by omega⟩
      have : (N' + 1) * (N + 1) - 1 = (N' + 1) * N + N' := by
        rw [Nat.sub_eq_iff_eq_add (Nat.succ_le_of_lt (by positivity))]; ring
      rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]
      ring
    · rw [sval_of_heq D F (Nat.mul_assoc k N' N) s₂ s₃ he (hst χ),
        (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 r₂ _ _ y J hJ, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 r₁ _ _ y J hJ,
        vu _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, hcl, Units.val_mul]
      ring
  · refine eq_zero_of_sval hL _ fun y J hJ => ?_
    rw [sval_of_heq D F (Nat.mul_assoc k N' N) s₂ s₃ he rfl]
    by_cases hb : ∃ χ', β = star a • χ'
    · obtain ⟨χ', rfl⟩ := hb
      obtain ⟨u₂, -, -, r₂⟩ := h₂.1 χ'
      rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 r₂ _ _ y J hJ,
        sval_eq_zero _ (h₁.2 χ' fun χ e => hβ χ (by rw [hst, e])), zero_mul]
    · exact sval_eq_zero _ (h₂.2 β fun χ e => hb ⟨χ, e⟩) _ _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgClosedValuedFieldOverCompleteDVR
section
namespace GlobalTheory.ClosedValuedField

open scoped NNReal

theorem exists_isAlgClosed_forall_isAdicComplete (F₀ : Type) [Field F₀] [IsAlgClosed F₀]
    (v₀ : AddValuation F₀ (WithTop ℚ)) {a : F₀} (ha : a ≠ 0) (hv : 0 < v₀ a) :
    ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (e : F₀ →+* F)
      (v : AddValuation F (WithTop ℚ)), (∀ x, v (e x) = v₀ x) ∧
      ∀ b : ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v, 0 < v (b : F) →
        IsAdicComplete (Ideal.span {b}) (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  let w := expNegAbsoluteValue v₀
  have hw : ∀ x, w x = (expNegTop (v₀ x) : ℝ) := fun _ => rfl
  have hp1 : w a < 1 := by
    rw [hw, ← NNReal.coe_one, NNReal.coe_lt_coe, ← expNegTop_zero, ← not_le, expNegTop_le_iff]
    exact not_le.2 hv
  have hp0 : 0 < w a := w.pos ha
  letI : NontriviallyNormedField (WithAbs w) :=
    { (inferInstance : NormedField (WithAbs w)) with
      non_trivial := ⟨(WithAbs.toAbs w a)⁻¹, by
        rw [norm_inv]
        change 1 < (w a)⁻¹
        exact (one_lt_inv₀ hp0).2 hp1⟩ }
  haveI : IsUltrametricDist (WithAbs w) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
      isNonarchimedean_expNegAbsoluteValue v₀ x.ofAbs y.ofAbs
  haveI : IsAlgClosed (WithAbs w) := IsAlgClosed.of_ringEquiv F₀ _ (WithAbs.equiv w).symm
  let C := UniformSpace.Completion (WithAbs w)
  letI : NontriviallyNormedField C := completionNontriviallyNormedField (WithAbs w)
  haveI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra (WithAbs w)
  haveI : IsAlgClosed C :=
    isAlgClosed_of_denseRange (K := WithAbs w) UniformSpace.Completion.denseRange_coe
  let e : F₀ →+* C := (algebraMap (WithAbs w) C).comp (WithAbs.equiv w).symm.toRingHom
  have he : ∀ x, ‖e x‖₊ = expNegTop (v₀ x) := fun x =>
    NNReal.coe_injective (UniformSpace.Completion.norm_coe (WithAbs.toAbs w x))
  obtain ⟨v, hvC⟩ := exists_addValuation_expNegTop_eq_nnnorm (C := C) fun x => by
    obtain ⟨y, hy⟩ := exists_norm_eq_of_completion x
    exact ⟨v₀ y.ofAbs, NNReal.coe_injective hy.symm⟩
  have hmem : ∀ x : C, NormedField.valuation x ≤ 1 ↔ 0 ≤ v x := fun x => by
    rw [NormedField.valuation_apply, ← hvC, ← expNegTop_zero, expNegTop_le_iff]
  have hO : (NormedField.valuation (K := C)).Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) :=
    ⟨Subtype.val_injective, fun x => (hmem _).2 x.2, fun r hr => ⟨⟨r, (hmem r).1 hr⟩, rfl⟩⟩
  refine ⟨C, inferInstance, inferInstance, e, v,
    fun x => expNegTop_inj_of_eq (by rw [hvC, he]), fun b hb =>
    NormIntegers.isAdicComplete_span_singleton hO (by
      change ‖(b : C)‖ < 1
      rw [← coe_nnnorm, ← hvC, ← NNReal.coe_one, NNReal.coe_lt_coe, ← expNegTop_zero, ← not_le,
        expNegTop_le_iff]
      exact not_le.2 hb)⟩

end GlobalTheory.ClosedValuedField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.ClosedValuedField

theorem exists_field_over_cdvr : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → CharZero T.Fr → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F) (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v ∧ ∃ (O : Type) (_ : CommRing O) (_ : Algebra O F) (_ : Algebra T.V O) (_ : IsScalarTower T.V O F), Function.Injective (algebraMap O F) ∧ (∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) ∧ ∀ g : ℕ, g ≠ 0 → ¬ IsUnit ((g : ℕ) : T.V) → IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O := by
  intro T ϖ hϖ _
  obtain ⟨v₀, hv₀⟩ := exists_valOver_of_isAlgebraic hϖ (AlgebraicClosure T.Fr)
  have hinj : Function.Injective (TWO.algVF (V := T.V) (F := AlgebraicClosure T.Fr)) :=
    (algebraMap T.Fr (AlgebraicClosure T.Fr)).injective.comp (IsFractionRing.injective T.V T.Fr)
  obtain ⟨F, _, _, e, v, he, hc⟩ := exists_isAlgClosed_forall_isAdicComplete
    (AlgebraicClosure T.Fr) v₀ ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero)
    (lt_of_lt_of_le zero_lt_one ((TWO.v_of_V v₀ hϖ hv₀ ϖ).2 hϖ.not_isUnit hϖ.ne_zero))
  letI : Algebra T.Fr F := (e.comp (algebraMap T.Fr (AlgebraicClosure T.Fr))).toAlgebra
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap T.Fr F).injective
  letI : Algebra T.V F := (TWO.algVF (V := T.V) (F := F)).toAlgebra
  haveI : IsScalarTower T.V T.Fr F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hv : ValOver ϖ F v := fun c n h => (he _).trans (hv₀ c n h)
  letI : Algebra T.V (TWO.Ov v) := (TWO.fO v hϖ hv).toAlgebra
  haveI : IsScalarTower T.V (TWO.Ov v) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, v, hv, TWO.Ov v, inferInstance, inferInstance, inferInstance, inferInstance,
    Subtype.val_injective, fun z => ⟨fun h => ⟨⟨z, h⟩, rfl⟩, ?_⟩, fun g hg hu => hc _ ?_⟩
  · rintro ⟨y, rfl⟩
    exact y.2
  · have h := (TWO.v_of_V v hϖ hv (g : T.V)).2 hu (Nat.cast_ne_zero.2 hg)
    rw [map_natCast] at h
    have e' : (((g : ℕ) : TWO.Ov v) : F) = (g : F) := map_natCast (algebraMap (TWO.Ov v) F) g
    rw [e']
    exact lt_of_lt_of_le zero_lt_one h

end GlobalTheory.ClosedValuedField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMap
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxLinear

open GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
  {Z : Scheme.{0}}

theorem ext_val {D : DegPre R} {S T : Fam D F k}
    (h : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      sval (S.s α) (𝟙 _) y J = sval (T.s α) (𝟙 _) y J) : S = T := by
  refine fam_ext fun α jj => fn_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  refine (sec_trans (S.s α) (𝟙 _) y hy (hJ.mem _ (𝟙 _))).trans
    (Eq.trans (congrArg _ (h α y J hJ)) (sec_trans (T.s α) (𝟙 _) y hy (hJ.mem _ (𝟙 _))).symm)

theorem sval_add {D : DegPre R} (S T : Fam D F k) (α : D.X) (q : Z ⟶ (DegPre.BF D F).left) (y : Z) {J}
    (hJ : Good D.P.L y J) :
    sval ((S + T).s α) q y J = sval (S.s α) q y J + sval (T.s α) q y J :=
  gs_add q y _ (hJ.mem _ q) _ _

theorem sval_smul {D : DegPre R} (c : F) (S : Fam D F k) (α : D.X) (q : Z ⟶ (DegPre.BF D F).left) (y : Z) {J}
    (hJ : Good D.P.L y J) :
    sval ((c • S).s α) q y J = gs (X := Spec (CommRingCat.of F)) (q ≫ (fst (TF (R := R) F) D.P.A).left) y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * sval (S.s α) q y J := by
  refine (gs_mul q y _ (hJ.mem _ q) _ _).trans (congrArg (· * _) ?_)
  exact (gs_res q y le_top (hJ.mem _ q) _).trans (gs_pull q (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _)

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem prB_fst (i : Fin j) : prB pD F i ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D'.P.A).left :=
  congrArg (fun g => g.left) (whiskerLeft_fst (TF (R := R) F) (pD.pw.pr i))

theorem box_val {S : Fam D' F k} {s : Fin j → Fam D F k} (h : IsBoxFam pD F k S s) (α' : D'.X)
    (y : (DegPre.BF D' F).left) {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    (∏ a, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F α' a) ^ DegPre.famε k a).val * sval (S.s α') (𝟙 _) y J' =
      ∏ i, sval ((s i).s (pD.xe α' i)) (𝟙 _ ≫ prB pD F i) y J := by
  obtain ⟨hφ, H⟩ := h α'
  exact boxPull_val (w := pD.w) (hφ := hφ) (s := fun i => (s i).s (pD.xe α' i)) H (𝟙 _) y hJ hJ'

theorem prod_update {A S : Type*} [CommMonoid S] {j : ℕ} [DecidableEq (Fin j)] (g : Fin j → A → S) (s : Fin j → A)
    (i : Fin j) (x : A) :
    ∏ l, g l (Function.update s i x l) = g i x * ∏ l ∈ Finset.univ.erase i, g l (s l) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  refine congrArg _ (Finset.prod_congr rfl fun l hl => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

theorem box_unique {S T : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    (hT : IsBoxFam pD F k T s) : S = T :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    exact (Units.mul_right_inj _).1 ((box_val pD hS α y hJ hJ').trans (box_val pD hT α y hJ hJ').symm)

theorem box_add [DecidableEq (Fin j)] {S S₁ S₂ : Fam D' F k} {s : Fin j → Fam D F k} {i : Fin j} {a b : Fam D F k}
    (h : IsBoxFam pD F k S (Function.update s i (a + b))) (h₁ : IsBoxFam pD F k S₁ (Function.update s i a))
    (h₂ : IsBoxFam pD F k S₂ (Function.update s i b)) : S = S₁ + S₂ :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    have p := prod_update (fun l (t : Fam D F k) => sval (t.s (pD.xe α l)) (𝟙 _ ≫ prB pD F l) y J) s i
    have e := (box_val pD h α y hJ hJ').trans (p _)
    have e₁ := (box_val pD h₁ α y hJ hJ').trans (p _)
    have e₂ := (box_val pD h₂ α y hJ hJ').trans (p _)
    refine (Units.mul_right_inj _).1 (e.trans ?_)
    rw [sval_add _ _ _ _ _ hJ, sval_add _ _ _ _ _ hJ', mul_add, add_mul, e₁, e₂]

theorem box_smul [DecidableEq (Fin j)] {S S₁ : Fam D' F k} {s : Fin j → Fam D F k} {i : Fin j} {c : F} {a : Fam D F k}
    (h : IsBoxFam pD F k S (Function.update s i (c • a))) (h₁ : IsBoxFam pD F k S₁ (Function.update s i a)) :
    S = c • S₁ :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    have p := prod_update (fun l (t : Fam D F k) => sval (t.s (pD.xe α l)) (𝟙 _ ≫ prB pD F l) y J) s i
    have e := (box_val pD h α y hJ hJ').trans (p _)
    have e₁ := (box_val pD h₁ α y hJ hJ').trans (p _)
    refine (Units.mul_right_inj _).1 (e.trans ?_)
    rw [sval_smul _ _ _ _ _ hJ, sval_smul _ _ _ _ _ hJ', Category.assoc, prB_fst, mul_left_comm, e₁,
      _root_.mul_assoc]

end GlobalTheory.BoxLinear

namespace GlobalTheory

theorem exists_boxFam_multilinear : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  intro hG R _ _ j D D' pD F _ _ k
  choose bx hbx using BoxFamily.exists_isBoxFam hG R j D D' pD F k
  refine ⟨⟨bx, fun s i a b => BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
    fun s i c a => BoxLinear.box_smul pD (hbx _) (hbx _)⟩, fun s S => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact BoxLinear.box_unique pD h (hbx s)
  · rw [h]; exact hbx s

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpandsGSum
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GroupExpansionLinear

open GlobalTheory.ExpansionLinear

theorem expandsG_sum : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k l : ℕ) (c : Fin l → F) (σ : Fin l → U.SecGF F k) (s : Fin l → Fam D.toPre F k) (σ' : U.SecGF F k), (∀ i, U.ExpandsG F k (σ i) (s i)) → (∀ jj, σ'.f jj = ∑ i, resTop _ (scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i)) * (σ i).f jj) → U.ExpandsG F k σ' (∑ i, c i • s i) := by
  intro R _ _ _ _ D A G _ _ U F _ _ k n c σ' s σ₀ ht h₀
  choose m d σ f hexp hG hB using ht
  let e : Fin (Fintype.card (Σ l, Fin (m l))) ≃ Σ l, Fin (m l) := (Fintype.equivFin _).symm
  refine ⟨_, fun i => c (e i).1 * d (e i).1 (e i).2, fun i => σ (e i).1 (e i).2, fun i => f (e i).1 (e i).2,
    fun i => hexp _ _, ?_, fun α => ?_⟩
  · exact secLin_comb _ _ _ _ _ _ _ σ' _ h₀ σ _ hG e _ (fun i => GlobalTheory.ExpansionLinear.scal_mul _ _ _)
  · exact secLin_comb _ _ _ _ _ _ (fun l => scal (fst (TF (R := R) F) D.toPre.P.A).left (c l))
      (fun l => (s l).s α) _ (fun j => fam_sum_f _ _ α j) (fun l i => f l i α) _ (fun l => hB l α) e _
      (fun i => GlobalTheory.ExpansionLinear.scal_mul _ _ _)

end GlobalTheory.GroupExpansionLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapCoefficientDerivativeBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem l2SG_of_ae_smul {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F G : Mx k r → Wp) (c : ℝ)
    (h : ∀ᵐ x ∂νq, F (Matrix.of x) = (c : ℂ) • G (Matrix.of x)) :
    PI.BesselPeriodGGP.l2SG νq F = ENNReal.ofReal (c ^ 2) * PI.BesselPeriodGGP.l2SG νq G := by
  unfold PI.BesselPeriodGGP.l2SG
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow]
  congr 1
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg c), ← Real.norm_eq_abs, ← Complex.norm_real,
    ofReal_norm_eq_enorm]
  rfl

theorem scaled_bessel_isometric : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → IsBeL R z π μW μN l → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → NzOn R l → IsIsoB R z π νq (fun w => ((Real.sqrt dd : ℝ) : ℂ) • l w) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq l dd hDS hgap hok hS hl hd hnz
  refine ⟨Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hl.1 _, fun w hw => ?_⟩
  obtain ⟨v, hv, hlv⟩ := GlobalTheory.bessel_nonzero_on_translates hH k r ε mu R Wp z π l hDS hl.1 hnz
  obtain ⟨-, -, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  obtain ⟨-, -, hdd, hP⟩ := GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS dd hd v hv (l v)
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hS0, hS1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq
  have hn : 0 < ‖l v‖ := norm_pos_iff.mpr hlv
  have hin : ⟪l v, l v⟫_ℂ = ((‖l v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; first | rfl | norm_cast | simp
  have hbe : ∀ y ∈ R.sm, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN y v (l v) = ((‖l v‖ ^ 2 : ℝ) : ℂ) • l y := by
    intro y hy
    rw [(hl.2 y hy v hv).2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hin]
  have hre : (⟪l v, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v (l v)⟫_ℂ).re = ‖l v‖ ^ 2 * ‖l v‖ ^ 2 := by
    rw [hbe v (hTK v hv), inner_smul_right, hin, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [l2SG_of_ae_smul νq _ (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v (l v))
    (Real.sqrt dd / ‖l v‖ ^ 2), hP w hw, hre, ← ENNReal.ofReal_mul (sq_nonneg _)]
  · congr 1
    rw [div_pow, Real.sq_sqrt hdd.le]
    field_simp
  · filter_upwards [hae] with x hx
    rw [hbe _ (hsm _ hx w hw), smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos hn 2).ne']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVR
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem expandsG_bijective_of_dvr : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ σ' : U.SecGF F k, ∃! s : Fam D.toPre F k, U.ExpandsG F k σ' s) ∧ ∀ s : Fam D.toPre F k, ∃! σ' : U.SecGF F k, U.ExpandsG F k σ' s :=
  fun hL _ _ _ _ _ _ _ _ _ _ _ _ _ U F _ _ k hk =>
    FieldBaseChange.expandsG_bijective U.toUnifPre F hL.globalFns hk (U.expand k hk)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ListProdHatLettersMemNormalFormProductSpan
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem hats_prod_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ H : List A, (∀ h ∈ H, h ∈ hats d.L) → H.prod ∈ nfSpan d T 0 (a * H.length) H.length := by
  intro P A _ _ _ _ d hd T a ha H
  induction H with
  | nil =>
    intro _
    refine Submodule.subset_span ⟨1, (bmon d).one_mem, [], rfl, by simp, ?_⟩
    simp
  | cons X H ih =>
    intro hH
    have h1 := ih (fun h hh => hH h (List.mem_cons_of_mem _ hh))
    have h2 := (_root_.GlobalTheory.HatNF.SpanMul.span_mul P A d hd T).2 a ha 0 (a * H.length) H.length X
      (hH X List.mem_cons_self) _ h1
    rw [List.prod_cons, List.length_cons, Nat.mul_succ]
    exact h2

end GlobalTheory.HatNF
end

