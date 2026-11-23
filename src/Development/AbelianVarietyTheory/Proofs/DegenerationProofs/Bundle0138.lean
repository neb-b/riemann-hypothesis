module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVROverPowerSeriesUniformiser
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.HasFields

theorem cdv_powerSeries (k : Type) [Field k] [CharZero k] : CDV (PowerSeries k) := by
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have h0 : CharZero (PowerSeries k) := algebraRat.charZero _
  exact (GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, h0⟩

theorem exists_lift (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [FaithfulSMul R K] [Algebra.IsAlgebraic R K] [Field L] [IsAlgClosed L] (ψ : R →+* L)
    (hψ : Function.Injective ψ) : ∃ e : K →+* L, ∀ x, e (algebraMap R K x) = ψ x := by
  letI : Algebra R L := ψ.toAlgebra
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 hψ
  let e : K →ₐ[R] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨e, fun x => e.commutes x⟩

theorem exists_cdv_over_powerSeries : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : PowerSeries O' →+* W) (K₁ : Type) (_ : Field K₁) (_ : Algebra (FractionRing W) K₁) (_ : Algebra.IsAlgebraic (FractionRing W) K₁) (e : K →+* K₁), CDV W ∧ φ PowerSeries.X ∈ IsLocalRing.maximalIdeal W ∧ ∀ x, e (algebraMap (PowerSeries O') K x) = algebraMap (FractionRing W) K₁ (algebraMap W _ (φ x)) := by
  intro O' _ _ _ K _ _ _ _
  let F := FractionRing O'
  haveI : CharZero F := IsFractionRing.charZero_of_isFractionRing O'
  let W := PowerSeries F
  let φ : PowerSeries O' →+* W := PowerSeries.map (algebraMap O' F)
  have hφ : Function.Injective φ :=
    PowerSeries.map_injective _ (IsFractionRing.injective O' F)
  let K₁ := AlgebraicClosure (FractionRing W)
  let ψ : PowerSeries O' →+* K₁ :=
    (algebraMap (FractionRing W) K₁).comp ((algebraMap W (FractionRing W)).comp φ)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing W) K₁).injective.comp
      ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  have key : ∃ e : K →+* K₁, ∀ x, e (algebraMap (PowerSeries O') K x) = ψ x :=
    exists_lift _ K K₁ ψ hψ
  obtain ⟨e, he⟩ := key
  refine ⟨W, inferInstance, inferInstance, inferInstance, φ, K₁, inferInstance, inferInstance,
    inferInstance, e, cdv_powerSeries F, ?_, he⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]
  have hX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
  rw [hX]
  exact Ideal.subset_span rfl

end GlobalTheory.HasFields
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCountableClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_countable_closed {K : Type} [Field K] [IsAlgClosed K] (K₀ : Subfield K) [Countable K₀] {X : Type}
    [Countable X] (a : X → K) : ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (α : K₀ →+* F₁)
      (β : F₁ →+* K), β.comp α = K₀.subtype ∧ ∀ x, a x ∈ Set.range β := by
  let K₁ : Subfield K := Subfield.closure ((K₀ : Set K) ∪ Set.range a)
  have hc : ((K₀ : Set K) ∪ Set.range a).Countable := (Set.to_countable _).union (Set.countable_range a)
  have c₁ : Cardinal.mk K₁ ≤ Cardinal.aleph0 :=
    (Subfield.cardinalMk_closure_le_max _).trans (max_le (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype) le_rfl)
  have h : K₀ ≤ K₁ := fun x hx => Subfield.subset_closure (Or.inl hx)
  let β : AlgebraicClosure K₁ →ₐ[K₁] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨AlgebraicClosure K₁, inferInstance, inferInstance, ?_, (algebraMap K₁ _).comp (Subfield.inclusion h),
    β.toRingHom, RingHom.ext fun x => β.commutes _, fun x =>
      ⟨algebraMap K₁ _ ⟨a x, Subfield.subset_closure (Or.inr ⟨x, rfl⟩)⟩, β.commutes _⟩⟩
  exact Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max K₁ _).trans (max_le c₁ le_rfl))

theorem exists_pre (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] {O : Type} [CommRing O] [StarRing O]
    [Module.Finite ℤ O] (D : DegPre K) (o : D.P.OAct O) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (β : F₁ →+* K) (D₁ : DegPre F₁)
      (hD : IsPullDeg β D₁ D) (o₁ : D₁.P.OAct O), ∀ a, (o.act a).left ≫ proj hD = proj hD ≫ (o₁.act a).left := by
  obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := D.X)
  have hgen' : Subring.closure (Set.range gen) = ⊤ := top_le_iff.1 fun x _ => by
    have hx : x ∈ Submodule.span ℤ (Set.range gen) := hgen ▸ Submodule.mem_top
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hx
    exact (AddSubgroup.closure_le (Subring.closure (Set.range gen)).toAddSubgroup).2 Subring.subset_closure hx
  have hb' : AddSubgroup.closure (Set.range b) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hb]; rfl
  obtain ⟨K₀, P₀, Φ, a₀, x₀, hc, gp, hw, ha, hx⟩ :=
    _root_.GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield K D.P (Fin n) (Fin m) (fun j => o.act (gen j)) (fun k => D.c (b k))
  obtain ⟨o₀, ho₀⟩ := _root_.GlobalTheory.polOAct_descend_of_generators O _ gen hgen' K₀ K _ P₀ D.P Φ gp hw o a₀ ha
  obtain ⟨c₀, hc₀, hc₁⟩ := _root_.GlobalTheory.PointDescent.additive_points_descend K₀ K _ P₀ D.P Φ gp D.X _ b hb' D.c D.c_add x₀ hx
  obtain ⟨D₀, ψ, hψ, h₀, rfl, e⟩ := _root_.GlobalTheory.FieldPull.exists_pre_below hL K₀ K _ D P₀ Φ gp hw c₀ hc₀ hc₁
  obtain rfl := eq_of_heq e
  obtain ⟨a, Ha⟩ := _root_.GlobalTheory.FieldPull.exists_ratio_descends K D ψ hψ
  have : Countable D.X := Finsupp.Countable.of_moduleFinite (R := ℤ)
  obtain ⟨F₁, _, _, _, α, β, hαβ, hβ⟩ := exists_countable_closed K₀ a
  obtain ⟨D', h₁, -, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange K₀ F₁ α D₀ ⊤ (nonempty_psiOn_field D₀) trivial
  generalize K₀.subtype = i at h₀ ho₀ hαβ
  subst hαβ
  obtain ⟨h₂, e₂⟩ := _root_.GlobalTheory.FieldPull.exists_isPullDeg_cancel K₀ F₁ K α β D₀ D' _ h₁ h₀
  obtain ⟨ψ₁, hψ₁, hD, e₃⟩ := Ha F₁ β D' h₂ hβ
  obtain ⟨o₁, ho₁⟩ := polOActPull _ _ _ D₀.P D'.P _ (pull_grp h₁) (LBIso.symm ⟨h₁.w, h₁.w_gen⟩) O o₀
  refine ⟨F₁, inferInstance, inferInstance, inferInstance, β, _, hD, o₁, fun c => ?_⟩
  rw [e₃]
  refine (pull_grp h₁).1.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans ((ho₀ c).trans ((congrArg (· ≫ _) e₂.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ho₁ c).symm).trans (Category.assoc _ _ _).symm)))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pull_grp h₂).1.w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w (o.act c))).trans ((pull_grp h₂).1.w.symm.trans
        ((congrArg (_ ≫ ·) (Over.w (o₁.act c)).symm).trans (Category.assoc _ _ _).symm)))))

theorem exists_data (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] {O : Type} [CommRing O] [StarRing O]
    [Module.Finite ℤ O] (D : DegPre K) [Module O D.X] (oa : D.OAct O) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (β : F₁ →+* K) (D₁ : DegPre F₁)
      (hD : IsPullDeg β D₁ D) (_ : Module O D₁.X) (oa₁ : D₁.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) ∧
      (∀ a, (oa.onB.act a).left ≫ proj hD = proj hD ≫ (oa₁.onB.act a).left) ∧ (D.PsiEven → D₁.PsiEven) ∧
      (D.TauBimult → D₁.TauBimult) ∧ ∀ w, TraceFormTwistIso D oa w → TraceFormTwistIso D₁ oa₁ w := by
  obtain ⟨F₁, _, _, _, β, D₁, hD, o₁, ho⟩ := exists_pre hL D oa.onB
  letI : Module O D₁.X := hD.xe.symm.module O
  have hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y := fun a y => by
    show _ = hD.xe (a • hD.xe.symm (hD.xe y))
    rw [AddEquiv.symm_apply_apply]
  obtain ⟨oa₁, rfl⟩ := _root_.GlobalTheory.exists_oAct_of_field_extension hL.globalFns F₁ K β D₁ D hD O o₁ oa hx ho
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective hL.globalFns F₁ K β β.injective D₁ D hD
  exact ⟨F₁, inferInstance, inferInstance, inferInstance, β, D₁, hD, inferInstance, oa₁, hx, ho, h₁, h₂,
    _root_.GlobalTheory.psi_relation_descend_field hL.globalFns F₁ K β D₁ D hD O oa₁ oa hx ho⟩

end GlobalTheory.FieldPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOfRescaledTwisted
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.RescaleValues

theorem vF_psi_rescale {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (q : D.X → (FractionRing R)ˣ) (χ : D.X) {J : (Sp F ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : ∀ ψ : Sp F ⟶ D.P.A.left, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) :
    vF ((TauTwist.rescale D q).psi χ) (jFK (R := R) F) J =
      algebraMap (FractionRing R) F (q χ) * vF (D.psi χ) (jFK (R := R) F) J := by
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have e := TauTwist.val_psi_rescale q χ (jFK (R := R) F) (z := z) (J := J) (fun ψ => hJ ψ trivial)
  have e₁ : TauTwist.unitAt (jFK (R := R) F) z (q χ) =
      TorusExt.stalkUnits z (Units.map (algebraMap (FractionRing R) F).toMonoidHom (q χ)) := by
    have h := TauTwist.unitAt_spMap (𝟙 (Sp F)) (algebraMap (FractionRing R) F) z (q χ)
    rw [Category.id_comp] at h
    exact h.trans (TorusExt.gm_unitOn z _)
  refine (GaugeValues.vF_eq hJ z _ _).symm.trans ?_
  refine (congrArg (fun x => (((TorusExt.stalkUnits z).symm x : Fˣ) : F)) (e.trans (congrArg (· * _) e₁))).trans ?_
  refine Eq.trans ?_ (congrArg (_ * ·) (GaugeValues.vF_eq hJ z _ _))
  simp only [map_mul, MulEquiv.symm_apply_apply, Units.val_mul]
  rfl

theorem exists_numOf_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (k : ℕ) (β : N.Form k) (u : Fˣ) (q : D.X → (FractionRing R)ˣ), (∀ y, algebraMap (FractionRing R) F (q (ν.eX y)) = ((u ^ (β.be y y / 2) : Fˣ) : F)) → ∃ ν' : NumOf (TauTwist.rescale D q) F (N.twist β u), (∀ y : N.X, ν'.eX y = ν.eX y) ∧ ∀ x : N.A, ν'.eA x = ν.eA x := by
  intro R _ _ D F _ _ N ν k β u q hq
  refine ⟨{ J := ν.J, good := ν.good, th := ν.th, th_gen := ν.th_gen, eA := ν.eA, eX := ν.eX, c_eq := ν.c_eq,
            θ_eq := ν.θ_eq, σ_eq := ν.σ_eq, th_eq := ν.th_eq, ψ_eq := fun (χ : N.X) => ?_ }, fun _ => rfl, fun _ => rfl⟩
  refine Eq.trans ?_ (congrArg (· * _) (vF_psi_rescale D q (ν.eX χ) ν.good).symm)
  show ((N.ψ χ * u ^ (β.be χ χ / 2) : Fˣ) : F) = _
  rw [Units.val_mul, ν.ψ_eq, hq]
  exact (mul_comm _ _).trans (_root_.mul_assoc _ _ _).symm

end GlobalTheory.RescaleValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOfStrictPullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

noncomputable section
namespace GlobalTheory.ValuesStrictPull
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport
open GlobalTheory.PsiEvenPull (proj)
open ReciprocityTheory.ChartRestriction.G.DVR (cP)

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm

theorem vF_congr {X' Y' : Scheme.{0}} {L' : LB X'} {K' : Type} [Fintype K'] {φ' : K' → (Y' ⟶ X')} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {r : Sp F ⟶ Y} {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J)
    {t' : LB.Gen (LB.LinComb L' φ' ε')} {r' : Sp F ⟶ Y'} {J' : (Sp F ⟶ X') → L'.ι} (hJ' : Good L' z J')
    (h : val t r z J = val t' r' z J') : vF t r J = vF t' r' J' :=
  (stalkConst z).injective ((const_vF t r hJ).trans ((congrArg Units.val h).trans (const_vF t' r' hJ').symm))
end Val

theorem exists_numOf_strict_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), Strict hD.w → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ x, algebraMap (FractionRing R') F (algebraMap R' _ (φ x)) = algebraMap (FractionRing R) F (algebraMap R _ x)) → ∀ (N : NumD F) (ν : NumOf D F N) (th' : H0 D'.P.L 1), (∀ s : H0 D'.P.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval ν.th (r ≫ PsiEvenPull.proj hD) z J = (gw hD.w r z (J (r ≫ PsiEvenPull.proj hD)) (J' r)).val * sval th' r z J') → ∃ ν' : NumOf D' F N, (∀ y, hD.xe (ν'.eX y) = ν.eX y) ∧ ∀ x, (ν'.eA x).left ≫ PsiEvenPull.proj hD = (ν.eA x).left := by
  intro hG R R' _ _ _ _ φ D D' hD hS F _ _ _ hF N ν th' hgen hth
  obtain ⟨c, hc⟩ := hS
  have hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom := base_comm fun r => (hF r).symm
  have hj : jFK (R := R') F ≫ jK R' ≫ spMap φ = jFK (R := R) F ≫ jK R := (Category.assoc _ _ _).symm.trans hT
  let z : Sp F := IsLocalRing.closedPoint F
  let J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι := fun ψ => c (ν.J (ψ ≫ proj hD))
  have hJ : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial
  have good' : ∀ ψ : Sp F ⟶ D'.P.A.left, ⊤ ≤ ψ ⁻¹ᵁ D'.P.L.U (J' ψ) := fun ψ y _ =>
    (hc _ ψ y _ (ν.good (ψ ≫ proj hD) (x := y) trivial)).1
  have hJ' : Good D'.P.L z J' := fun ψ => good' ψ trivial
  have one : ∀ ψ : Sp F ⟶ D'.P.A.left, Geo.Tor.gw hD.w ψ z (ν.J (ψ ≫ proj hD)) (J' ψ) = 1 := fun ψ =>
    (hc _ ψ z _ (hJ (ψ ≫ proj hD))).2
  have one' : ∀ ψ : Sp F ⟶ D'.P.A.left, om hD.w z ν.J J' ψ = 1 := one
  have one'' : ∀ x : TF (R := R') F ⟶ D'.P.A, wVal hD.w z ν.J J' x = 1 := fun x => one x.left
  let P : (TF (R := R') F ⟶ D'.P.A) ≃* (TF (R := R) F ⟶ D.P.A) :=
    MulEquiv.ofBijective (MonoidHom.mk' (pushF (pull_grp hD) hT) (pushF_mul _ _))
      ⟨pushF_injective (pull_grp hD) hT, pushF_surjective (pull_grp hD) hT⟩
  obtain ⟨eA, heA⟩ : ∃ eA : N.A ≃* (TF (R := R') F ⟶ D'.P.A), ∀ x, pushF (pull_grp hD) hT (eA x) = ν.eA x :=
    ⟨ν.eA.trans P.symm, fun x => P.apply_symm_apply _⟩
  have hl : ∀ x, (eA x).left ≫ proj hD = (ν.eA x).left := fun x => congrArg (fun q => q.left) (heA x)
  obtain ⟨eX, heX⟩ : ∃ eX : N.X ≃+ D'.X, ∀ y, hD.xe (eX y) = ν.eX y :=
    ⟨ν.eX.trans hD.xe.symm, fun y => hD.xe.apply_symm_apply _⟩
  have rig : vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom ν.J =
      vF (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (TF (R := R') F).hom J' := by
    have e := ArcPull.rig_val hD (Z := Sp F) _ _ hj hJ hJ'
    rw [one', _root_.one_mul] at e
    exact vF_congr hJ hJ' ((val_pull hJ _ _ _).symm.trans (e.trans (val_pull hJ' _ _ _)))
  refine ⟨{
    J := J', good := good', th := th', th_gen := hgen, eA := eA, eX := eX
    c_eq := fun χ => ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_
    ψ_eq := fun χ => ?_ }, heX, hl⟩
  · apply pushF_injective (pull_grp hD) hT
    rw [heA, ν.c_eq, ← heX]
    exact Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
      (hT.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm
  · have k := thS_push (pull_grp hD) hT ((isGen_iff _).1 hD.w_gen) hG hJ hJ' (eA x) (eA y) (eA u)
    simp only [one'', heA, inv_one, _root_.one_mul] at k
    exact (ν.θ_eq x y u).trans (vF_congr hJ hJ' k)
  · have k := PsiEvenPull.sym_pull hG hD (Z := Sp F) (eA x).left z hJ hJ'
    rw [one, one, inv_one, _root_.one_mul, _root_.one_mul] at k
    refine (ν.σ_eq x).trans (vF_congr hJ hJ' (Eq.trans ?_ k))
    exact congrArg (fun q => val (Z := Sp F) D.sym q z ν.J) (hl x).symm
  · have k := hth (Sp F) (eA x).left z ν.J J' hJ hJ'
    rw [one, Units.val_one, _root_.one_mul] at k
    rw [← rig, ν.th_eq x]
    refine (stalkConst z).injective ((const_sF _ _ hJ).trans (Eq.trans ?_ (k.trans (const_sF _ _ hJ').symm)))
    exact congrArg (fun q => sval (Z := Sp F) ν.th q z ν.J) (hl x).symm
  · have k := ArcPull.psi_val hD (Z := Sp F) _ _ hj hJ hJ' (eX χ)
    rw [one', inv_one, _root_.one_mul, heX] at k
    rw [← rig, ν.ψ_eq χ]
    exact congrArg (· * _) (vF_congr hJ hJ' k)

end GlobalTheory.ValuesStrictPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOverSubfield
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ValuesSubfield
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_numOf_th {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) (th : H0 D.P.L 1)
    (hth : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) :
    ∃ (N₁ : NumD F) (ν₁ : NumOf D F N₁), ν₁.J = ν.J ∧ ν₁.th = th :=
  ⟨{ N with th := fun x => sF th (ν.eA x).left ν.J / rigVal ν },
    { ν with th := th, th_gen := hth, th_eq := fun _ => div_mul_cancel₀ _ (vF_ne_zero ν.good _ _) }, rfl, rfl⟩

theorem exists_values_subfield : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N' : NumD F') (ν' : NumOf D F' N'), ∃ (N : NumD F) (ν : NumOf D F N) (I : NumD.Hom f N N'), (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (c : N.Gt) (c' : N'.Gt), QkExt f p p' → ν.Pt p.g c → ν'.Pt p'.g c' → I.Rel c c' := by
  intro hG R _ _ D he hb F F' _ _ _ _ f hf N' ν'
  obtain ⟨N₀, ν₀, h₀⟩ := ValuesExist.exists_numOf D F hG he hb ν'.th ν'.th_gen (fun ψ => ν'.J (spMap f ≫ ψ))
    fun ψ z _ => (Subsingleton.elim (α := PrimeSpectrum F) (spMap f (IsLocalRing.closedPoint F')) z) ▸
      ν'.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F'))
  obtain ⟨N, ν, h₁, h₂⟩ := exists_numOf_th ν₀ ν'.th ν'.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = ν.J ψ := fun ψ => by rw [h₁, h₀]
  refine ⟨N, ν, numHom f hf ν ν' hJ h₂.symm, eX_numHom f hf ν ν' hJ h₂.symm, fun k p p' c c' h hc hc' => ?_⟩
  have hg : p'.g = gtExt D f hf p.g := (eq_gtExt_iff f hf _ _).2 h.2
  rw [hg] at hc'
  exact numHom_rel f hf ν ν' hJ h₂.symm hc hc'

end GlobalTheory.ValuesSubfield
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfSmoothOfGeometricPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory

theorem exists_desc_of_smooth_of_geometricPoints :
    ∀ (K C : Type) [Field K] [CharZero K] [Field C] [Algebra K C] (X Y : Over (Sp K)), Smooth X.hom → IsSeparated Y.hom → ∀ f : pullback X.hom (spMap (algebraMap K C)) ⟶ Y.left, f ≫ Y.hom = pullback.fst X.hom (spMap (algebraMap K C)) ≫ X.hom → (∀ (F : Type) [Field F] [IsAlgClosed F] (x x' : Sp F ⟶ pullback X.hom (spMap (algebraMap K C))), x ≫ pullback.fst _ _ = x' ≫ pullback.fst _ _ → x ≫ f = x' ≫ f) → ∃ f₀ : X ⟶ Y, pullback.fst X.hom (spMap (algebraMap K C)) ≫ f₀.left = f := by
  intro K C _ _ _ _ X Y hX hY f hf H
  have : IsReduced (pullback X.hom (spMap (algebraMap K C))) :=
    isReduced_of_smooth_of_isReduced (pullback.snd X.hom (spMap (algebraMap K C)))
  obtain ⟨ψ, hψ⟩ := ArcDataDescent.exists_desc_of_points (algebraMap K C)
    (IsPullback.of_hasPullback X.hom (spMap (algebraMap K C))) Y.hom f X.hom hf H
  have f₁ : Flat (spMap (algebraMap K C)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have f₂ : Surjective (spMap (algebraMap K C)) :=
    ⟨fun y => ⟨(default : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Epi (pullback.fst X.hom (spMap (algebraMap K C))) := Flat.epi_of_flat_of_surjective _
  refine ⟨Over.homMk ψ ?_, hψ⟩
  rw [← cancel_epi (pullback.fst X.hom (spMap (algebraMap K C))), ← Category.assoc, hψ]
  exact hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalExtContainingAlgebraicElements
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis

theorem exists_extend_of_isAlgebraic {A B F : Type} [Field A] [Field B] [Field F] [IsAlgClosed F] [Algebra A B]
    [Algebra.IsAlgebraic A B] (g : A →+* F) : ∃ σ : B →+* F, ∀ x, σ (algebraMap A B x) = g x := by
  letI : Algebra A F := g.toAlgebra
  let σ : B →ₐ[A] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨(σ : B →+* F), fun x => σ.commutes x⟩

theorem exists_finite_normal_containing : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [CharZero R₁], IsIntegrallyClosed R₁ → ∀ (I : Type) [Finite I] (Φ : I → AlgebraicClosure (FractionRing R₁)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂) (j : FractionRing R₂ →+* AlgebraicClosure (FractionRing R₁)) (Φ₂ : I → FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ (∀ x, j (h' x) = algebraMap (FractionRing R₁) _ x) ∧ (∀ i, j (Φ₂ i) = Φ i) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (ga : FractionRing R₂ →+* F), ∃ σ : AlgebraicClosure (FractionRing R₁) →+* F, ∀ x, σ (j x) = ga x := by
  intro R₁ _ _ _ _ hIC I _ Φ
  let K := FractionRing R₁
  let L := AlgebraicClosure K
  let K₂ : IntermediateField K L := IntermediateField.adjoin K (Set.range Φ)
  haveI : Finite (Set.range Φ) := (Set.finite_range Φ).to_subtype
  haveI : FiniteDimensional K K₂ :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R₁
  haveI : Algebra.IsSeparable K K₂ := inferInstance
  let R₂ := integralClosure R₁ K₂
  haveI : IsFractionRing R₂ K₂ := IsIntegralClosure.isFractionRing_of_finite_extension R₁ K K₂ R₂
  haveI hfin : Module.Finite R₁ R₂ := IsIntegralClosure.finite R₁ K K₂ R₂
  let e : FractionRing R₂ ≃ₐ[R₂] K₂ := FractionRing.algEquiv R₂ K₂
  have hinj : Function.Injective (algebraMap R₁ K₂) := by
    rw [IsScalarTower.algebraMap_eq R₁ K K₂]
    exact (algebraMap K K₂).injective.comp (IsFractionRing.injective R₁ K)
  refine ⟨R₂, inferInstance, inferInstance, algebraMap R₁ R₂,
    (e.symm : K₂ →+* FractionRing R₂).comp (algebraMap K K₂),
    (algebraMap K₂ L).comp (e : FractionRing R₂ →+* K₂),
    fun i => e.symm ⟨Φ i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply hinj
    rw [IsScalarTower.algebraMap_apply R₁ R₂ K₂ a, IsScalarTower.algebraMap_apply R₁ R₂ K₂ b, hab]
  · exact RingHom.finite_algebraMap.mpr hfin
  · exact integralClosure.isIntegrallyClosedOfFiniteExtension K
  · intro r
    change e.symm (algebraMap K K₂ (algebraMap R₁ K r)) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₁ R₂ K₂, AlgEquiv.commutes]
  · intro x
    change algebraMap K₂ L (e (e.symm (algebraMap K K₂ x))) = _
    rw [e.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
  · intro i
    change algebraMap K₂ L (e (e.symm _)) = _
    rw [e.apply_symm_apply]; rfl
  · intro F _ _ ga
    haveI : Algebra.IsAlgebraic K₂ L := Algebra.IsAlgebraic.tower_top (K := K) K₂
    obtain ⟨σ, hσ⟩ := exists_extend_of_isAlgebraic (A := K₂) (B := L) (ga.comp (e.symm : K₂ →+* FractionRing R₂))
    refine ⟨σ, fun x => (hσ (e x)).trans ?_⟩
    exact congrArg ga (e.symm_apply_apply x)

end GlobalTheory.OneBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibLieOfLaws
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch


open GlobalTheory.PointUnif GlobalTheory.EigenSplit in
theorem fibLie_of_laws : Laws → FibLieSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hfib O _ act F hF τ n hn
  obtain ⟨-, P', φ, w, u, -, hφ, -, -, h1, h2, -, hex, -⟩ := hfib
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ _) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have he := isExp_push hφ u h1 h2 Φ hΦ
  have hx : ∀ z, Φ (u.ex z) = ex z := fun z => Over.OverMorphism.ext ((hΦ _).trans (hex z).symm)
  have hker : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  have hF' : ∀ a z, Φ (u.ex (F a z)) = Φ (u.ex z) ≫ act.act a := fun a z => by
    rw [hx, hx]; exact hF a z
  obtain ⟨ρ, hρ⟩ := he.exists_rep act u.Λ u.discrete hker fun a => ⟨F a, hF' a⟩
  have hρF : ∀ a, ρ a = F a := fun a => by
    refine sub_eq_zero.1 (linear_eq_zero_of_discrete u.Λ u.discrete _ fun z => (hker _).1 ?_)
    have := he.1 ((ρ a - F a) z) (F a z)
    simp only [LinearMap.sub_apply, sub_add_cancel] at this
    rw [hρ, ← hF'] at this
    exact mul_eq_right.1 this.symm
  have hy : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R _)) :=
    (Spec.map_comp _ _).symm
  rw [← hy] at hn
  have hE : (⨅ a, (F a).eigenspace (τ a) : Submodule ℂ (Fin g → ℂ)) = eigenSub ρ τ := by
    ext z
    simp only [mem_eigenSub, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, hρF]
  rw [hE]
  exact he.finrank_eigenSub act ρ hρ hn

end GlobalTheory.Ex.Arch
end
end

