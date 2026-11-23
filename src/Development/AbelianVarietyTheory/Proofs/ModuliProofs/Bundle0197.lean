module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0196
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSpreadThetaLevelAbelianSchemeAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsCountSqEqDetFormOnTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseModelSemiAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_model_semiAbelian : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (n J : ℕ) (T : Top Xo n (n ^ J)) (l₀ : Level H), AuxiliaryInertOddPrime H n → 1 ≤ J → l₀.A = 1 → Nonempty (BaseModel T l₀) := by
  first | exact @GlobalTheory.BaseModelEx.exists_baseModel | exact GlobalTheory.BaseModelEx.exists_baseModel | (intros; apply GlobalTheory.BaseModelEx.exists_baseModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_model_of_local_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ S : System Xo, N6 S.Y := by
  first | exact @GlobalTheory.GlobalModel.exists_global_model | exact GlobalTheory.GlobalModel.exists_global_model | (intros; apply GlobalTheory.GlobalModel.exists_global_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectOverCompleteDvrSpecialisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_complete_dvr_point (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) (f : R) (hf : f ≠ 0) :
    ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V))
      (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V),
      (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ y f ≠ 0 := by
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.exists_prime_natCast_mem_of_finiteType_int 𝔪
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hL, y, hy, hyf⟩ := GlobalTheory.exists_padic_point 𝔪 hpm hf
  exact ⟨integralClosure ℤ_[p] L, L, inferInstance, inferInstance, inferInstance,
    GlobalTheory.DiscEval.isAdicComplete_integralClosure L, GlobalTheory.DiscEval.finite_residueField_integralClosure L,
    inferInstance, charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective, inferInstance,
    inferInstance, y, hy, hyf⟩

theorem exists_obj_over_complete_dvr : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [CharZero R] [Algebra.FiniteType ℤ R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)) (𝔪 : Ideal R), 𝔪.IsMaximal → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V)) (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V) (tF : TObj g (N' ^ 2) J b (spMap (algebraMap V F) ≫ spMap (y.comp β))), (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ tF.Shape Mat κ ∧ tF.Prim w w' ∧ tF.HasTh (𝟙 _) (fun a => algebraMap V F (y (v a))) := by
  intro L1 L2 o _ g N' J b Mat κ w w' _ R K _ _ _ _ _ _ _ β v t 𝔪 h𝔪 hth hsh hpr
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨f, hf, t', ψ, -, -, hth', hsh', hpr'⟩ :=
    _root_.GlobalTheory.SpreadGeneric.exists_spread L1 L2 o g N' J b Mat κ w w' R K β v t hth hsh hpr
  obtain ⟨V, F, i1, i2, i3, i4, i5, i6, i7, i8, i9, y, hy, hyf⟩ :=
    exists_complete_dvr_point R 𝔪 h𝔪 f hf
  have hu : IsUnit (((algebraMap V F).comp y) f) :=
    isUnit_iff_ne_zero.mpr fun h => hyf (IsFractionRing.injective V F (h.trans (map_zero _).symm))
  let φ : Localization.Away f →+* F := IsLocalization.Away.lift f hu
  have hφ : φ.comp (algebraMap R (Localization.Away f)) = (algebraMap V F).comp y :=
    IsLocalization.Away.lift_comp f hu
  have hsq : spMap φ ≫ spMap (algebraMap R (Localization.Away f)) ≫ spMap β =
      spMap (algebraMap V F) ≫ spMap (y.comp β) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← RingHom.comp_assoc, hφ, RingHom.comp_assoc]
  obtain ⟨tF, hm⟩ := _root_.GlobalTheory.tObj_pull o g (N' ^ 2) J b _ _ _ _ (spMap φ) t' hsq
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.shape_prim_pull_and_descend o g (N' ^ 2) J b Mat κ w w' _ _ _ _ _ t' tF hm
  refine ⟨V, F, i1, i2, i3, i4, i5, i6, i7, i8, i9, y, tF, hy, h1 hsh', h2 hpr', ?_⟩
  have h3 := _root_.GlobalTheory.hasTh_baseChange L2 o g N' J b _ _ t' _ _ φ _ _ hth'
  refine (_root_.GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t' _ _ tF _ F _ _ hm).mpr ?_
  rw [Category.id_comp]
  rw [Category.comp_id] at h3
  have e : (fun a => algebraMap V F (y (v a))) =
      fun a => φ (algebraMap R (Localization.Away f) (v a)) :=
    funext fun a => (RingHom.congr_fun hφ (v a)).symm
  rw [e]
  exact h3

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.RaisedTransition

theorem mono_spMap_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Mono (spMap β) := by
  letI := β.toAlgebra
  have := h.2.2
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F)
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDedFrac_of_isInc (l : Level H) (S A : ℕ) (hS : 0 < S) (hA : l.A = A) (h1 : A = 1) (β : RZ H S A →+* KA l)
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) : IsDedFrac β := by
  subst hA
  exact (GlobalTheory.BaseRing.isDedFrac_RZ E H l S 0 hS (by rw [h1, pow_zero])).2.2 β hβ

theorem j_over {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F}
    (C : Cpt c t β) : C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem div_mul_div {a b c : ℕ} (h : a ∣ b) (h' : b ∣ c) : c / b * (b / a) = c / a := by
  exact Nat.div_mul_div h' h

theorem levComp_trans {D : Datum H} {l l' l'' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l'' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l'' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    {ξ : SABMap o''.t o'.t g} {ν : SABMap o'.t o.t r} (hd : l.Dvd l') (hd' : l'.Dvd l'') (h' : LevComp o'' o' g ξ)
    (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r)) (e : ν'.φ = ξ.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← div_mul_div hd.1 hd'.1, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.1 a), Category.assoc, h.1,
      Category.assoc]
  · rw [← div_mul_div hd.2.2 hd'.2.2, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.2 a), Category.assoc,
      h.2, Category.assoc]

theorem exists_isTransition : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₀' : Level H) (B : BaseModel T l₀) (B' : BaseModel T l₀') (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β) (l₂ : Level H) (c₂ : Coeff l₂) (O₂ : Type) [CommRing O₂] (β₂ : O₂ →+* c₂.F) (Y₂ : Model (Xo l₂) c₂ β₂) (b : O →+* O₂), 0 < n → (∃ e, N ∣ n ^ e) → l₀.Dvd l₀' → l₀.Dvd l → l₀'.Dvd l₂ → l.Dvd l₂ → c.F ≤ c₂.F → IsDedFrac β → IsDedFrac β₂ → IsInc (c.F.val.toRingHom.comp β) (c₂.F.val.toRingHom.comp β₂) b → Raises B Y → Raises B' Y₂ → ∃ π : Y₂.X ⟶ Y.X, IsTransition Y Y₂ b π := by
  intro hext L₁ L₂ L₃ E _ _ _ H D Xo n N T hN l₀ l₀' B B' l c O _ β Y l₂ c₂ O₂ _ β₂ Y₂ b hn hNe d₀ d₁ d₂ d hc hβ hβ₂ hb
    hR hR₂
  obtain ⟨b₁, r₁, ν₁, hb₁, hl₁, ⟨a₁⟩⟩ := hR
  obtain ⟨b₂, r₂, ν₂, hb₂, hl₂, ⟨a₂⟩⟩ := hR₂
  obtain ⟨b₀, r₀, ν₀, hb₀, hl₀, ⟨a₀⟩⟩ := GlobalTheory.T.deeper_level_base_model_finite_over_shallower hext L₁ L₂ L₃ E H D Xo n N T hN l₀ l₀' B B' hn hNe d₀
  obtain ⟨k, r, ν, hr, hk, hl, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l l₂ c₂ Y₂.oF Y₂.m0 d

  have hkk : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : (Xo l₂).XF c₂ ⟶ (Xo l).XF c, r' ≫ pullback.fst _ _ = r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨pullback.lift r (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom)
      (by rw [hr, hkk, spMap_comp, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m0.toSABMap ν r' hr₁
  have hl' : LevComp Y₂.oF Y.oF r' ν' :=
    ⟨fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.1, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.eta x).symm),
      fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.2, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.etaA x).symm)⟩

  have hbβ : β₂.comp b = (IntermediateField.inclusion hc).toRingHom.comp β :=
    RingHom.ext fun x => Subtype.ext (hb x)
  have hinj : Function.Injective β₂ := by
    letI := β₂.toAlgebra
    have := hβ₂.2.2
    exact IsFractionRing.injective O₂ c₂.F
  have hbb : b₂.comp b₀ = b.comp b₁ := RingHom.ext fun x => hinj (Subtype.ext
    ((hb₂ (b₀ x)).trans ((hb₀ x).trans ((hb (b₁ x)).trans (hb₁ x)).symm)))

  obtain ⟨ν₃, hν₃⟩ := LevelCover.sab_comp ν₂ ν₀ rfl
  obtain ⟨ν₄, hν₄⟩ := LevelCover.sab_comp ν' ν₁ rfl
  obtain ⟨a⟩ : Nonempty ((ofModel Y₂).Above B.C (b.comp b₁) (r₂ ≫ r₀) ν₃) := by
    rw [← hbb]
    exact ⟨(GlobalTheory.Models.above_comp E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C B'.C (ofModel Y₂) b₀ b₂ r₀ ν₀ r₂ ν₂ ν₃
      a₀ a₂ hν₃).choose⟩

  have hred : IsReduced ((Xo l₂).XF c₂) := by
    have := (Xo l₂).smooth
    have : Smooth (Xo l₂).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c₂.F _ (pullback.snd _ _)
      inferInstance).1
  have hover : (r₂ ≫ r₀) ≫ (Xo l₀).s = (r' ≫ r₁) ≫ (Xo l₀).s := by
    have hS : 0 < n * l₀.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l₀.three_le)
    have := mono_spMap_of_isDedFrac (isDedFrac_of_isInc l₀ _ 1 hS B.A_one rfl _ B.β_inc)
    have q₁ : (r₂ ≫ r₀) ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap β₂ ≫ spMap (b.comp b₁) := by
      rw [← Category.assoc, ← a.j_comm, Category.assoc, a.π_over, ← Category.assoc, j_over, Category.assoc]
    have q₂ : r₁ ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap β ≫ spMap b₁ := by
      rw [← Category.assoc, ← a₁.j_comm, Category.assoc, a₁.π_over, ← Category.assoc, j_over, Category.assoc]
    rw [← cancel_mono (spMap B.β), Category.assoc, ← j_over B.C, q₁, Category.assoc, ← j_over B.C, Category.assoc, q₂,
      reassoc_of% hr₂, spMap_comp, ← Category.assoc (spMap β₂), ← spMap_comp, hbβ, spMap_comp, Category.assoc]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₀ l₂ (Xo l₀) _ _ _ _ Y₂.oF _ _ ν₃ ν₄ hred hover
    (levComp_trans d₀ d₂ hl₂ hl₀ ν₃ hν₃) (levComp_trans d₁ d hl' hl₁ ν₄ hν₄)
  obtain ⟨h, mu, hh, -, -, hj, hφ, hf⟩ := GlobalTheory.Models.Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    B.C (ofModel Y) (ofModel Y₂) b₁ b (IntermediateField.inclusion hc).toRingHom r₁ ν₁ a₁ r' ν' a.π a.mu a.π_over
    hβ₂ hbβ hr₂ (by rw [a.j_comm, e₁, Category.assoc]) (by rw [a.φ_comm, e₂, hν₄, Category.assoc])
  have hφ' : Y₂.m.φ ≫ mu.φ = ν'.φ ≫ Y.m.φ := hφ
  refine ⟨h, pullback.lift h Y₂.s hh, mu, r', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, hf a.fin, hj,
    fun x => ?_, fun x => ?_⟩
  · exact (congrArg (_ ≫ ·) hφ').trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Y.m.φ) (hl'.1 x)).trans (Category.assoc _ _ _)))
  · exact (congrArg (_ ≫ ·) hφ').trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Y.m.φ) (hl'.2 x)).trans (Category.assoc _ _ _)))

end GlobalTheory.RaisedTransition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionEndomorphismGraphOfTorsionAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.GraphVolume

open GlobalTheory.CechPic

private theorem sec_eq_sec_one_pow {X : Scheme.{0}} {A : LB X} (hA : A.IsLB) (s : A.Sec) :
    ∀ k : ℕ, ∃ u : (lbPow A (k + 1)).Sec, Out.nonzeroLocus u = Out.nonzeroLocus s := by
  intro k
  induction k with
  | zero =>
    have hA1 : (lbPow A (0 + 1)).IsLB := LB.isLB_linComb hA _ _
    refine exists_sec_nonzeroLocus_eq_of_lbIso hA1 hA ((cls_eq_iff hA1 hA).1 ?_) s
    rw [cls_lbPow hA _ hA1, zero_add, one_smul]
  | succ k ih =>
    obtain ⟨u, hu⟩ := ih
    have hB : (lbPow A (k + 1)).IsLB := LB.isLB_linComb hA _ _
    have hC : (lbPow A (k + 1 + 1)).IsLB := LB.isLB_linComb hA _ _
    have hD : (LB.div (lbPow A (k + 1 + 1)) (lbPow A (k + 1))).IsLB := LB.isLB_div hC hB
    have hI : LBIso (LB.div (lbPow A (k + 1 + 1)) (lbPow A (k + 1))) A := by
      refine (cls_eq_iff hD hA).1 ?_
      rw [cls_div hC hB hD, cls_lbPow hA _ hC, cls_lbPow hA _ hB, succ_nsmul, add_sub_cancel_left]
    obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hD hA hI s
    obtain ⟨w, hw⟩ := exists_sec_nonzeroLocus_eq_inf_div hB hC t u
    exact ⟨w, by rw [hw, ht, hu, inf_idem]⟩

private theorem mem_nonzeroLocus_pullSec {X : Scheme.{0}} {L : LB X} (f : X ⟶ X) (n : ℕ) (s : (lbPow L n).Sec) (x : X)
    (hx : f.base x ∈ Out.nonzeroLocus s) :
    x ∈ Out.nonzeroLocus (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s f) := by
  obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hx
  have hxj : x ∈ (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n : ℤ))).U j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
  rw [mem_nonzeroLocus_iff_isUnit _ hxj]
  have e : gs (𝟙 X) x _ ((ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s f).f j) = gs (𝟙 X ≫ f) x _ (s.f j) :=
    (gs_res _ x _ hxj _).trans (gs_pull _ f x _ hj _)
  rw [e]
  exact (mem_nonzeroLocus_iff_pull s (𝟙 X ≫ f) x (by simpa using hj)).1 (by simpa using hx)

theorem isAmpleLB_graph {X : Scheme.{0}} {L : LB X} (hL : IsAmpleLB L) (f : X ⟶ X) {N : ℕ} (hN : 1 ≤ N) :
    IsAmpleLB (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) := by
  have hLB : L.IsLB := hL.isLB
  have hM : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]).IsLB := LB.isLB_linComb hLB _ _
  refine { isLB := hM, compactSpace := hL.compactSpace, exists_affine := fun x => ?_ }
  obtain ⟨n1, hn1, s1, hx1, ha1⟩ := hL.exists_affine x
  obtain ⟨n2, hn2, s2, hx2, -⟩ := hL.exists_affine (f.base x)
  have hxt := mem_nonzeroLocus_pullSec f n2 s2 x hx2
  have hT : (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n2 : ℤ))).IsLB := LB.isLB_linComb hLB _ _
  have hA : (lbPow L n1).IsLB := LB.isLB_linComb hLB _ _
  obtain ⟨k1, hk1⟩ : ∃ k, k + 1 = n2 * N := ⟨n2 * N - 1, by have := Nat.mul_pos hn2 hN; omega⟩
  obtain ⟨k2, hk2⟩ : ∃ k, k + 1 = n1 * N := ⟨n1 * N - 1, by have := Nat.mul_pos hn1 hN; omega⟩
  obtain ⟨u1, hu1⟩ := sec_eq_sec_one_pow hA s1 k1
  obtain ⟨u2, hu2⟩ := sec_eq_sec_one_pow hT (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s2 f) k2
  have hA1 : (lbPow (lbPow L n1) (k1 + 1)).IsLB := LB.isLB_linComb hA _ _
  have hT2 : (lbPow (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n2 : ℤ))) (k2 + 1)).IsLB :=
    LB.isLB_linComb hT _ _
  have hB : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) (n1 * n2)).IsLB :=
    LB.isLB_linComb hM _ _
  have hDv := LB.isLB_div hB hA1
  have hI : LBIso (LB.div (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) (n1 * n2))
      (lbPow (lbPow L n1) (k1 + 1)))
      (lbPow (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n2 : ℤ))) (k2 + 1)) := by
    refine (cls_eq_iff hDv hT2).1 ?_
    rw [cls_div hB hA1 hDv, cls_lbPow hM _ hB, cls_lbPow hA _ hA1, cls_lbPow hLB _ hA, cls_lbPow hT _ hT2,
      cls_linComb hLB _ _ hM, cls_linComb hLB _ _ hT, Fin.sum_univ_two, hk1, hk2]
    simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
      Category.comp_id, GlobalTheory.CechPic.pull_id]
    module
  obtain ⟨w, hw⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hDv hT2 hI u2
  obtain ⟨v, hv⟩ := exists_sec_nonzeroLocus_eq_inf_div hA1 hB w u1
  refine ⟨n1 * n2, Nat.mul_pos hn1 hn2, v, ?_, ?_⟩
  · rw [hv, hw, hu2, hu1]
    exact ⟨hxt, hx1⟩
  · rw [hv, hw, hu2, hu1]
    exact isAffineOpen_nonzeroLocus_inf hT _ ha1

theorem exists_sec_ne_zero {X : Scheme.{0}} [Nonempty X] {L : LB X} (hL : L.IsLB) (f : X ⟶ X) (N κ : ℕ)
    (hD : IsAmpleLB (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1])) :
    ∃ n, 1 ≤ n ∧ ∃ s : (LB.div (lbPow (lbPow L (N * (1 + κ))) n)
      (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) n)).Sec, ∃ j, s.f j ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨n, hn, s, hx, -⟩ := hD.exists_affine x
  refine ⟨n, hn, ?_⟩
  suffices H : ∃ v : (LB.div (lbPow (lbPow L (N * (1 + κ))) n)
      (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) n)).Sec, x ∈ Out.nonzeroLocus v by
    obtain ⟨v, hxv⟩ := H
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hxv
    refine ⟨v, k, fun h0 => ?_⟩
    have hb := (mem_nonzeroLocus_iff_basicOpen v hk).1 hxv
    rw [h0, Scheme.basicOpen_zero] at hb
    exact hb
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hLc : (lbPow L (0 * (1 + κ))).IsLB := LB.isLB_linComb hL _ _
    have hLcn : (lbPow (lbPow L (0 * (1 + κ))) n).IsLB := LB.isLB_linComb hLc _ _
    have hM : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)]).IsLB := LB.isLB_linComb hL _ _
    have hMn : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)]) n).IsLB :=
      LB.isLB_linComb hM _ _
    have hQ := LB.isLB_div hLcn hMn
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hQ).1 (by
      rw [cls_div hLcn hMn hQ, cls_lbPow hLc _ hLcn, cls_lbPow hL _ hLc, cls_lbPow hM _ hMn,
        cls_linComb hL _ _ hM, Fin.sum_univ_two]
      simp)
    refine ⟨DVR.genSec t ht, ?_⟩
    rw [nonzeroLocus_genSec hQ t ht]
    trivial
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hDL : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1]).IsLB := hD.isLB
  have hDn : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1]) n).IsLB := LB.isLB_linComb hDL _ _
  obtain ⟨u, hu⟩ := sec_eq_sec_one_pow hDn s m
  have hDnm := LB.isLB_linComb hDn (K := PUnit) (fun _ => 𝟙 X) (fun _ => ((m + 1 : ℕ) : ℤ))
  have hLc : (lbPow L ((m + 1) * (1 + κ))).IsLB := LB.isLB_linComb hL _ _
  have hLcn : (lbPow (lbPow L ((m + 1) * (1 + κ))) n).IsLB := LB.isLB_linComb hLc _ _
  have hM : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ)]).IsLB :=
    LB.isLB_linComb hL _ _
  have hMn : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ)]) n).IsLB :=
    LB.isLB_linComb hM _ _
  have hQ := LB.isLB_div hLcn hMn
  have hI : LBIso (LB.div (lbPow (lbPow L ((m + 1) * (1 + κ))) n)
      (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ)]) n))
      (lbPow (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1]) n) (m + 1)) := by
    refine (cls_eq_iff hQ hDnm).1 ?_
    rw [cls_div hLcn hMn hQ, cls_lbPow hLc _ hLcn, cls_lbPow hL _ hLc, cls_lbPow hM _ hMn,
      cls_lbPow hDn _ hDnm, cls_lbPow hDL _ hDn, cls_linComb hL _ _ hM, cls_linComb hL _ _ hDL,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, GlobalTheory.CechPic.pull_id]
    module
  obtain ⟨v, hv⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hQ hDnm hI u
  exact ⟨v, by rw [hv, hu]; exact hx⟩

theorem symB_graph {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (h : SymB L)
    (f : A ⟶ A) [IsMonHom f] (a b : ℤ) : SymB (LB.LinComb L (K := Fin 2) ![𝟙 A.left, f.left] ![a, b]) := by
  have hM := LB.isLB_linComb hL ![𝟙 A.left, f.left] ![a, b]
  have hMi := pull_isLB hM (GrpObj.inv : A ⟶ A).left
  have hLi := pull_isLB hL (GrpObj.inv : A ⟶ A).left
  have e0 : GlobalTheory.CechPic.pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
    rw [← cls_pull hL _ hLi]
    exact ((cls_eq_iff hL hLi).2 h).symm
  have e1 : (GrpObj.inv : A ⟶ A).left ≫ f.left = f.left ≫ (GrpObj.inv : A ⟶ A).left := by
    rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
  refine (cls_eq_iff hM hMi).1 ?_
  rw [cls_pull hM _ hMi, cls_linComb hL _ _ hM, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, GlobalTheory.CechPic.pull_id, map_add (f := _), map_zsmul]
  rw [e0, ← GlobalTheory.CechPic.pull_comp, e1, GlobalTheory.CechPic.pull_comp, e0]

theorem eq_of_sq_eq {k B a b : ℕ} (hB : B ^ 2 < k) (ha : a ≤ B) (hb : b ≤ B)
    (h : (a : ZMod k) ^ 2 = (b : ZMod k) ^ 2) : a = b := by
  have ha2 : a ^ 2 < k := lt_of_le_of_lt (Nat.pow_le_pow_left ha 2) hB
  have hb2 : b ^ 2 < k := lt_of_le_of_lt (Nat.pow_le_pow_left hb 2) hB
  have h' : ((a ^ 2 : ℕ) : ZMod k) = ((b ^ 2 : ℕ) : ZMod k) := by push_cast; exact h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at h'
  exact Nat.pow_left_injective (by norm_num) h'

end GlobalTheory.GraphVolume

namespace GlobalTheory

open GraphVolume

theorem hilbert_graph_of_torsion : Out.Laws → Out.Laws2 → ∀ (g N κ l j : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (l ^ j))), 1 ≤ N → l.Prime → (N * (1 + κ)) ^ (2 * g) < l ^ j → ∃ δ ≤ (N * (1 + κ)) ^ g, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f : P.A ⟶ P.A), P.g = g → (l : K) ≠ 0 → IsPrimitiveRoot ζ (l ^ j) → TorsBasis P.A (l ^ j) pt → (∀ i i', Out.WeilIs P.A P.L ((l ^ j : ℕ) : ℤ) (pt i) (pt i') (unitOn (ζ ^ Out.stdSymp g i i'))) → IsMonHom f → ActsBy pt f Mat → Out.RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) → SymB (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) e) (δ * e ^ g) := by
  intro hL1 hL2 g N κ l j Mat hN hl hB
  obtain ⟨S, hS⟩ := GlobalTheory.T.weil_pairing_torsion_basis_symplectic hL1 hL2 g N (l ^ j) Mat
  classical
  have hBk : ((N * (1 + κ)) ^ g) ^ 2 < l ^ j := by rw [← pow_mul, mul_comm g 2]; exact hB
  refine ⟨if h : ∃ d ≤ (N * (1 + κ)) ^ g, (d : ZMod (l ^ j)) ^ 2 = S.det then Classical.choose h else 0, ?_, ?_⟩
  · split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact Nat.zero_le _
  intro K _ _ P pt ζ f hg hl0 hζ hT hW hf hAct hD
  subst hg
  have := hf
  have hprop : IsProper P.A.hom := P.isAb.proper
  have hPL : P.L.IsLB := P.isLB
  set M := LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)] with hMdef
  have hM : M.IsLB := LB.isLB_linComb hPL _ _
  have hSym : SymB M := symB_graph hPL (_root_.GlobalTheory.principal_polarisation_numerics hL1 hL2 K P).2.2.1 f _ _
  have hAmpL : IsAmpleLB P.L := (relAmple_iff_isAmpleLB_of_isAffine P.A hPL).1 P.ample
  have hAmpM : IsAmpleLB M := isAmpleLB_graph hAmpL f.left hN
  have hRelM : Out.RelAmple P.A M := (relAmple_iff_isAmpleLB_of_isAffine P.A hM).2 hAmpM
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.BundleForm.exists_formIs hL1 hL2 K P M hM
  have hk : ((l ^ j : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hl0
  have hSs : ActsBy pt s S := hS K P pt ζ f s hk hζ hT hW hf hAct hs
  obtain ⟨δ, hVol, hH0, hdet⟩ := _root_.GlobalTheory.SectionCount.sq_vol_eq_det hL1 hL2 K P M s l hl hl0 hM hRelM hSym hs
  have hδ2 : (δ : ZMod (l ^ j)) ^ 2 = S.det := hdet j pt S hT hSs

  have hc : 1 ≤ N * (1 + κ) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hDa : IsAmpleLB (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) :=
    (relAmple_iff_isAmpleLB_of_isAffine P.A (LB.isLB_linComb hPL _ _)).1 hD
  have hne : Nonempty (𝟙_ (Over (Sp K))).left := by
    change Nonempty (Sp K)
    infer_instance
  have : Nonempty P.A.left := ⟨(η[P.A] : 𝟙_ (Over (Sp K)) ⟶ P.A).left.base (Classical.choice hne)⟩
  obtain ⟨n, hn, t, ht⟩ := exists_sec_ne_zero hPL f.left N κ hDa
  have hLc : (lbPow P.L (N * (1 + κ))).IsLB := LB.isLB_linComb hPL _ _
  have hLcn : (lbPow (lbPow P.L (N * (1 + κ))) n).IsLB := LB.isLB_linComb hLc _ _
  have hMn : (lbPow M n).IsLB := LB.isLB_linComb hM _ _
  have V1 : Vol P.A.hom P.L P.g 1 := (_root_.GlobalTheory.principal_polarisation_numerics hL1 hL2 K P).1
  have V2 : Vol P.A.hom (lbPow P.L (N * (1 + κ))) P.g (((N * (1 + κ) : ℕ) : ℝ) ^ P.g * 1) :=
    (_root_.GlobalTheory.VolBasic.vol_basic K P P.L P.g hPL).2.2.2.1 _ 1 hc V1
  have V3 : Vol P.A.hom (lbPow (lbPow P.L (N * (1 + κ))) n) P.g
      ((n : ℝ) ^ P.g * (((N * (1 + κ) : ℕ) : ℝ) ^ P.g * 1)) :=
    (_root_.GlobalTheory.VolBasic.vol_basic K P _ P.g hLc).2.2.2.1 n _ hn V2
  have V4 : Vol P.A.hom (lbPow M n) P.g ((n : ℝ) ^ P.g * (δ : ℝ)) :=
    (_root_.GlobalTheory.VolBasic.vol_basic K P M P.g hM).2.2.2.1 n _ hn hVol
  have hle := ((_root_.GlobalTheory.VolBasic.vol_basic K P (lbPow M n) P.g hMn).2.2.2.2.2 _ t hLcn ht).2 _ _ V4 V3
  have hnpos : (0 : ℝ) < (n : ℝ) ^ P.g := pow_pos (by exact_mod_cast hn) _
  have hδB : δ ≤ (N * (1 + κ)) ^ P.g := by
    have h1 : (δ : ℝ) ≤ ((N * (1 + κ) : ℕ) : ℝ) ^ P.g := by
      have := le_of_mul_le_mul_left (by simpa using hle) hnpos
      simpa using this
    exact_mod_cast h1
  have hex : ∃ d ≤ (N * (1 + κ)) ^ P.g, (d : ZMod (l ^ j)) ^ 2 = S.det := ⟨δ, hδB, hδ2⟩
  rw [dite_eq_left hex]
  have hsp := Classical.choose_spec hex
  have hEq : δ = Classical.choose hex := eq_of_sq_eq hBk hδB hsp.1 (hδ2.trans hsp.2.symm)
  rw [← hEq]
  exact ⟨hSym, hH0⟩

end GlobalTheory
end

