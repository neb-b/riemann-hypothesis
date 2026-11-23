module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCocycleTangentContractionCohomologousTorsor
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardTwoNsmulPullbackEqZeroOnTripleParamete
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pull_two_nsmul_eq_zero_of_triples : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → A.hom ⁻¹ᵁ U ≤ W → W ≤ A.hom ⁻¹ᵁ U ⊔ V → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), p ≫ V.ι = v.left → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) → GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) → e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ → GlobalTheory.CechPic.pull (x.left ∣_ W) (2 • c) = 0 := by
  intro S _ _ hS A _ hA U V W hV hU hsurj hUW hWUV c hc Y x a v p e hpv hmem hsm hgi he
  have := hA.smooth
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : GlobalTheory.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff S).mpr hS
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨s0, hs0⟩ := hU
  obtain ⟨a0, ha0V, ha0⟩ := hsurj s0
  have : Nonempty V := ⟨⟨a0, ha0V⟩⟩
  have : IsIntegral V.toScheme := inferInstance
  have hVn : GlobalTheory.IsNormalScheme V.toScheme := GlobalTheory.isNormalScheme_of_smooth (V.ι ≫ A.hom)
  let i0 := (x.left ⁻¹ᵁ W).ι
  let O : (x.left ⁻¹ᵁ W).toScheme.Opens := i0 ⁻¹ᵁ (x.left ⁻¹ᵁ V)
  have hrange : Set.range (x.left ⁻¹ᵁ V).ι = Set.range (O.ι ≫ i0) := by
    have hO : (O : Set _) = i0 ⁻¹' (x.left ⁻¹ᵁ V : Set Y.left) := rfl
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, hO, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    ext z
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Scheme.Hom.mem_preimage]
    exact ⟨fun h => ⟨h, hV h⟩, fun h => h.1⟩
  let φ := IsOpenImmersion.isoOfRangeEq (x.left ⁻¹ᵁ V).ι (O.ι ≫ i0) hrange
  have hφ : φ.hom ≫ O.ι ≫ i0 = (x.left ⁻¹ᵁ V).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let UT : V.toScheme.Opens := (V.ι ≫ A.hom) ⁻¹ᵁ U
  have hUT : (UT : Set V.toScheme).Nonempty := ⟨⟨a0, ha0V⟩, by
    show A.hom (V.ι ⟨a0, ha0V⟩) ∈ U
    simpa [ha0] using hs0⟩
  let p' := i0 ≫ p
  have hOp : O.ι ≫ p' = φ.inv ≫ (x.left ⁻¹ᵁ V).ι ≫ p := by
    rw [← hφ]; simp [p']
  have hsm' : Smooth (O.ι ≫ p') := by rw [hOp]; infer_instance
  have hgi' : GeometricallyIntegral (O.ι ≫ p') := by
    have : MorphismProperty.RespectsIso @GeometricallyIntegral :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [hOp]; exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral φ.inv _).mpr hgi
  have he' : (e ≫ φ.hom) ≫ O.ι ≫ p' = 𝟙 _ := by
    simp only [p', Category.assoc]; rw [reassoc_of% hφ]; exact he
  have hpY : p' ≫ V.ι ≫ A.hom = i0 ≫ Y.hom := by
    simp only [p', Category.assoc]; rw [reassoc_of% hpv, Over.w v]
  have hcover : O ⊔ p' ⁻¹ᵁ UT = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : x.left (i0 z) ∈ W := z.2
    have h' : x.left (i0 z) ∈ ((A.hom ⁻¹ᵁ U ⊔ V : A.left.Opens) : Set A.left) := hWUV hz
    rw [TopologicalSpace.Opens.coe_sup] at h'
    rcases h' with h | h
    · right
      show (V.ι ≫ A.hom) (p' z) ∈ U
      rw [← Scheme.Hom.comp_apply, hpY, ← Over.w x, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact h
    · left
      exact h
  have key : ∀ c' : Pic (x.left ⁻¹ᵁ W).toScheme, pull O.ι c' = 0 → pull (p' ⁻¹ᵁ UT).ι c' = 0 →
      c' = 0 := fun c' h1 h2 =>
    _root_.GlobalTheory.PicGlue.eq_zero_of_pull_eq_zero V.toScheme (x.left ⁻¹ᵁ W).toScheme ((GlobalTheory.isNormalScheme_iff _).mp hVn) UT hUT p'
      O (e ≫ φ.hom) hsm' hgi' he' hcover c' h1 h2
  apply key
  · rw [← pull_comp]
    have hfac : O.ι ≫ (x.left ∣_ W) = φ.inv ≫ (x.left ∣_ V) ≫ A.left.homOfLE hV := by
      rw [← cancel_mono W.ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
      rw [← reassoc_of% hφ]
      simp [i0]
    rw [hfac, pull_comp, pull_comp, map_nsmul, hc, smul_zero, map_zero, map_zero]
  · rw [← pull_comp]
    let j := (p' ⁻¹ᵁ UT).ι
    let Y' : Over S := Over.mk (j ≫ i0 ≫ Y.hom)
    let q : Y' ⟶ Y := Over.homMk (j ≫ i0) (by simp [Y'])
    refine _root_.GlobalTheory.twice_cls_eq_zero_of_translates_mem S A hA U V W hV hUW c hc Y' (q ≫ x) (q ≫ a) (q ≫ v) ?_ ?_ ?_
      (j ≫ (x.left ∣_ W)) ?_
    · intro y
      show (j ≫ i0 ≫ Y.hom) y ∈ U
      rw [← hpY]
      exact y.2
    · intro y
      have : (q ≫ v).left = (j ≫ i0 ≫ p) ≫ V.ι := by simp [q, hpv]
      rw [this, Scheme.Hom.comp_apply]
      exact ((j ≫ i0 ≫ p) y).2
    · intro y
      simp only [← GrpObj.comp_inv, ← MonObj.comp_mul, Over.comp_left, Scheme.Hom.comp_apply]
      exact hmem _
    · simp [q, j, i0, morphismRestrict_ι]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupSubsingletonOfBoundedRamification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorsRam

theorem classes_fixed {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W)
    {D : DegData W (maximalIdeal W)} {Q : PolAV (Sp (FractionRing W))} {H : Over (Sp W)} [GrpObj H] [IsCommMonObj H]
    (hH : IsSemiAbelian H) (U : Unif (maximalIdeal W) D Q H) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing W) F] {k : ℕ} (hk : 1 ≤ k) (σ : F ≃+* F)
    (hσ : σ.toRingHom.comp (algebraMap (FractionRing W) F) = algebraMap (FractionRing W) F)
    (hfixH : ∀ x : TF (R := W) F ⟶ H, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left)
    (p q : QkPt D.toPre F k) (hpq : QkExt σ.toRingHom p q) : QkPt.Equiv D.toPre F p q := by
  haveI : CharZero W := hW.2.2
  have hA := GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hW
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨f, hf, hiff⟩ := GlobalTheory.Mum.Recog.exists_goodLab hA hH U F
  have hx₀ : f k p ^ k = 1 := hf.pow k hk p
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback Q.A H (jK W) (U.gen.inv.left ≫ pullback.fst H.hom (jK W)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback H (jK W))).congr (Category.id_comp _) rfl
  have w₁ : ((f k p).left ≫ U.gen.inv.left ≫ pullback.fst H.hom (jK W)) ≫ H.hom = jFK (R := W) F ≫ jK W := by
    rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w (f k p)]; rfl
  let xG : TF (R := W) F ⟶ H := Over.homMk ((f k p).left ≫ U.gen.inv.left ≫ pullback.fst H.hom (jK W)) w₁
  have hxG : xG ^ k = 1 := (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull rfl gp (x := xG) (x' := f k p) rfl).1 hx₀
  have fixG := hfixH xG hxG
  let σ' : F →ₐ[FractionRing W] F := ⟨σ.toRingHom, RingHom.congr_fun hσ⟩
  have s₂ : spMap σ.toRingHom ≫ jFK (R := W) F = jFK (R := W) F := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]
  have fix₀ : spMap σ.toRingHom ≫ (f k p).left = (f k p).left := by
    refine gp.1.hom_ext ?_ ?_
    · rw [Category.assoc]; exact fixG
    · rw [Category.assoc, Over.w (f k p)]; exact s₂
  let x' : TFK (R := W) F ⟶ Q.A := Over.homMk (spMap σ.toRingHom ≫ (f k p).left) (by
    rw [Category.assoc, Over.w (f k p)]; exact s₂)
  have hq : QkToAkU U.toUnifPre F k q x' :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hL W (maximalIdeal W) hA D Q H hH U F F σ' k hk p q (f k p) x' hpq rfl).1
      ((hiff k hk p (f k p)).2 rfl)
  have e : x' = f k p := Over.OverMorphism.ext fix₀
  exact (hf.eqv k hk p q).1 (e.symm.trans ((hiff k hk q x').1 hq))

end GlobalTheory.TorsRam

namespace GlobalTheory.TorsRam

open GlobalTheory.BXOf in
theorem psiLoc_not_unit {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (D : DegData W (maximalIdeal W))
    (J₀ : D.toPre.P.A.left → D.toPre.P.L.ι) (h₀ : ∀ x, x ∈ D.toPre.P.L.U (J₀ x)) (χ : D.toPre.X) (hχ : χ ≠ 0) (u : Wˣ)
    (hu : (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W))) : FractionRing W) =
      algebraMap W _ u) : False := by
  obtain ⟨e, -, a, ha, hψ⟩ := GlobalTheory.LevelOneIdeal.exists_psi_val D.toPre χ (D.psi_pos χ hχ)
  have := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := GlobalTheory.UnramTorsion.exists_good_ext D.toPre.P.isLB (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W)) J₀ h₀
  have h1 := hψ (TK W).left (𝟙 _) (closedPoint (FractionRing W)) J hJ
  have hj : J (𝟙 _ ≫ D.toPre.xK χ) = J₀ ((D.toPre.c χ).left (closedPoint W)) := by
    rw [Category.id_comp]
    exact eJ (D.toPre.c χ).left
  have e0 := val_of (D.toPre.psi χ) (𝟙 _) (closedPoint (FractionRing W)) J _ (fun _ => hj)
  have e1 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (val (D.toPre.psi χ) (𝟙 _) (closedPoint (FractionRing W)) J).val = algebraMap W _ u := by
    rw [e0]; exact hu
  obtain ⟨u', hu'⟩ := GlobalTheory.UnramTorsion.val_integral (algebraMap W (FractionRing W)) h₀ eJ e (𝟙 _)
  have e2 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (cst (𝟙 (TK W).left ≫ jK W) (closedPoint (FractionRing W)) a) = algebraMap W _ a := by
    rw [Category.id_comp]; exact GlobalTheory.UnramTorsion.stalk_gs_top _ a
  have e3 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (val e (𝟙 (TK W).left ≫ jK W) (closedPoint (FractionRing W)) J).val = algebraMap W _ u' := by
    rw [Category.id_comp]; exact hu'
  have e4 := congrArg (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom h1
  rw [map_mul, e1, e2, e3, ← map_mul] at e4
  have e5 := IsFractionRing.injective W (FractionRing W) e4
  exact (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_mul_isUnit_left (e5 ▸ u.isUnit))

end GlobalTheory.TorsRam

namespace GlobalTheory.TorsRam

theorem zpow_of_mul_eq {F : Type} [Field F] {a b c : F} {e : ℕ} (hb : b ≠ 0) (h : a * b = c ^ e) (m : ℤ) :
    a ^ m = c ^ ((e : ℤ) * m) * b ^ (-m) := by
  rw [show a = c ^ e * b⁻¹ by rw [← h, mul_inv_cancel_right₀ hb], mul_zpow, zpow_mul, zpow_natCast, inv_zpow']

theorem coe_units_zpow {F : Type} [Field F] (T : Subring F) (w : Tˣ) (z : ℤ) :
    (((w ^ z : Tˣ) : T) : F) = ((w : T) : F) ^ z :=
  (congrArg Units.val (map_zpow (Units.map T.subtype.toMonoidHom) w z)).trans (Units.val_zpow_eq_zpow_val _ _)

theorem subsingleton_of_bounded_ramification : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ U : Unif (maximalIdeal W) D Q H, GlobalTheory.LN.ToATotal U.toUnifPre → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] (n N : ℕ), 2 ≤ n → (∀ j : ℕ, ∃ (T : Subring F) (_ : IsDiscreteValuationRing T) (g : W →+* T) (e : ℕ), (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ (∀ π, Irreducible π → ∃ ϖ : T, Irreducible ϖ ∧ Associated (g π) (ϖ ^ e)) ∧ ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) → ∀ x : TF (R := W) F ⟶ H, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → Subsingleton D.toPre.X := by
  intro W _ _ _ hW D Q H _ _ hH U _ F _ _ _ n N hn Hj
  haveI : IsDiscreteValuationRing W := hW.1
  haveI : CharZero W := hW.2.2
  haveI : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing W) F).injective
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  choose J₀ h₀ using fun x : D.toPre.P.A.left => exists_chart D.toPre.P.isLB x
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  choose m u hu using fun χ => IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := FractionRing W) hπ
    (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W)))).ne_zero
  have key : ∀ j : ℕ, ∃ e : ℕ, 1 ≤ e ∧ e ≤ N ∧ (∀ y χ, ((n ^ j : ℕ) : ℤ) ∣ (e : ℤ) * m (y + χ) - (e : ℤ) * m y - (e : ℤ) * m χ) ∧
      ∀ χ, (e : ℤ) * m (-χ) = (e : ℤ) * m χ := fun j => by
    obtain ⟨T, hT, g, e, hg, he1, heN, hram, hfix⟩ := Hj j
    obtain ⟨ϖ, hϖ, v, hv⟩ := hram π hπ
    have hP : ∀ r, r ∈ (closedPoint W).asIdeal ↔ ¬ IsUnit (g r) := fun r => by
      show r ∈ maximalIdeal W ↔ _
      refine ⟨fun hr hgr => ?_, fun h => (mem_maximalIdeal r).2 fun hr => h (hr.map g)⟩
      · rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
        obtain ⟨s, rfl⟩ := hr
        rw [map_mul] at hgr
        have h1 : IsUnit (ϖ ^ e) := hv ▸ (isUnit_of_mul_isUnit_left hgr).mul v.isUnit
        exact hϖ.not_isUnit (isUnit_pow_iff (by omega) |>.1 h1)
    have hv' : (g π : F) * ((v : T) : F) = (ϖ : F) ^ e := by
      have := congrArg (fun t : T => (t : F)) hv
      simpa only [Subring.coe_mul, Subring.coe_pow] using this
    have hvne : ((v : T) : F) ≠ 0 := fun h => v.ne_zero (Subtype.ext h)
    have hm : ∀ χ, ∃ u' : Tˣ, algebraMap (FractionRing W) F
        (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W))) : FractionRing W) =
        ((u' : T) : F) * (ϖ : F) ^ ((fun χ => (e : ℤ) * m χ) χ) := fun χ =>
      ⟨Units.map g.toMonoidHom (u χ) * v ^ (-(m χ)), by
        rw [hu χ, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, ← hg, ← hg, Units.val_mul, Subring.coe_mul,
          coe_units_zpow, zpow_of_mul_eq hvne hv' (m χ)]
        rw [show (((Units.map g.toMonoidHom (u χ) : Tˣ) : T) : F) = (g (u χ) : F) from rfl]
        ring⟩
    have hσ : ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) →
        σ.toRingHom.comp (algebraMap (FractionRing W) F) = algebraMap (FractionRing W) F := fun σ hσ =>
      IsLocalization.ringHom_ext (nonZeroDivisors W) (RingHom.ext fun r => by
        show σ (algebraMap (FractionRing W) F (algebraMap W _ r)) = algebraMap (FractionRing W) F (algebraMap W _ r)
        rw [← hg]; exact hσ _ (g r).2)
    obtain ⟨h1, h2⟩ := GlobalTheory.UnramTorsion.level_step hL.1.mulN D.tau_bimult D.psi_even (closedPoint W) J₀ h₀ (n ^ j)
      (pow_ne_zero _ (by omega)) T g hg hP ϖ hϖ (fun χ => (e : ℤ) * m χ) hm
      (fun σ hσ' p q hpq => classes_fixed hW hH U F (Nat.one_le_pow _ _ (by omega)) σ (hσ σ hσ')
        (fun x hx => hfix σ hσ' x hx) p q hpq)
    exact ⟨e, he1, heN, h1, h2⟩
  have add : ∀ y χ, m (y + χ) = m y + m χ := fun y χ => by
    obtain ⟨e, he1, heN, hdiv, -⟩ := key (N * (m (y + χ) - m y - m χ).natAbs)
    have h1 := hdiv y χ
    rw [show (e : ℤ) * m (y + χ) - (e : ℤ) * m y - (e : ℤ) * m χ = (e : ℤ) * (m (y + χ) - m y - m χ) by ring] at h1
    by_contra hne
    have hd : m (y + χ) - m y - m χ ≠ 0 := fun h => hne (by omega)
    have h2 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h1 (by
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ heN) (Nat.lt_pow_self (by omega)))
    exact (mul_ne_zero (by exact_mod_cast (show e ≠ 0 by omega)) hd) h2
  have even : ∀ χ, m (-χ) = m χ := fun χ => by
    obtain ⟨e, he1, -, -, h⟩ := key 0
    exact Int.eq_of_mul_eq_mul_left (by exact_mod_cast (show e ≠ 0 by omega)) (h χ)
  have m0 : ∀ y, m y = 0 := fun y => by
    have a := add 0 0
    have b := add y (-y)
    rw [add_zero] at a
    rw [add_neg_cancel, even] at b
    omega
  have z : ∀ y : D.toPre.X, y = 0 := fun y => by
    by_contra hy
    refine psiLoc_not_unit D J₀ h₀ y hy (u y) ?_
    rw [hu y, m0, zpow_zero, Units.smul_def, Algebra.smul_def, _root_.mul_one]
  exact ⟨fun a b => (z a).trans (z b).symm⟩

end GlobalTheory.TorsRam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumMult

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def ChartExpOn (U : UnifPre I D A G) (e k : ℕ) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens)
    (g : Γ((thickObj R I e G).left, W)) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) : Prop :=
  ∃ S : Finset D.toPre.X,
    (∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) ∧
    ∀ (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
      (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
      i' 0 = p.2 PUnit.unit →
      CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) →
      (res ((inf_le_left.trans inf_le_left).trans inf_le_left :
          U.expW e p i' S jf jt ⊓ W ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
            (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ k *
        ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_right :
          U.expW e p i' S jf jt ⊓ W ≤ W)).op).hom g =
      ∑ α ∈ S.attach,
        ((thickObj R I e G).left.presheaf.map
            (homOfLE (inf_le_left.trans (U.expW_le_f e p i' jf jt α.2))).op).hom
            (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
          (res (inf_le_left.trans (U.expWeight_le_chart_weight e p i' jf jt α.2)) (((U.gt e).t α.1).s (jt α.1))).val

end GlobalTheory.MumMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartOverlapEqPreimageOpenOfFibreStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Div.DescendOpens

theorem overlap_preimage_open : ∀ (B S X : Scheme.{0}) (π : S ⟶ B) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), IsProper π → Surjective π → (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ i j : J, ∃ V : U.left.Opens, ∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j) := by
  intro B S X π U J e hP _ hO key i j
  haveI := hP
  haveI : UniversallyClosed (pullback.fst U.hom π) := inferInstance
  set p := pullback.fst U.hom π with hp
  let W : Set ↥(pullback U.hom π) := (e i) ⁻¹' Set.range (e j)
  have hWo : IsOpen W := by
    haveI := hO j
    exact (e i).continuous.isOpen_preimage _ (e j).isOpenEmbedding.isOpen_range
  have sat : ∀ a c : ↥(pullback U.hom π), p a = p c → a ∈ W → c ∈ W := by
    intro a c hac ha
    obtain ⟨b, hb⟩ := ha
    obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := p) a c hac
    have h1 : (pullback.fst p p ≫ e i) t = e j b := by
      simp only [Scheme.Hom.comp_apply, ht1]; exact hb.symm
    obtain ⟨t', ht'1, ht'2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := pullback.fst p p ≫ e i) (g := e j) t b h1
    obtain ⟨h₂, hh₂, -⟩ := key i j _
      (pullback.fst (pullback.fst p p ≫ e i) (e j) ≫ pullback.fst p p)
      (pullback.fst (pullback.fst p p ≫ e i) (e j) ≫ pullback.snd p p)
      (pullback.snd (pullback.fst p p ≫ e i) (e j))
      (by simp only [Category.assoc]; rw [pullback.condition])
      (by rw [← pullback.condition, Category.assoc])
    refine ⟨h₂ t', ?_⟩
    have := congrArg (fun f => f t') hh₂
    simp only [Scheme.Hom.comp_apply, ht'1, ht2] at this
    exact this
  refine ⟨⟨(p '' Wᶜ)ᶜ, ?_⟩, ?_⟩
  · exact (p.isClosedMap _ hWo.isClosed_compl).isOpen_compl
  · intro a
    change p a ∈ (p '' Wᶜ)ᶜ ↔ a ∈ W
    constructor
    · intro h
      by_contra ha
      exact h ⟨a, ha, rfl⟩
    · rintro ha ⟨c, hc, hca⟩
      exact hc (sat a c hca.symm ha)

end GlobalTheory.Div.DescendOpens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

def chartVal {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) (j : L.ι) (W : X.Opens)
    (hW : W ≤ L.U j) : Γ(Y, α ⁻¹ᵁ W) :=
  (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op).hom (s.f (fun _ => j))

def IntAt {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) (x : X) : Prop :=
  ∃ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), x ∈ W ∧ IsAffineOpen W ∧
    (α.app W).hom.IsIntegralElem (chartVal L α s j W hW)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassContractionTangentEqTorsorCocycle
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem contr_chern_eq_tanCoc : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) → (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) → ∀ κ : Fn1 A, IsContr w.1 v κ → ∃ u : Fn1 (A ⊗ B), IsCoc P.U u ∧ Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull u v)) := by
  intro R _ A B _ _ P hP v hv j hj w hch hw κ hκ
  obtain ⟨i, hi, U, ℓ, hU, hℓ, hcl⟩ := hch
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hcl
  obtain ⟨n, hn⟩ := hcl
  refine ⟨cocOf P.U n, ?_, ?_⟩
  · apply GlobalTheory.PtExt.isCoc_cocOf
    intro T T' T'' a b h h' h''
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hn T) T') T'') a) b
    rw [e]
    have h0 : ℓ.1 T T' T'' a b = 0 := by
      have hm := (hℓ T T' T'' a b).1
      rw [h''] at hm
      exact Ideal.mem_bot.mp hm
    change w.1 _ _ _ _ _ - ℓ.1 T T' T'' a b = 0
    rw [h0, sub_zero]
    exact hw _ _ _ _ _ h h' h''
  · exact _root_.GlobalTheory.PtExt.ChernContr.contr_cohom
      R A B P hP v hv j hj w hw i hi U ℓ hU hℓ n hn κ hκ

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeProjOverModL
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option autoImplicit false

namespace GlobalTheory.FibreProj

theorem isProjOver_closed_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (q : X ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) (X := Z)) := by
  intro k _ X q D hX Z i _ l _ _
  haveI : Module.Finite ℤ k := hX.finite
  exact GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver l i

end GlobalTheory.FibreProj
end

