module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTauLineBundleCoordinateEqExp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.TauNorm

theorem valF_id {F : Type} [Field F] (U : (Sp F).Opens) (h : ⊤ ≤ U) (f : Γ(Sp F, U)) :
    valF (𝟙 (Sp F)) U f =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
        (((Sp F).presheaf.map (homOfLE h).op).hom f) := by
  have h' : ⊤ ≤ (𝟙 (Sp F) : Sp F ⟶ Sp F) ⁻¹ᵁ U := h
  unfold valF
  rw [dite_eq_left h']
  congr 1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}

theorem norm_psiCoord (u : ρ.UTest p y₀) (l : u.Lab) (χ : u.D.toPre.X)
    (x : (FractionRing u.V)ˣ) (hx : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord u.D.toPre χ x) :
    ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (x : FractionRing u.V)‖ =
      Real.exp (-l.q χ) := by
  obtain ⟨j, h, hj, rfl⟩ := hx
  have := l.q_eq χ j hj
  rw [valF_id _ h] at this
  exact this

theorem norm_unit (u : ρ.UTest p y₀) (w : (u.V)ˣ) :
    ‖algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (w : u.V))‖ = 1 := by
  have h1 := (u.norm_le (algebraMap u.V (FractionRing u.V) (w : u.V))).2 ⟨_, rfl⟩
  have h2 := (u.norm_le (algebraMap u.V (FractionRing u.V) ((w⁻¹ : (u.V)ˣ) : u.V))).2 ⟨_, rfl⟩
  have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (w : u.V))‖ *
      ‖algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) ((w⁻¹ : (u.V)ˣ) : u.V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a b : u.D.toPre.X) (x : (FractionRing u.V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord u.D.toPre a b x → ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (x : FractionRing u.V)‖ = Real.exp (-(l.q (a + b) - l.q a - l.q b)) := by
  intro o Ω _ _ _ S ρ p _ y₀ u l a b x hx
  obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord u.D.toPre (a + b)
  obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord u.D.toPre a
  obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord u.D.toPre b
  obtain ⟨w, hw⟩ := GlobalTheory.TauCoordQuot.main u.V u.D.toPre a b x x₁ x₂ x₃ hx h₁ h₂ h₃
  rw [hw, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, norm_mul, norm_mul, norm_mul,
    norm_inv, norm_inv, norm_unit, norm_psiCoord u l _ _ h₁, norm_psiCoord u l _ _ h₂,
    norm_psiCoord u l _ _ h₃, _root_.one_mul, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

end GlobalTheory.Poinc.TauNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeExtensionThroughFiniteCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NormalFiniteLift

theorem finite_lift_of_integral (R K : CommRingCat.{0}) (φ : R ⟶ K) (hinj : Function.Injective φ.hom)
    (H : ∀ x : K, φ.hom.IsIntegralElem x → ∃ r : R, φ.hom r = x)
    (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Spec R ⟶ P) (y : Spec K ⟶ Z)
    (hp : IsFinite p) (hy : y ≫ p = Spec.map φ ≫ ξ₀) :
    ∃ ξ : Spec R ⟶ Z, Spec.map φ ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first
  | exact @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite
  | exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite
  | (apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite ..)

theorem isDominant_of_generic {T S : Scheme.{0}} [IsIntegral S] (r : T ⟶ S) [IsOpenImmersion r]
    (K : CommRingCat.{0}) [IsLocalRing K] (w : Spec K ⟶ T)
    (hw : r (w (IsLocalRing.closedPoint K)) = genericPoint S) : IsDominant w := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_inter_open]
  rintro O hO ⟨t, ht⟩
  obtain ⟨t', ht', e⟩ : genericPoint S ∈ r '' O :=
    ((genericPoint_spec S).mem_open_set_iff (r.isOpenEmbedding.isOpenMap O hO)).2 ⟨r t, Set.mem_univ _, t, ht, rfl⟩
  refine ⟨w (IsLocalRing.closedPoint K), ?_, ⟨_, rfl⟩⟩
  rw [← r.isOpenEmbedding.injective (e.trans hw.symm)]
  exact ht'

end GlobalTheory.NormalFiniteLift

namespace GlobalTheory.NormalFiniteLift

theorem exists_lift_of_finite : ∀ (o : Type) [CommRing o] (N : ℕ) (S' X Z : Scheme.{0}) (U : S'.Opens)
    (c : U.toScheme ⟶ X) (i : X ⟶ Z) (p : Z ⟶ PSpace o N) (h : S' ⟶ PSpace o N), IsIntegral S' →
    Geo.Tor.IsNormalScheme S' → IsIntegral Z → Dense (U : Set S') → IsDominant c → IsFinite p →
    IsOpenImmersion i → Dense (Set.range i) → U.ι ≫ h = c ≫ i ≫ p →
    ∃ π : S' ⟶ Z, U.ι ≫ π = c ≫ i ∧ π ≫ p = h := by
  intro o _ N S' X Z U c i p h _ hN _ hU _ hp _ _ e
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have hη : ∀ V : S'.Opens, (V : Set S').Nonempty → genericPoint S' ∈ V := fun V hV =>
    ((genericPoint_spec S').mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hηU : genericPoint S' ∈ U := hη U hU.nonempty
  let gS : Spec S'.functionField ⟶ S' := S'.fromSpecStalk (genericPoint S')
  have hgS : gS (IsLocalRing.closedPoint S'.functionField) = genericPoint S' := Scheme.fromSpecStalk_closedPoint
  have hrO : ∀ O : S'.Opens, genericPoint S' ∈ O → Set.range gS ⊆ Set.range O.ι := by
    rintro O hO _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : gS q ⤳ genericPoint S' := (S'.range_fromSpecStalk (x := genericPoint S')).le ⟨q, rfl⟩
    exact this.mem_open O.isOpen hO
  let gO : ∀ O : S'.Opens, genericPoint S' ∈ O → (Spec S'.functionField ⟶ O.toScheme) := fun O hO =>
    IsOpenImmersion.lift O.ι gS (hrO O hO)
  have hgO : ∀ O hO, gO O hO ≫ O.ι = gS := fun O hO => IsOpenImmersion.lift_fac _ _ _
  let y : Spec S'.functionField ⟶ Z := gO U hηU ≫ c ≫ i
  have hy : y ≫ p = gS ≫ h := by
    simp only [y, Category.assoc, ← e]
    rw [← Category.assoc, hgO U hηU]

  have loc : ∀ (V : S'.Opens) (hV : IsAffineOpen V) (hηV : genericPoint S' ∈ V),
      ∃ m : V.toScheme ⟶ Z, m ≫ p = V.ι ≫ h ∧ gO V hηV ≫ m = y := by
    intro V hV hηV
    have : Nonempty V := ⟨⟨_, hηV⟩⟩
    have : IsIntegrallyClosed Γ(S', V) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hV
    have : IsFractionRing Γ(S', V) S'.functionField := functionField_isFractionRing_of_isAffineOpen S' V hV
    have hsp : Spec.map (S'.germToFunctionField V) ≫ hV.fromSpec = gS :=
      hV.fromSpecStalk_eq_fromSpecStalk hηV
    obtain ⟨ξ, h1, h2⟩ := finite_lift_of_integral Γ(S', V) S'.functionField (S'.germToFunctionField V)
      (S'.germToFunctionField_injective V) (fun x hx => IsIntegrallyClosed.isIntegral_iff.1 hx) Z _ p
      (hV.fromSpec ≫ h) y hp (by rw [hy, ← Category.assoc, hsp])
    have hg : gO V hηV ≫ hV.isoSpec.hom = Spec.map (S'.germToFunctionField V) := by
      rw [← cancel_mono hV.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, hgO V hηV, hsp]
    refine ⟨hV.isoSpec.hom ≫ ξ, ?_, ?_⟩
    · rw [Category.assoc, h2, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
    · rw [← Category.assoc, hg, h1]

  choose V hVa hxV _ using fun x : S' => exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := x) (by simp)
  have hcov : TopologicalSpace.IsOpenCover V := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  have hηV : ∀ x, genericPoint S' ∈ V x := fun x => hη (V x) ⟨x, hxV x⟩
  choose m hm hmy using fun x => loc (V x) (hVa x) (hηV x)
  let 𝒰 := S'.openCoverOfIsOpenCover V hcov
  have hc : ∀ a b, pullback.fst (V a).ι (V b).ι ≫ m a = pullback.snd (V a).ι (V b).ι ≫ m b := by
    intro a b
    let r := pullback.fst (V a).ι (V b).ι ≫ (V a).ι
    have : IsReduced (pullback (V a).ι (V b).ι) := isReduced_of_isOpenImmersion r
    let w : Spec S'.functionField ⟶ pullback (V a).ι (V b).ι :=
      pullback.lift (gO (V a) (hηV a)) (gO (V b) (hηV b)) ((hgO (V a) (hηV a)).trans (hgO (V b) (hηV b)).symm)
    have : IsDominant w := isDominant_of_generic r _ w (by
      show (w ≫ pullback.fst _ _ ≫ (V a).ι) (IsLocalRing.closedPoint _) = _
      rw [pullback.lift_fst_assoc, hgO (V a) (hηV a)]; exact hgS)
    refine ext_of_isDominant_of_isSeparated p ?_ w ?_
    · rw [Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hmy, hmy]
  have hg : ∀ a, (V a).ι ≫ 𝒰.glueMorphisms m hc = m a := fun a => 𝒰.ι_glueMorphisms m hc a
  let π := 𝒰.glueMorphisms m hc
  have hπp : π ≫ p = h := 𝒰.hom_ext _ _ fun a => ((reassoc_of% hg a) p).trans (hm a)
  refine ⟨π, ?_, hπp⟩
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IsDominant (gO U hηU) := isDominant_of_generic U.ι _ _ (by
    show (gO U hηU ≫ U.ι) (IsLocalRing.closedPoint _) = _
    rw [hgO U hηU]; exact hgS)
  refine ext_of_isDominant_of_isSeparated p ?_ (gO U hηU) ?_
  · rw [Category.assoc, hπp, e]; simp only [Category.assoc]
  · let x := genericPoint S'
    rw [← Category.assoc, hgO U hηU, ← hgO (V x) (hηV x), Category.assoc, hg, hmy]
end GlobalTheory.NormalFiniteLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMulIsoUniformisationGenericFibreOneCon
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GenericMove

theorem move_one_const : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (N : ℕ) (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![𝟙 A.A.left, (mulA A.A N).left] ![(N : ℤ) ^ 2, -1])), α.IsGen → ∀ (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (mulA G N).left] ![(N : ℤ) ^ 2, -1])), β.IsGen → ∃ c : FractionRing V, c ≠ 0 ∧ ∀ (r : (TF (R := V) (FractionRing V)).left ⟶ ((Over.pullback (jK V)).obj G).left), r ≫ ((Over.pullback (jK V)).obj G).hom = 𝟙 _ → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (val β (r ≫ pullback.fst G.hom (jK V)) z JG).val = GlobalTheory.UT.cst (FractionRing V) z c * (GlobalTheory.TorsFrameInt.wv w₀ r z JG JA ^ ((N : ℤ) ^ 2) * (GlobalTheory.TorsFrameInt.wv w₀ (r ≫ (mulA ((Over.pullback (jK V)).obj G) N).left) z JG JA)⁻¹ * val α (r ≫ U.gen.hom.left) z JA).val := by
  intro V _ _ I D A G _ _ U w₀ hw₀ N α hα β hβ
  haveI := U.gen_hom
  have h₁ : ∀ k : Fin 2, (![𝟙 ((Over.pullback (jK V)).obj G).left,
      (mulA ((Over.pullback (jK V)).obj G) N).left] : Fin 2 → _) k ≫ pullback.fst G.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ (![𝟙 G.left, (mulA G N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact GlobalTheory.TorsFrameInt.mulA_comm (isGrpPullback_pullback G (jK V)) N
  have hmA : mulA ((Over.pullback (jK V)).obj G) N ≫ U.gen.hom = U.gen.hom ≫ mulA A.A N := by
    rw [mulA, mulA, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have h₂ : ∀ k : Fin 2, (![𝟙 ((Over.pullback (jK V)).obj G).left,
      (mulA ((Over.pullback (jK V)).obj G) N).left] : Fin 2 → _) k ≫ U.gen.hom.left =
      U.gen.hom.left ≫ (![𝟙 A.A.left, (mulA A.A N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact congrArg (fun q => q.left) hmA
  obtain ⟨a, ha, hav⟩ := GlobalTheory.TorsFrameInt.exists_move U.LG.isLB A.isLB w₀ hw₀ _ _ _ ![(N : ℤ) ^ 2, -1] h₁ h₂ β hβ
  obtain ⟨ρ, hρ⟩ := exists_ratio A.isLB rfl a (LB.pullGen A.L _ _ α U.gen.hom.left) ha
    (pullGen_isGen _ _ _ _ hα _)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.BoxExpansion.unit_const GlobalTheory.abelianSchemeLaws_all.1.globalFns A U.gen ρ
  refine ⟨c, hc0, fun r hr z JA JG hJA hJG => ?_⟩
  have hg : (gm r z ⊤ ρ).val = GlobalTheory.UT.cst (FractionRing V) z c := by
    rw [← gs_unit r z ⊤ trivial ρ, hc]
    exact (gs_pull r ((Over.pullback (jK V)).obj G).hom z ⊤ trivial _).trans (by rw [hr]; rfl)
  have e := hav _ r z JG JA hJG hJA
  rw [Fin.prod_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at e
  rw [e, hρ _ r z JA hJA, val_pull hJA, zpow_neg_one, mul_left_comm, Units.val_mul, hg]

end GlobalTheory.GenericMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedTwistedFactorValueAtLatticePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFacVal

section General

variable {X Y Z : Scheme.{0}}

def pt (q : Y ⟶ X) : Multiplicative (FreeAbelianGroup (Y ⟶ X)) := Multiplicative.ofAdd (FreeAbelianGroup.of q)

def ratSub {L : LB X} (e₀ e₁ : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Subgroup (Multiplicative (FreeAbelianGroup (Y ⟶ X)) × (Z.presheaf.stalk z)ˣ) where
  carrier := {g | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ ∏ k, pt (φ k) ^ ε k = g.1 ∧ val t e₁ z J = g.2 * val t e₀ z J}
  one_mem' := ⟨PEmpty, inferInstance, _, _, LB.oneGen L, (fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm), Fintype.prod_empty _, by
      rw [val_one, val_one]; exact (_root_.mul_one _).symm⟩
  mul_mem' := by
    rintro g g' ⟨K, _, φ, ε, t, ht, f, v⟩ ⟨K', _, φ', ε', t', ht', f', v'⟩
    refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
      DVR.prod_sum₂ _ f f', ?_⟩
    rw [val_mul hJ, val_mul hJ, v, v']
    exact mul_mul_mul_comm _ _ _ _
  inv_mem' := by
    rintro g ⟨K, _, φ, ε, t, ht, f, v⟩
    refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht, DVR.prod_neg _ _ f, ?_⟩
    rw [val_inv, val_inv, v]
    exact mul_inv _ _

theorem ratSub_eq_one {L : LB X} (hL : L.IsLB) (p : Y ⟶ Z) (e₀ e₁ : Z ⟶ Y) (h₀ : e₀ ≫ p = 𝟙 _) (h₁ : e₁ ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    {g : Multiplicative (FreeAbelianGroup (Y ⟶ X)) × (Z.presheaf.stalk z)ˣ} (hg : g ∈ ratSub e₀ e₁ hJ) (h : g.1 = 1) :
    g.2 = 1 := by
  obtain ⟨K, _, φ, ε, t, ht, f, v⟩ := hg
  have triv : ∀ (U : Type) [CommGroup U] (k : (Y ⟶ X) → U), ∏ i, k (φ i) ^ ε i = 1 := fun U _ k => by
    let F : Multiplicative (FreeAbelianGroup (Y ⟶ X)) →* U :=
      AddMonoidHom.toMultiplicativeLeft (FreeAbelianGroup.lift fun q => Additive.ofMul (k q))
    have hF : ∀ q, F (pt q) = k q := fun q => by simp [F, pt]
    have := congrArg F (f.trans h)
    simpa only [map_prod, map_zpow, hF, map_one] using this
  have key := gen_unique' hL (φ := φ) (ε := ε) (φ' := fun k => (p ≫ e₀) ≫ φ k) (ε' := ε)
    (fun U _ k => (triv U fun q => k ((p ≫ e₀) ≫ q)).trans (triv U k).symm) p e₀ h₀ hp ht
    (DVR.pullGen_isGen _ _ _ _ ht (p ≫ e₀)) (fun y I hI => by
      rw [val_pull hI, ← Category.assoc, h₀, Category.id_comp]) _ e₁ z J hJ
  rw [val_pull hJ, ← Category.assoc, h₁, Category.id_comp, v] at key
  exact mul_eq_right.1 key

end General

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T B : Over (Spec (CommRingCat.of R))}

theorem prod_tφ (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) (ρ : B ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : (B.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ tφ D a β i) ^ tε n j i =
      h ρ.left ^ (n - 1) * h (ρ * DVR.cP D B β).left * (h (DVR.cP D B β).left)⁻¹ * h (1 : B ⟶ D.P.A).left *
        h (ρ ≫ a).left ^ j := by
  have e₀ : ρ.left ≫ tφ D a β 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ tφ D a β 1 = (ρ * DVR.cP D B β).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 D.P.A) (DVR.cP D _ β)).trans (by rw [DVR.comp_cP, Category.comp_id]))
  have e₂ : ρ.left ≫ tφ D a β 2 = (DVR.cP D B β).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ β)
  have e₃ : ρ.left ≫ tφ D a β 3 = (1 : B ⟶ D.P.A).left :=
    congrArg (fun q : B ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

variable (ρ₀ ρ₁ : T ⟶ B) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)

theorem mem_const (κ : B ⟶ TK R) (hκ : ρ₁ ≫ κ = ρ₀ ≫ κ) (χ : D.X) :
    (pt (DVR.cP D B χ).left, 1) ∈ ratSub ρ₀.left ρ₁.left hJ := by
  refine (Subgroup.inv_mem_iff _).1 ⟨PUnit, inferInstance, _, _, LB.pullGen D.P.L _ _ (D.psi χ) κ.left,
    DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) _, ?_, ?_⟩
  · rw [Fintype.prod_unique, zpow_neg_one, ← DVR.comp_cP D κ χ]; rfl
  · rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, hκ]
    simp

theorem mem_cub (x x' y : B ⟶ D.P.A) :
    (pt (x * x' * y).left * (pt (x * x').left)⁻¹ * (pt (x * y).left)⁻¹ * (pt (x' * y).left)⁻¹ * pt x.left * pt x'.left *
        pt y.left * (pt (1 : B ⟶ D.P.A).left)⁻¹,
      cubV D.cub z J (ρ₁ ≫ x) (ρ₁ ≫ x') (ρ₁ ≫ y) * (cubV D.cub z J (ρ₀ ≫ x) (ρ₀ ≫ x') (ρ₀ ≫ y))⁻¹) ∈
      ratSub ρ₀.left ρ₁.left hJ :=
  ⟨thK, inferInstance, _, _, LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left,
    DVR.pullGen_isGen _ _ _ _ D.cub.isGen _, prod_cub x x' y pt,
    (val_cub D.cub ρ₁ hJ x x' y).trans ((inv_mul_cancel_right _ _).symm.trans
      (congrArg (_ * ·) (val_cub D.cub ρ₀ hJ x x' y).symm))⟩

theorem mem_ros (f g : D.P.A ⟶ D.P.A) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (x y : B ⟶ D.P.A) :
    (pt ((x ≫ f) * y).left * (pt (x ≫ f).left)⁻¹ * (pt y.left)⁻¹ * (pt (x * (y ≫ g)).left)⁻¹ * pt x.left * pt (y ≫ g).left,
      val₂ u z J (ρ₁ ≫ x) (ρ₁ ≫ y) * (val₂ u z J (ρ₀ ≫ x) (ρ₀ ≫ y))⁻¹) ∈ ratSub ρ₀.left ρ₁.left hJ := by
  refine ⟨Fin 6, inferInstance, _, _, LB.pullGen D.P.L _ _ u (lift x y).left,
    DVR.pullGen_isGen _ _ _ _ hu _, prod_ros f g x y pt, ?_⟩
  rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift]
  exact (inv_mul_cancel_right _ _).symm

end Points

theorem mem_of_add {X G : Type} [AddCommGroup X] [CommGroup G] (H : Subgroup G) (l : X → G)
    (hl : ∀ a b, l (a + b) * (l a)⁻¹ * (l b)⁻¹ ∈ H) (n j : ℤ) (β ν δ : X) :
    l (β + (n • ν + j • δ)) * (l β * l ν ^ n * l δ ^ j)⁻¹ ∈ H := by
  let f : X →+ Additive (G ⧸ H) := AddMonoidHom.mk' (fun a => Additive.ofMul (QuotientGroup.mk' H (l a))) (fun a b => by
    have := (QuotientGroup.eq_one_iff _).2 (hl a b)
    rw [← QuotientGroup.mk'_apply, map_mul, map_mul, map_inv, map_inv, _root_.mul_assoc, ← mul_inv, mul_inv_eq_one] at this
    rw [this, ofMul_mul])
  have e : f (β + (n • ν + j • δ)) = f β + (n • f ν + j • f δ) := by simp only [map_add (f := _), map_zsmul]
  refine (QuotientGroup.eq_one_iff _).1 ?_
  rw [← QuotientGroup.mk'_apply, map_mul, map_inv, map_mul, map_mul, map_zpow, map_zpow, mul_inv_eq_one, _root_.mul_assoc]
  exact congrArg Additive.toMul e

theorem val_fac {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (a a' : D.P.A ⟶ D.P.A)
    (h h' : D.X →+ D.X) (hE : EndData D a a' h h') (n j : ℤ) (ν mu β₀ β₁ : D.X) (hβ : β₁ = β₀ + shift h h' n j ν)
    (u₁ : LB.Gen (LB.LinComb D.P.L (dφ D a ν β₀ β₁) (dε n j))) (hu₁ : IsFac D a h n j ν β₀ β₁ u₁)
    (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : Good D.P.L z J) :
    val u₁ ((DegPre.zF D (FractionRing R)).left ≫ (DegPre.trF D (FractionRing R) mu).left) z J =
      (val (D.psi (ν + mu)) (jFK (R := R) (FractionRing R)) z J ^ n *
        val (D.psi (h (ν + mu))) (jFK (R := R) (FractionRing R)) z J ^ j *
        val (D.tau (ν + mu) β₀) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)) *
      (val (D.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j *
        val (D.tau mu β₁) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j))⁻¹ := by
  obtain ⟨ha, ha', hr, hc, hc', hbal⟩ := hE
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  let T : Over (Spec (CommRingCat.of R)) := TF (R := R) (FractionRing R)
  let B : Over (Spec (CommRingCat.of R)) := DegPre.BF D (FractionRing R)
  let ρ₀ : T ⟶ B := DegPre.zF D (FractionRing R)
  let ρ₁ : T ⟶ B := DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu
  let x : B ⟶ D.P.A := DegPre.prB D (FractionRing R)
  let p : B ⟶ T := fst _ _
  let κ : T ⟶ TK R := Over.homMk (jFK (R := R) (FractionRing R)) rfl
  have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
  have tx : ∀ χ, DegPre.trF D (FractionRing R) χ ≫ x = x * DVR.cP D B χ := fun χ => lift_snd _ _
  have p₀ : ρ₀ ≫ p = 𝟙 _ := lift_fst _ _
  have p₁ : ρ₁ ≫ p = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (ρ₀ ≫ ·) (lift_fst _ _)).trans p₀)
  have x₀ : ρ₀ ≫ x = 1 := lift_snd _ _
  have x₁ : ρ₁ ≫ x = DVR.cP D T mu := by
    refine (Category.assoc _ _ _).trans ((congrArg (ρ₀ ≫ ·) (tx mu)).trans ((MonObj.comp_mul _ _ _).trans ?_))
    rw [x₀, DVR.comp_cP, _root_.one_mul]
  have ca : ∀ S χ, DVR.cP D S χ ≫ a = DVR.cP D S (h χ) := fun S χ => by rw [DVR.cP, DVR.cP, hc, Category.assoc]
  have ca' : ∀ S χ, DVR.cP D S χ ≫ a' = DVR.cP D S (h' χ) := fun S χ => by rw [DVR.cP, DVR.cP, hc', Category.assoc]
  have c0 : DVR.cP D B 0 = 1 := by simpa using DVR.cPoint_nsmul D B 0 0
  have s : (𝟙 T : T ⟶ T).left ≫ jFK (R := R) (FractionRing R) = jFK (R := R) (FractionRing R) := Category.id_comp _

  let τ : D.X → D.X → (T.left.presheaf.stalk z)ˣ := fun χ χ' => val (D.tau χ χ') (jFK (R := R) (FractionRing R)) z J
  have tm : ∀ χ χ' b, τ (χ + χ') b * cubV D.cub z J (DVR.cP D T χ) (DVR.cP D T χ') (DVR.cP D T b) = τ χ b * τ χ' b :=
    fun χ χ' b => by have := DVR.tau_mul (𝟙 T) hJ hB χ χ' b; rw [s] at this; exact this
  have ts : ∀ χ χ', τ χ χ' = τ χ' χ := fun χ χ' => by have := DVR.tau_symm (𝟙 T) hJ χ χ'; rw [s] at this; exact this
  let ψ : D.X → (T.left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (jFK (R := R) (FractionRing R)) z J
  let rg : (T.left.presheaf.stalk z)ˣ := val D.rigK (jFK (R := R) (FractionRing R)) z J
  have pa : ∀ χ χ', ψ (χ + χ') = τ χ χ' * ψ χ * ψ χ' * rg := fun χ χ' => by
    have := DVR.UUA.psi_add (𝟙 T) hJ χ χ'; rw [s] at this; exact this
  have tb : τ (h mu) (h ν) * val₂ u (T := T) z J (DVR.cP D T mu) (DVR.cP D T (h ν)) = τ mu (h' (h ν)) := by
    have := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ mu (h ν)) κ.left)
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
    rw [val_pull hJ, val₂, ← DVR.comp_cP D κ, ← DVR.comp_cP D κ, ← comp_lift]
    rfl
  have r₀ : val₂ u (T := T) z J 1 (DVR.cP D T (h ν)) = 1 := by
    have e := (ros_add D.cub hG D.P.isAb a a' u hu u₀ (T := T) hJ 1 1 (DVR.cP D _ (h ν))).1
    rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm

  have mc : ∀ χ, (pt (DVR.cP D B χ).left, 1) ∈ ratSub ρ₀.left ρ₁.left hJ :=
    mem_const ρ₀ ρ₁ hJ (p ≫ κ) (by rw [← Category.assoc, ← Category.assoc, p₀, p₁])
  have ml := mem_of_add (ratSub ρ₀.left ρ₁.left hJ) (fun χ => (pt (DVR.cP D B χ * x).left * (pt x.left)⁻¹ *
      (pt (DVR.cP D B χ).left)⁻¹ * pt (1 : B ⟶ D.P.A).left, (τ χ mu)⁻¹)) (fun χ χ' => by
    have m := mem_cub ρ₀ ρ₁ hJ (DVR.cP D B χ) (DVR.cP D B χ') x
    simp only [DVR.comp_cP, x₀, x₁, C.face₃] at m
    convert m using 1
    have t := congrArg Additive.ofMul (tm χ χ' mu)
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.fst_inv, DVR.cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · simp only [Prod.snd_mul, Prod.snd_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at t ⊢
      linear_combination (norm := abel) -t) n j β₀ ν (h' (h ν))
  rw [show β₀ + (n • ν + j • h' (h ν)) = β₁ from hβ.symm] at ml
  have mr := mem_ros ρ₀ ρ₁ hJ a a' u hu x (DVR.cP D B (h ν))
  simp only [DVR.comp_cP, x₀, x₁, r₀, ca'] at mr
  have mk := mem_cub ρ₀ ρ₁ hJ (DVR.cP D B ν) x (DVR.cP D B β₀)
  simp only [DVR.comp_cP, x₀, x₁, C.face₂] at mk
  have f₁ := prod_tφ a n j β₁ x pt
  have f₀ := prod_tφ a n j β₀ (DegPre.trF D (FractionRing R) ν ≫ x) pt
  have mu₁ : (_, val u₁ ρ₁.left z J * (val u₁ ρ₀.left z J)⁻¹) ∈ ratSub ρ₀.left ρ₁.left hJ :=
    ⟨Fin 5 ⊕ Fin 5, inferInstance, _, _, u₁, hu₁.1, DVR.prod_sum₂ _ f₁ (DVR.prod_neg _ _
      ((Finset.prod_congr rfl fun i _ => by rw [Over.comp_left, Category.assoc]; rfl).trans f₀)),
      (inv_mul_cancel_right _ _).symm⟩
  rw [tx, MonObj.mul_comp, ca] at mu₁
  have key := ratSub_eq_one D.P.isLB p.left ρ₀.left ρ₁.left (congrArg (fun q => q.left) p₀) (congrArg (fun q => q.left) p₁)
    (DVR.surj_appTop D (FractionRing R) hG) hJ
    (mul_mem (mul_mem (mul_mem (mul_mem mu₁ (inv_mem ml)) (zpow_mem mr j)) mk)
      (mul_mem (mul_mem (mul_mem (mul_mem (mc (ν + β₀)) (zpow_mem (mc ν) (n - 1))) (inv_mem (mc β₀)))
        (zpow_mem (mc 0) (1 - n - j))) (zpow_mem (mc (h ν)) j))) (by
      simp only [Prod.fst_mul, Prod.fst_inv, Prod.pow_fst, DVR.cPoint_add, c0, _root_.mul_comm (DVR.cP D B _) x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  have v₀ := hu₁.2 z J hJ
  simp only [Prod.snd_mul, Prod.snd_inv, Prod.pow_snd] at key
  show val u₁ ρ₁.left z J = ψ (ν + mu) ^ n * ψ (h (ν + mu)) ^ j * τ (ν + mu) β₀ * rg ^ (n + j) *
    (ψ mu ^ n * ψ (h mu) ^ j * τ mu β₁ * rg ^ (n + j))⁻¹
  change val u₁ ρ₀.left z J = ψ ν ^ n * ψ (h ν) ^ j * τ ν β₀ * rg ^ (n + j) at v₀
  rw [map_add (f := _), pa, pa]
  rw [v₀, ts β₁, ts β₀, ts (h' (h ν)), ← tb, ts (h mu)] at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  have t := congrArg Additive.ofMul (tm ν mu β₀)
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, smul_add, smul_neg] at k t ⊢
  linear_combination (norm := module) k - t

theorem val_fac_at_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ : D.toPre.X), β₁ = β₀ + shift h h' n j ν → ∀ (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a ν β₀ β₁) (dε n j))), IsFac D.toPre a h n j ν β₀ β₁ u₁ → ∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val u₁ ((DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.trF D.toPre (FractionRing R) mu).left) z J = (val (D.toPre.psi (ν + mu)) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h (ν + mu))) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau (ν + mu) β₀) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)) * (val (D.toPre.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau mu β₁) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j))⁻¹ :=
  fun _ _ _ _ _ D a a' h h' hE n j ν mu β₀ β₁ hβ u₁ hu₁ z J hJ =>
    val_fac D.toPre D.tau_bimult a a' h h' hE n j ν mu β₀ β₁ hβ u₁ hu₁ z J hJ

end GlobalTheory.TwFacVal
end
end

