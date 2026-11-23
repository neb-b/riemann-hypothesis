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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPull

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem trPt_aF (oa : D.toPre.OAct O) (a : O) (b b' : TF (R := V) F ⟶ D.toPre.P.A)
    (hb : b' = b ≫ oa.onB.act a) :
    DegPre.trPt D.toPre F b ≫ aF D F oa a = aF D F oa a ≫ DegPre.trPt D.toPre F b' := by
  have := oa.onB.hom a
  have ap : aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a := by
    simp [aF, DegPre.prB]
  have af : aF D F oa a ≫ fst (TF (R := V) F) D.toPre.P.A = fst _ _ := lift_fst _ _
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, af, tr_fst, Category.assoc, tr_fst, af]
  · show (DegPre.trPt D.toPre F b ≫ aF D F oa a) ≫ DegPre.prB D.toPre F =
      (aF D F oa a ≫ DegPre.trPt D.toPre F b') ≫ DegPre.prB D.toPre F
    rw [Category.assoc, ap, ← Category.assoc, tr_pr, MonObj.mul_comp, Category.assoc, ← hb,
      Category.assoc, tr_pr, MonObj.comp_mul, ap, ← Category.assoc, af]

theorem gen_eq_of_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (p' : QkPt D.toPre F k)
    (p₁ : QkPt D.toPre F (k * N)) (hy : p₁.y = star a • p'.y) (hb : p'.g.b = p₁.g.b ≫ oa.onB.act a)
    (χ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (huχ : uχ.IsGen)
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a (χ + p'.y)) (pullε k N))) (huχz : uχz.IsGen)
    (Ψ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p'.y χ p'.g.b) (DegPre.deltaε k))) (hΨ : Ψ.IsGen)
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b) (DegPre.deltaε (k * N))))
    (hΦ : Φ.IsGen)
    (horig : ∀ y J, Good D.toPre.P.L y J →
      val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p₁.g.b).left) Φ)
          (DegPre.zF D.toPre F).left y J =
        val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ Ψ (aF D F oa a).left))
          (DegPre.zF D.toPre F).left y J)
    (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z' : Z) (J) (hJ : Good D.toPre.P.L z' J) :
    val uχ (ρ ≫ (DegPre.trPt D.toPre F p₁.g.b).left) z' J * val Φ ρ z' J =
      val uχz ρ z' J * val Ψ (ρ ≫ (aF D F oa a).left) z' J := by
  have e1 : ∀ i, (DegPre.trPt D.toPre F p₁.g.b).left ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left, trPt_aF oa a p₁.g.b p'.g.b hb]
  have e2 : ∀ i, (aF D F oa a).left ≫ (DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left]
  have e3 : star a • χ + p₁.y = star a • (χ + p'.y) := by rw [hy, smul_add]
  have hF : FormEq (Sum.elim (pullφ D F oa a (χ + p'.y))
      (fun i => (aF D F oa a).left ≫ DegPre.phiφ D.toPre F p'.y χ p'.g.b i)) (Sum.elim (pullε k N) (DegPre.deltaε k))
      (Sum.elim (fun i => (DegPre.trPt D.toPre F p₁.g.b).left ≫ pullφ D F oa a χ i)
        (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b)) (Sum.elim (pullε k N) (DegPre.deltaε (k * N))) :=
    fun U _ h => by
      simp only [pullφ, pullε, DegPre.phiφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl,
        Sum.elim_inr, e1, e2, e3]
      simp only [Fin.prod_univ_four]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module
  have key := gen_unique' D.toPre.P.isLB hF (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.zF D.toPre F).left
    (GC.zF_fst (D := D) (F := F)) (surj_appTop D.toPre F hG)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ huχ _) hΦ)
    (mulGen_isGen _ _ _ _ _ _ _ huχz (pullGen_isGen _ _ _ _ hΨ _)) horig Z ρ z' J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ] at key
  exact key

theorem exists_normalisation (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN : 1 ≤ N)
    (b b' : TF (R := V) F ⟶ D.toPre.P.A) (hb : b' = b ≫ oa.onB.act a)
    (w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b') (DegPre.lineε k))) (hw' : w'.IsGen)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen) :
    ∃ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b) (DegPre.lineε (k * N))), w.IsGen ∧
      ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val w' (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left y J)⁻¹ := by
  have := oa.onB.hom a
  have h1 : (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ DegPre.prB D.toPre F = b :=
    CanonicalLiftTraces.zF_tr_pr b
  have h2 : ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a) ≫ DegPre.prB D.toPre F = b' := by
    rw [Category.assoc, show aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a by
      simp [aF, DegPre.prB], ← Category.assoc, h1, hb]
  have e2 : ∀ i, (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left ≫ (aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i = ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i := fun i => by rw [← Category.assoc, ← Over.comp_left]
  have c0 : cP D.toPre (TF (R := V) F) 0 = 1 := cPoint_zero _
  have p0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := rfl
  have p1 : jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left :=
    (Category.assoc _ _ _).symm
  have hN' : ((k * (N - 1) : ℕ) : ℤ) = ((k * N : ℕ) : ℤ) - k := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN]; push_cast; ring
  obtain ⟨w, hw, hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F b) (ε' := DegPre.lineε (k * N))
    (fun U _ h => by
      simp only [pullφ, pullε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, e2, p1]
      simp only [CanonicalLiftTraces.comp_famφ, h1, h2, Fin.prod_univ_four, Fin.prod_univ_two, Matrix.cons_val,
        DegPre.famε, smul_zero, c0, _root_.mul_one, DegPre.lineφ, DegPre.lineε, p0, hN']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) w')
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (pullGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _) _) hw')
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu0 _)))
  refine ⟨w, hw, fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ u0, Category.id_comp]

theorem gen_eq_at_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (p' : QkPt D.toPre F k)
    (p₁ : QkPt D.toPre F (k * N)) (hgt : GtAct oa a p₁.g p'.g)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)))
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε (k * N))))
    (hwv : ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val w' (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F p₁.g.b).left y J)⁻¹)
    (χ ξ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (huχ : uχ.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a ξ) (pullε k N)))
    (hcz : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχz (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (Ψ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p'.y χ p'.g.b) (DegPre.deltaε k)))
    (hcΨ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Ψ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p'.g.s χ) w'))
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b) (DegPre.deltaε (k * N))))
    (hcΦ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Φ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p₁.g.s (star a • χ)) w))
    (y : (TF (R := V) F).left) (J) (hJ : Good D.toPre.P.L y J) :
    val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p₁.g.b).left) Φ)
        (DegPre.zF D.toPre F).left y J =
      val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ Ψ (aF D F oa a).left))
        (DegPre.zF D.toPre F).left y J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hros := oa.onB.rosati (star a)
  rw [star_star] at hros
  obtain ⟨r, hr, hr0⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hros
  have hl : ((DegPre.zF D.toPre F).left ≫ (DegPre.trPt D.toPre F p₁.g.b).left) ≫
      (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left = (lift (DegPre.cF D.toPre F χ) p₁.g.b).left := by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_cP, CanonicalLiftTraces.zF_tr_pr]
    rfl
  have e1 := val_corr hJ hcz (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at e1
  have e2 := val_corr hJ hcΨ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_mul hJ] at e2
  have e3 := val_corr hJ hcΦ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_mul hJ] at e3
  have e5 := hwv y J hJ
  rw [Over.comp_left] at e5
  have e6 := val_corr hJ (hgt.2 r hr hr0 χ) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, Category.id_comp] at e6
  have e7 : val Ψ ((DegPre.zF D.toPre F).left ≫ (aF D F oa a).left) y J = val Ψ (DegPre.zF D.toPre F).left y J := by
    rw [← Over.comp_left, CanonicalLiftTraces.zF_aF]
  rw [val_mul hJ, val_pull hJ, val_mul hJ, val_pull hJ, e3,
    CanonicalLiftValuation.pull_val_chi hG oa a k N χ uχ huχ hc u0 hu0 hc0 r hr hr0 _ _ y J hJ, val_pull hJ, hl,
    e5, e7, e1, e2, ← e6]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem phiRel_pullAl : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (p' : QkPt D.toPre F k) (p₁ : QkPt D.toPre F (k * N)), GtAct oa a p₁.g p'.g → p₁.y = star a • p'.y → ∀ w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)), w'.IsGen → ∃ w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε (k * N))), w₁.IsGen ∧ ∀ (s t : Fam D.toPre F k) (s' t' : Fam D.toPre F (k * N)), PhiRel D.toPre F k p' w' s t → PullAl D F oa a k N s s' → PullAl D F oa a k N t t' → PhiRel D.toPre F (k * N) p₁ w₁ s' t' := by
  intro hL V _ _ _ D F _ _ O _ _ _ oa w0 hw0 a N k hN _ haa p' p₁ hgt hy w' hw'
  have hG := hL.globalFns
  obtain ⟨uΨ, huΨ, -⟩ := hw0
  obtain ⟨u0, hu0, hc0⟩ := exists_pullGen D F D.toPre.P.isLB oa w0 uΨ huΨ a N haa hN k 0
  obtain ⟨w, hw, hwv⟩ := exists_normalisation oa a k N hN p₁.g.b p'.g.b hgt.1 w' hw' u0 hu0
  refine ⟨w, hw, fun s t s' t' hst hs' ht' => ?_⟩
  rw [phiRel_iff hG p₁ w hw s' t']
  intro a' β hβ T ρ z' J hJ
  by_cases ha : ∃ χ, a' = star a • χ
  · obtain ⟨χ, rfl⟩ := ha
    subst hβ
    have e3 : star a • χ + p₁.y = star a • (χ + p'.y) := by rw [hy, smul_add]
    rw [e3]
    obtain ⟨uχz, huχz, hcz, hsz⟩ := ht'.1 (χ + p'.y)
    obtain ⟨uχ, huχ, hc, hs⟩ := hs'.1 χ
    obtain ⟨⟨Ψ, hΨ, hcΨ⟩, -⟩ := gen_phi hG p' w' hw' χ
    obtain ⟨⟨Φ, hΦ, hcΦ⟩, hΦv⟩ := gen_phi hG p₁ w hw (star a • χ)
    have s1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχz).1 hsz _ ρ.left z' J hJ
    have s2 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ Ψ).1 (hst χ Ψ hΨ hcΨ) _
      (ρ.left ≫ (aF D F oa a).left) z' J hJ
    have s3 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχ).1 hs _ (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left z' J hJ
    have pt : (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left ≫ (aF D F oa a).left =
        (ρ.left ≫ (aF D F oa a).left) ≫ (DegPre.trPt D.toPre F p'.g.b).left := by
      rw [← Over.comp_left, Category.assoc, trPt_aF oa a p₁.g.b p'.g.b hgt.1, ← Category.assoc, Over.comp_left,
        Over.comp_left]
    have eig := gen_eq_of_origin hG oa a k N p' p₁ hy hgt.1 χ uχ huχ uχz huχz Ψ hΨ Φ hΦ
      (fun y J hJ => gen_eq_at_origin hG oa a k N p' p₁ hgt u0 hu0 hc0 w' w hwv χ _ uχ huχ hc uχz hcz Ψ hcΨ
        Φ hcΦ y J hJ) _ ρ.left z' J hJ
    have hΦρ := hΦv Φ hΦ hcΦ T ρ z' J hJ
    have eig' : (val Ψ (ρ.left ≫ (aF D F oa a).left) z' J).val * (val uχz ρ.left z' J).val =
        (val uχ (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left z' J).val * (val Φ ρ.left z' J).val := by
      rw [← Units.val_mul, ← Units.val_mul, _root_.mul_comm]
      exact congrArg Units.val eig.symm
    rw [s1, s2, s3, pt, ← hΦρ, _root_.mul_assoc, _root_.mul_assoc, eig']
  · have hβn : ∀ χ, β ≠ star a • χ := by
      intro χ h
      apply ha
      refine ⟨χ - p'.y, ?_⟩
      rw [smul_sub, ← h, ← hβ, hy]
      abel
    rw [CanonicalLiftFrobenius.sval_zero _ (ht'.2 β hβn), CanonicalLiftFrobenius.sval_zero _ (hs'.2 a' (fun χ h => ha ⟨χ, h⟩)),
      MulZeroClass.zero_mul]

end GlobalTheory.ThetaPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBessel
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_regular_rep_vec_bigPt_eq_bessel :
    ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ γ ∈ JF.Om P.k P.r p.T.base.z p.T.base.z', Formalism.QuantumDeterminants.Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) ∧ ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), p.V F (TBB.bigPt P.r c) = B.JF p.T.base F γ := by
  intro P Wp Wq _ _ _ _ _ _ p d hl0 hG
  have hd : ∀ a, d a ≠ 0 := fun a =>
    (hl0.1 (1, d a) (by unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨a, rfl⟩)).2
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := hl0
  have hG' : 0 < D.ptG (Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z * Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z') P.r
      (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  obtain ⟨hγ, hZγ, -⟩ := h'.choose_spec
  have hpos : 0 < Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  refine ⟨h'.choose, ⟨hγ, fun l _ => ?_, hpos⟩, hZγ, fun F => ?_⟩
  · unfold Formalism.QuantumDeterminants.Dmin
    rw [hZγ, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hd _
  · show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d) = _
    unfold D.vecV
    rw [dite_eq_left ⟨hl, hG'⟩, dite_eq_left h']
    have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
    rw [hw] at hmono
    rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ hpos hnz (hZγ.trans hmono) F]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyMoment
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomentStep

theorem lintegral_le_of_le_sum {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (f : Ω → ℝ)
    (g : ι → ι → Ω → ℝ) (C : ℝ) (N : ι → ι → ℝ) (hC : 0 ≤ C) (hg0 : ∀ d s x, 0 ≤ g d s x)
    (hm : ∀ d s, AEMeasurable (g d s) ν) (hpt : ∀ᵐ x ∂ν, f x ≤ C * ∑ d, ∑ s, g d s x)
    (hN : ∀ d s, 0 ≤ N d s) (hint : ∀ d s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν ≤ ENNReal.ofReal (N d s)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal (C * ∑ d, ∑ s, N d s) := by
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (g d s x) ∂ν := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        refine (ENNReal.ofReal_le_ofReal hx).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hg0 d s x]
        congr 1
        exact Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hg0 d s x
    _ = ENNReal.ofReal C * ∑ d, ∑ s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun d _ => Finset.aemeasurable_fun_sum _ fun s _ => (hm d s).ennreal_ofReal]
        congr 1
        exact Finset.sum_congr rfl fun d _ => lintegral_finsetSum' _ fun s _ => (hm d s).ennreal_ofReal
    _ ≤ ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (N d s) := by
        gcongr with d _ s _
        exact hint d s
    _ = _ := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hN d s]
        congr 1
        exact (Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hN d s).symm

theorem norm_sum_smul_sq_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ)
    (v : ι → V) : ‖∑ s, c s • v s‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ s, ‖c s‖ ^ 2 * ‖v s‖ ^ 2 := by
  have h1 : ‖∑ s, c s • v s‖ ≤ ∑ s, ‖c s‖ * ‖v s‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => norm_smul _ _))
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun s => ‖c s‖ * ‖v s‖)
  simp only [mul_pow, Finset.card_univ] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem pointwise_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (L D A : ℝ) (q : ℕ)
    (a β : ι → ℂ) (Ds : ι → ℝ) (v : V) (y : ι → ι → V) (hD : 0 ≤ D) (hL : ∑ d, ‖a d‖ ^ 2 = L ^ 2)
    (he : ∀ d, a d • v = ∑ s, β s • y d s) (hβ : ∀ s, ‖β s‖ ^ 2 * D ≤ A * Ds s) :
    L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) ≤
      ((Fintype.card ι : ℝ) * A) * ∑ d, ∑ s, L ^ (2 * q) * (Ds s * ‖y d s‖ ^ 2) := by
  have hP : 0 ≤ L ^ (2 * q) := by rw [pow_mul]; positivity
  have e1 : L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) = ∑ d, L ^ (2 * q) * (D * ‖a d • v‖ ^ 2) := by
    rw [mul_add, pow_add, mul_one, ← hL, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [norm_smul]; ring
  rw [e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [he d]
  calc L ^ (2 * q) * (D * ‖∑ s, β s • y d s‖ ^ 2)
      ≤ L ^ (2 * q) * (D * ((Fintype.card ι : ℝ) * ∑ s, ‖β s‖ ^ 2 * ‖y d s‖ ^ 2)) := by
        gcongr
        exact norm_sum_smul_sq_le β (y d)
    _ = ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (‖β s‖ ^ 2 * D) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (A * Ds s) := by
        exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hβ s) (by positivity)
    _ = _ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) : n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_sub_le _ _

theorem param_sub_single {n : ℕ} (lam : Fin n → ℝ) (ν : Fin n → ℤ) (s : Fin n) :
    (fun a => lam a + (((ν - Pi.single s 1) : Fin n → ℤ) a : ℝ)) =
      (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
  funext a
  by_cases h : a = s
  · subst h; simp; ring
  · simp [h]


set_option maxHeartbeats 1000000 in
theorem moment_step : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν + 1 ≤ q0 → ∀ (j q : ℕ) (MM : ℝ), j ≤ 4 * (2 * r + k + 1) ^ 2 → 0 ≤ MM → (∀ (s : Fin (2 * r + k + 1)) (y : (R (ν - Pi.single s 1)).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1)) (fun a => lam a + (((ν - Pi.single s 1) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) (j + 2) y → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) * ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x) y)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (MM * ‖y‖ ^ 2)) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * MM * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q MM hj hMM hind w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hNum, hFam, hG, hSide⟩ := id hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hνs : ∀ s, n1 (ν - Pi.single s 1) ≤ q0 := fun s => (lOneNorm_sub_single_one_le ν s).trans hν
  have hDS := hFam ν hν0
  have hDSs := fun s => hFam _ (hνs s)
  obtain ⟨hBe, hdg, -⟩ := hSide ν hν0
  have hBes := fun s => (hSide _ (hνs s)).1
  have hdgs := fun s => (hSide _ (hνs s)).2.1
  obtain ⟨hae, -, hmL, hml⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG
  by_cases hnz : NzOn (R ν) (l ν)
  swap
  · have : ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) *
        (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      rw [← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae (hae.mono fun x hx => ?_)
      have : l ν ((R ν).σ (Matrix.of x) w) = 0 := by
        by_contra hne
        exact hnz ⟨_, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hDS.2 w.2 hx, hne⟩
      simp [this]
    rw [this]
    exact bot_le
  obtain ⟨io, pr, ep, hT⟩ := (GlobalTheory.T.pieri_tensor_decomposition hH k r lam u b bv ga h q0 R hNum hFam ν).2 hν
  have hF := GlobalTheory.isFRep_dualM k r
  have hkap := fun s => GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν)
    (fun s => R (ν - Pi.single s 1)) io pr ep _ _ _ Wp z π u μW μN μG νq
    (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (l ν) hDS hDSs hF hT hG
    (fun s hs => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hG.1 s hs).2) hBe hnz s
    (l (ν - Pi.single s 1)) (hBes s)
  choose κ hκ using fun s => (hkap s).1
  have hdual := fun s => (hkap s).2 (κ s) (hκ s)
  have hA : ∀ s, ‖(ep s : ℂ) * star (κ s)‖ ^ 2 * dg ν ≤
      (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * dg (ν - Pi.single s 1) := by
    intro s
    have h1 := GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s
      (κ s) (hκ s)
    rw [div_le_iff₀ (hdgs s)] at h1
    have h2 : ‖(ep s : ℂ) * star (κ s)‖ = ‖κ s‖ := by
      rcases hT.ep_sq s with h | h <;> simp [h]
    rwa [h2]
  obtain ⟨io', pr', hAlg, hpr⟩ := GlobalTheory.T.dual_tensor_cayley_weighted hK k r _ _ (R ν) hDS (fun s => R (ν - Pi.single s 1)) _ io pr ep Q
    (E ν) (fun s => E (ν - Pi.single s 1)) hDSs hT hQ (hE ν hν0).1 (fun s => (hE _ (hνs s)).1)
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDS Q (E ν) hQ (hE ν hν0).1
  have hMods : ∀ s, IsMod (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1))
      ((fun a => lam a + (ν a : ℝ)) - Pi.single s 1) := fun s => by
    rw [← param_sub_single]
    exact GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ _ hNum.1 (hDSs s) Q _ hQ (hE _ (hνs s)).1
  have hShape := ((GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum).2 ν hν0).2.1
  have hlev := _root_.GlobalTheory.lev_proj_and_sum_sq_le _ _ _ (E ν) (fun s => (R (ν - Pi.single s 1)).smSub) (fun s => E (ν - Pi.single s 1))
    io' pr' _ k j bv w hMod hMods hAlg hShape hj hw
  have hexp : 2 * r + k + 1 + 1 - k = 2 * r + 2 := by omega
  rw [hexp] at hlev
  have hy : ∀ d s, ((pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub) : (R (ν - Pi.single s 1)).H) =
      ∑ c, pr s c (tm (R ν) (fun c => Q d c) w c) := by
    intro d s
    rw [hpr]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [Finset.sum_eq_single d]
    · simp [tm]
    · intro e _ he; simp [he]
    · simp
  have hA0 : 0 ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := mul_nonneg hG.2.1.le (by positivity)
  have key := lintegral_le_of_le_sum νq
    (fun x => lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2))
    (fun d s x => lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) *
      ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x)
        (pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub))‖ ^ 2))
    ((Fintype.card (Fin (2 * r + k + 1)) : ℝ) * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4))
    (fun d s => MM * ‖pr' s (Pi.single d w)‖ ^ 2) (by positivity)
    (fun d s x => mul_nonneg (by rw [pow_mul]; positivity) (mul_nonneg (hdgs s).le (by positivity)))
    (fun d s => ((hmL 0).pow_const _).mul
      ((((GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ _ Wp z π u μW μN μG νq (hDSs s) hG).2.2.2 _ (hBes s).1 _
        (pr' s (Pi.single d w)).2).norm.aemeasurable.pow_const _).const_mul _))
    (hae.mono fun x hx => by
      refine pointwise_le _ _ _ q
        (fun d => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (dualM (Matrix.of x) *ᵥ (fun c => Q d c))
          (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)))
        (fun s => (ep s : ℂ) * star (κ s)) _ _ _ hdg.le ?_ (fun d => ?_) hA
      · rw [_root_.GlobalTheory.MomentParseval.sum_herm_sq k r _ dualM _ Q 1 _ hF hQ.2 _ hx]
        exact (GlobalTheory.TensLen.lengths k r z hG.1 hG.2.1 _ hx).2.1
      · simp only [hy]
        exact GlobalTheory.T.tensor_bessel_transfer hK k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν) (fun s => R (ν - Pi.single s 1)) io pr _ _ _
          Wp _ (l ν) (fun s => l (ν - Pi.single s 1)) _ hDS hDSs hT.raw hBe.1.1 hBe.1.2.1 hdual _ w w.2 _ hx)
    (fun d s => by positivity)
    (fun d s => hind s _ (by rw [param_sub_single]; exact (hlev d).1 s))
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsum : ∑ d, ∑ s, MM * ‖pr' s (Pi.single d w)‖ ^ 2 ≤
      ∑ _d : Fin (2 * r + k + 1), MM * ((6 * bv) ^ (2 * (2 * r + 2)) * ‖w‖ ^ 2) := by
    refine Finset.sum_le_sum fun d _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hlev d).2 hMM
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.MomentStep
end

