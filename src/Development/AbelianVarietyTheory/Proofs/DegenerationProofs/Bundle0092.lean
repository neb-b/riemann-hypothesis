module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulMemAdjoinOfMemPowRange
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimQuotientLeOne
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisTermsAtOtherClassMembers
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.Shift
open ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing

theorem lin_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {R : Type} [CommRing R] (p : Y ⟶ Sp R) {I : Type} [Fintype I] (a : I → R)
    (s : LB.Sec (LB.LinComb L φ ε)) (t : I → LB.Sec (LB.LinComb L φ ε)) :
    (∀ j, s.f j = ∑ i, constFn p _ (a i) * (t i).f j) ↔
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
        sval s r z J = ∑ i, cst (r ≫ p) z (a i) * sval (t i) r z J := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι) (hm : r z ∈ LB.wchart L φ j),
      gs r z (LB.wchart L φ j) (∑ i, constFn p (LB.wchart L φ j) (a i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j)) =
        ∑ i, cst (r ≫ p) z (a i) * gs r z (LB.wchart L φ j) ((t i).f j) := fun Z r z j hm => by
    have e : ∀ (b : I → Γ(Y, LB.wchart L φ j)), gs r z _ (∑ i, b i) = ∑ i, gs r z _ (b i) := fun b => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [gs_eq r z _ hm, map_sum]
    rw [e]
    exact Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_constFn p _ r z hm _) rfl)
  constructor
  · intro h Z r z J hJ
    exact (congrArg (gs r z _) (h _)).trans (key Z r z _ (hJ.mem φ r))
  · intro h j
    refine fn_ext fun y hy => ?_
    choose J hJ using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
    have hJ' : Good L y J := hJ
    have m := hJ'.mem φ (𝟙 Y)
    refine (sec_trans s (𝟙 Y) y (j := j) hy m).trans (Eq.trans ?_ (key Y (𝟙 Y) y j hy).symm)
    refine (congrArg _ (h Y (𝟙 Y) y J hJ')).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_trans (t i) (𝟙 Y) y (j := j) hy m]
    exact mul_left_comm _ _ _

section
variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V)

abbrev tr (mu : D.X) : D.P.A.left ⟶ D.P.A.left := (𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A mu).left

theorem tr_hom (mu : D.X) : tr D mu ≫ D.P.A.hom = D.P.A.hom := Over.w _

theorem tr_tr (mu nu : D.X) (h : mu + nu = 0) : tr D mu ≫ tr D nu = 𝟙 _ := by
  have c₃ : SectionScalarValuation.cQ D D.P.A 0 = 1 := by
    have := SectionScalarValuation.cQ_nsmul D D.P.A 0 0
    rwa [zero_nsmul, pow_zero] at this
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ, _root_.mul_assoc, ← SectionScalarValuation.cQ_add, h, c₃,
    _root_.mul_one, Over.id_left]

abbrev EB (k : ℕ) (α mu : D.X) : Type :=
  LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + k • mu)) (fun i => tr D mu ≫ D.famφB α i)) (DegPre.deltaε k))

def Rel {k : ℕ} {α mu : D.X} (e : EB D k α mu) (β : D.SecB k α) (gm : D.SecB k (α + k • mu)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
    sval gm r z J = sval β (r ≫ tr D mu) z J * (val e r z J).val

theorem exists_fwd {k : ℕ} {α mu : D.X} (e : EB D k α mu) (he : e.IsGen) (β : D.SecB k α) : ∃ gm, Rel D e β gm := by
  have hform : FormEq (Sum.elim (fun i => tr D mu ≫ D.famφB α i)
      (Sum.elim (D.famφB (α + k • mu)) (fun i => tr D mu ≫ D.famφB α i)))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.famφB (α + k • mu)) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨gm, hgm⟩ := exists_sec D.P.isLB hform (pullMulSec β (tr D mu) e he)
  exact ⟨gm, fun Z r z J hJ => (hgm Z r z J hJ).trans (sval_pullMulSec _ _ _ he r z hJ)⟩

theorem exists_bwd {k : ℕ} {α mu : D.X} (e : EB D k α mu) (he : e.IsGen) (gm : D.SecB k (α + k • mu)) :
    ∃ β, Rel D e β gm := by
  have h1 : tr D (-mu) ≫ tr D mu = 𝟙 _ := tr_tr D _ _ (neg_add_cancel mu)
  have h2 : tr D mu ≫ tr D (-mu) = 𝟙 _ := tr_tr D _ _ (add_neg_cancel mu)
  have hform : FormEq (Sum.elim (fun i => tr D (-mu) ≫ D.famφB (α + k • mu) i)
      (fun i => tr D (-mu) ≫ Sum.elim (D.famφB (α + k • mu)) (fun i => tr D mu ≫ D.famφB α i) i))
      (Sum.elim (DegPre.famε k) (fun i => - DegPre.deltaε k i)) (D.famφB α) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib, inv_inv,
      ← Category.assoc, h1, Category.id_comp]
    rw [← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  obtain ⟨β, hβ⟩ := exists_sec D.P.isLB hform (pullMulSec gm (tr D (-mu))
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ e (tr D (-mu)))) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ he _)))
  refine ⟨β, fun Z r z J hJ => ?_⟩
  rw [hβ Z _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, val_inv, val_pull hJ, Category.assoc, h2, Category.comp_id,
    _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem isBasisB_move {k : ℕ} {α mu : D.X} (e : EB D k α mu) (he : e.IsGen) {I : Type} [Fintype I]
    (β : I → D.SecB k α) (hβ : IsBasisB D β) (gm : I → D.SecB k (α + k • mu)) (u : Vˣ)
    (h : ∀ i, ∃ g, Rel D e (β i) g ∧ ∀ j, (gm i).f j = constFn D.P.A.hom _ (u : V) * g.f j) : IsBasisB D gm := by
  intro s
  obtain ⟨s₀, hs⟩ := exists_bwd D e he s
  choose g hg hgm using h
  have h1 : tr D (-mu) ≫ tr D mu = 𝟙 _ := tr_tr D _ _ (neg_add_cancel mu)
  have hv : ∀ i (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval (gm i) r z J = cst (r ≫ D.P.A.hom) z (u : V) * (sval (β i) (r ≫ tr D mu) z J * (val e r z J).val) :=
    fun i Z r z J hJ => by
      rw [← hg i Z r z J hJ]
      exact (congrArg (gs r z _) (hgm i _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans
        (congrArg₂ (· * ·) (gs_constFn _ _ r z (hJ.mem _ r) _) rfl))
  have key : ∀ b : I → V, (∀ j, s.f j = ∑ i, constFn D.P.A.hom _ (b i) * (gm i).f j) ↔
      (∀ j, s₀.f j = ∑ i, constFn D.P.A.hom _ (b i * u) * (β i).f j) := fun b => by
    rw [lin_iff D.P.isLB D.P.A.hom b s gm, lin_iff D.P.isLB D.P.A.hom (fun i => b i * u) s₀ β]
    constructor
    · intro H Z r z J hJ
      have e1 := H Z (r ≫ tr D (-mu)) z J hJ
      rw [hs Z _ z J hJ] at e1
      simp only [hv _ Z _ z J hJ, Category.assoc, h1, Category.comp_id, tr_hom] at e1
      refine (val e (r ≫ tr D (-mu)) z J).isUnit.mul_right_cancel (e1.trans ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [H1.cst_mul]; ring
    · intro H Z r z J hJ
      rw [hs Z _ z J hJ, H Z _ z J hJ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [hv _ Z _ z J hJ, H1.cst_mul, Category.assoc, tr_hom]; ring
  obtain ⟨a, ha, hu⟩ := hβ s₀
  refine ⟨fun i => a i * (u⁻¹ : Vˣ), (key _).2 (by simpa using ha), fun b hb => funext fun i => ?_⟩
  rw [← hu _ ((key b).1 hb)]
  simp
end

theorem shift (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    (k : ℕ) (α mu : D.toPre.X) (n : ℕ) (hn : k * Q mu + QForm.bOf D.toPre Q mu α = n) :
    ∃ (e : EB D.toPre k α mu) (u : Vˣ), e.IsGen ∧ ∀ (f : ∀ α, D.toPre.SecB k α) (s : Fam D.toPre (FractionRing V) k),
      FamOf D.toPre _ f s → ∃ g, Rel D.toPre e (f α) g ∧
        ∀ j, (f (α + k • mu)).f j = constFn D.toPre.P.A.hom _ (ϖ ^ n * u) * g.f j := by
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, ⟨u, hc₀⟩, hval⟩ := SectionScalarValuation.famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D.toPre k α mu e' he' hC
  refine ⟨eB, u, heB, fun f s hf => ?_⟩
  obtain ⟨g, hg⟩ := exists_fwd D.toPre eB heB (f α)
  refine ⟨g, hg, GlobalTheory.LevelOneIdeal.secIsMul_of_sval hL D.toPre.P.A.hom
    (IntegralExpansion.prB_app_injective D.toPre) fun y J hJ => ?_⟩
  obtain ⟨⟨w, hw, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing V) hG k mu α
  have vu := hv w hw hc _ (𝟙 _) y J hJ
  have hrel := (secRel_iff hL _ _ _ _ _ _ _ _ _ w).1 (s.fe mu α w hw hc) _ (𝟙 _) y J hJ
  rw [← SectionScalarValuation.secScal_sval (hf _) _ y hJ, ← SectionScalarValuation.secScal_sval (hf _) _ y hJ, Category.id_comp, Category.id_comp,
    SectionScalarValuation.trF_prB] at hrel
  rw [hrel, hg _ _ y J hJ, mul_left_comm]
  congr 1
  have w₁ : (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V) ≫ jK V =
      (DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.P.A.hom :=
    (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre (FractionRing V))).symm
  have v₁ := veB _ (DegPre.prB D.toPre (FractionRing V)) y J hJ
  have v₂ := hval (FractionRing V) _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y J hJ
  have hc₁ : c₀ = algebraMap V (FractionRing V) (ϖ ^ n * u) := by
    rw [hc₀, hn, zpow_natCast, map_mul, map_pow]
  have v₃ : gs ((fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V)) y ⊤ (scal (𝟙 _) c₀) =
      cst ((DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.P.A.hom) y (ϖ ^ n * u) := by
    rw [← w₁, ← Category.assoc, hc₁]
    exact (cst_comp _ (algebraMap V (FractionRing V)) y _).symm
  have v₄ : (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ DegPre.jFR (R := V) (FractionRing V) =
      (DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.P.A.hom := w₁
  rw [v₃, v₄] at v₂
  rw [Over.id_left, Category.id_comp, uVal, Category.id_comp, Category.id_comp, comp_cP] at vu
  rw [vu, v₁]
  simp only [Units.val_mul]
  rw [v₂]
  simp only [SectionScalarValuation.cQ, cP, th]
  ring

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ (i₀ : J) (α : u.D.toPre.X), (∃ m, α = cls i₀ + k • m) → (Short l.q k α → IsBasisB u.D.toPre (fun i : {i // cls i = cls i₀} => f i α)) ∧ (¬ Short l.q k α → ∃ (a : u.V) (β : u.D.toPre.SecB k α), a ∈ IsLocalRing.maximalIdeal u.V ∧ ∀ j, (f i₀ α).f j = constFn u.D.toPre.P.A.hom _ a * β.f j) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ σ cls f ⟨hsh, _, _, _, hfam, _, hB⟩ i₀ α ⟨m, hm⟩
  subst hm
  obtain ⟨ϖ, Q, hϖ, hQ, hlt, hq⟩ := GlobalTheory.ZH.PsiForm.q_eq_val_mul o Ω S ρ p y₀ u l
  have hne : (u.j ϖ : PadicAlgCl p) ≠ 0 := by
    show algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ) ≠ 0
    rw [map_ne_zero, map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))]
    exact hϖ.ne_zero
  have hc : 0 < -Real.log ‖(u.j ϖ : PadicAlgCl p)‖ := neg_pos.2 (Real.log_neg (norm_pos_iff.2 hne) hlt)
  have hle : ∀ a b, l.q a ≤ l.q b ↔ Q a ≤ Q b := fun a b => by
    rw [hq, hq, mul_le_mul_iff_left₀ hc, Int.cast_le]
  have hs := q_shift hϖ hQ (cls i₀) m k
  have h0 := (hle _ _).1 (hsh i₀ m)
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hnn : 0 ≤ k * Q m + QForm.bOf u.D.toPre Q m (cls i₀) :=
    nonneg_of_mul_nonneg_right (a := (k : ℤ)) (by linarith) hk'
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  obtain ⟨e, w, he, H⟩ := shift hLL.1.globalFns hϖ u.D hQ k (cls i₀) m n hn
  rw [hn] at hs
  constructor
  · intro hS
    have h1 := (hle _ _).1 (hS (-m))
    rw [smul_neg, add_neg_cancel_right, hs] at h1
    have hn0 : n = 0 := by
      have : (n : ℤ) ≤ 0 := by nlinarith
      omega
    subst hn0
    refine isBasisB_move u.D.toPre e he _ (hB i₀) _ w fun i => ?_
    obtain ⟨s, hs'⟩ := hfam i.1
    obtain ⟨g, hg, hg'⟩ := H (f i.1) s hs'
    rw [pow_zero, _root_.one_mul] at hg'
    exact ⟨g, hg, hg'⟩
  · intro hS
    obtain ⟨s, hs'⟩ := hfam i₀
    obtain ⟨g, -, hg'⟩ := H (f i₀) s hs'
    refine ⟨_, g, ?_, hg'⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      refine hS fun m' => ?_
      rw [add_assoc, ← smul_add]
      refine le_trans ((hle _ _).2 ?_) (hsh i₀ (m + m'))
      rw [hs]; simp
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hϖ.not_isUnit) n
      (Nat.pos_of_ne_zero hn0))

end GlobalTheory.ZH.Shift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AmpleCubPullAndPullPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.AmpSub

def chartPullPw {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (t : ℤ) :
    ChartPull (AbLaw.pw (L.pull f) t) (AbLaw.pw L t) f where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hJ hJ' := (map_zpow _ _ _).trans
    ((congrArg (· ^ t) ((Geo.Tor.chartPullPull L f f rfl).g y J J' hJ hJ')).trans (map_zpow _ _ _).symm)

theorem hasGen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι)
    (h : ∀ y, f y ∈ L.U i) : MulPull.HasGen L (K := PUnit) (fun _ => f) (fun _ => 1) := by
  have le : ∀ J : PUnit → L.ι, (L.pull f).U J ≤ f ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, h y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (L.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans (gm_rp₁ f y _ _ (le J) hy.1 _)).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (gm_pull_g L f (𝟙 Y) y J J' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_rp₁ f y _ _ (le J') hy.2 _))).trans ?_)))
  rw [Category.id_comp]
  exact gm_cocycle hL f y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (h y)

theorem exists_chart_local {X S : Scheme.{0}} {L : LB X} (hL : L.IsLB) [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (f : S ⟶ X) : ∃ i, ∀ y, f y ∈ L.U i := by
  obtain ⟨i, hi⟩ := exists_chart hL ((S.isoSpec.inv ≫ f) (IsLocalRing.closedPoint Γ(S, ⊤)))
  have e : (S.isoSpec.inv ≫ f) ⁻¹ᵁ L.U i = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 hi
  refine ⟨i, fun y => ?_⟩
  have : S.isoSpec.hom y ∈ (S.isoSpec.inv ≫ f) ⁻¹ᵁ L.U i := by rw [e]; trivial
  have h2 : (S.isoSpec.hom ≫ S.isoSpec.inv ≫ f) y ∈ L.U i := this
  rwa [Iso.hom_inv_id_assoc] at h2

theorem psum_comp {S : Scheme.{0}} {N G : Over S} [GrpObj N] [GrpObj G] (ν : N ⟶ G) [IsMonHom ν]
    {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ N)) (y : Fin n → (T ⟶ G)) (h : T' ⟶ T)
    (e : ∀ k, x k ≫ ν = h ≫ y k) (I : Finset (Fin n)) : psum N x I ≫ ν = h ≫ psum G y I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact (MonObj.one_comp ν).trans (MonObj.comp_one h).symm
  | cons k l ih =>
    exact (MonObj.mul_comp _ _ ν).trans ((congrArg₂ (· * ·) (e k) ih).trans (MonObj.comp_mul h _ _).symm)

theorem ampleCub_pull_and_pullPow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), AmpleCub G L → (∀ (N : Over S) [GrpObj N] (ν : N ⟶ G), IsMonHom ν → IsClosedImmersion ν.left → AmpleCub N (L.pull ν.left)) ∧ (IsLocalRing Γ(S, ⊤) → IsAffine S → ∀ n : ℕ, PullPow ((𝟙 G) ^ n).left L ((n : ℤ) ^ 2)) := by
  intro S G _ _ L ⟨hL, ⟨c, hc⟩, ⟨s, hs⟩, n, hn, ha⟩
  refine ⟨fun N _ ν hν hcl => ⟨pull_isLB hL _, ?_, ?_, n, hn, fun x => ?_⟩, fun _ _ m => ?_⟩
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ (ν ⊗ₘ ν ⊗ₘ ν).left fun I => ?_) c hc
    refine congrArg (fun z => z.left) (psum_comp ν (x3 N) (x3 G) (ν ⊗ₘ ν ⊗ₘ ν) (fun k => ?_) I.down)
    fin_cases k <;> simp [x3]
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ ν.left fun k => ?_) s hs
    fin_cases k
    · exact congrArg (fun z => z.left) (GrpObj.inv_hom ν)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨σ, hx, hσ⟩ := ha (ν.left x)
    have e : Out.nonzeroLocus (chartSec (chartPullPw L ν.left n) σ) = ν.left ⁻¹ᵁ Out.nonzeroLocus σ :=
      nonzeroLocus_chartSec _ σ fun y j hj => ⟨fun _ => j, mem_pull.2 hj⟩
    refine ⟨chartSec (chartPullPw L ν.left n) σ, ?_, ?_⟩ <;> rw [e]
    · exact hx
    · exact hσ.preimage _
  · have hcube : MulPull.HasGen L (thφ G (x3 G)) thε := ⟨c, hc⟩
    have hsym : MulPull.HasGen L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] := ⟨s, hs⟩
    obtain ⟨i, hi⟩ := exists_chart_local (S := S) hL (eSec G)
    have hrig := hasGen_of_chart hL (eSec G) i hi
    have h := MulPull.hasGen_pow hL hcube (𝟙 G) ((hrig.pull (toUnit G).left).of_formEq hL (fun U _ h => by
        simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
          Matrix.cons_val_zero, _root_.mul_one]
        rfl))
      (hsym.inv.of_formEq hL (fun U _ h => by
        rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
        rfl)) m
    refine h.inv.of_formEq hL fun U _ h => ?_
    rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
    rfl

end GlobalTheory.SS.AmpSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionZerosTwistLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem card_torsion_zeros_twist_le :
    Out.Laws → Out.Laws2 → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (c : Out.baseOver (Sp K) ⟶ P.A), 1 ≤ P.g → 4 ≤ N → 1 ≤ d → (k : K) ≠ 0 → ∀ s : LB.Sec (Out.twistLB P.A P.L (N * d) c), (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = 1 ∧ ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s} ≤ N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) :=
  fun h _ => torsion_zero_count_twist h.mulN h.square
    (card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSections
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

namespace GlobalTheory.ZH.ImmProj

theorem exists_closedImmersion_of_immBy : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (m : ℕ) (e : Fin (m + 1) ≃ J), ImmBy p H s Set.univ → ∃ φ : X ⟶ PSpace k m, IsClosedImmersion φ ∧ φ ≫ PSpace.str k m = p ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd (ProjSpace.O1 k m) (ProjSpace.coord k m) (x ≫ φ) (fun i => v (e i)) := by
  intro k _ X p H J s m e ⟨hc, hi⟩
  have hs : ⨆ i, nonzeroLocus (s (e i)) = ⊤ := by
    rw [e.iSup_comp (g := fun j => nonzeroLocus (s j))]
    simpa only [Set.mem_univ, iSup_pos] using hc
  refine ⟨ProjSpace.toProj p (fun i => s (e i)) hs, ?_, ProjSpace.toProj_str _ _ _, ?_⟩
  · refine (ProjSpace.isClosedImmersion_toProj_iff p _ hs).2 fun i => ⟨(hi (e i) trivial).1, ?_⟩
    obtain ⟨r, hr, hcl⟩ := (hi (e i) trivial).2
    obtain rfl : r = fun j => ProjSpace.secRatio (s (e i)) (s j) :=
      funext fun j => ProjSpace.eq_secRatio _ _ (hr j)
    rw [← SpanImm.closure_eq_top_iff, ← hcl]
    congr 2
    exact e.surjective.range_comp (fun j => ProjSpace.secRatio (s (e i)) (s j))
  · intro K _ x v hv
    obtain ⟨i, hx⟩ := Points.exists_le_preimage_of_iSup_eq_top x hs
    have hu := (CrdCalc.crd_isUnit_iff (e i) hv).2 hx
    have hle := (ProjSpace.toProj_preimage_chart p (fun i => s (e i)) hs i).ge
    refine ⟨i, hu.unit, hx.trans (x.preimage_mono hle), fun j => ?_⟩
    have h1 := CrdCalc.crd_ratio (i := e i) (j := e j) hv (ProjSpace.secRatio_spec (s (e i)) (s (e j))) hx
    beta_reduce
    rw [h1, IsUnit.unit_spec, mul_comm, ← ProjSpace.pullRatio_toProj p (fun i => s (e i)) hs i j]
    exact congrArg _ (Points.valR_appLE x _ hle hx _)

end GlobalTheory.ZH.ImmProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIso
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open FrameMove ConstFam ThetaPtMove

theorem exists_frames_move_through {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'}
    {φ : P'.A.left ⟶ P.A.left} {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}
    (gp : IsGrpPullback P'.A P.A f φ) (hw : w.IsGen)
    {rig : LB.Gen (P.L.pull (eSec P.A))} (hrig : rig.IsGen) {I : Type} {x : I → (T ⟶ P.A)} {x' : I → (T' ⟶ P'.A)}
    (hx : ∀ i, (x' i).left ≫ φ = h ≫ (x i).left) {n : ℕ}
    {τ : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (x i).left) (fun _ => 1))}
    (H : ∀ i, IsTorsFrame P rig n (x i) (τ i)) :
    ∃ (rig' : LB.Gen (P'.L.pull (eSec P'.A)))
      (τ' : ∀ i, LB.Gen (LB.LinComb P'.L (Y := T'.left) (K := Fin 1) (fun _ => (x' i).left) (fun _ => 1))),
      rig'.IsGen ∧ GenThrough w (fun _ : PUnit => eSec P'.A) (fun _ : PUnit => eSec P.A) (fun _ => 1) rig' rig f ∧
        ∀ i, IsTorsFrame P' rig' n (x' i) (τ' i) ∧
          GenThrough w (fun _ : Fin 1 => (x' i).left) (fun _ : Fin 1 => (x i).left) (fun _ => 1) (τ' i) (τ i) h := by
  obtain ⟨rig', hrig', Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec P'.A) (φ := fun _ => eSec P.A)
    (ε := fun _ => 1) (h := f) hw P.isLB P'.isLB (fun _ => PolBaseChange.eSec_comm gp) rig hrig
  choose τ' hτ' Hτ using fun i => exists_gen_through (φ' := fun _ : Fin 1 => (x' i).left) (h := h) hw P.isLB P'.isLB
    (fun _ => hx i) (τ i) (H i).2.1
  have ht : ∀ i (z : T'.left) J J', Good P.L z J → Good P'.L z J' →
      val (τ i) h z J = wVal w z J J' (x' i).left * val (τ' i) (𝟙 _) z J' := fun i z J J' hJ hJ' => by
    have := Hτ i _ (𝟙 _) z J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
      rval rig (r ≫ f) z J = wVal w z J J' (r ≫ eSec P'.A) * rval rig' r z J' := fun Z r z J J' hJ hJ' =>
    (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  exact ⟨rig', τ', hrig', Hr, fun i => ⟨isTorsFrame_move gp hw hr (hx i) (H i) (hτ' i) (ht i), Hτ i⟩⟩

theorem exists_frames_on_fibre_through : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ w : LB.Iso u.A.L (ρ.P.L.pull u.φ), w.IsGen → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrAt (x a)), rig.IsGen ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : PUnit => eSec u.A.A) (fun _ : PUnit => eSec ρ.P.A) (fun _ => 1) rig ρ.rig (spMap u.yK) ∧ ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : Fin 1 => (x a).left) (fun _ : Fin 1 => (ρ.pt a).left) (fun _ => 1) (e a) (ρ.fr a) (spMap y₀) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u x hx w hw
  exact exists_frames_move_through (T := baseOver (Sp S.R)) (T' := TFK (R := u.V) (PadicAlgCl p))
    u.cart hw ρ.rig_gen hx ρ.fr_tors

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frames_on_uniformisedModel_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∀ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, LB.Gen (LB.LinComb u.A.L (Y := (TFK (R := u.V) (PadicAlgCl p)).left) (K := Fin 1) (fun _ => (x a).left) (fun _ => 1))), rig.IsGen ∧ (∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a)) ∧ ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))), ∃ t : SecA u.A (PadicAlgCl p) k, ∀ (a : S.Gam) (c : S.R), IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) → ∀ z J, Good u.A.L z J → sA t (ptSecT u.A.A (x a)).left z J = @id ((TFK (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z) (cst (R := u.V) (PadicAlgCl p) z (y₀ c)) * (val (powFrame u.A.A u.A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  first | exact @GlobalTheory.exists_frames_on_fibre | exact GlobalTheory.exists_frames_on_fibre | (intros; apply GlobalTheory.exists_frames_on_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_section_of_baseProduct_section : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), ∃ θ : LB.Sec P.L, (∀ y ∈ nonzeroLocus th, (snd (baseOver (Sp R)) P.A).left y ∈ nonzeroLocus θ) ∧ ∀ (z : baseOver (Sp R) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (a : R), IsValueAt P.A P.L 1 th z τ (fn a) → ∀ (F : Type) [CommRing F] (f : R →+* F) (k : P.L.ι), ⊤ ≤ (spMap f ≫ z.left) ⁻¹ᵁ P.L.U k → valR (spMap f ≫ z.left) _ (θ.f k) = f a * valR (X := (baseOver (Sp R)).left) (spMap f) _ (τ.s (fun _ => k)).val := by
  first | exact @GlobalTheory.UnitTheta.exists_sec_of_baseOver | exact GlobalTheory.UnitTheta.exists_sec_of_baseOver | (intros; apply GlobalTheory.UnitTheta.exists_sec_of_baseOver <;> assumption)
end

