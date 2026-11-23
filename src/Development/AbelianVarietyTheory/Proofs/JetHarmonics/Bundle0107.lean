module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Jets.SurjectiveAppTopSqCube
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPref
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GsSpMapGermAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartHatCoeffBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0106

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartFromPointDatumOfLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartLink

theorem cubical_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (h : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  have e : c.t.s = c'.t.s := by
    refine JetSer.gen_ext_val (φ := thφ G (x3 G)) (ε := thε) L.isLB c.isGen c'.isGen fun y J hJ => ?_
    refine gen_unique L.isLB (G ⊗ G ⊗ G).hom (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left (Over.w _) h c.isGen c'.isGen
      (fun y J hJ => ?_) _ _ y J hJ
    exact ((isCub_cubV c (T := 𝟙_ (Over S)) hJ).face 1 1).trans ((isCub_cubV c' (T := 𝟙_ (Over S)) hJ).face 1 1).symm
  obtain ⟨⟨s⟩, _, _, _, _, _⟩ := c
  obtain ⟨⟨s'⟩, _, _, _, _, _⟩ := c'
  obtain rfl : s = s' := e
  rfl

theorem surjective_of_sq {S : Scheme.{0}} {G : Over S} (h : Function.Surjective (G ⊗ G).hom.appTop.hom) :
    Function.Surjective G.hom.appTop.hom := by
  intro f
  obtain ⟨a, ha⟩ := h ((fst G G).left.appTop.hom f)
  refine ⟨a, ?_⟩
  have e₁ : (lift (𝟙 G) (𝟙 G)).left ≫ (G ⊗ G).hom = G.hom := Over.w _
  have e₂ : (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 G) (𝟙 G))
  have := congrArg (lift (𝟙 G) (𝟙 G)).left.appTop.hom ha
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, e₁, e₂] at this
  simpa using this

theorem psJet_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (g : MvPowerSeries κ R) : psJet m (MvPowerSeries.map f g) = jetCoef f κ m (psJet m g) := by
  unfold psJet jetCoef
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
  congr 1
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem germA_comb {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {κ : Type} [Fintype κ] [DecidableEq κ] (z : JetPts G κ) (τ : Frames U.LG.L z) (hτ : τ.Gen)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ)
    {l : ℕ} (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (g : Fin l → MvPowerSeries κ V)
    (hσ : ∀ i m (y : Sp (Jet V κ m)) J, Good U.LG.L y J →
      sval (σ i) (z m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m (g i))) * (val (τ m) (𝟙 _) y J ^ q).val)
    (σ' : U.SecGF F q)
    (hlin : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (q : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (q : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i))) :
    GermA U z τ F q σ' (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)) := by
  intro m
  have hL := U.LG.isLB
  have key : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
      sval (σ i) (r ≫ (z m).left) y J = cst r y (psJet m (g i)) * (val (τ m) r y J ^ q).val := by
    intro i
    obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet V κ m) hL (σ i) (z m).left
      (GeneratorPullback.powGen U.LG.L _ _ (τ m) q) (powGen_isGen_of_isGen _ (hτ m) q)
      (fun W _ h => by simp only [Category.comp_id, _root_.mul_one])
    have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
        sval (σ i) (r ≫ (z m).left) y J = cst r y v * (val (τ m) r y J ^ q).val := fun Z r y J hJ =>
      (hv Z r y J hJ).trans (congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _))
    obtain rfl : v = psJet m (g i) := H1.cst_ext fun y => by
      obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
      have e := hv' _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e
      exact (Units.mul_left_inj _).1 (e.symm.trans (hσ i m y J hJ))
    exact hv'
  obtain ⟨a, a₁, a₂⟩ := GermBasic.exists_jetPt (F := F) z m
  refine ⟨a, a₁, a₂, fun y J hJ => ?_⟩
  refine (BoxExpansion.secLin_val hlin a y hJ).trans ?_
  have e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)))) =
      ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) *
        cst (𝟙 _) y (psJet m (MvPowerSeries.map (algebraMap V F) (g i))) := by
    refine (congrArg (cst (𝟙 _) y) (GermBasic.psJet_sum m c _)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)
    exact Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a₂, key i _ _ y J hJ, _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ rfl)
  · refine (gs_pull a _ y ⊤ trivial _).trans ?_
    rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
    rfl
  · rw [psJet_map, ← ExpansionValueZero.cst_comp, Category.id_comp]

theorem exists_chartData {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {V : Type} [CommRing V]
    [IsLocalRing V] (t : SAB H (Sp V)) (Lr : RigLB t.G) (h : Lr = t.PP) (c : CubicalStr t.G Lr)
    (s₂ : Function.Surjective (t.G ⊗ t.G).hom.appTop.hom)
    (s₃ : Function.Surjective (t.G ⊗ t.G ⊗ t.G).hom.appTop.hom) :
    letI := H.starRing
    ∀ (d : ℕ) (BT : FB V d (𝓞 E)) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
      (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
      IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
      IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT →
      IsUnivJ t.G (Fin 1 × Fin d) xT → FrTrunc t (𝟙 (Sp V)) d xT eT →
    ∀ τ : Frames Lr.L (κ := Fin 1 × Fin d) xT,
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
        Good Lr.L y J → val (τ m) (𝟙 _) y J =
          val (genCast (congrArg RigLB.L h).symm _ _ (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m)) (𝟙 _) y J) →
    ∃ (x : JetSer.Fam t.G (Fin d)) (j : Lr.L.ι)
      (u : ∀ a : 𝓞 E, LB.Gen (LB.LinComb Lr.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε))
      (B : FB V d (𝓞 E)) (ρ : LB.Gen (LB.LinComb Lr.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (ε : PS V 2 d),
      Chart.IsUnivChart t.G d x ∧ ⊤ ≤ η[t.G].left ⁻¹ᵁ Lr.L.U j ∧ (∀ a, JetSer.IsNormRos Lr.L _ _ (u a)) ∧
      JetSer.IsFBOf Lr c t.act u x j B ∧ ρ.IsGen ∧ JetSer.Related B BT (pt V (n := 1) d 0) (pt V (n := 1) d 0) ε ∧
      ∀ (q : ℕ) (σ : H0 Lr.L q) (r S g : PS V 1 d), JetSer.IsSer1 x _ (ρ.s (fun _ => j)).val r →
        JetSer.IsSer1 x _ (σ.f (fun _ => j)) S → g * (diagSer BT H.w0 ε * r) ^ q = S →
        ∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
          Good Lr.L y J →
          sval σ (xT m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (τ m) (𝟙 _) y J ^ q).val := by
  subst h
  obtain rfl : c = t.cub := cubical_eq s₃ _ _
  letI := H.starRing
  intro d BT tg xT eT wPT hC hF hW hU hT τ hEL
  obtain ⟨x, hx, hM⟩ := univConv V t.G _ xT hU d (oneCol d)
  obtain ⟨j, hj⟩ := JetSer.exists_index_of_local t.PP.L t.PP.isLB η[t.G].left
  have hu : ∀ a : 𝓞 E, ∃ u, JetSer.IsNormRos t.PP.L (t.act.act a) (t.act.act (star a)) u := fun a => by
    have := t.act.hom a
    have := t.act.hom (star a)
    exact (NormRos.normRos_of_lbIso _ t.G t.PP.L t.PP.isLB _ _ (t.adj a)).1
  choose u hu using hu
  obtain ⟨B, hB⟩ := JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.1 V t.G s₂ s₃ t.PP t.cub (𝓞 E) t.act u hu d x hx j hj
  have := t.act.hom H.w0
  obtain ⟨ρ, hρ, hρc⟩ := (JetSer.exists_unique_normPrim _ t.G t.PP (t.act.act H.w0) t.prim).1
  obtain ⟨ε, hε⟩ := _root_.GlobalTheory.LinkEps.linkEps E H V t d _ _ _ _ _ _ tg xT eT wPT hC hF hW hT j hj
  refine ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ,
    LinkRel.linkRel E H V t s₂ d BT tg xT eT wPT hC hF hW x hx hM j hj u hu B hB ε hε,
    fun q σ r S g hr hS hg m y J hJ => ?_⟩
  rw [hEL m y J hJ]
  exact LinkSec.linkSec E H V t (surjective_of_sq s₂) d BT tg xT eT wPT hC hF hW x hx hM j hj ρ hρ hρc ε hε q σ r S g
    hr hS hg m y J hJ

theorem isUnit_diagSer {V : Type} [CommRing V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B B' : FB V d O}
    {φ φi : Pt V 1 d} {ε : PS V 2 d} (h : JetSer.Related B B' φ φi ε) (w0 : O) : IsUnit (diagSer B' w0 ε) := by
  have e₀ : MvPowerSeries.constantCoeff ε = 1 := by
    rw [← GaugeAdjoint.constantCoeff_ev (a := ![0, pt V (n := 1) d 0]) (fun j i => by fin_cases j <;> simp [pt]) ε,
      h.ax0, map_one]
  have c : comp1 (B'.A.act w0) (pt V (n := 1) d 0) = B'.A.act w0 := funext fun i => LinkSec.ev_pt_one _
  rw [MvPowerSeries.isUnit_iff_constantCoeff, diagSer, c, GaugeAdjoint.constantCoeff_ev (fun j i => ?_) ε, e₀]
  · exact isUnit_one
  · fin_cases j
    · simp [pt]
    · exact B'.A.const w0 i

theorem linkSt_holds : LinkSt := by
  intro E _ _ _ H V _ _ _ hc t P tors ϖ hϖ Q hQ F _ _ _ _ v hv d BT tg xT eT wPT hC hF hW hU hT τ hτ hEL
  letI := H.starRing
  obtain ⟨s₂, s₃⟩ := FamGerm.surjective_appTop_sq_cube P.U.toUnifPre
  obtain ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ, hR, hS⟩ := exists_chartData H t P.U.LG P.bundle P.U.cubG s₂ s₃
    d BT tg xT eT wPT hC hF hW hU hT τ hEL
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hR, ?_⟩
  rintro q s f f' ⟨l, c, σ, fi, g, r, h₁, h₂, h₃, h₄, h₅⟩ hf
  obtain ⟨w, hw⟩ := (isUnit_diagSer hR H.w0).exists_right_inv
  obtain ⟨σ', hσ'⟩ := BoxExpansion.exists_secLin P.U.LG.isLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left (UnifPre.gFK (R := V) (G := t.G) F)
    (fun _ : Fin 1 => UnifPre.gFK (R := V) (G := t.G) F) (fun _ => (Category.comp_id _).symm) σ c
  refine ⟨σ', ⟨l, c, σ, fi, h₁, hσ', h₂⟩, ?_⟩
  have eV : TWO.algVF (V := V) (F := F) = algebraMap V F := (IsScalarTower.algebraMap_eq V _ F).symm
  have e : f' = ∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i * w ^ q) := by
    have e₁ : f' = f * MvPowerSeries.map (algebraMap V F) (w ^ q) := by
      rw [← hf, _root_.mul_assoc, ← map_pow, ← map_mul, ← mul_pow, hw, one_pow, map_one, _root_.mul_one]
    rw [e₁, h₅, Finset.sum_mul, eV]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPowerSeries.smul_eq_C_mul, _root_.mul_assoc]
  rw [e]
  refine germA_comb P.U.toUnifPre xT τ hτ F q c σ _ (fun i m y J hJ => ?_) σ' hσ'
  obtain ⟨S, hS₁, hS₂⟩ := h₄ i
  refine hS q (σ i) r S _ h₃ hS₁ ?_ m y J hJ
  rw [← hS₂, _root_.mul_assoc, ← mul_pow, ← _root_.mul_assoc, _root_.mul_comm w, hw, _root_.one_mul]

theorem link : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → LinkSt := fun _ _ _ _ => linkSt_holds

end GlobalTheory.ChartLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesTranslateNormLe
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TransNorm

variable {q : ℕ} [Fact q.Prime]

lemma bd_add {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) (hg : Bd B g) : Bd B (f + g) := by
  simpa using ((sup_norm_laws q).1 f g B B hf hg).1

lemma bd_mul_one {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) (hg : Bd 1 g) : Bd B (f * g) := by
  simpa using ((sup_norm_laws q).1 f g B 1 hf hg).2

lemma bd_C {a : ℂ_[q]} {B : ℝ} (ha : ‖a‖ ≤ B) : Bd B (C a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · simpa using (norm_nonneg a).trans ha

lemma bd_one : Bd 1 (1 : ℂ_[q]⟦X⟧) := by
  simpa using (bd_C (a := (1 : ℂ_[q])) (B := 1) (by simp))

lemma bd_X : Bd 1 (X : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_X]
  split_ifs <;> simp

lemma bd_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero => simpa using bd_one
  | succ n ih => rw [pow_succ]; exact bd_mul_one ih hf

lemma bd_sum {α : Type} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, Bd B (f i)) : Bd B (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (Bd B) (fun _ _ => bd_add) ?_ hf
  intro n
  simpa using hB

lemma bd_prod {α : Type} (s : Finset α) (f : α → ℂ_[q]⟦X⟧)
    (hf : ∀ i ∈ s, Bd 1 (f i)) : Bd 1 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (Bd 1) (fun _ _ => bd_mul_one) bd_one hf

lemma bd_sub_C {f : ℂ_[q]⟦X⟧} {a : ℂ_[q]} (hf : Bd 1 f) (ha : ‖a‖ ≤ 1) : Bd 1 (f - C a) := by
  have := bd_add hf (bd_C (a := -a) (by simpa using ha))
  simpa [sub_eq_add_neg] using this

lemma bd_cancel {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bdd f) (hg : Bd 1 g)
    (hg' : ∀ r : ℝ, r < 1 → ∃ n, r < ‖coeff n g‖) (h : Bd B (f * g)) : Bd B f := by
  intro i
  have key := (sup_norm_laws q).2.2.2.1 f g B hf ⟨1, hg⟩ h i
  by_contra hlt
  push Not at hlt
  have hB : 0 ≤ B := (norm_nonneg _).trans (h 0)
  have hpos : 0 < ‖coeff i f‖ := hB.trans_lt hlt
  obtain ⟨n, hn⟩ := hg' (B / ‖coeff i f‖) ((div_lt_one hpos).2 hlt)
  have := key n
  rw [div_lt_iff₀ hpos] at hn
  nlinarith

lemma bd_cancel_prod {α : Type} (s : Finset α) (g : α → ℂ_[q]⟦X⟧) {B : ℝ}
    (hg : ∀ i, Bd 1 (g i)) (hg' : ∀ i, ∀ r : ℝ, r < 1 → ∃ n, r < ‖coeff n (g i)‖)
    {f : ℂ_[q]⟦X⟧} (hf : Bdd f) (h : Bd B (f * ∏ i ∈ s, g i)) : Bd B f := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    apply ih
    rw [Finset.prod_insert ha, mul_comm (g a), ← mul_assoc] at h
    obtain ⟨C, hC⟩ := hf
    exact bd_cancel ⟨C, bd_mul_one hC (bd_prod s g fun i _ => hg i)⟩ (hg a) (hg' a) h

lemma analyticAt_eval (p : Polynomial ℂ) {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (fun z => p.eval (F z)) z := by
  simp only [Polynomial.eval_eq_sum_range]
  exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (hF.pow i)

lemma hat_eval (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) (p : Polynomial ℂ)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    hat ι ℓ (fun z => p.eval (F z)) =
      p.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (ι : ℂ →+* ℂ_[q])) (hat ι ℓ F) := by
  obtain ⟨h1, h2, -⟩ := TaylorRead.hat_laws q ι ℓ hℓ
  induction p using Polynomial.induction_on with
  | C a => simpa using h2 a
  | add p r hp hr =>
    simp only [Polynomial.eval_add, Polynomial.eval₂_add]
    rw [(h1 _ _ (analyticAt_eval p hF) (analyticAt_eval r hF)).1, hp, hr]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc]
    simp only [Polynomial.eval_mul (q := Polynomial.X), Polynomial.eval_X, Polynomial.eval₂_mul_X]
    rw [(h1 _ _ (analyticAt_eval _ hF) hF).2.1, ih]

lemma bd_eval₂ (ι : ℂ ≃+* ℂ_[q]) (p : Polynomial ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ i ≤ p.natDegree, ‖ι (p.coeff i)‖ ≤ B) {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) :
    Bd B (p.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (ι : ℂ →+* ℂ_[q])) f) := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine bd_sum _ _ hB fun i hi => bd_mul_one (bd_C ?_) (bd_pow hf i)
  exact hp i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

lemma norm_coeff_prod (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (a : Fin m → ℂ) (ha : ∀ i, ‖ι (a i)‖ ≤ 1) (n : ℕ) :
    ‖ι ((∏ i, (Polynomial.X - Polynomial.C (a i))).coeff n)‖ ≤ 1 := by
  have h : Bd 1 (∏ i, (X - C (ι (a i)) : ℂ_[q]⟦X⟧)) :=
    bd_prod _ _ fun i _ => bd_sub_C bd_X (ha i)
  have e : (∏ i, (X - C (ι (a i)) : ℂ_[q]⟦X⟧)) =
      Polynomial.coeToPowerSeries.ringHom
        ((∏ i, (Polynomial.X - Polynomial.C (a i))).map (ι : ℂ →+* ℂ_[q])) := by
    simp [Polynomial.map_prod, map_prod]
  have := h n
  rw [e] at this
  simpa only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, Polynomial.coeff_map, RingHom.coe_coe] using this

lemma analyticAt_x_of_not_mem_lattice (M : Mdl q) {t : ℂ} (ht : t ∉ M.L.lattice) : AnalyticAt ℂ M.x t := by
  have := M.L.analyticOnNhd_weierstrassP t ht
  unfold Mdl.x
  fun_prop

lemma analyticAt_y (M : Mdl q) {t : ℂ} (ht : t ∉ M.L.lattice) : AnalyticAt ℂ M.y t := by
  have := M.L.analyticOnNhd_derivWeierstrassP t ht
  have := analyticAt_x_of_not_mem_lattice M ht
  unfold Mdl.y
  fun_prop

lemma analyticAt_shift {F : ℂ → ℂ} {t : ℂ} (hF : AnalyticAt ℂ F t) :
    AnalyticAt ℂ (fun z => F (z + t)) 0 :=
  AnalyticAt.comp_of_eq (g := F) (f := fun z => z + t) hF (by fun_prop) (by simp)

theorem translate_norm_le : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ) (t : ℂ) (B : ℝ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → AnalyticAt ℂ φ t → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → ¬ M.Small t → Bdd (hat M.ι ℓ (fun z => φ (z + t))) → Bd B (hat M.ι ℓ φ) → Bd B (hat M.ι ℓ (fun z => φ (z + t))) := by
  intro q _ M ℓ φ t B hc hE h0 ht hpole hts hbdd hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hℓ := hc.2.1
  obtain ⟨hl1, hl2, -⟩ := TaylorRead.hat_laws q M.ι ℓ hℓ
  obtain ⟨m, P, A, B', hP, hid⟩ := GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy q M φ hc.1 hE
  have hPx : ∀ i, ‖M.ι (M.x (P i))‖ ≤ 1 := fun i =>
    not_lt.1 fun h => hpole _ (hP i).2 (Or.inr h)
  obtain ⟨-, v, xs, ys, -, hxs, hys, -, hxs0, hys0, -, -, -, hread⟩ := _root_.GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ hc
  set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD
  set k := max A.natDegree B'.natDegree with hk
  have e0 := hread φ A B' k h0 (le_max_left _ _) (le_max_right _ _) (fun _ => 1) analyticAt_const
    D D.natDegree le_rfl (by simpa only [one_mul] using hid 0)
  have hS : Bd B (∑ i ∈ Finset.range (k + 1),
      (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * xs ^ i +
        C (M.ι (B'.coeff i)) * X ^ (2 * (k - i)) * xs ^ i * ys)) := by
    refine (sup_norm_laws q).2.2.2.2.2 _ 1 (2 * D.natDegree) B bd_one (by simp) ?_
    rw [hl2, map_one, map_one, one_mul] at e0
    rw [mul_one, ← e0]
    refine bd_mul_one (bd_mul_one hB (bd_pow bd_X _)) (bd_sum _ _ zero_le_one fun i _ => ?_)
    exact bd_mul_one (bd_mul_one (bd_C (norm_coeff_prod M.ι _ hPx i)) (bd_pow bd_X _)) (bd_pow hxs _)
  have hco := Triang.coeff_norm_le q xs ys k (fun i => M.ι (A.coeff i)) (fun i => M.ι (B'.coeff i)) B
    hxs hys hxs0 hys0 hS
  obtain ⟨hxt, hyt, hbig⟩ := _root_.GlobalTheory.MomOne.Transl.translate_integral q M ℓ t hc hts
  have htl : t ∉ M.L.lattice := fun h => hts (Or.inl h)
  have ax := analyticAt_shift (analyticAt_x_of_not_mem_lattice M htl)
  have ay := analyticAt_shift (analyticAt_y M htl)
  have aφ := analyticAt_shift ht
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), φ (z + t) * D.eval (M.x (z + t)) =
      A.eval (M.x (z + t)) + B'.eval (M.x (z + t)) * M.y (z + t) := by
    have tt : Filter.Tendsto (fun z : ℂ => z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Filter.Tendsto (fun z : ℂ => z + t) (𝓝 0) (𝓝 (0 + t)) :=
          (continuous_id.add continuous_const).tendsto 0
        rw [zero_add] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    exact tt.eventually (hid t)
  have e1 := (hl1 _ _ (aφ.mul (analyticAt_eval D ax))
    ((analyticAt_eval A ax).add ((analyticAt_eval B' ax).mul ay))).2.2.1 hev
  have e2 := (hl1 _ _ aφ (analyticAt_eval D ax)).2.1
  have e3 := (hl1 _ _ (analyticAt_eval A ax) ((analyticAt_eval B' ax).mul ay)).1
  have e4 := (hl1 _ _ (analyticAt_eval B' ax) ay).2.1
  have e5 : hat M.ι ℓ (fun z => φ (z + t)) * hat M.ι ℓ (fun z => D.eval (M.x (z + t))) =
      hat M.ι ℓ (fun z => A.eval (M.x (z + t))) +
        hat M.ι ℓ (fun z => B'.eval (M.x (z + t))) * hat M.ι ℓ (fun z => M.y (z + t)) := by
    rw [← e2, ← e4]
    exact e1.trans e3
  rw [hat_eval _ _ hℓ D ax, hat_eval _ _ hℓ A ax, hat_eval _ _ hℓ B' ax] at e5
  have e6 : D.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (M.ι : ℂ →+* ℂ_[q]))
      (hat M.ι ℓ (fun z => M.x (z + t))) =
      ∏ i, (hat M.ι ℓ (fun z => M.x (z + t)) - C (M.ι (M.x (P i)))) := by
    rw [hD, Polynomial.eval₂_finsetProd]
    simp
  rw [e6] at e5
  refine bd_cancel_prod Finset.univ _ (fun i => bd_sub_C hxt (hPx i)) (fun i r hr => ?_) hbdd ?_
  · obtain ⟨n, hn, hn'⟩ := hbig r hr
    refine ⟨n, ?_⟩
    rwa [map_sub, coeff_C, if_neg hn.ne', sub_zero]
  · rw [e5]
    exact bd_add (bd_eval₂ _ _ hB0 (fun i hi => (hco i (hi.trans (le_max_left _ _))).1) hxt)
      (bd_mul_one (bd_eval₂ _ _ hB0 (fun i hi => (hco i (hi.trans (le_max_right _ _))).2) hxt) hyt)

end GlobalTheory.MomOne.TransNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DescentOneGenerator
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.OneGenerator

theorem transport_level {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
    (P : PELUnif (maximalIdeal V) t) {F : Type} [Field F] [Algebra (FractionRing V) F] {n m : ℕ} (h : n = m)
    (θ r₀ r : Fam P.D.toPre F n) (p : QkPt P.D.toPre F n)
    (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε n))) (ζ : F)
    (x : TFK (R := V) F ⟶ P.A.A) (hx : P.ToA F n p x) (hw : w.IsGen) (hf : FinOrd P.D F n p w ζ)
    (hΦ : PhiRel P.D.toPre F n p w θ r₀) (hs : Fam.IsSmul P.D.toPre F ζ r₀ r) :
    ∃ (θ' r₀' r' : Fam P.D.toPre F m) (p' : QkPt P.D.toPre F m)
      (w' : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p'.g.b) (DegPre.lineε m))),
      HEq θ θ' ∧ P.ToA F m p' x ∧ w'.IsGen ∧ FinOrd P.D F m p' w' ζ ∧ PhiRel P.D.toPre F m p' w' θ' r₀' ∧
        Fam.IsSmul P.D.toPre F ζ r₀' r' ∧ HEq r r' := by
  subst h
  exact ⟨θ, r₀, r, p, w, HEq.rfl, hx, hw, hf, hΦ, hs, HEq.rfl⟩

end GlobalTheory.OneGenerator

namespace GlobalTheory


open OneGenerator in
theorem descent_one_generator : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → letI := H.starRing; ∀ (a a' : 𝓞 E) (g g' : ℕ), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' → a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1) (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα → ∀ (pb : QkPt P.D.toPre F (1 * g')) (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g')))) (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')), P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 → FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ → Fam.IsSmul P.D.toPre F ζb tb₀ tb → ∀ (p : QkPt P.D.toPre F (1 * g' * g)) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * g' * g)))) (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (1 * g' * g) p w ζ → P.ToA F (1 * g' * g) p x → x ≫ P.oA.act (star a) = 1 → ∀ (s₂ t₀ r : Fam P.D.toPre F (1 * g' * g)), PullAl P.D F P.oD a (1 * g') g tb s₂ → PhiRel P.D.toPre F (1 * g' * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r → ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g))) (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g))))) (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))), PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  intro hL _ _ _ V _ _ _ _ E _ _ _ H t P hT
  letI := H.starRing
  intro a a' g g' hg hg' hco haa haa' F _ _ _ θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
    p w ζ x hw hζ hf hx hxa s₂ t₀ r hs₂ hΦ hr
  have hk : 1 ≤ 1 * g' := by omega
  have hkN : 1 ≤ 1 * g' * g := Nat.mul_pos hk hg
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a g (1 * g') hg hk haa
  have key : ∃ (p₂ : QkPt P.D.toPre F (1 * g' * g))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * g' * g))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ : Fam P.D.toPre F (1 * g' * g)),
      P.ToA F (1 * g' * g) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a' * a)) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧
        FinOrd P.D F (1 * g' * g) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * g' * g) p₂ w₂ (π θα) r₀ ∧
        Fam.IsSmul P.D.toPre F ζ₂ r₀ r := by
    by_cases h0 : θα = 0
    · obtain ⟨Φ, hΦ'⟩ := phiFun_of hL V _ P.D F (1 * g') hk pb wb hwb
      have e₀ : tb = 0 := by
        rw [(DVR.isSmul_iff _ _ _).1 hsb, (hΦ' _ _).1 hΦb, h0, map_zero, smul_zero]
      have e₁ : s₂ = π θα := by rw [(hπ _ _).1 hs₂, e₀, h0]
      refine ⟨p, w, ζ, x, t₀, hx, ?_, hw, hζ, hf, e₁ ▸ hΦ, hr⟩
      have := P.oA.hom (star a')
      rw [star_mul', P.oA.map_mul, ← Category.assoc, hxa, MonObj.one_comp]
    · obtain ⟨p₂, x₂, w₂, ζ₂, t₂, k₁, k₂, k₃, k₄, k₅⟩ := operator_on_pullback_eq_sum hL E H V t P hT a a' g g'
        hg hg' hco haa haa' F θα tb (π θα) s₂ t₀ r h0 ((hπ _ _).2 rfl) hs₂ 1 (fun _ => 1) (fun _ => pb)
        (fun _ => xb) (fun _ => wb) (fun _ => ζb) (fun _ => tb)
        ⟨fun _ => hxb, fun _ => hxba, fun _ => ⟨hwb, hζb, hfb⟩, fun _ => ⟨tb₀, hΦb, hsb⟩, by simp⟩
        p x w ζ hx hxa hw hζ hf hΦ hr
      obtain ⟨r₀, l₁, l₂⟩ := k₄ 0
      have e : r = t₂ 0 := by simpa using k₅
      exact ⟨p₂ 0, w₂ 0, ζ₂ 0, x₂ 0, r₀, k₁ 0, k₂ 0, (k₃ 0).1, (k₃ 0).2.1, (k₃ 0).2.2, l₁, e ▸ l₂⟩
  obtain ⟨p₂, w₂, ζ₂, x₂, r₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ := key
  obtain ⟨θ', r₀', r', p', w', m₁, m₂, m₃, m₄, m₅, m₆, m₇⟩ :=
    transport_level P (Nat.mul_assoc 1 g' g) (π θα) r₀ r p₂ w₂ ζ₂ x₂ k₁ k₃ k₅ k₆ k₇
  have hc := pullAl_comp hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a a' g g' 1 hg hg' le_rfl haa haa' θ θα (π θα) θ' hθ
    ((hπ _ _).2 rfl) m₁
  rw [_root_.mul_comm a' a] at hc k₂
  exact ⟨θ', p', w', ζ₂, x₂, r₀', r', hc, m₂, k₂, m₃, k₄, m₄, m₅, m₆, m₇⟩

end GlobalTheory
end
end

