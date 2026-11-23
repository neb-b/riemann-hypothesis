module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0125
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistSections
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ThetaData

theorem valR_eq_gs {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint R) ∈ U) (f : Γ(X, U)) :
    valR x U f = (stalkClosedPointIso (CommRingCat.of R)).hom.hom (gs x (IsLocalRing.closedPoint R) U f) := by
  have h' := (CrdCalc.top_le_iff x U).2 h
  rw [CrdCalc.valR_eq x U h', gs_eq x _ U h]
  have e := germ_stalkClosedPointIso_hom (CommRingCat.of R)
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Sp R).presheaf.map (homOfLE h').op).hom ((x.app U).hom f)) = _
  rw [← e]
  exact congrArg (stalkClosedPointIso (CommRingCat.of R)).hom.hom
    (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE h') _ trivial _)

theorem crd_of_chartSec {R : Type} [CommRing R] [IsLocalRing R] {Y Y' : Scheme.{0}} {A' : LB Y'} {A : LB Y}
    {h : Y' ⟶ Y} (a : ChartPull A' A h) {J : Type} (s : J → A.Sec) (x : Sp R ⟶ Y') (v : J → R)
    (H : Crd A' (fun j => chartSec a (s j)) x v) : Crd A s (x ≫ h) v := by
  obtain ⟨l, c, hl, hv⟩ := H
  have m := (CrdCalc.top_le_iff x _).1 hl
  have m' : (x ≫ h) (IsLocalRing.closedPoint R) ∈ A.U (a.idx l) := a.le l m
  refine ⟨a.idx l, c, (CrdCalc.top_le_iff _ _).2 m', fun j => ?_⟩
  rw [hv, valR_eq_gs x _ m, valR_eq_gs _ _ m', gs_chartSec a (s j) x _ l m]

theorem crd_secPull {R : Type} [CommRing R] [IsLocalRing R] {Y Y' : Scheme.{0}} {A : LB Y}
    (h : Y' ⟶ Y) {J : Type} (s : J → A.Sec) (x : Sp R ⟶ Y') (v : J → R)
    (H : Crd A s (x ≫ h) v) : Crd (A.pull h) (fun j => secPull (s j) h) x v := by
  obtain ⟨l, c, hl, hv⟩ := H
  have m' := (CrdCalc.top_le_iff _ _).1 hl
  have m : x (IsLocalRing.closedPoint R) ∈ (A.pull h).U (fun _ => l) := mem_pull.2 m'
  refine ⟨fun _ => l, c, (CrdCalc.top_le_iff _ _).2 m, fun j => ?_⟩
  rw [hv, valR_eq_gs x _ m, valR_eq_gs _ _ m']
  exact congrArg (fun q => (c : R) * (stalkClosedPointIso (CommRingCat.of R)).hom.hom q)
    (gs_chartSec (GlobalTheory.chartPullPull A h) (s j) x _ (fun _ => l) m).symm

theorem exists_twist_sections {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -1])} (hα : α.IsGen) {J : Type}
    (s : J → LB.Sec (LPow A L a T)) (th : LB.Sec (LPow A L 1 T)) (i₀ : J)
    (H : IsTwistPull A L ψ m hm a 1 α th (s i₀)) {Y : Scheme.{0}} (κ : Y ⟶ (T ⊗ A).left) (F : Y ⟶ A.left)
    (hF : κ ≫ (snd T A).left = F) (n : Y ⟶ Y) (hn : n ≫ κ = κ ≫ ψ.left) :
    ∃ (θ : (L.pull F).Sec) (t : J → ((L.pull F).pull n).Sec),
      (∀ (K : Type) [Field K] (x : Sp K ⟶ Y) (v : J → K), Crd _ t x v → Crd (LPow A L a T) s (x ≫ κ) v) ∧
      ∀ (y : Y) (j : (L.pull F).ι), n y ∈ (L.pull F).U j →
        gs (𝟙 Y) y _ ((t i₀).f (fun _ => j)) = gs n y _ (θ.f j) := by
  have e : κ ≫ m.left = n ≫ F := by
    rw [← hm, Over.comp_left, ← Category.assoc, ← hn, Category.assoc, hF]
  obtain ⟨θ, hθ⟩ := exists_sec hL (φ := fun _ : Fin 1 => F) (ε := fun _ => 1) (φ' := fun _ : PUnit => F)
    (ε' := fun _ => 1) (fun U _ h => by simp)
    (VVRank.pullTo (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => 1) th κ (fun _ => hF))
  have hu := LB.isGen_invGen L _ _ _ (LB.isGen_pullGen L _ _ α hα κ)
  have hσ : ∀ j, ∃ σ : (L.pull (n ≫ F)).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I), Good L z I →
      sval (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) σ r z I =
        VVRank.sv A (s j) (r ≫ κ) z I * ((val α (r ≫ κ) z I)⁻¹).val := by
    intro j
    obtain ⟨σ, hσ⟩ := exists_sec hL (φ' := fun _ : PUnit => n ≫ F) (ε' := fun _ => 1)
      (fun U _ h => by simp [Fintype.prod_sum_type, e])
      (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s j) κ _ hu)
    refine ⟨σ, fun Z r z I hI => (hσ Z r z I hI).trans ((sval_pullMulSec _ κ _ hu r z hI).trans ?_)⟩
    rw [val_inv, val_pull hI]
  choose σ hσ using hσ
  let c := chartPullLinComb L F (fun _ : PUnit => n) (fun _ : PUnit => n ≫ F) (fun _ => 1) (𝟙 Y)
    (fun _ => (Category.id_comp _).symm)
  refine ⟨θ, fun j => chartSec c (σ j), fun K _ x v hv => ?_, fun y j hj => ?_⟩
  · obtain ⟨l, u, hl, hv⟩ := crd_of_chartSec c σ x v hv
    rw [Category.comp_id] at hl hv
    have m₁ := (CrdCalc.top_le_iff _ _).1 hl
    obtain ⟨I, hI, eI⟩ := exists_good L hL (IsLocalRing.closedPoint K : Sp K) (fun _ : PUnit => x ≫ n ≫ F) l
      (fun _ _ _ => rfl) (fun k => Set.mem_iInter.1 m₁ k)
    have m₂ := hI.mem (fun _ : Fin 1 => (snd T A).left) (x ≫ κ)
    refine ⟨fun _ => I ((x ≫ κ) ≫ (snd T A).left), u * Units.map (stalkClosedPointIso (CommRingCat.of K)).hom.hom.toMonoidHom
      (val α (x ≫ κ) _ I)⁻¹, (CrdCalc.top_le_iff _ _).2 m₂, fun j => ?_⟩
    have e₁ := (sval_of (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) (σ j) x _ I l eI).symm.trans (hσ j _ x _ I hI)
    refine (hv j).trans ?_
    refine (congrArg (_ * ·) ((valR_eq_gs x _ m₁ _).trans ((congrArg _ e₁).trans (map_mul _ _ _)))).trans ?_
    rw [Units.val_mul, _root_.mul_assoc, _root_.mul_comm (Units.val (Units.map _ _))]
    exact congrArg (fun q => (u : K) * (q * _)) (valR_eq_gs (x ≫ κ) _ m₂ _).symm
  · have m₁ : (n ≫ F) y ∈ L.U (j PUnit.unit) := mem_pull (F := F).1 hj
    obtain ⟨I, hI, eI⟩ := exists_good L hL y (fun _ : PUnit => n ≫ F) j (fun _ _ _ => rfl) (fun k => m₁)
    refine (gs_chartSec c (σ i₀) (𝟙 Y) y (fun _ => j) (mem_pull (F := n).2 hj)).trans ?_
    have e₁ := (sval_of (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) (σ i₀) (𝟙 Y ≫ 𝟙 Y) y I j
      (fun k => by simpa using eI k)).symm.trans (hσ i₀ _ _ _ I hI)
    have e₂ := (sval_of (φ := fun _ : PUnit => F) (ε := fun _ => 1) θ n y I j eI).symm.trans
      ((hθ _ n y I hI).trans (VVRank.sval_pullTo _ _ _ _ _ hI))
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    rw [VVRank.sv_of_isTwistPull A H _ y hI, mul_right_comm, Units.mul_inv, _root_.one_mul, hn]
    simp only [Category.id_comp]

theorem mulN_eq_id_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem mulN_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (mulN G' n).left ≫ φ = φ ≫ (𝟙 G ^ n : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ 𝟙 G ^ n = pushHom h G' (𝟙 G') ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [← e₂, ← mulN_eq_id_pow] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_iso [ArithBase o Ω] (hLL : GlobalTheory.UT.LL) {S : ThetaSys o Ω} (ρ : S.Real) {B : Scheme.{0}} (A' : Over B)
    [GrpObj A'] [IsCommMonObj A'] [IsIntegral A'.left] {f : B ⟶ Sp S.R} {F : A'.left ⟶ ρ.P.A.left}
    (h : IsGrpPullback A' ρ.P.A f F) {Y : Scheme.{0}} (a : A'.left ⟶ Y) {O : LB Y} (hO : O.IsLB) (st : S.J → O.Sec)
    (hc : ∀ (K : Type) [Field K] (x : Sp K ⟶ A'.left) (v : S.J → K), ρ.Crd (x ≫ F) v → Crd O st (x ≫ a) v) :
    ∃ (θ : (ρ.P.L.pull F).Sec) (w : LB.Iso ((ρ.P.L.pull F).pull (mulN A' (ρ.n ^ ρ.k)).left) (O.pull a)), w.IsGen ∧
      ∀ (x : A'.left) (i : O.ι) (j : (ρ.P.L.pull F).ι), a x ∈ O.U i →
        (mulN A' (ρ.n ^ ρ.k)).left x ∈ (ρ.P.L.pull F).U j →
        gs a x _ ((st ρ.i₀).f i) = gs (𝟙 _) x _ (w.s (fun _ => i, fun _ => j)).val *
          gs (mulN A' (ρ.n ^ ρ.k)).left x _ (θ.f j) := by
  have : IsIso (snd (baseOver (Sp S.R)) ρ.P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom))
  let κ := F ≫ inv (snd (baseOver (Sp S.R)) ρ.P.A).left
  have hκ : κ ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = F := by simp [κ]
  have hn : (mulN A' (ρ.n ^ ρ.k)).left ≫ κ = κ ≫ (mulT ρ.P.A (baseOver (Sp S.R)) (ρ.n ^ ρ.k)).left := by
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, Category.assoc, hκ, mulN_comp h, Category.assoc,
      ← Over.comp_left, mulT, lift_snd, ← hκ, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨θ, t, ht, hθ⟩ := exists_twist_sections ρ.P.A ρ.P.isLB ρ.α_gen ρ.s ρ.th₁ ρ.i₀ ρ.s_zero κ F hκ _ hn
  have hH := LB.isLB_pull (LB.isLB_pull ρ.P.isLB F) (mulN A' (ρ.n ^ ρ.k)).left
  have hcov : ⨆ j, nonzeroLocus (t j) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨K, _, p, hp⟩ := CrdIso.exists_pt y
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists hH t p
    have h₀ := (ThetaSys.Real.immBy_basis hLL o Ω S ρ).1
    have h₁ : (p ≫ κ) (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (ρ.s i) := by
      rw [h₀]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h₁
    obtain ⟨-, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have h₂ := (CrdCalc.crd_isUnit_iff i (ht K p v hv)).2 ((CrdCalc.top_le_iff _ _).2 hi)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hp _).1 ((CrdCalc.crd_isUnit_iff i hv).1 h₂)⟩
  obtain ⟨w, hw, hs⟩ := CrdIso.exists_iso_of_crd _ _ (O.pull a) _ t (fun j => secPull (st j) a) hH
    (LB.isLB_pull hO a) hcov (fun K _ x v hv => crd_secPull a st x v
      (hc K x v ⟨x ≫ κ, by rw [Category.assoc, hκ], ht K x v hv⟩))
  refine ⟨θ, w, hw, fun x i j hi hj => ?_⟩
  have e := hs ρ.i₀ x (fun _ => j) (fun _ => i) (mem_pull.2 hj) (mem_pull.2 hi)
  rw [hθ x j hj] at e
  refine Eq.trans ?_ e
  have e' := gs_chartSec (GlobalTheory.chartPullPull O a) (st ρ.i₀) (𝟙 _) x (fun _ => i) (mem_pull.2 hi)
  rw [Category.id_comp] at e'
  exact e'.symm

theorem exists_theta : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) := by
  intro hLL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have : IsLocallyNoetherian (Sp S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of S.R)))
  have := ex.ab.comm
  have hI : IsIntegral ex.core.A.left := by
    have := ex.core.isIntegral_G
    have := ex.core.isOpenImmersion_a
    have := ex.core.nonempty_A
    exact isIntegral_of_isOpenImmersion ex.core.a
  have : IsIntegral ((Over.pullback Q.u₀).obj ρ.P.A).left := hI
  have h := isGrpPullback_pullback ρ.P.A Q.u₀
  obtain ⟨c⟩ := (hLL.1.cube _ ρ.P ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩ rfl).1
  obtain ⟨hL, hr, ⟨c', -⟩, -⟩ := hLL.2.2.1.cubePull _ _ _ _ (cubeMapOf h) _ c
  obtain ⟨θ, w, hw, hs⟩ := exists_iso hLL ρ _ h ex.a (LB.isLB_pull Q.isLB Q.G.ι) (fun j => secPull (Q.st j) Q.G.ι)
    (fun K _ x v hv => crd_secPull _ _ _ _ (by
      have e := Q.crd K x v hv
      rw [← ex.a_eq] at e
      rw [Category.assoc]
      exact e))
  have hm : IsUnit ((ρ.n ^ ρ.k : ℕ) : Γ(M.Z, ⊤)) := by
    have h₁ : IsUnit ((ρ.n ^ ρ.k : ℕ) : o) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast (ρ.N_eq ▸ Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) S.r)) S.unit
    have h₂ := h₁.map (M.s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rwa [map_natCast] at h₂
  refine ⟨⟨_, c', θ, ρ.n ^ ρ.k, hm, _, LB.isLB_pull Q.isLB Q.G.ι, secPull (Q.st ρ.i₀) Q.G.ι, w, hw, hs,
    fun z hz => ?_⟩, lbIso_refl hL⟩
  obtain ⟨x, hx, hG', e⟩ := _root_.GlobalTheory.ZH.ThetaFibre.exists_mem_nonzeroLocus_fibre hLL o Ω S ρ M U₀ EE hB Q hS hG z hz
  refine ⟨⟨x, hG'⟩, ?_, e⟩
  erw [nonzeroLocus_secPull]
  exact hx

end GlobalTheory.ZH.ThetaData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumOfAdicSumUnitBallExtension
section
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AdicNormSum

open Filter Topology in
private lemma exists_norm_le_mul_of_mem_ideal_smul_fg {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] {_ : Module R C} (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1)
    (hsmul : ∀ (r : R) (y : C), r • y = φ r * y) {N : Submodule R C} (hN : N.FG) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (J : Ideal R) (t : ℝ), 0 ≤ t → (∀ r ∈ J, ‖φ r‖ ≤ t) →
      ∀ y ∈ J • N, ‖y‖ ≤ t * M := by
  obtain ⟨G, rfl⟩ := hN
  have hbound : ∀ y ∈ Submodule.span R (G : Set C), ‖y‖ ≤ (G.sup fun g => ‖g‖₊ : NNReal) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro g hg
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun g => ‖g‖₊) hg)
    · simp
    · intro a b _ _ ha hb
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · intro a b _ hb
      rw [hsmul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb
  refine ⟨(G.sup fun g => ‖g‖₊ : NNReal), NNReal.coe_nonneg _, ?_⟩
  intro J t ht hJ y hy
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr z hz
    rw [hsmul, norm_mul]
    exact mul_le_mul (hJ r hr) (hbound z hz) (norm_nonneg _) ht
  · intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

open Filter Topology in
private lemma exists_uniform_norm_bound_lt_one_of_fg {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1) {I : Ideal R} (hfg : I.FG)
    (hI : ∀ r ∈ I, ‖φ r‖ < 1) : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ r ∈ I, ‖φ r‖ ≤ c := by
  obtain ⟨G, rfl⟩ := hfg
  refine ⟨(G.sup fun g => ‖φ g‖₊ : NNReal), NNReal.coe_nonneg _, ?_, ?_⟩
  · have h : G.sup (fun g => ‖φ g‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro g hg
      have hg' := hI g (Ideal.subset_span hg)
      exact_mod_cast hg'
    exact_mod_cast h
  · intro r hr
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hr
    · intro g hg
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun g => ‖φ g‖₊) hg)
    · simp
    · intro a b _ _ ha hb
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · intro a b _ hb
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb

open Filter Topology in
private lemma hasSum_of_norm_sub_le_geometric {Ix E : Type} [NormedAddCommGroup E]
    {x : Ix → E} {s : E} {c M : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (h : ∀ n : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → ‖s - ∑ i ∈ T, x i‖ ≤ c ^ n * M) :
    HasSum x s := by
  show Tendsto (fun T : Finset Ix => ∑ i ∈ T, x i) atTop (𝓝 s)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hlim : Tendsto (fun n : ℕ => c ^ n * M) atTop (𝓝 (0 * M)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const M
  rw [zero_mul] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨S, hS⟩ := h n
  refine Filter.eventually_atTop.2 ⟨S, fun T hT => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (hS T hT).trans_lt hn

open Filter Topology in
private lemma norm_le_pow_of_mem_ideal_pow {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1) {I : Ideal R} {c : ℝ}
    (hc0 : 0 ≤ c) (hI : ∀ r ∈ I, ‖φ r‖ ≤ c) : ∀ n : ℕ, ∀ r ∈ I ^ n, ‖φ r‖ ≤ c ^ n := by
  intro n
  induction n with
  | zero => intro r _; simpa using hφ r
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih a ha) (hI b hb) (norm_nonneg _) (pow_nonneg hc0 n)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)


open Filter Topology in
theorem _root_.GlobalTheory.Ex.AdicNormSum.main : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (I : Ideal R) (C : Type) [NormedField C] [IsUltrametricDist C]
    [Algebra (FractionRing R) C], _root_.GlobalTheory.Ex.CExt R I C → ∀ (Ix : Type) (x : Ix → C)
    (s : C), _root_.GlobalTheory.UT.SumF I C x s → HasSum x s := by
  intro R _ _ _ I C _ _ _ hC Ix x s hs
  obtain ⟨hle, hlt⟩ := hC
  letI : Module R C := Module.compHom C (algebraMap R (FractionRing R))
  have hs' : _root_.GlobalTheory.UT.SumI I x s := hs
  unfold _root_.GlobalTheory.UT.SumI at hs'
  obtain ⟨N, hNfg, -, -, hconv⟩ := hs'
  let φ : R →+* C := (algebraMap (FractionRing R) C).comp (algebraMap R (FractionRing R))
  have hφ : ∀ r, ‖φ r‖ ≤ 1 := hle
  obtain ⟨M, -, hM⟩ := exists_norm_le_mul_of_mem_ideal_smul_fg (N := N) φ hφ
    (fun r y => Algebra.smul_def (algebraMap R (FractionRing R) r) y) hNfg
  obtain ⟨c, hc0, hc1, hcI⟩ := exists_uniform_norm_bound_lt_one_of_fg φ hφ (IsNoetherian.noetherian I) hlt
  exact hasSum_of_norm_sub_le_geometric hc0 hc1 fun n => (hconv n).imp fun S hS T hT =>
    hM (I ^ n) (c ^ n) (pow_nonneg hc0 n) (norm_le_pow_of_mem_ideal_pow φ hφ hc0 hcI n) _ (hS T hT)

end GlobalTheory.Ex.AdicNormSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelledTorsionValuesAdditiveKernelSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem arcF_values_add_ker_onto : BrGtSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (A : ArcF D R F) (n : ℕ), 0 < n → (∀ a b, A.N.QEq (A.q n a * A.q n b) (A.q n (a + b))) ∧ (∀ a b, A.N.QEq (A.q n a) (A.q n b) ↔ ∃ e, a = b + n • e) ∧ ∀ p, ∃ a, A.N.QEq (A.q n a) p := by
  intro hG E _ _ _ H D R _ _ F _ _ _ A n hn
  obtain ⟨-, -, hadd, -, hQ⟩ := hG R A.D₀ A.even A.bimult F A.N A.ν
  refine ⟨fun a b => ?_, fun a b => ?_, fun q => ?_⟩
  · obtain ⟨p, h₁, h₂, h₃⟩ := A.I.add n hn a b
    obtain ⟨q, hq⟩ := ((hQ n).1 p).exists
    have e : q = A.q n a * A.q n b := by
      refine Subtype.ext (Prod.ext ?_ ((hadd _ _ _ _ _ _ (A.hq n a).2 (A.hq n b).2 hq.2).1 h₂))
      apply Multiplicative.toAdd.injective
      apply A.ν.eX.injective
      rw [hq.1, h₁, ← (A.hq n a).1, ← (A.hq n b).1, ← map_add (f := _)]
      rfl
    rw [← e]
    exact ((hQ n).2.2 _ _ _ _ hq (A.hq n _)).1 h₃
  · rw [← (hQ n).2.2 _ _ _ _ (A.hq n a) (A.hq n b)]
    exact A.I.ker n hn a b
  · obtain ⟨p₀, hp₀⟩ := (hQ n).2.1 q
    obtain ⟨a, ha⟩ := A.I.onto n hn p₀
    exact ⟨a, ((hQ n).2.2 _ _ _ _ (A.hq n a) hp₀).1 ha⟩

end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProperStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_spreads_out_from_genericFibre_proper : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → Flat f → IsProper f → ∀ L₀ : LB X₀, L₀.IsLB → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g → ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') := by
  first | exact @GlobalTheory.GenSpread.lineBundle_spreads_out | exact GlobalTheory.GenSpread.lineBundle_spreads_out | (intros; apply GlobalTheory.GenSpread.lineBundle_spreads_out <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTorusExtensionOfSurjectivePoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem nonempty_torusExtension_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G₁ : Over (Sp k)) [GrpObj G] [GrpObj G₁], SmConn G₁ → Nonempty (TorusExtension G) → ∀ r : G ⟶ G₁, IsMonHom r → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G₁), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ r = y) → Nonempty (TorusExtension G₁) := by
  intro k _ _ G G₁ _ _ hG₁ ⟨E⟩ r hr hsurj
  obtain ⟨X, _, _, _, B₁, _, i₁, q₁, ⟨hi, hq, hfl, hsu, haf, hker, hc, hsm, hsep, hqc, hgc⟩, hno⟩ :=
    MaxTorus.exists_quot_no_cocharacter k G₁ hG₁
  let _ := E.addCommGroup
  let _ := E.free
  let _ := E.finite
  let _ := E.grpB
  have := E.i_hom
  have := E.q_hom
  have hkill : E.i ≫ r ≫ q₁ = 1 := _root_.GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter _ B₁ E.X hno _ inferInstance
  obtain ⟨⟨ψ, -, hψ⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ G E.B B₁ E.q (r ≫ q₁)
    E.q_hom inferInstance E.q_flat E.q_surjective E.q_quasiCompact (fun T x hx => by
      have h := E.isKernel.lift_fst x (toUnit T) hx
      rw [← h, Category.assoc, hkill, MonObj.comp_one])
  have := E.isAbelian.proper
  have : UniversallyClosed (ψ.left ≫ B₁.hom) := by rw [Over.w]; infer_instance
  have : UniversallyClosed ψ.left := .of_comp_of_isSeparated _ B₁.hom
  have := hG₁.2.1
  have : JacobsonSpace G₁.left := LocallyOfFiniteType.jacobsonSpace G₁.hom
  have hZ : IsClosed (q₁.left ⁻¹' Set.range ψ.left) :=
    ψ.left.isClosedMap.isClosed_range.preimage q₁.left.continuous
  let pt : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  have hsub : closedPoints G₁.left ⊆ q₁.left ⁻¹' Set.range ψ.left := by
    intro y hy
    obtain ⟨x, hx⟩ := hsurj (Over.homMk (pointOfClosedPoint (K := k) G₁.hom y hy)
      (pointOfClosedPoint_comp (K := k) G₁.hom y hy))
    have hy' : r.left (x.left pt) = y := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]
      exact pointOfClosedPoint_apply (K := k) G₁.hom y hy pt
    refine ⟨E.q.left (x.left pt), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hψ, Over.comp_left, Scheme.Hom.comp_apply, hy']
  have hall := closure_minimal hsub hZ
  rw [closure_closedPoints] at hall
  have : Surjective ψ.left := ⟨fun b => by
    obtain ⟨g, rfl⟩ := q₁.left.surjective b
    exact hall (Set.mem_univ g)⟩
  have : UniversallyClosed B₁.hom := .of_comp_surjective ψ.left _
  have : IsProper B₁.hom := {}
  exact ⟨{ X := X, B := B₁, isAbelian := ⟨hc, hsm, this, hgc⟩, q := q₁, q_hom := hq, q_flat := hfl,
           q_surjective := hsu, q_quasiCompact := inferInstance, i := i₁, i_hom := hi,
           isKernel := hker }⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Relabel

def TwJ {O : Type} [CommRing O] {N N' : NumD O} {k : ℕ} (β : N.Form k) (u r : Oˣ) (J : NumD.Iso (N.twist β u) N')
    {j : ℕ} (q : N.QT j) (q' : N'.QT j) : Prop :=
  ∃ p : (N.twist β u).QT j, TwRel β u r q p ∧ q'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q'.1.2
section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} {O : Type} [CommRing O] [StarRing O]

def actV (ν : NumOf D F N) (oa : D.P.OAct O) (x : O) (b : N.A) : N.A := ν.eA.symm (ν.eA b ≫ oa.act x)

def RosV (ν : NumOf D F N) (oa : D.P.OAct O) (x : O) (ρ : N.A → N.A → F) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.act (star x)) (oa.act x)) rosatiε), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) ∧
    ∀ b b', ρ b b' = vF u (lift (ν.eA b) (ν.eA b')).left ν.J

def ActCompat [Module O D.X] (ν : NumOf D F N) (oa : D.OAct O) {R' : Type} [CommRing R'] [IsDomain R'] {D' : DegPre R'}
    [Algebra (FractionRing R') F] {N' : NumD F} [Module O D'.X] (ν' : NumOf D' F N') (oa' : D'.OAct O) {k : ℕ}
    (β : N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (N.twist β u) N') : Prop :=
  ∀ j, 0 < j → ∀ (x : O) (p₀ p₁ : QkPt D F j) (p₀' p₁' : QkPt D' F j) q₀ q₁ q₀' q₁', QkAct oa x p₀ p₁ → ν.QPt p₀ q₀ →
    ν.QPt p₁ q₁ → TwJ β u (r j) J q₀ q₀' → TwJ β u (r j) J q₁ q₁' → ν'.QPt p₀' q₀' → ν'.QPt p₁' q₁' →
    QkAct oa' x p₀' p₁'
end
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {K : Type} [Field K]

abbrev FullI (o : Full D K) : Type :=
  letI := H.starRing
  TateIso D K (baseOver (Sp K) ⟶ o.P.A) (fun a g => g ≫ o.oa.act a) (fun n g g' c => WeilIs o.P.A o.P.L n g g' (unitOn c))

def withI (o : Full D K) (I : FullI o) : Full D K := { o with I := I }

end GlobalTheory.Relabel
end
end

