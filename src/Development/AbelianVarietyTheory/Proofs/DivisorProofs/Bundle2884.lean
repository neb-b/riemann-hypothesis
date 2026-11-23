module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjTensorPowerIntMatrixEndomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataA
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensAct

theorem exists_integer_ring_action_on_tensor_degeneration_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) ∧ (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) := by
  intro R _ _ _ hR E _ _ _ H D D' r W hpos hdet T ρ hρ hw
  letI := H.starRing
  letI md : Module (𝓞 E) D'.toPre.X := tensModule T ρ
  let oB : D'.toPre.P.OAct (𝓞 E) :=
    { ringAct T ρ with rosati := fun a ↦ _root_.GlobalTheory.TensAct.rosatiAdj_matAct R D.toPre D'.toPre W T (ρ a) (ρ (star a)) (hρ a) }
  let o : D'.toPre.OAct (𝓞 E) :=
    { onB := oB
      c_lin := fun a y ↦ c_lin T (ρ a) y
      tau_bal := fun a ↦ _root_.GlobalTheory.TensBal.tauBal_tens R _ D D' W T (ρ a) (ρ (star a)) (hρ a) }
  exact ⟨md, o, ⟨fun a z i ↦ xe_latAct T (ρ a) z i, fun a i ↦ matAct_pr T (ρ a) i⟩,
    _root_.GlobalTheory.TensPsi.tensorData_symmetric_pullback_and_psi_eq_tau R _ D D' W T (ρ H.w0) (𝓞 E) o H.w0 rfl (fun y ↦ rfl) hw⟩

end GlobalTheory.TensAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.AbLevel

theorem torsRat_of_isGrpPullback {R O : Type} [CommRing R] [IsDomain R] [CommRing O] [IsDomain O] (ρ : R →+* O)
    (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {A : Over (Sp O)} [GrpObj A] {π : A.left ⟶ G.left}
    (hπ : IsGrpPullback A G (spMap ρ) π) {n : ℕ} (h : TorsRat G n) : TorsRat A n := by
  intro K _ _ κ x hx
  have hj : Function.Injective ((algebraMap O (FractionRing O)).comp ρ) :=
    (IsFractionRing.injective O (FractionRing O)).comp hρ
  let i : FractionRing R →+* FractionRing O := IsFractionRing.lift hj
  have hsq : spMap i ≫ jK R = jK O ≫ spMap ρ := by
    show spMap i ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap O (FractionRing O)) ≫ spMap ρ
    rw [← spMap_comp, ← spMap_comp]
    have hi : ∀ r, i (algebraMap R (FractionRing R) r) = algebraMap O (FractionRing O) (ρ r) := fun r =>
      IsFractionRing.lift_algebraMap (K := FractionRing R) hj r
    exact congrArg spMap (RingHom.ext hi)
  let x0 := GlobalTheory.ObjPull.pushEquiv hπ _ x
  have hx0 : x0 ^ n = 1 := by simp only [x0, ← map_pow, hx, map_one]
  have hT : spMap (κ.comp i) ≫ jK R = (Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ := by
    show _ = (spMap κ ≫ jK O) ≫ spMap ρ
    rw [spMap_comp, Category.assoc, hsq, Category.assoc]
  let e : Over.mk (spMap (κ.comp i) ≫ jK R) ⟶ Over.mk ((Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
  obtain ⟨y, hy⟩ := h K (κ.comp i) (e ≫ x0) (by rw [← MonObj.comp_pow, hx0, MonObj.comp_one])
  have hy' : x.left ≫ π = spMap κ ≫ spMap i ≫ y.left := by
    have e₁ : x.left ≫ π = (e ≫ x0).left := (Category.id_comp _).symm
    exact e₁.trans (hy.trans ((congrArg (· ≫ y.left) (spMap_comp i κ)).trans (Category.assoc _ _ _)))
  have hz : (spMap i ≫ y.left) ≫ G.hom = jK O ≫ spMap ρ := by
    rw [Category.assoc, Over.w y]
    exact hsq
  refine ⟨Over.homMk (hπ.1.lift _ (jK O) hz) (hπ.1.lift_snd _ _ _), hπ.1.hom_ext ?_ ?_⟩
  · show x.left ≫ π = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ π
    rw [Category.assoc, hπ.1.lift_fst, hy']
  · show x.left ≫ A.hom = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ A.hom
    rw [Category.assoc, hπ.1.lift_snd]
    exact Over.w x

theorem exists_factor {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {H : Over T} [GrpObj H]
    {f : S' ⟶ S} {t : T ⟶ S'} {u : T ⟶ S} (hu : t ≫ f = u) {π : A.left ⟶ G.left} {π₂ : (A ⊗ A).left ⟶ (G ⊗ G).left}
    (hπ : IsGrpPullback A G f π) (sπ : IsSquare π π₂) {a : H.left ⟶ G.left} {a₂ : (H ⊗ H).left ⟶ (G ⊗ G).left}
    (ha : IsGrpPullback H G u a) (sa : IsSquare a a₂) :
    ∃ (ψ : H.left ⟶ A.left) (ψ₂ : (H ⊗ H).left ⟶ (A ⊗ A).left), IsGrpPullback H A t ψ ∧ IsSquare ψ ψ₂ ∧ a₂ = ψ₂ ≫ π₂ := by
  let ψ := hπ.1.lift a (H.hom ≫ t) (by rw [Category.assoc, hu]; exact ha.1.w)
  have hψ : ψ ≫ π = a := hπ.1.lift_fst _ _ _
  have hpb : IsGrpPullback H A t ψ := hπ.cancel (ha.congr hu.symm hψ.symm) (hπ.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  exact ⟨ψ, _, hpb, sψ, GlobalTheory.LamPull.isSquare_unique sa (hψ ▸ AbPol.isSquare_comp sψ sπ)⟩

theorem sameFib_factor {S₁ S₂ S₁' S₂' T : Scheme.{0}} {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {P₁ : LB (G2 G₁).left}
    {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {P₂ : LB (G2 G₂).left} (h₁ : P₁.IsLB) (h₂ : P₂.IsLB)
    {A₁ : Over S₁'} [GrpObj A₁] [IsCommMonObj A₁] {A₂ : Over S₂'} [GrpObj A₂] [IsCommMonObj A₂]
    {f₁ : S₁' ⟶ S₁} {t₁ : T ⟶ S₁'} {u₁ : T ⟶ S₁} (e₁ : t₁ ≫ f₁ = u₁)
    {f₂ : S₂' ⟶ S₂} {t₂ : T ⟶ S₂'} {u₂ : T ⟶ S₂} (e₂ : t₂ ≫ f₂ = u₂)
    {π₁ : A₁.left ⟶ G₁.left} {q₁ : (G2 A₁).left ⟶ (G2 G₁).left} (p₁ : IsGrpPullback A₁ G₁ f₁ π₁) (s₁ : IsSquare π₁ q₁)
    {π₂ : A₂.left ⟶ G₂.left} {q₂ : (G2 A₂).left ⟶ (G2 G₂).left} (p₂ : IsGrpPullback A₂ G₂ f₂ π₂) (s₂ : IsSquare π₂ q₂)
    (h : SameFib G₁ P₁ u₁ G₂ P₂ u₂) : SameFib A₁ (P₁.pull q₁) t₁ A₂ (P₂.pull q₂) t₂ := by
  obtain ⟨H, _, _, a, a₂, a', a₂', ha, sa, ha', sa', e⟩ := h
  obtain ⟨ψ, ψ₂, hψ, sψ, rfl⟩ := exists_factor e₁ p₁ s₁ ha sa
  obtain ⟨χ, χ₂, hχ, sχ, rfl⟩ := exists_factor e₂ p₂ s₂ ha' sa'
  refine ⟨H, inferInstance, inferInstance, ψ, ψ₂, χ, χ₂, hψ, sψ, hχ, sχ, ?_⟩
  have c := (CechPic.cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).2 e
  apply (CechPic.cls_eq_iff (pull_isLB (pull_isLB h₁ _) _) (pull_isLB (pull_isLB h₂ _) _)).1
  rw [CechPic.cls_pull (pull_isLB h₁ _), CechPic.cls_pull (pull_isLB h₂ _), CechPic.cls_pull h₁, CechPic.cls_pull h₂,
    ← CechPic.pull_comp, ← CechPic.pull_comp]
  rwa [CechPic.cls_pull h₁, CechPic.cls_pull h₂] at c

theorem lbIso_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {N : LB Z} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    {a : Y ⟶ X} {b : Z ⟶ Y} (e : LBIso M (L.pull a)) (e' : LBIso N (M.pull b)) : LBIso N (L.pull (b ≫ a)) := by
  have c := (CechPic.cls_eq_iff hM (pull_isLB hL _)).2 e
  have c' := (CechPic.cls_eq_iff hN (pull_isLB hM _)).2 e'
  apply (CechPic.cls_eq_iff hN (pull_isLB hL _)).1
  rw [c', CechPic.cls_pull hM, c, CechPic.cls_pull hL, CechPic.cls_pull hL,
    CechPic.pull_comp]

theorem siegPB_trans {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {u : SiegPre h n ζ s} {c : SiegPre h n ζ s'} {c' : SiegPre h n ζ s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : SiegPB c' c f') (m : SiegPB c u f) : SiegPB c' u (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩ := m'
  exact ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, AbPol.isSquare_comp hs' hs, lbIso_comp u.isLB c.isLB c'.isLB hw hw', fun a =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))⟩

theorem exists_level : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → TorsRat G₁ n → ∀ (K : Type) [Field K] (κ : Localization.Away (∏ k, C.t k) →+* K) (x₀ : Sp K ⟶ F.X), x₀ ≫ F.s = spMap ((κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) → SameFib F.univ.A F.univ.P x₀ G₁ P (spMap (κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))))) → ∃ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal ∧ (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) ∧ ∀ yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X, SiegPB c F.univ yU → yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) → spMap κ ≫ yU = x₀ := by
  intro g n φ hn hodd F C G₁ _ _ P hM hab hT K _ κ x₀ hx₀ hsf
  obtain ⟨A, _, _, π₀, π₂, hπ, sπ, hA, hP⟩ := AbPol.exists_isPPol_away g n φ hn C G₁ P hM hab
  have hCN := hM.1
  have hPG := hM.2.2.2.1.1
  let t := ∏ k, C.t k
  let O := Localization.Away t
  have ht0 : t ≠ 0 := fun h0 => by
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := O) t).map κ
    have : algebraMap C.R O t = 0 := (congrArg (algebraMap C.R O) h0).trans (map_zero _)
    rw [this, map_zero] at hu
    exact not_isUnit_zero hu
  haveI := hCN.1
  haveI := hCN.2.1
  have hle : Submonoid.powers t ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  haveI : IsDomain O := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Submonoid.powers t) _ inferInstance
  haveI : IsIntegrallyClosed O := isIntegrallyClosed_of_isLocalization O (Submonoid.powers t) hle
  have hTA : TorsRat A n := torsRat_of_isGrpPullback _ (IsLocalization.injective O hle) hπ hT
  let b : cycAway n →+* O := (algebraMap C.R O).comp C.b
  let c₀ : SiegPre g n (zetaAway n) (spMap (κ.comp b)) := GlobalTheory.LowChart.siegPull F.univ x₀ _ hx₀
  have pb₀ : SiegPB c₀ F.univ x₀ := GlobalTheory.LowChart.siegPB_siegPull _ _ _ _
  have hs₀ : SameFib c₀.A c₀.P (𝟙 _) A (P.pull π₂) (spMap κ) := by
    dsimp only [c₀, GlobalTheory.LowChart.siegPull]
    exact sameFib_factor F.univ.isLB hPG (Category.id_comp x₀) (spMap_comp _ _).symm
      (Pdiv.PullbackComparison.isGrpPullback x₀ F.univ.A) (Pdiv.PullbackComparison.isSquare x₀ F.univ.A) hπ sπ hsf
  obtain ⟨c, hc, hcc, a, a₂, ha, sa, ea⟩ := GlobalTheory.LevSpread.level_spreads n hn hodd O b A (P.pull π₂) hA hP hTA g K κ c₀
    (GlobalTheory.LowChart.principal_siegPull _ _ _ _ F.princ) hs₀
  refine ⟨c, hc, ⟨a ≫ π₀, a₂ ≫ π₂, (ha.comp hπ).congr (Category.id_comp _) rfl, AbPol.isSquare_comp sa sπ,
    lbIso_comp hPG (pull_isLB hPG _) c.isLB (GlobalTheory.lbIso_refl (pull_isLB hPG _)) ea⟩, fun yU hy hys => ?_⟩
  refine F.inj K _ _ _ c₀ ?_ (siegPB_trans hcc hy) pb₀
  rw [Category.assoc, hys, hx₀, ← spMap_comp, RingHom.comp_assoc]

end GlobalTheory.TChart.AbLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LBObs.exists_lift_of_lam_iso_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left) (L₀ : LB B₀.left), P.IsLB → L₀.IsLB → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → ∃ L : LB B.left, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ _ π hπ hI B _ B₀ _ _ i i₂ hB hgp hsq P L₀ hP hL₀ hΛ
  have hab : IsAbelianScheme B₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hgp
  obtain ⟨g, hdim⟩ := GlobalTheory.AbelianDim.exists_relDim R₀ B₀ hab
  have hsm : Smooth B.hom := hB.smooth
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.Obs.exists_aug R R₀ (RingHom.ker π) hI π hπ rfl
  have hpb : IsPullback i B₀.hom B.hom (spMap π) := hgp.1
  obtain ⟨S, ⟨Pr⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl B₀.left B₀.hom B.left B.hom i hpb hsm
  obtain ⟨k, hkp, hkμ, hkf, hks⟩ := _root_.GlobalTheory.SqPull.sq_of_grpPullback (Sp R) (Sp R₀) (spMap π) B B₀ i hgp
  have hki : i₂ = k := (GlobalTheory.SqPull.tensor_isPullback B B).hom_ext (hsq.1.trans hkf.symm) (hsq.2.trans hks.symm)
  subst hki
  have hsm2 : Smooth (B ⊗ B).hom := inferInstanceAs (Smooth (Limits.pullback.fst B.hom B.hom ≫ B.hom))
  obtain ⟨S₂, ⟨P₂⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom (B ⊗ B).left
    (B ⊗ B).hom i₂ hkp hsm2
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.LBObs.ObEx.exists_isObL R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S L₀ hL₀
  have h1 : (L₀.pull (fst B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h2 : (L₀.pull (snd B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h3 : (P.pull i₂).IsLB := pull_isLB hP _
  obtain ⟨c₁, hc₁⟩ := _root_.GlobalTheory.LBObs.ObEx.exists_isObL R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h1
  obtain ⟨c₂, hc₂⟩ := _root_.GlobalTheory.LBObs.ObEx.exists_isObL R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h2
  have hc₃ : IsObL S₂ α (P.pull i₂) 0 :=
    _root_.GlobalTheory.LBObs.isObL_pull_zero R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ (B ⊗ B).left (B ⊗ B).hom i₂ P₂ P hkp hP
  have hc₁₂ := _root_.GlobalTheory.LBObs.isObL_tens R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ c₁ c₂ hc₁ hc₂
  have hc₁₂₃ := _root_.GlobalTheory.LBObs.isObL_tens R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ _ _ hc₁₂ hc₃
  rw [add_zero] at hc₁₂₃

  have hz : GlobalTheory.CechPic.pull (1 : B₀ ⊗ B₀ ⟶ B₀).left (cls L₀ hL₀) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp]
    have h0 : cls (L₀.pull (η[B₀]).left) (pull_isLB hL₀ _) = 0 :=
      (cls_eq_zero_iff _).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₀) (pull_isLB hL₀ _))
    rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), h0, map_zero]
  have hmul : (fst B₀ B₀ * snd B₀ B₀ : B₀ ⊗ B₀ ⟶ B₀) = μ[B₀] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hLam : (abelian₂ B₀ L₀).IsLB := LB.isLB_linComb hL₀ _ _
  have hcube : cls (abelian₂ B₀ L₀) hLam = lam (cls L₀ hL₀) (fst B₀ B₀) (snd B₀ B₀) :=
    GlobalTheory.CechPic.cls_cube_two hL₀ (fst B₀ B₀) (snd B₀ B₀) hLam
  have hΛc : cls _ hLam = cls _ h3 := (cls_eq_iff hLam h3).2 hΛ
  have hiso : LBIso (tens (tens (L₀.pull (fst B₀ B₀).left) (L₀.pull (snd B₀ B₀).left)) (P.pull i₂))
      (L₀.pull (μ[B₀]).left) := by
    refine (cls_eq_iff (isLB_tens (isLB_tens h1 h2) h3) (pull_isLB hL₀ _)).1 ?_
    rw [cls_tens (isLB_tens h1 h2) h3, cls_tens h1 h2, ← hΛc, hcube, lam, hmul, hz, cls_pull hL₀, cls_pull hL₀,
      cls_pull hL₀]
    abel
  have hpb2 : IsPullback i₂ (B₀ ⊗ B₀).hom (B ⊗ B).hom (spMap π) := hkp
  have nat : ∀ (f₀ : (B₀ ⊗ B₀) ⟶ B₀) (f : (B ⊗ B) ⟶ B), i₂ ≫ f.left = f₀.left ≫ i →
      ∀ (L' : LB (B₀ ⊗ B₀).left) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff (B₀ ⊗ B₀).hom))), L'.IsLB →
        LBIso L' (L₀.pull f₀.left) → IsObL S₂ α L' c' → IsExtendedPullbackDegTwo R₁ (overW f₀) c c' := by
    intro f₀ f hf L' c' hL' hiso hob
    obtain ⟨l, hl, hn⟩ := GlobalTheory.Obs.exists_chart_lifts R R₀ _ hI π hπ rfl B₀.left (B₀ ⊗ B₀).left B.left (B ⊗ B).left
      B₀.hom (B₀ ⊗ B₀).hom B.hom (B ⊗ B).hom i i₂ hpb hkp S S₂ Pr P₂ f₀.left (overW f₀) f.left (Over.w f) hf
    exact _root_.GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt R R₀ _ hI π hπ rfl R₁ α B₀.left (B₀ ⊗ B₀).left B₀.hom (B₀ ⊗ B₀).hom S S₂ f₀.left (overW f₀)
      l hl hn L₀ L' c c' hL₀ hL' hiso hc hob
  have eμ := nat μ[B₀] μ[B] hkμ _ (c₁ + c₂) (isLB_tens (isLB_tens h1 h2) h3) hiso hc₁₂₃
  have e1 := nat (fst B₀ B₀) (fst B B) hkf _ c₁ h1 (GlobalTheory.PolBaseChange.lbIso_refl h1) hc₁
  have e2 := nat (snd B₀ B₀) (snd B B) hks _ c₂ h2 (GlobalTheory.PolBaseChange.lbIso_refl h2) hc₂
  have h0 : c = 0 := _root_.GlobalTheory.Obs.primE2_any_ring R₀ R₁ α.q α.sq B₀ g hab hdim c c₁ c₂ eμ e1 e2
  subst h0
  exact _root_.GlobalTheory.LBObs.exists_lift_of_isObL_zero R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S B.left B.hom i Pr L₀ hpb hL₀ hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionExtendBasicOpen
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecAff

theorem rsT_eq_rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) : rsT s V = rs h s :=
  GlobalTheory.KS.rsT_of_le h s

theorem sec_extend_basicOpen : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (M : LB X), M.IsLB → ∀ (f : Γ(X, ⊤)) (t : ∀ c, Γ(X, M.U c ⊓ X.basicOpen f)), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ X.basicOpen f) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ X.basicOpen f) * rsT (t c') (M.U c ⊓ M.U c' ⊓ X.basicOpen f)) → ∃ (N : ℕ) (s : LB.Sec M), ∀ c, rsT (s.f c) (M.U c ⊓ X.basicOpen f) = rsT f (M.U c ⊓ X.basicOpen f) ^ N * t c := by
  intro X _ _ M hM f t ht
  let φ := (X.basicOpen f).ι
  have hφ : φ.opensRange = X.basicOpen f := Scheme.Opens.opensRange_ι _
  have hr : ∀ x, φ x ∈ X.basicOpen f := by
    intro x
    have hx : φ x ∈ φ.opensRange := ⟨x, rfl⟩
    rwa [hφ] at hx
  have hc : ∀ c, φ ⁻¹ᵁ M.U c ≤ φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f) := fun c x hx => ⟨hx, hr x⟩
  let t' : ∀ c, Γ(↑(X.basicOpen f), φ ⁻¹ᵁ M.U c) := fun c => pa φ (hc c) (t c)
  have ht' : ∀ i j, rs (inf_le_left : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U i) (t' i) =
      pa φ (le_pre_inf (inf_le_left.trans (le_refl (φ ⁻¹ᵁ M.U i)))
        (inf_le_right.trans (le_refl (φ ⁻¹ᵁ M.U j))))
        (M.g i j : Γ(X, M.U i ⊓ M.U j)) *
        rs (inf_le_right : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U j) (t' j) := by
    intro i j
    have e : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ (M.U i ⊓ M.U j ⊓ X.basicOpen f) :=
      fun x hx => ⟨⟨hx.1, hx.2⟩, hr x⟩
    have h1 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_left
    have h2 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ M.U j := inf_le_left
    have h3 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U j ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_right
    have := ht i j
    rw [rsT_eq_rs h1, rsT_eq_rs h2, rsT_eq_rs h3] at this
    have := congrArg (pa φ e) this
    rw [map_mul, pa_rs, pa_rs, pa_rs] at this
    simp only [t']
    rw [rs_pa, rs_pa]
    exact this
  obtain ⟨N, s, hs⟩ := sec_extend φ f hφ M hM (fun c => φ ⁻¹ᵁ M.U c) (fun c => le_rfl)
    (fun c => le_rfl) t' ht'
  refine ⟨N, s, fun c => ?_⟩
  have hU : M.U c ⊓ X.basicOpen f ≤ φ.opensRange := by rw [hφ]; exact inf_le_right
  apply (pa_bijective φ (le_refl (φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f))) le_rfl hU).1
  have hV : φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f) ≤ φ ⁻¹ᵁ M.U c := fun x hx => hx.1
  have := congrArg (rs hV) (hs c)
  rw [rs_pa, map_mul, map_pow, rs_pa] at this
  simp only [t'] at this
  rw [rs_pa] at this
  rw [rsT_eq_rs inf_le_left, rsT_eq_rs le_top, map_mul, map_pow, pa_rs, pa_rs, this]

end GlobalTheory.SecAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRepresentingSchemeHomFixedPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.HomFixLocal

theorem exists_local_homFixRep : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∀ p : Sp Rg, ∃ U : (Sp Rg).Opens, p ∈ U ∧ ∃ (AU : Over (U).toScheme) (_ : GrpObj AU) (BU : Over (U).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U).ι φA ∧ IsGrpPullback BU B (U).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M hA hB hL hM rL rM aL aM p
  obtain ⟨k, hk, hva⟩ := GlobalTheory.RelAmpleFixed.veryAmpleAt_baseChange Rg B M hB hM aM
  obtain ⟨f₁, hp₁, hb₁⟩ := GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis Rg A L hA hL rL aL k hk p
  obtain ⟨f₂, hp₂, hb₂⟩ := GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis Rg B M hB hM rM aM k hk p
  have le₁ : PrimeSpectrum.basicOpen (f₁ * f₂) ≤ PrimeSpectrum.basicOpen f₁ := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left
  have le₂ : PrimeSpectrum.basicOpen (f₁ * f₂) ≤ PrimeSpectrum.basicOpen f₂ := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_right
  have hp : p ∈ PrimeSpectrum.basicOpen (f₁ * f₂) := by
    rw [PrimeSpectrum.basicOpen_mul]; exact ⟨hp₁, hp₂⟩
  refine ⟨PrimeSpectrum.basicOpen (f₁ * f₂), hp, GlobalTheory.HomFixTransport.homFixRep_basicOpen Rg A B L M (f₁ * f₂) hL hM ?_ _ rfl⟩
  intro Af Bf _ _ φA φB hpA hpB
  haveI := GlobalTheory.isCommMonObj_of_grpPullback _ _ A Af _ φA hpA
  haveI := GlobalTheory.isCommMonObj_of_grpPullback _ _ B Bf _ φB hpB
  obtain ⟨hA', hL', rL', aL'⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ _ A Af φA L hpA hA hL rL aL
  obtain ⟨hB', hM', rM', -⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ _ B Bf φB M hpB hB hM rM aM
  exact GlobalTheory.T.exists_fixedPullbackHomScheme_of_sectionBases (Localization.Away (f₁ * f₂)) Af Bf (L.pull φA) (M.pull φB) k hA' hB' hL' hM' rL' rM' aL' hk
    (hva _ _ Bf φB hpB) (hb₁ _ le₁ Af φA hpA) (hb₂ _ le₂ Bf φB hpB)

end GlobalTheory.HomFixLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonicRatCharPolyAbelianVarietyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_rat_charPoly_abelianVariety : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f).asHom : ℚ) := by
  intro K _ A f
  obtain ⟨F, hF, hev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl 2 ![𝟙 A, f.asHom]
  set N := 2 * A.dim with hN
  have hsupp : ∀ d ∈ F.support, d 0 + d 1 = N := by
    intro d hd
    by_contra h
    refine (MvPolynomial.mem_support_iff.mp hd) (hF.coeff_eq_zero ?_)
    rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  let P : Polynomial ℚ := ∑ d ∈ F.support,
    Polynomial.C (AddMonoidAlgebra.coeff F d * (-1) ^ d 1) * Polynomial.X ^ d 0
  have hPeval : ∀ q : ℚ, P.eval q = MvPolynomial.eval ![q, -1] F := by
    intro q
    rw [MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [Fin.prod_univ_two]
    ring
  have hcoef : P.coeff N = AddMonoidAlgebra.coeff F (Finsupp.single 0 N) := by
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp
    · intro d hd hne
      rw [ite_eq_right]
      intro h0
      apply hne
      have := hsupp d hd
      ext i
      fin_cases i <;> simp <;> omega
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hdeg : P.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro d hd
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := hsupp d hd; omega)
  have h10 : MvPolynomial.eval ![1, 0] F = AddMonoidAlgebra.coeff F (Finsupp.single 0 N) := by
    rw [MvPolynomial.eval_eq', Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp [Fin.prod_univ_two]
    · intro d hd hne
      have := hsupp d hd
      have h1 : d 1 ≠ 0 := by
        intro h1
        apply hne
        ext i
        fin_cases i <;> simp <;> omega
      simp [Fin.prod_univ_two, h1]
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hone : MvPolynomial.eval ![1, 0] F = 1 := by
    have h := hev ![1, 0]
    have e1 : (fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![1, 0] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    have h2 := (GlobalTheory.MulIsogeny.mul_isogeny K A 1 one_ne_zero).2
    simp only [one_smul, Int.natAbs_one, one_pow] at h2
    simp [Fin.sum_univ_two, h2]
  have hnat : P.natDegree = N := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg
    rw [hcoef, ← h10, hone]
    exact one_ne_zero
  refine ⟨P, ?_, hnat, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hnat, hcoef, ← h10, hone]
  · intro n
    rw [hPeval]
    have h := hev ![n, -1]
    have e1 : (fun i => (((![n, -1] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![(n : ℚ), -1] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    congr 2
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, one_smul]
    rw [← zsmul_one (R := End A) n, End.sub_asHom, End.smul_asHom, End.one_asHom, sub_eq_add_neg]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionRatioIntegralThetaFamil
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_sec_exp_intFam_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1), ∃ θ₀ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ := by
  intro R _ _ _ hR D C F₁
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.Mum.exists_map_exp_all_traits R hR D C 0
  refine ⟨Φ F₁, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, h⟩ := hΦ W T
  exact ⟨a, b, ha, hb, h F₁⟩

end GlobalTheory.Mum
end

