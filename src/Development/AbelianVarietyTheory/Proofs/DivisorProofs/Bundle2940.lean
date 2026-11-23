module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem finrank_ratF_eq_gdeg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  intro hA k _ X _ p D hX P hamp e x hg
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  obtain ⟨hI, π, hπ, hgen, hr0, hr, hiso⟩ := _root_.GlobalTheory.HSAmp.toProj_gens k X p D hX P hamp e x hg
  obtain ⟨B, -, hB⟩ := _root_.GlobalTheory.HSAmp.exists_isCan_bdd k X p D hX P e x hg
  obtain ⟨u, hu, -⟩ := hB 1 le_rfl
  have h1 := (hiso u hu).gdeg_eq D
  obtain ⟨hPV, hdeg, hcard⟩ := _root_.GlobalTheory.PSpaceDeg.main k D
  have h2 := (_root_.GlobalTheory.HSAmp.PullPow.gdeg_pull_and_isSelfInter_pow hA k (PSpace k D) (PSpace.str k D) D hPV).1 X p hX π hπ hgen hr0 (ProjSpace.hermitianTwistingSheaf k D)
  have h3 : gdeg ((up P.L u).pow e) D = (e : ℝ) ^ D * gdeg (up P.L u) D :=
    _root_.GlobalTheory.HSAmp.chInt_pow k X p D hX (up P.L u) e fun _ _ => 1
  have h4 := _root_.GlobalTheory.GdegMetric.gdeg_up hA k X p D hX P.L u
  rw [← hr]
  push_cast
  rw [← hcard, ← hdeg, ← h2, ← h1, h3, h4]

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreNormalProjectiveAmpleCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.GenFibNormal

theorem genFibre_of_fieldChange (hd2 : ∀ (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0}) (g : Y ⟶ Sp F), GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme (pullback g (spMap c))) : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) := by
  intro o K _ _ _ _ b hb Z z L hP hN hL hA
  haveI hsa : IsAffineHom (spMap b) := inferInstance
  haveI : IsAffineHom (pullback.fst z (spMap b)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback z (spMap b)).flip hsa
  refine ⟨ProjSpace.isProjOver_pullback_snd b hP, ?_, LB.isLB_pull hL _, IsAmpleLB.pull_of_isAffineHom hA _⟩
  haveI : CharZero o := ⟨fun m n h => by
    have := congrArg b h; simp only [map_natCast] at this; exact_mod_cast this⟩
  let F := FractionRing o
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective o F)
  let b' : F →+* K := IsFractionRing.lift hb
  have hbb : b'.comp (algebraMap o F) = b := RingHom.ext fun x => IsFractionRing.lift_algebraMap hb x
  have hZF : GlobalTheory.IsNormalScheme (pullback z (spMap (algebraMap o F))) :=
    IsNormalScheme.of_pred (FlagCls.isNormalScheme_of_isPullback_fractionField o F Z _ z
      (pullback.fst z (spMap (algebraMap o F))) (pullback.snd z (spMap (algebraMap o F)))
      (IsPullback.of_hasPullback _ _) ((isNormalScheme_iff_pred Z).mp hN))
  have h1 := hd2 F K b' _ (pullback.snd z (spMap (algebraMap o F))) hZF
  have e := pullbackLeftPullbackSndIso z (spMap (algebraMap o F)) (spMap b')
  have hc : spMap b' ≫ spMap (algebraMap o F) = spMap b := by
    rw [← hbb]
    simp only [spMap, ← Spec.map_comp]
    rfl
  exact (IsNormalScheme.iff_of_iso (e ≪≫ pullback.congrHom rfl hc)).mp h1

theorem genericFibre_normal_projective_ample : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) :=
  genFibre_of_fieldChange (GlobalTheory.T.isNormalScheme_pullback_spMap_of_isNormalScheme (GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt _root_.GlobalTheory.exists_smooth_subalgebra_of_finset _root_.GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring))

end GlobalTheory.GenFibNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.HeatDefect

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem val_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    (val t (r ≫ h) z J).val = (r.stalkMap z).hom (val t h (r z) (fun ψ => J (r ≫ ψ))).val := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t h (r z) (fun ψ => J (r ≫ ψ)) (fun k => J (r ≫ h ≫ φ k)) (fun k => rfl)]
  have hm : (r ≫ h) z ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gs_unit _ z _ hm _).symm.trans ((gs_comp_stalk r h z _ hm _).trans (congrArg _ (gs_unit h (r z) _ hm _)))

theorem good_comp {X Z : Scheme.{0}} {L : LB X} (r : Z ⟶ Z) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
  have := hJ (r ≫ ψ)
  rwa [Scheme.Hom.comp_apply] at this

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem gs_scal (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (c : R) : (m.left.stalkMap z).hom (gs (𝟙 _) (m.left z) ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c)) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c) := by
  rw [← gs_comp_stalk m.left (𝟙 _) z ⊤ trivial, Category.comp_id]
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  have e₁ := gs_pull m.left (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  have e₂ := gs_pull (𝟙 _) (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  rw [Over.w m] at e₁
  rw [Category.id_comp] at e₂
  exact e₁.trans e₂.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem shiftEq_at {k : ℕ} {mu α : Q.X} {σ : Q.SecB k α} {σ₁ σ₂ : Q.SecB k (α + k • mu)} {c : R}
    (H : ShiftEq Q k mu α σ σ₁ c σ₂)
    (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α))
    (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L z J) :
    sval σ₁ (m ≫ DegPre.prB Q (FractionRing R)).left z J =
      (val u m.left z J).val *
          sval σ (m ≫ DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left z J +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom c) *
          sval σ₂ (m ≫ DegPre.prB Q (FractionRing R)).left z J := by
  have e := congrArg (m.left.stalkMap z).hom (H u hu hc (m.left z) _ (good_comp m.left z hJ))
  rw [Over.comp_left, Over.comp_left, Over.comp_left, sval_comp_stalk _ _ _ _ hJ, sval_comp_stalk _ _ _ _ hJ,
    sval_comp_stalk _ _ _ _ hJ, e, map_add, map_mul, map_mul, gs_scal]
  congr 2
  have := val_comp_stalk u (𝟙 _) m.left z hJ
  rw [Category.comp_id] at this
  exact this.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem scal_injective (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    Function.Injective (fun r : R => gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom r)) := by
  let F := FractionRing R
  let χ : F →+* (DegPre.BF Q F).left.presheaf.stalk z :=
    ((DegPre.BF Q F).left.presheaf.germ ⊤ z trivial).hom.comp
      ((fst (TF (R := R) F) Q.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)
  have hT : (DegPre.BF Q F).hom = (fst (TF (R := R) F) Q.P.A).left ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [← Over.w (fst (TF (R := R) F) Q.P.A)]
    show _ ≫ (jFK (R := R) F ≫ jK R) = _
    rw [jFK, jK, ← Spec.map_comp]
    rfl
  have key : ∀ r : R, gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q F).hom r) = χ (algebraMap R F r) := by
    intro r
    unfold ReciprocityTheory.ChartRestriction.G.Out.scal
    rw [hT, gs_eq _ z ⊤ trivial]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R F))
    have n' := congrArg (fun f => f.hom r) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n'
    simp only [χ, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, n']
    rfl
  intro a b hab
  have : χ (algebraMap R F a) = χ (algebraMap R F b) := (key a).symm.trans (hab.trans (key b))
  exact IsFractionRing.injective R F (χ.injective this)
end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem sval_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {x y : Q.X} (e : x = y)
    (he : Q.SecB k x = Q.SecB k y) (σ : Q.SecB k x) {Z : Scheme.{0}} (r : Z ⟶ Q.P.A.left) (z : Z)
    (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) : sval (cast he σ) r z J = sval σ r z J := by
  subst e; rfl

theorem tActs_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R}
    {h : Heat Y.H Y.q.left Q.P.L dd D} {k : ℕ} {x y : Q.X} (e : x = y) (he : Q.SecB k x = Q.SecB k y)
    {σ σ' : Q.SecB k x} (H : TActs Y h k x σ σ') : TActs Y h k y (cast he σ) (cast he σ') := by
  subst e; exact H

theorem scal_add {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) (a b : R) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom (a + b)) =
      gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom a) +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom b) := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  rw [map_add (f := _), map_add (f := _)]
  exact gs_add (𝟙 _) z ⊤ trivial _ _

theorem scal_zero {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom 0) = 0 := by
  have := scal_add Q z 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem defect_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (c : ℕ → Dd.toPre.X → Dd.toPre.X → R), IsBasic Y h → HasDefect Y h c → ∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α, c k (mu + mu') α = c k mu α + c k mu' (α + k • mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h c hB hD k hk mu mu' α
  obtain ⟨σ, σ₁, σ₂, he, h1, h2, h3, z, J, hJ, hs⟩ := _root_.GlobalTheory.IntegralFamTriple.exists_triple R Dd k hk mu mu' α
  have e : α + k • mu + k • mu' = α + k • (mu + mu') := by rw [smul_add, add_assoc]
  obtain ⟨σ', a1⟩ := _root_.GlobalTheory.Heat.heat_acts_on_terms R Dd O oa Y n v dd hv D h hB k α σ
  obtain ⟨σ₁', a2⟩ := _root_.GlobalTheory.Heat.heat_acts_on_terms R Dd O oa Y n v dd hv D h hB k _ σ₁
  obtain ⟨σ₂', a3⟩ := _root_.GlobalTheory.Heat.heat_acts_on_terms R Dd O oa Y n v dd hv D h hB k _ σ₂
  have d1 := hD k mu α σ σ' σ₁ σ₁' hk h1 a1 a2
  have d2 := hD k mu' (α + k • mu) σ₁ σ₁' σ₂ σ₂' hk h2 a2 a3
  have d3 := hD k (mu + mu') α σ σ' _ _ hk h3 a1 (tActs_cast e he a3)
  obtain ⟨⟨u1, hu1, hc1⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α
  obtain ⟨⟨u2, hu2, hc2⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu' (α + k • mu)
  obtain ⟨⟨u3, hu3, hc3⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k (mu + mu') α
  have E1 := shiftEq_at d1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E10 := shiftEq_at h1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E2 := shiftEq_at d2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E20 := shiftEq_at h2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E3 := shiftEq_at d3 u3 hu3 hc3 (𝟙 _) z J hJ
  have E30 := shiftEq_at h3 u3 hu3 hc3 (𝟙 _) z J hJ
  simp only [Category.id_comp, scal_zero, zero_mul, add_zero] at E1 E10 E2 E20 E3 E30
  rw [sval_cast e he, sval_cast e he] at E3
  rw [sval_cast e he] at E30
  rw [← Category.assoc, UUA.trF_add, add_comm mu' mu] at E1 E10
  set s := sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set s' := sval σ' (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set v1 := (val u1 (DegPre.trF Dd.toPre (FractionRing R) mu').left z J).val
  set v2 := (val u2 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set v3 := (val u3 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set p1 := sval σ₁ (DegPre.trF Dd.toPre (FractionRing R) mu' ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set q := sval σ₂ (DegPre.prB Dd.toPre (FractionRing R)).left z J
  set C1 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu α))
  set C2 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu' (α + k • mu)))
  set C3 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k (mu + mu') α))
  have k1 : (v2 * v1 - v3) * s = 0 := by linear_combination (-v2) * E10 - E20 + E30
  have hv' : v2 * v1 - v3 = 0 := hs.mul_left_eq_zero.mp k1
  have k2 : (C3 - (C1 + C2)) * q = 0 := by linear_combination E2 - E3 + v2 * E1 + s' * hv' - C1 * E20
  have hq : IsUnit q := by
    rw [E30]; exact (Units.isUnit _).mul hs
  have hC : C3 = C1 + C2 := sub_eq_zero.mp (hq.mul_left_eq_zero.mp k2)
  rw [← scal_add] at hC
  exact scal_injective R Dd.toPre z hC

end GlobalTheory.HeatDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePullbackGenOfFrameIsGen
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem pulled_back_lineBundle_transition_unit_eq_restriction {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j j' : PUnit.{1} → L.ι) :
    (L.pull f).g j j' = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ => f) j' PUnit.unit)))
      (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
  have e : ∀ u : Γ(Y, L.wchart (fun _ => f) j ⊓ L.wchart (fun _ => f) j')ˣ, (∏ _k : PUnit.{1}, u ^ (1 : ℤ)) = u :=
    fun u => by simp
  exact e _

theorem pull_g_eq (h : IsGrpPullback H G x ψ) (j j' : ((hodge G g).pull x).ι) :
    ((hodge G g).pull x).g j j' =
      (isFrame_chart h j).detUnit (isFrame_chart h j') inf_le_left inf_le_right := by
  have frame_pb {X Y : Scheme.{0}} {I : Type} [Fintype I] (f : Y ⟶ X)
      {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens} {e : I → Γ(F, U)} (he : IsFrame e)
      {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) : IsFrame fun i => pullbackSections f F h (e i) := by
    have k := (he.pullback f).res h
    exact (funext fun l => QCoh.res_pullbackSections f F le_rfl h (e l)) ▸ k
  have e₁ := IsFrame.detUnit_map_iso
    (frame_pb x (j PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
    (frame_pb x (j' PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
    (omegaBase h) (inf_le_left : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤ _)
    inf_le_right
  refine Eq.trans ?_ e₁.symm
  have hT : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤
      x ⁻¹ᵁ ((j PUnit.unit).U ⊓ (j' PUnit.unit).U) :=
    le_inf (inf_le_left.trans (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
  refine Eq.trans ?_ (GlobalTheory.Vert.DivPull.detUnit_congr _ _ ((j PUnit.unit).isFrame.pullback x)
    ((j' PUnit.unit).isFrame.pullback x) _ _ (hT.trans (x.preimage_mono inf_le_left))
    (hT.trans (x.preimage_mono inf_le_right))
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)).symm
  refine Units.ext ?_
  refine (congrArg Units.val (pulled_back_lineBundle_transition_unit_eq_restriction (hodge G g) x j j')).trans (Eq.trans ?_
    (IsFrame.val_detUnit_pullback (j PUnit.unit).isFrame (j' PUnit.unit).isFrame x inf_le_left inf_le_right hT).symm)
  rfl

theorem gen_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  intro S' T G _ H _ x ψ _ g h a ha j j'
  refine (IsFrame.res_detUnit _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (pull_g_eq h j j').symm (IsFrame.res_detUnit _ _ _ _ _).symm)
  exact (IsFrame.detUnit_mul _ _ _ _ _ _).symm

end GlobalTheory.HodgeFrameGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullback
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem gm_eq_of_appLE {T Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {U : T.Opens} {W : Z.Opens} (hW : W ≤ r ⁻¹ᵁ U)
    (hz : z ∈ W) (u : Γ(T, U)ˣ) (v : Γ(Z, W)ˣ) (e : v.val = (r.appLE U W hW).hom u.val) :
    gm r z U u = gm (𝟙 Z) z W v := by
  refine Units.ext ?_
  rw [gm_val r z U (hW hz), gm_val (𝟙 Z) z W hz, e]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hW) z hz _).symm

theorem val_gen_pull : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  intro S' T Z G _ H _ x ψ _ g h a ha r B _ ρ q x' ψ' h' e e' b hb hab z J hJ
  have : QuasiSeparated H.hom := MorphismProperty.of_isPullback h.1 ‹_›
  rw [val_of (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J (fun _ => J x')
      (fun _ => by rw [e]),
    val_of (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J (fun _ => J x')
      (fun _ => by rw [Category.id_comp])]
  have hW : LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') ≤
      r ⁻¹ᵁ LB.wchart (hodge G g) (fun _ : PUnit => x) (fun _ => J x') := fun y hy =>
    Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      rw [← e] at this ⊢
      exact this
  have hz : z ∈ LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') := Set.mem_iInter.2 fun _ => hJ x'
  have k {U : T.Opens} {V W : Z.Opens} (hV : V ≤ r ⁻¹ᵁ U) (h₁ : W ≤ V) (s : Γ(omega H, U)) :
      GlobalTheory.Twist.resM _ h₁ ((omegaBase q).app V (pullbackSections r _ hV s)) =
        (omegaBase q).app W (pullbackSections r _ (h₁.trans hV) s) := by
    rw [← GlobalTheory.QCoh.res_pullbackSections r _ hV h₁ s]
    exact congr($((omegaBase q).mapPresheaf.naturality (homOfLE h₁).op) (pullbackSections r _ hV s)).symm
  refine gm_eq_of_appLE r z hW hz _ _ ?_
  have hc := isFrame_chart h (fun _ => J x')
  refine Eq.trans ?_ (hc.val_detUnit_pullback ha r le_rfl le_top hW)
  refine congrArg Units.val ?_
  refine Eq.trans ?_ (IsFrame.detUnit_map_iso _ _ (omegaBase q) _ _)
  refine GlobalTheory.Vert.DivPull.detUnit_congr _ _ _ _ _ _ _ _ (fun i => ?_) (fun i => ?_)
  · refine Eq.trans (GlobalTheory.Twist.resM_self _ _) (Eq.trans ?_ (k _ _ _).symm)
    exact (GlobalTheory.BadPt.Fibre.omegaBase_comp h q h' e e' _ _ _ _).symm
  · rw [hab]
    exact (k _ _ _).trans (k _ _ _).symm

end GlobalTheory.HodgeFrameGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastFurther
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiCoordRescaleLocal

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (q : D.X → (FractionRing R)ˣ) (y : D.X),
    PsiUnitOn D y Set.univ → ∀ s : R, (q y : FractionRing R) = algebraMap R (FractionRing R) s →
      ∃ u : Rˣ, Formalism.L2.Pj.PsiCoord (GlobalTheory.PolDeg.rescale D q) y (u * s) := by
  intro R _ _ _ D q y h s hs
  have hex : ∃ v : Rˣ, Formalism.L2.Pj.PsiCoord D y v := by
    obtain ⟨j, hj⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top D y
    have hh := GlobalTheory.PsiCoordLocal.generic_le D y j hj
    obtain ⟨t, ht, e⟩ := h j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj hh
    obtain ⟨r, rfl⟩ := GlobalTheory.PsiCoordLocal.toOpen_top_bijective.2 t
    have hu : IsUnit r := (MulEquiv.isUnit_map
      (RingEquiv.ofBijective (Out.DegPre.toOpen (R := R) ⊤)
        GlobalTheory.PsiCoordLocal.toOpen_top_bijective).toMulEquiv).1 ht
    exact ⟨hu.unit, j, hj, hh, e⟩
  obtain ⟨v, hv⟩ := hex
  have h2 : Formalism.L2.Pj.PsiCoord (GlobalTheory.TauTwist.rescale D q) y (s * (v : R)) := by
    obtain ⟨x, ⟨j, hj, hj', rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y v).1 hv
    refine (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D q) y (s * (v : R))).2
      ⟨q y * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi y) j hj, ⟨j, hj, hj', ?_⟩, ?_⟩
    · dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
      rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
      congr 1
      ext
      show (q y : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
        (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (q y : FractionRing R)))
      rw [CategoryTheory.Functor.map_id]
      exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
    · rw [Units.val_mul, hs, e, map_mul]
  refine ⟨v, ?_⟩
  rw [mul_comm]
  exact h2

end GlobalTheory.PsiCoordRescaleLocal
end

