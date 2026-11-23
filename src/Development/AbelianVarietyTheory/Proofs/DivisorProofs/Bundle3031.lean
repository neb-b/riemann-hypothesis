module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmLevelOneDefectFrobeniusPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneDefectsIndependentModMaximal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingPairsOfPrincipalisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusNilpotentModMaximalConnectedPDivGroup
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem isNil_frobenius_chart : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU
  set M := U * blk d k (p : F.B) 1 with hM
  let T : (Fin d ⊕ Fin k → F.B) → (Fin d ⊕ Fin k → F.B) := fun w => M.mulVec fun j => F.σ (w j)
  have hp : ¬IsUnit (p : O) := Fact.out
  have hθp : F.θ (p : F.B) = (p : O) := map_natCast _ _
  have nu_iff : ∀ x : O, ¬IsUnit x ↔ v (algebraMap O C x) < 1 := fun x => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => h.ne⟩
  have nu_add : ∀ x y : O, ¬IsUnit x → ¬IsUnit y → ¬IsUnit (x + y) := by
    intro x y hx hy
    rw [nu_iff] at hx hy ⊢
    rw [map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  have nu_sum : ∀ (s : Finset (Fin d ⊕ Fin k)) (f : Fin d ⊕ Fin k → O),
      (∀ i ∈ s, ¬IsUnit (f i)) → ¬IsUnit (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using not_isUnit_zero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact nu_add _ _ (hf a (Finset.mem_insert_self _ _))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have stepA : ∀ w : Fin d ⊕ Fin k → F.B, (∀ j, ¬IsUnit (F.θ (w (Sum.inr j)))) →
      ∀ i, ¬IsUnit (F.θ (T w i)) := by
    intro w hw i
    show ¬IsUnit (F.θ (∑ l, M i l * F.σ (w l)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply nu_sum
    intro l _
    rw [hM, blk, Matrix.mul_diagonal]
    cases l with
    | inl l =>
      simp only [Sum.elim_inl, map_mul, hθp]
      exact fun h => hp (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h))
    | inr j =>
      simp only [Sum.elim_inr, mul_one, map_mul]
      obtain ⟨c', hc'⟩ := F.σ_pow (w (Sum.inr j))
      have hs : F.θ (F.σ (w (Sum.inr j))) = F.θ (w (Sum.inr j)) ^ p + p * F.θ c' := by
        have := congrArg F.θ hc'
        rw [map_sub, map_mul, map_pow, hθp] at this
        linear_combination this
      rw [hs]
      refine fun h => nu_add _ _ ?_ ?_ (isUnit_of_mul_isUnit_right h)
      · exact fun h' => hw j ((isUnit_pow_iff (Fact.out : p.Prime).ne_zero).1 h')
      · exact fun h' => hp (isUnit_of_mul_isUnit_left h')
  have hQL : ∀ w : Fin d ⊕ Fin k → F.B, QL μ' ⊤ (comb w e) := fun w => _root_.GlobalTheory.QLog.ql_comb_top _ _ _ F.θ d μ' hlift _ e hbas.1 w
  have hstep : ∀ w : Fin d ⊕ Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb w e) - comb (T w) e) :=
    fun w => _root_.GlobalTheory.FrobStep.frob_comb_step p F.B F.Q F.σ F.s F.s_alg d _ e M hU w
  have hlf : ∀ w : Fin d ⊕ Fin k → F.B, ∃ a : MvPowerSeries (Fin d) F.B,
      map (algebraMap F.B F.Q) a = defect μ' p (comb w e) := by
    intro w
    have h := (QLogDefect.main p F.B O F.Q F.θ F.frame d μ' hlift ⊤ _ (hQL w) p).1
    choose b _ hb using h
    refine ⟨(fun α => b α : MvPowerSeries (Fin d) F.B), MvPowerSeries.ext fun α => ?_⟩
    exact (hb α).symm
  choose A hA using hlf
  let δ : (Fin d ⊕ Fin k → F.B) → G.A 1 := fun w => c.ev 1 (map F.θ (A w))
  set I := Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) with hI
  have hδstep : ∀ w : Fin d ⊕ Fin k → F.B, δ (T w) - δ w ^ p ∈ I := fun w =>
    _root_.GlobalTheory.QLog.defect_frob_pow p C v O hv ε hε F G d c μ' hlift hmap _ _ _ _ (hQL w) (hQL (T w)) (hstep w) (hA w) (hA (T w))
  have hδit : ∀ n w, δ (T^[n] w) - δ w ^ (p ^ n) ∈ I := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', pow_succ, pow_mul]
      have h1 := hδstep (T^[n] w)
      have h2 : δ (T^[n] w) ^ p - (δ w ^ p ^ n) ^ p ∈ I :=
        I.mem_of_dvd (sub_dvd_pow_sub_pow _ _ p) (ih w)
      have := I.add_mem h1 h2
      rwa [sub_add_sub_cancel] at this
  have hconst : ∀ w : Fin d ⊕ Fin k → F.B, constantCoeff (map F.θ (A w)) = 0 := by
    intro w
    have h0 := _root_.GlobalTheory.QLogDefect.constantCoeff_defect p F.B O F.Q F.θ F.frame d μ' hlift _ (hQL w) p
    rw [← hA w, MvPowerSeries.constantCoeff_map] at h0
    have h2 : constantCoeff (A w) = 0 := F.frame.inj (by rw [h0, map_zero])
    rw [MvPowerSeries.constantCoeff_map, h2, map_zero]
  obtain ⟨N0, hN0⟩ := _root_.GlobalTheory.AugNil.aug_nil p O G d c
  have hsmallp : ∀ x : G.A 1, (p : G.A 1) ∣ x → x ∈ I := by
    rintro x ⟨y, rfl⟩
    apply I.mul_mem_right
    apply Ideal.subset_span
    exact ⟨(p : O), hp, map_natCast _ _⟩
  have hδ0 : ∀ w : Fin d ⊕ Fin k → F.B, δ w ^ (p ^ N0) ∈ I := by
    intro w
    apply hsmallp
    have hle : N0 ≤ p ^ N0 := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    rw [← Nat.sub_add_cancel hle, pow_add]
    exact Dvd.dvd.mul_left (hN0 _ (hconst w)) _
  refine ⟨N0 + 1, fun w i => ?_⟩
  rw [Function.iterate_succ_apply']
  apply stepA
  intro j
  apply _root_.GlobalTheory.LevelOneIndep.defect_level_one_nonunit p C v O hv ε hε F G d c μ' hlift hmap k e hbas hadp _ (A _) (hA _)
  have := I.add_mem (hδit N0 w) (hδ0 w)
  rwa [sub_add_cancel] at this

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelIsProperOfCompactStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_integralModel_isProper_of_compact : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (M : Model b N), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → IsProper M.s := by
  first | exact @GlobalTheory.UPel.HT.isProper_model_of_compact | exact GlobalTheory.UPel.HT.isProper_model_of_compact | (intros; apply GlobalTheory.UPel.HT.isProper_model_of_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFiniteType
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualConFT

theorem hasRep_quot_of_factor {S T : Type} [CommRing S] [CommRing T] (J : Ideal S) (φ : S →+* T)
    (ψ : T →+* S ⧸ J) (hcomp : ψ.comp φ = Ideal.Quotient.mk J) (g : ℕ)
    (h : ∀ (B : Over (Sp T)) [GrpObj B], IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      HasRep B g (𝟙_ _))
    (A : Over (Sp S)) [GrpObj A] (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) := by
  let f : Sp T ⟶ Sp S := spMap φ
  let B : Over (Sp T) := (Over.pullback f).obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsGrpPullback B A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨hAB, hgB⟩ :=
    GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback φ A B _ g hB hA hg
  have h2 := (_root_.GlobalTheory.DualCon.hasRep_baseChange_iff _ _ f A B _ hB g (𝟙_ _)).1.mp (h B hAB hgB)
  refine GlobalTheory.T.baseChangeBis _ A (Over.mk ((𝟙_ (Over (Sp T))).hom ≫ f)) (Over.mk (spMap (Ideal.Quotient.mk J))) g
    (Over.homMk (spMap ψ) ?_) h2
  change spMap ψ ≫ 𝟙 _ ≫ spMap φ = spMap (Ideal.Quotient.mk J)
  rw [Category.id_comp, ← hcomp, spMap_comp]

end GlobalTheory.DualConFT

namespace GlobalTheory.DualConFT

theorem hasRep_quot (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (g : ℕ) (I : Ideal R) :
    ∀ (A : Over (Sp (R ⧸ I))) [GrpObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      HasRep A g (𝟙_ _) := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  induction I using WellFoundedGT.induction with
  | _ I ih =>
    intro A _ hA hg
    haveI : @Algebra.FiniteType ℤ (R ⧸ I) _ _ (Ring.toIntAlgebra _) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mk I).toIntAlgHom Ideal.Quotient.mk_surjective
    refine _root_.GlobalTheory.DualCon.Step.step (R ⧸ I) A g hA hg fun J' hJ' => ?_
    let J : Ideal R := J'.comap (Ideal.Quotient.mk I)
    have hle : I ≤ J := fun a ha => by
      show Ideal.Quotient.mk I a ∈ J'
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact J'.zero_mem
    have hlt : I < J := by
      refine lt_of_le_of_ne hle fun hIJ => hJ' ?_
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      have ha : a ∈ J := hx
      rw [← hIJ] at ha
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact (⊥ : Ideal (R ⧸ I)).zero_mem
    let ψ : R ⧸ J →+* (R ⧸ I) ⧸ J' :=
      Ideal.Quotient.lift J ((Ideal.Quotient.mk J').comp (Ideal.Quotient.mk I)) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.mpr ha
    refine hasRep_quot_of_factor J' (Ideal.Quotient.factor hle) ψ ?_ g (fun B _ hB hgB => ih J hlt B hB hgB)
      A hA hg
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl

theorem hasRep_of_finiteType : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg
  refine _root_.GlobalTheory.DualCon.Step.step R A g hA hg fun J _ => ?_
  exact hasRep_quot_of_factor J (Ideal.Quotient.mk J) (RingHom.id _) rfl g
    (fun B _ hB hgB => hasRep_quot R g J B hB hgB) A hA hg

end GlobalTheory.DualConFT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjTranslationGauge
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

namespace GlobalTheory.Heat.ConjGauge
open ReciprocityTheory.ChartRestriction.G.Semi

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

theorem exists_pullSec {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (m : Y ⟶ X) (T : Y ⟶ Y) (k : ℕ)
    (τ : SecM m L k) : ∃ σ : SecM (T ≫ m) L k, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → sval σ r z J = sval τ (r ≫ T) z J := by
  have hF : FormEq (K := Fin 1 ⊕ PEmpty.{1}) (Sum.elim (fun _ : Fin 1 => T ≫ m) PEmpty.elim)
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) PEmpty.elim) (K' := Fin 1) (fun _ => T ≫ m) (fun _ => (k : ℤ)) := by
    intro U _ h
    simp [Fintype.prod_sum_type]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF (pullMulSec τ T (LB.oneGen L (Y := Y)) (oneGen_isGen L))
  refine ⟨σ, fun Z r z J hJ => ?_⟩
  rw [hσ Z r z J hJ, sval_pullMulSec τ T _ _ r z hJ, val_one, Units.val_one, _root_.mul_one]

theorem conj_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (τ τ' ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → h.Acts k τ τ' → h'.Acts k ρ ρ' := by
  intro R _ _ _ Q O _ _ _ oa Y n v dd hv D h hB x e β he hwt
  obtain ⟨h₁, hΘ₁, hu₁, hB₁, hA₁⟩ := _root_.GlobalTheory.HeatTrans.exists_heat_translate R Q O oa Y n v dd hv D h hB x
  obtain ⟨h', hB', hΘ', hu', hA'⟩ := GlobalTheory.T.exists_gauged_torusInvariant_heatOperator R Q O oa Y n v dd hv D x h₁ hB₁ e β he hwt
  refine ⟨h', hB', hΘ'.trans hΘ₁, hu'.trans hu₁, fun k τ τ' ρ ρ' hρ hρ' hact => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_pullSec Q.P.L Q.P.isLB Y.q.left (𝟙 Y.H * (toUnit Y.H ≫ x)).left k τ
  obtain ⟨σ', hσ'⟩ := exists_pullSec Q.P.L Q.P.isLB Y.q.left (𝟙 Y.H * (toUnit Y.H ≫ x)).left k τ'
  exact hA' k σ σ' ρ ρ' (fun Z r z J hJ => by rw [hσ Z r z J hJ]; exact hρ Z r z J hJ)
    (fun Z r z J hJ => by rw [hσ' Z r z J hJ]; exact hρ' Z r z J hJ) (hA₁ k τ τ' σ σ' hσ hσ' hact)

end GlobalTheory.Heat.ConjGauge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConnectionClosedFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_connection_closedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (e : ℕ), 1 ≤ e → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∃ (V : h.J → P.D.toPre.P.A.left.Opens) (ed : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.D.toPre.P.A P.D.toPre.P.L A₀ m₀ (fun r => (ρ r).snd) V h.j ed pb ∧ (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∃ c : P.D.toPre.X →+ k, ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ P.D.toPre.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ O : A₀.left.Opens, O ≤ m₀ ⁻¹ᵁ LB.wchart P.D.toPre.P.L (P.D.toPre.famφB α) (fun j => h.j (i j)) → (∀ j, O ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) O = 2 * (e : Γ(A₀.left, O)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) O + pbT m₀ (σ.f (fun j => h.j (i j))) O * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, O)) * pbT (T j) (pb (i j)) O + constFn A₀.hom O (c α))) := by
  first | exact @GlobalTheory.HeatConn.heat_connection | exact GlobalTheory.HeatConn.heat_connection | (intros; apply GlobalTheory.HeatConn.heat_connection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDimStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim : ∀ (K : Type) [Field K] (A B : AbVar K), Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧ Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  first | (exact @GlobalTheory.AV.AbVar.hom_finite_free_rank_le) | (exact GlobalTheory.AV.AbVar.hom_finite_free_rank_le) | (intros; apply GlobalTheory.AV.AbVar.hom_finite_free_rank_le  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaTermsTorsionPointsFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.Poinc.Sep.FrameInt

theorem exists_rescale_gen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (u : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t' r z J = gm r z ⊤ u * val t r z J := by
  refine ⟨⟨fun j => t.s j * res le_top u⟩, fun i j => ?_, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, ht i j, _root_.mul_assoc]
    refine congrArg (fun q => _ * (_ * q)) (unit_ext fun y hy => ?_)
    exact ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · exact (map_mul _ _ _).trans ((mul_comm _ _).trans (congrArg (· * _) (gm_res r z le_top (hJ.mem φ r) u)))

end GlobalTheory.Poinc.Sep.FrameInt

namespace GlobalTheory.Poinc.Sep.FrameInt

theorem gs_top_eq {V : Type} [CommRing V] [IsDomain V] (a : V) (z : (TF (R := V) (FractionRing V)).left) :
    gs (toUnit (TF (R := V) (FractionRing V))).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  rw [toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

theorem map_map_unit {V : Type} [CommRing V] (ε : Vˣ) :
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom ε) : Vˣ) : V) = ε := by
  show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ε) = ε
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Poinc.Sep.FrameInt


open GlobalTheory.Poinc.Sep.FrameInt in
theorem GlobalTheory.Poinc.Sep.FrameInt.integral_terms : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)) (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))) (s₀ : V₁), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ (m ^ 2) = 1 → ∃ c, p = toUnit _ ≫ b c) ∧ (∀ c, (t c).IsGen) ∧ (∀ c (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)), Normd κ → ∀ (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → val (t c) r z J ^ ((m ^ 2) ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧ (∀ c (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c).left) z J * (val (t c) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (s₀ * u 0 c)) * (val ρ₀ r z J).val) := by
  intro m hm hm3 V₁ _ _ _ hV hk D X C _ e u mo hmo hT θ hθ ρ₀ hρ₀
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨th, g, b, w, hgb, -, hcov, hw, hcoef, ⟨c₀, hc₀⟩, hbN, hfr, -⟩ :=
    thetaTerms_integral D hN1 e _ hT

  have ht : ∀ c, ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)), t.IsGen ∧
      ∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J = val (w c) (𝟙 _) z J := by
    intro c
    obtain ⟨t', ht'⟩ := _root_.GlobalTheory.GenLocal.exists_gen_unit_point V₁ D (b c)
    obtain ⟨ε, hε⟩ := hfr c t' ht'
    obtain ⟨t, htg, htv⟩ := exists_rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε)
    refine ⟨t, htg, fun z J hJ => Units.ext ?_⟩
    rw [htv _ _ z J hJ, Units.val_mul, hε z J hJ, gm_top_eq, map_map_unit]
  choose t htg htv using ht

  obtain ⟨ν, hν⟩ := exists_ratio (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.P.isLB rfl ρ₀ D.rig hρ₀ D.rig_gen
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.thetaFamily_term_zero_integral_torusPoint V₁ D θ hθ th
  choose f hf using fun c => _root_.GlobalTheory.IntPointFn.fn_of_theta V₁ D θ (b c) (t c) (htg c) ρ₀ hρ₀
  obtain ⟨z⟩ := exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have hTF : (TF (R := V₁) (FractionRing V₁)).hom = (toUnit (TF (R := V₁) (FractionRing V₁))).left := by
    simpa using (Over.w (toUnit (TF (R := V₁) (FractionRing V₁)))).symm
  set ν' : V₁ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom.toMonoidHom ν with hν'
  have key : ∀ c, algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) =
      lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' := by
    intro c
    have h0 := hcoef 0 c
    rw [show e 0 = 0 from map_zero e] at h0
    have a := hlam (g c) (b c) (hgb c) (w c) _ h0 z J hJ
    rw [← htv c z J hJ, _root_.mul_assoc, hf c _ _ z J hJ, gs_top_eq,
      hν _ _ z J hJ, Units.val_mul, gm_top_eq, rigV, hTF] at a
    have a' : cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0)) *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val =
        cst (FractionRing V₁) z (lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν') *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val := by
      rw [a, cst_eq, cst_eq, cst_eq, cst_eq, map_mul, map_mul]
      ring
    exact cst_inj z ((Units.isUnit _).mul_left_inj.1 a')

  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  have hlam0 : lam ≠ 0 := by
    intro h
    have := key c₀
    rw [h, zero_mul, zero_mul] at this
    have h1 : u 0 c₀ * mo 0 = 1 := hc₀
    rw [h1, map_one] at this
    exact one_ne_zero this
  have hν0 : algebraMap V₁ (FractionRing V₁) (ν' : V₁) ≠ 0 :=
    (IsUnit.map (algebraMap V₁ (FractionRing V₁)) ν'.isUnit).ne_zero
  have cross : ∀ c, f c * u 0 c₁ = f c₁ * u 0 c := by
    intro c
    apply hinj
    have k1 := key c
    have k2 := key c₁
    have : lam * algebraMap V₁ (FractionRing V₁) ν' *
        algebraMap V₁ (FractionRing V₁) (f c * u 0 c₁) =
        lam * algebraMap V₁ (FractionRing V₁) ν' * algebraMap V₁ (FractionRing V₁) (f c₁ * u 0 c) := by
      rw [map_mul, map_mul]
      have e1 : lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) = algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) := by rw [k1]
      have e2 : lam * algebraMap V₁ (FractionRing V₁) (f c₁) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c) = algebraMap V₁ (FractionRing V₁) (u 0 c₁ * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c) := by rw [k2]
      simp only [map_mul] at e1 e2
      linear_combination e1 - e2
    exact mul_left_cancel₀ (mul_ne_zero hlam0 hν0) this
  refine ⟨b, t, f c₁ * ↑(hc₁.unit⁻¹), hcov, htg, ?_, ?_⟩
  · intro c κ hκ Z r z' J' hJ'
    refine GlobalTheory.T.integralFrame_identity_of_genericPoint V₁ D (m ^ 2) (b c) (hbN c) (t c) (htg c) κ hκ (fun y I hI => ?_) Z r z' J' hJ'
    rw [htv c y I hI]
    have := (hw c).2 κ hκ y I hI
    rwa [show (g c).b.left = (toUnit (TF (R := V₁) (FractionRing V₁))).left ≫ (b c).left from
      congrArg (fun q => q.left) (hgb c)] at this
  · intro c Z r z' J' hJ'
    have hs : f c = f c₁ * ↑(hc₁.unit⁻¹) * u 0 c := by
      rw [mul_right_comm, ← cross c, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]
    rw [hf c Z r z' J' hJ', hs]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingPairsOfPrincipalisationStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nadel_vanishing_pairs_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair := by
  first | exact @GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | exact GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | (intros; apply GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation <;> assumption)
end

