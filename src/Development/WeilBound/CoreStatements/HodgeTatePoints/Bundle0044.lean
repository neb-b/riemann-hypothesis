module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoPiece
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWLift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0019
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A36
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0009
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RdBase
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0047

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.A53
section
namespace PositivityTheory.HtPt.Ktw

theorem a52 :
    GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.proof
    GroundTheory.Heights₂.Heights.Kleiman.GlobalFunctionsIntegral.proof

theorem a53 :
    GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.proof a52

theorem a54 :
    GroundTheory.Heights₂.Heights.Kleiman.CutComponent.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutComponent.proof
    GroundTheory.Heights₂.Heights.Kleiman.CutZeroNotLe.proof a53
    GroundTheory.Heights₂.Heights.Kleiman.CutDimLower.proof

theorem a55 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.proof hR
    GroundTheory.Heights₂.Heights.Kleiman.PointDegreePos.proof a54
    GroundTheory.Heights₂.Heights.Kleiman.CutMultPos.proof

theorem a56 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.proof
    GroundTheory.Heights₂.Heights.Kleiman.ZeroIdealChart.proof

theorem a57 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.proof
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.Exists.proof

theorem a58 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.proof a57
    GroundTheory.Heights₂.Heights.Kleiman.QuotTrans.proof
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Piece.proof

theorem a59 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimVanish.Statement.{0, 0} :=
  PositivityTheory.HtPt.KtwS.ClaimVanish.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof a56

theorem a60 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Statement.{0, 0, 0} :=
  PositivityTheory.HtPt.KtwS.StepTwo.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof

theorem a61 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.proof a56 a59 a60

theorem a62 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.proof a4
    GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated.proof

theorem a63 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

theorem a72 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

end PositivityTheory.HtPt.Ktw
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfTop
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.HopfOrderEqTop

theorem btOrder_eq_top (hHenselian : type_of% @_root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime) (hBaseChange : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T]
    [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hU : Γ.IsFinOpenSub U) :
    Γ.btOrder U = Γ.btOrder ⊤ := by
  ext f
  rw [PositivityTheory.HtPt.Twhopf.mem_order, PositivityTheory.HtPt.Twhopf.mem_order]
  refine ⟨fun hf t g _ => ?_, fun hf t g _ => hf t g trivial⟩
  obtain ⟨R', _, _, _, _, hN, hflat, hP⟩ :=
    @hHenselian R _ _ _ (Γ.G.hom g).asIdeal (Γ.G.hom g).isPrime
  have hinj : Function.Injective (algebraMap R R') := FaithfulSMul.algebraMap_injective R R'
  obtain ⟨Γ', F, hF⟩ := hBaseChange R T Γ R' (algebraMap R R') hinj
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp (algebraMap R R')) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hinj
  let κ : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hκa : ∀ r, κ (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) := fun r =>
    IsFractionRing.lift_algebraMap hinj' r
  have hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') := RingHom.ext hκa
  obtain ⟨g', hg1, hg2⟩ := Scheme.exists_preimage_of_isPullback hF.cart g (IsLocalRing.closedPoint R') (by
    apply PrimeSpectrum.ext
    exact hP.symm)
  haveI := Γ'.quasiFinite
  haveI := Γ'.finPres
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  obtain ⟨U', hU'fin, hU'cl⟩ := PositivityTheory.HtPt.Twhopf.finite_part R' Γ'.G.left Γ'.G.hom
  have hU' := PositivityTheory.HtPt.Twhopf.finite_sub R' T Γ' U' hU'fin hU'cl
  have hFU := _root_.GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange R T Γ R' Γ' F hF U hU
  have hle : F ⁻¹ᵁ U ≤ U' := PositivityTheory.HtPt.Twhopf.finite_le R' _ Γ'.G.hom _ _ hFU.finite hU'cl
  have h1 : (fun h => algebraMap R R' (f h)) ∈ Γ'.btSet (F ⁻¹ᵁ U) := by
    intro s x hx
    have := hRegular R T Γ R' Γ' F hF κ hκ _ x (hf s (F x) hx)
    simpa only [hκa] using this
  rw [← PositivityTheory.HtPt.Twhopf.mem_order, ← _root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le R' T Γ' U' _ hU' hFU hle, PositivityTheory.HtPt.Twhopf.mem_order] at h1
  rw [← hg1]
  refine PositivityTheory.HtPt.Htat.bt_reg_descent R T Γ R' Γ' F hF hflat κ hκ _ g' ?_
  simpa only [hκa] using h1 t g' (hU'cl g' hg2)

end PositivityTheory.HtPt.Htat.HopfOrderEqTop

theorem PositivityTheory.HtPt.Htat.bt_sub_eq_top_of (hHenselian : type_of% @_root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime) (hBaseChange : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  @PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RdNonunit
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

section

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem sq_le_aug {X : Type} [AddCommGroup X] {M : Submodule R (X → C)}
    (hmul : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M) : sqIdeal (augIdeal M) ≤ augIdeal M := by
  rw [sqIdeal, Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine mem_aug.2 ⟨hmul a ha.1 b hb.1, ?_⟩
  rw [Pi.mul_apply, (mem_aug.1 ha).2, zero_mul]

theorem adjoin_decomp (p : ℕ) {N : Type} [AddCommGroup N] {M : Submodule R (N → C)}
    (hone : (1 : N → C) ∈ M) (hmul : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M) (hint : M ≤ intFun R N)
    {g : N → C} (hg : g ∈ Algebra.adjoin R ((afFun p M : Submodule R (N → C)) : Set (N → C))) :
    ∃ r : R, ∃ h ∈ afFun p M ⊓ augIdeal M, ∃ w ∈ sqIdeal (augIdeal M),
      g = r • (1 : N → C) + h + w := by
  induction hg using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨hg, hadd⟩ := hg
    obtain ⟨r, hr⟩ := hint hg 0
    have hval : ∀ x, (g - r • (1 : N → C)) x = g x - g 0 := fun x => by
      simp [Algebra.smul_def, hr]
    have hm : g - r • (1 : N → C) ∈ M := M.sub_mem hg (M.smul_mem r hone)
    refine ⟨r, g - r • (1 : N → C), ⟨⟨hm, fun x y => ?_⟩, mem_aug.2 ⟨hm, ?_⟩⟩, 0,
      Submodule.zero_mem _, by abel⟩
    · have := Submodule.sub_mem _ (hadd x y) (hadd 0 0)
      convert this using 1
      simp only [hval, add_zero]; ring
    · rw [hval, sub_self]
  | algebraMap r =>
    exact ⟨r, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by
      rw [add_zero, add_zero, Algebra.algebraMap_eq_smul_one]⟩
  | add a b _ _ ha hb =>
    obtain ⟨r, h, hh, w, hw, rfl⟩ := ha
    obtain ⟨r', h', hh', w', hw', rfl⟩ := hb
    exact ⟨r + r', h + h', Submodule.add_mem _ hh hh', w + w', Submodule.add_mem _ hw hw', by
      rw [add_smul]; abel⟩
  | mul a b _ _ ha hb =>
    obtain ⟨r, h, hh, w, hw, rfl⟩ := ha
    obtain ⟨r', h', hh', w', hw', rfl⟩ := hb
    refine ⟨r * r', r • h' + r' • h,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hh') (Submodule.smul_mem _ _ hh),
      r • w' + r' • w + (h + w) * (h' + w'),
      Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hw')
        (Submodule.smul_mem _ _ hw)) (Submodule.subset_span
          ⟨h + w, Submodule.add_mem _ hh.2 (sq_le_aug hmul hw),
            h' + w', Submodule.add_mem _ hh'.2 (sq_le_aug hmul hw'), rfl⟩), ?_⟩
    simp only [Algebra.smul_def, map_mul]
    ring

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {N : Type} [AddCommGroup N] [Module F N]

theorem proj_add (χ : MulChar F R) (g h : N → C) (x : N) :
    proj χ (g + h) x = proj χ g x + proj χ h x := by
  simp only [proj, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem proj_line (χ : MulChar F R) (g : N → C) (t : N) :
    proj χ (g ∘ LinearMap.toSpanSingleton F N t) 1 = proj χ g t := by
  simp [proj]

theorem proj_self [CharZero C] (χ : MulChar F R) (g : N → C) (t : N) (c : R)
    (hg : ∀ a : F, g (a • t) = algebraMap R C (c * χ a)) : proj χ g t = algebraMap R C c := by
  have h1 : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • t) = algebraMap R C c := by
    intro a
    have : χ⁻¹ (a : F) * χ a = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply_coe]
    rw [hg, ← map_mul, mul_left_comm, this, mul_one]
  have h0 : (Fintype.card Fˣ : C) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [proj, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]

end

theorem a_nonunit_of (hproj : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_character) (hstep : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_translation)
    (hom : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_product) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) := by
  intro p hp C _ _ _ v R _ _ hv hp1 F _ _ _ _ f hF N _ _ _ _ AA hst K t ht hgen τ hτ c' c hc' hc hlt
  obtain ⟨⟨S, hS, hSst⟩, -⟩ := hstep p C v R hv hp1 F f hF N AA hst K t ht
  have hprin := GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp1 F f hF S hSst
  choose cc hcc0 hcc using fun χ => (hprin χ).1
  have hcm : c ∈ idealX AA.carrier K t (τ ^ p) := by rw [hc]; exact Ideal.mem_span_singleton_self c
  obtain ⟨g₀, hg₀, e₀⟩ := hcm
  have e1 : ∀ a : F, g₀ (a • t) = algebraMap R C (c * (τ ^ p) a) := fun a => by
    have := congrFun e₀ a
    simpa [LinearMap.funLeft_apply, Algebra.smul_def] using this
  have hmul : ∀ a ∈ invFun AA.carrier K.toAddSubgroup, ∀ b ∈ invFun AA.carrier K.toAddSubgroup,
      a * b ∈ invFun AA.carrier K.toAddSubgroup := fun a ha b hb =>
    ⟨AA.mul_mem a b ha.1 hb.1, fun x k hk => by
      rw [Pi.mul_apply, Pi.mul_apply, ha.2 x k hk, hb.2 x k hk]⟩
  obtain ⟨r, h, ⟨hh, hh0⟩, w, hw, e⟩ := adjoin_decomp p (M := invFun AA.carrier K.toAddSubgroup)
    ⟨AA.one_mem, fun _ _ _ => rfl⟩ hmul (fun a ha => AA.le_int ha.1) (hgen hg₀)
  have hw0 := (mem_aug.1 (sq_le_aug hmul hw)).2
  have hr : r • (1 : N → C) = 0 := by
    have h1 := congrFun e 0
    have h2 := e1 0
    rw [zero_smul, MulChar.map_zero, mul_zero, map_zero] at h2
    rw [h2, Pi.add_apply, Pi.add_apply, (mem_aug.1 hh0).2, hw0, add_zero, add_zero] at h1
    funext x
    exact h1.symm
  rw [hr, zero_add] at e
  have hwS : w ∘ LinearMap.toSpanSingleton F N t ∈ sqIdeal (augIdeal S.carrier) :=
    sq_pull _ (fun g hg => by rw [hS]; exact ⟨g, hg, rfl⟩) hw
  have hwS' := sq_le_aug (fun a ha b hb => S.mul_mem a b ha hb) hwS
  obtain ⟨w1, -, -, -, w5⟩ := hproj p C v R hv hp1 F f hF F S hSst τ hτ _ hwS'
  obtain ⟨ρ, -, hρ⟩ := ((hprin (τ ^ p)).2 _).1 (w1 (τ ^ p))
  have hρ1 := w5 hwS (τ ^ p)
  have hρ2 : ρ ∈ Ideal.span {cc (τ ^ p ^ 0) ^ p} := by
    refine ((hom p C v R hv hp1 F f hF S hSst τ hτ (fun n => cc (τ ^ p ^ n)) (fun n => hcc _)
      0).1 ρ).1 ?_
    rw [zero_add, pow_one, ← hρ]
    exact hρ1
  have hcc' : cc (τ ^ p ^ 0) ∈ Ideal.span {c'} := by
    rw [← hc', idealX, ← hS, pow_zero, pow_one, hcc]
    exact Ideal.mem_span_singleton_self _
  have hρ3 : v (algebraMap R C ρ) < v (algebraMap R C c) := by
    refine lt_of_le_of_lt ?_ hlt
    rw [← map_pow, ← map_pow]
    exact hv.le_of_dvd ((pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.1 hcc') p).trans
      (Ideal.mem_span_singleton.1 hρ2))
  have hwt : proj (τ ^ p) w t = algebraMap R C ρ := by
    rw [← proj_line, hρ]
    simp
  have hht : proj (τ ^ p) h t = algebraMap R C (c - ρ) := by
    have := proj_self (τ ^ p) g₀ t c e1
    rw [e, proj_add, hwt] at this
    rw [map_sub, ← this, add_sub_cancel_right]
  obtain ⟨q1, -, q3, q4, -⟩ := hproj p C v R hv hp1 F f hF N AA hst τ hτ h
    (mem_aug.2 ⟨hh.1.1, (mem_aug.1 hh0).2⟩)
  have hD : c - ρ ∈ idealD p AA.carrier K t (τ ^ p) := by
    refine ⟨proj (τ ^ p) h, q3 ⟨hh.1.1, hh.2⟩ _, fun a x => ?_, fun k hk => ?_, ?_⟩
    · rw [(q1 (τ ^ p)).2 a x, sub_self]; exact Submodule.zero_mem _
    · have := (q4 K hh.1 (τ ^ p)).2 0 k hk
      rw [zero_add, eig_zero (q1 (τ ^ p))] at this
      rw [this]; exact Submodule.zero_mem _
    · rw [hht, sub_self]; exact Submodule.zero_mem _
  have hdvd : c - ρ ∣ c := by
    apply hv.dvd_of_le
    rw [map_sub, v.map_sub_eq_of_lt_left hρ3]
  exact Ideal.mem_of_dvd _ hdvd hD

end PositivityTheory.HtPt.Rd
end

