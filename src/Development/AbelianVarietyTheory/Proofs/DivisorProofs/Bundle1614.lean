module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1590
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeSplitPlaceEqAddComponentPartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLatticeSplitPlace_eq_add_componentParts : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γA ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γB ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
        γ = γA + γB ∧ γA.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
          γB.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 := by
  first | exact @GlobalTheory.SplitPlaceLat.latAtV_eq_add_parts | exact GlobalTheory.SplitPlaceLat.latAtV_eq_add_parts | (intros; apply GlobalTheory.SplitPlaceLat.latAtV_eq_add_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem zCo_iota {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hch : GlobalTheory.FockCompare.Chart θ σ) {S T : HSp D}
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (z : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) =
      fun τ => (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ := by
  funext τ
  have e : compAt θ τ (GlobalTheory.FockCompare.iotaW σ T S z) = Matrix.of (z τ) := congrFun (hch.pi_iota T S z) τ
  simp only [GlobalTheory.FockPos.zCo, e]
  rfl

theorem frAt_inv {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt fr τ)⁻¹ * GlobalTheory.FockPos.frAt fr τ = 1 ∧ GlobalTheory.FockPos.frAt fr τ * (GlobalTheory.FockPos.frAt fr τ)⁻¹ = 1 :=
  ⟨Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ)),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ))⟩

theorem coord_back {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹) *
      GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) := by
  have h1 := (frAt_inv frS τ).1
  have h2 := (frAt_inv frT τ).1
  calc _ = ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * GlobalTheory.FockPos.frAt frT τ) * Matrix.of (Z τ) *
        ((GlobalTheory.FockPos.frAt frS τ)⁻¹ * GlobalTheory.FockPos.frAt frS τ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ThetaLawOF

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem trace_conjTranspose_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    (Aᴴ * B).trace = ∑ a, ∑ b, starRingEnd ℂ (A a b) * B a b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

theorem omO_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (x y : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.VacUnique.omO S T x y = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (y τ) * GlobalTheory.FockPos.frAt frS τ) a b) *
        ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (x τ) * GlobalTheory.FockPos.frAt frS τ) a b)).re := by
  rw [GlobalTheory.VacUnique.omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (Matrix.of (x τ)) (Matrix.of (y τ))).re = _
  rw [GlobalTheory.FockJetOrigin.hAt_coord (BS := fun τ => GlobalTheory.FockPos.frAt frS τ)
    (BT := fun τ => GlobalTheory.FockPos.frAt frT τ) (GlobalTheory.FockPos.frAt_on frS hS τ) (GlobalTheory.FockPos.frAt_on frT hT τ),
    trace_conjTranspose_mul, GlobalTheory.FockJetOrigin.realPlace_cmTrace_zero_element_eq_I_mul_abs, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]

theorem torusHermitianForm_scaled_coordinate_eq {N N' : ℕ} {δ : ℂ} (hδ : δ ≠ 0) (Z X : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Z) (δ • X) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b) := by
  have e : (∑ τ, ∑ i, ∑ j, (δ • Z) τ i j * starRingEnd ℂ ((δ • X) τ i j)) =
      (δ * starRingEnd ℂ δ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hL : (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ).abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ := rfl
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, e, hL, GlobalTheory.MomDict.area_lamOf D D.host.ccK δ D.host.ccK_ne_bot, hxi, Complex.mul_conj]
  have h0 : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hδ).ne'
  have h1 : ((Ideal.absNorm D.host.ccK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0)
  have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : Real.sqrt D.host.d ≠ 0)
  push_cast
  field_simp

theorem al_mul_self {N N' : ℕ} (T0 : Formalism.MainNotions.TaylorLogMetric.Tor D) (x : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.al D T0 x * Formalism.MainNotions.TaylorLogMetric.al D T0 x = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.al, ← mul_zpow, show (-1 : ℂ) * -1 = 1 by norm_num, _root_.one_zpow]

theorem entry (zz xx : ℂ) (r : ℝ) :
    (Real.pi : ℂ) * Complex.I * ((2 * (Complex.I * (r : ℂ) * (starRingEnd ℂ zz * xx)).re : ℝ) : ℂ) -
      2 * (Real.pi : ℂ) * (r : ℂ) * (zz * starRingEnd ℂ xx) - (Real.pi : ℂ) * (r : ℂ) * (xx * starRingEnd ℂ xx) =
      (Real.pi : ℂ) * (r : ℂ) * ((‖zz‖ ^ 2 : ℝ) - (‖zz + xx‖ ^ 2 : ℝ) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

end GlobalTheory.ThetaLawOF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualRingOfIntegersIffOfUnramifiedExtension
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped nonZeroDivisors

namespace GlobalTheory.UnrTraceDual

theorem traceDual_ringOfIntegers_iff_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔ ∀ d ∈ differentIdeal ℤ (𝓞 F), IsIntegral ℤ (algebraMap F E (d : F) * e) := by
  intro F E _ _ _ _ _ hU e
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := inferInstance
  have hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]
  have hint : ∀ x : E, IsIntegral ℤ x ↔ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro x
    rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]
  have h1 : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔
      e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    constructor
    · intro h a ha
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 ha
      rw [Algebra.traceForm_apply, mul_comm]
      exact RingHom.mem_range.2 (IsIntegrallyClosed.isIntegral_iff.1 (h o))
    · intro h o
      have := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).2 ⟨o, rfl⟩)
      rw [Algebra.traceForm_apply, mul_comm] at this
      exact IsIntegrallyClosed.isIntegral_iff.2 (RingHom.mem_range.1 this)
  have h2 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  have hne : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [h1, h2, FractionalIdeal.mem_inv_iff hne, hEq]
  let J : Ideal (𝓞 E) :=
    { carrier := {x | IsIntegral ℤ (algebraMap (𝓞 E) E x * e)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _), add_mul] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, zero_mul]
        exact isIntegral_zero
      smul_mem' := by
        intro c x hx
        have hx' : IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := hx
        have hc : IsIntegral ℤ (algebraMap (𝓞 E) E c) := RingOfIntegers.isIntegral_coe c
        show IsIntegral ℤ (algebraMap (𝓞 E) E (c * x) * e)
        rw [map_mul, mul_assoc]
        exact IsIntegral.mul hc hx' }
  have hJ : ∀ x : 𝓞 E, x ∈ J ↔ IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := fun _ => Iff.rfl
  have hL : (∀ y ∈ (((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 E)) :
      FractionalIdeal (𝓞 E)⁰ E), e * y ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔
      (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) ≤ J := by
    constructor
    · intro h x hx
      rw [hJ, hint, mul_comm]
      exact h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hx)
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      rw [mul_comm, ← hint]
      exact (hJ x).1 (h hx)
  rw [hL, Ideal.map_le_iff_le_comap]
  constructor
  · intro h d hd
    have := (hJ _).1 (h hd)
    rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
  · intro h d hd
    show algebraMap (𝓞 F) (𝓞 E) d ∈ J
    rw [hJ, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact h d hd

end GlobalTheory.UnrTraceDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHermitianTensorIntegralOfCharTrivial
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.KFinLoc

theorem symp_incM_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (θ : E) (x y : Matrix (Fin n) (Fin d) E) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) (inclR (F := F) (AF F) θ) (incM F JA) (incM F JB)
      (incM F x) (incM F y) =
      algebraMap F (AF F) (Algebra.trace F E (θ * GlobalTheory.WeilM.hTens σ JA JB x y)) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (AF F ⊗[F] E) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [← ht, GlobalTheory.WeilM.symp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, hc, map_mul, map_sum]

theorem trace_hTens_integral_of_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ X₀ : Matrix (Fin n) (Fin d) E, (∀ γ ∈ latAtV X Y v,
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1) →
    ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v) (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)))
      ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ ψ n d X Y v hψ X₀ h x hx y hy
  refine (hψ _).1 fun t ht => ?_
  have hat : At (evFin F v) (GlobalTheory.EmbChart.atPlace v t) := fun u hu => by
    rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hmem : GlobalTheory.EmbChart.atPlace v t • incM F (Matrix.vecMulVec x y) ∈ latAtV X Y v :=
    AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v t, hat, by rw [GlobalTheory.EmbChart.evFin_atPlace]; exact ht,
      x, hx, y, hy, rfl⟩
  have h1 := h _ hmem
  have hm : (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = inclR (F := F) (AF F) (-1 : E) := by rw [map_neg, map_one]
  rw [GlobalTheory.LatVac.symp_smul_smul, hm, symp_incM_mat, GlobalTheory.EmbChart.atPlace_mul_right,
    GlobalTheory.EmbChart.atPlace_mul_right, GlobalTheory.EmbChart.evFin_atPlace, one_mul, AlgHom.commutes, neg_one_mul,
    mul_comm] at h1
  exact h1

end GlobalTheory.KFinLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupportedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceSymplectic_self_zero_splitSupported : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
    (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∨ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) →
    ∀ ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E),
      symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u = 0 := by
  first | exact @GlobalTheory.VacIso.symp_self_eq_zero | exact GlobalTheory.VacIso.symp_self_eq_zero | (intros; apply GlobalTheory.VacIso.symp_self_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueIndependentOfTheta
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacThetaInd

theorem psi_half_symp_theta_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have ht : cA σ (hTens (cA σ) (incM F X.J) (incM F W.J) γ γ) = -hTens (cA σ) (incM F X.J) (incM F W.J) γ γ :=
    GlobalTheory.VacCocycle.conj_hTens (cA σ) hc (fun i j => by simp only [incM, Matrix.map_apply, hi, hX.herm])
      (fun i j => by simp only [incM, Matrix.map_apply, hi, hW.skew, map_neg]) γ γ
  set t := hTens (cA σ) (incM F X.J) (incM F W.J) γ γ with htdef
  have htr : ∀ z, Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (cA σ z) = Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z :=
    GlobalTheory.VacCocycle.trace_conj (cA σ) hc
  set a := inclR (F := F) (AF F) (θ : E) with ha
  set a' := inclR (F := F) (AF F) (θ' : E) with ha'
  have hca : cA σ a = 1 - a := by
    rw [ha, hi, eq_sub_of_add_eq' hθ, map_sub, map_one]
  have hca' : cA σ a' = 1 - a' := by
    rw [ha', hi, eq_sub_of_add_eq' hθ', map_sub, map_one]
  set z := (a - a') * t with hz
  have hcz : cA σ z = z := by
    rw [hz, map_mul, map_sub, hca, hca', ht]; ring
  have h2 : Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z = 2 * Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (a * z) := by
    have e1 : Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (cA σ (a * z)) = Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (a * z) := htr _
    rw [map_mul, hca, hcz, sub_mul, one_mul, map_sub] at e1
    linear_combination e1
  have hmul : inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E) = a * (a - a') := by
    rw [ha, ha', ← map_sub, ← map_mul]; push_cast; rfl
  have key : symp (R := AF F) (cA σ) a (incM F X.J) (incM F W.J) γ γ =
      symp (R := AF F) (cA σ) a' (incM F X.J) (incM F W.J) γ γ +
        2 * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ := by
    simp only [symp, hmul]
    rw [← htdef, mul_assoc, ← hz, ← h2, hz, sub_mul, map_sub]; ring
  have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v (θ * (θ - θ')) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ hγ
  rw [key, mul_add, ← mul_assoc, invOf_mul_self, one_mul, AddChar.map_add_eq_mul, ← one_mul (symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ), h1, mul_one]

end GlobalTheory.VacThetaInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedUnifAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

namespace GlobalTheory.CondLESplit

open ValuativeRel

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) := by
  have : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))

theorem valued_unifAt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  have he := isEquiv_Fv v
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ' : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    he.lt_one_iff_lt_one.1 (hϖ ▸ uniformizer_lt_one)
  apply le_antisymm
  · have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · rw [← hπ']
    have hπ1 : valuation (Fv F v) ((π : F) : Fv F v) < 1 := by
      refine he.lt_one_iff_lt_one.2 ?_
      rw [hπ', ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    exact (he _ _).1 (hϖ ▸ le_uniformizer_iff.2 hπ1)

end GlobalTheory.CondLESplit

open GlobalTheory.CondLESplit in
theorem GlobalTheory.CondLESplit.condLE_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (ρ : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ →* ℂˣ) (n : ℕ),
    GlobalTheory.SplitFlip.CondLE (unifAt v) n (ρ.comp (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom)) ↔
      ∀ x : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ, Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) x →
        Valued.v ((x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) → ρ x = 1 := by
  intro F E _ _ _ _ _ v τ ρ n
  set hw := GlobalTheory.AdelicU.splitPrime_under τ
  set f := GlobalTheory.LFun.complMap hw
  have he := isEquiv_Fv v
  have hval : ∀ a : Fv F v, Valued.v (f a) = Valued.v a := GlobalTheory.LFun.SplitTie.valued_complMap τ hw
  have hbij : Function.Bijective f := GlobalTheory.LFun.SplitTie.complMap_bijective τ hw
  have key : ∀ y : (Fv F v)ˣ, y ∈ GlobalTheory.SplitFlip.unitCong (unifAt v ^ n) ↔
      (Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) (Units.map f.toMonoidHom y) ∧
        Valued.v (((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
          (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ))) := by
    intro y
    have h1 : ((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
        (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) = f y := rfl
    have hp : Valued.v (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v) = WithZero.exp (-(n : ℤ)) := by
      rw [Units.val_pow_eq_pow_val, map_pow, valued_unifAt, ← WithZero.exp_nsmul]
      congr 1; simp
    show (ValuativeRel.valuation (Fv F v) (y : Fv F v) = 1 ∧ ValuativeRel.valuation (Fv F v) ((y : Fv F v) - 1) ≤
        ValuativeRel.valuation (Fv F v) (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v)) ↔ _
    unfold Formalism.L2.Host.IsUnitAt
    rw [h1, he.eq_one_iff_eq_one, he, hp, ← map_one f, ← map_sub, hval, hval]
  constructor
  · intro h x hx1 hx2
    obtain ⟨a, ha⟩ := hbij.2 (x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [map_zero] at ha; exact x.ne_zero ha.symm
    set y := Units.mk0 a ha0
    have hy : Units.map f.toMonoidHom y = x := Units.ext ha
    have := h y ((key y).2 (hy ▸ ⟨hx1, hx2⟩))
    rw [← hy]; exact this
  · intro h y hy
    exact h _ ((key y).1 hy).1 ((key y).1 hy).2
end

