module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0064
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0605
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharFiniteIdelesIsAlgebraicOfResEta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

section Reformulated
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open IsDedekindDomain NumberField Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinValAlg

theorem isAlgebraic_unit_zpow {z : ℂ} (hz : IsAlgebraic ℚ z) (n : ℤ) :
    IsAlgebraic ℚ ((z / ((‖z‖ : ℝ) : ℂ)) ^ n) := by
  have hc : IsAlgebraic ℚ (starRingEnd ℂ z) := hz.algHom (starRingEnd ℂ).toRatAlgHom
  have hn : IsAlgebraic ℚ (((‖z‖ : ℝ) : ℂ)) := by
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [← Complex.conj_mul']
    exact (mem_algebraicClosure_iff.1 (mul_mem (mem_algebraicClosure_iff.2 hc) (mem_algebraicClosure_iff.2 hz)))
  rw [← mem_algebraicClosure_iff] at hz hn ⊢
  exact zpow_mem (div_mem hz hn) n

variable {D : D7}

theorem finPart_incA (e : D.host.E) : finPart D (incA D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e := by
  change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem int_of_val_eq_one (ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) (z : (AE D)ˣ)
    (hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (z : AE D)) P) = 1) :
    finPart D (z : AE D) ∈ intAE D ∧ finPart D ((z⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  refine ⟨(hι2 _).2 fun P => (hv P).le, (hι2 _).2 fun P => le_of_eq ?_⟩
  have e : ι (finPart D ((z⁻¹ : (AE D)ˣ) : AE D)) * ι (finPart D (z : AE D)) = 1 := by
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  have e2 : ι (finPart D ((z⁻¹ : (AE D)ˣ) : AE D)) P * ι (finPart D (z : AE D)) P = 1 := by
    have := congrArg (fun w : FiniteAdeleRing (𝓞 D.host.E) D.host.E => w P) e
    exact this
  have := congrArg Valued.v e2
  rwa [map_mul, hv, mul_one, map_one] at this

theorem ι_finPart_pow_mul (ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (x : (AE D)ˣ) (h : ℕ) (k : D.host.Eˣ) :
    ι (finPart D ((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D)) =
      ι (finPart D (x : AE D)) ^ h * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) := by
  have e : ((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D) = (x : AE D) ^ h * incA D (k : D.host.E) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  rw [e, map_mul, map_pow, map_mul, map_pow, finPart_incA, hι1]

theorem exists_pow_mul_int (x : (AE D)ˣ) : ∃ h : ℕ, 0 < h ∧ ∃ k : D.host.Eˣ,
    finPart D (((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ)) : AE D) ∈ intAE D ∧
    finPart D ((((x ^ h * Units.map (incA D).toMonoidHom k)⁻¹ : (AE D)ˣ)) : AE D) ∈ intAE D := by
  obtain ⟨ι, hι1, hι2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h, hh, hX⟩ := Formalism.L2.Host.CharEx.classExp D.host.E
  obtain ⟨a, a', haa, haa', ha⟩ : ∃ a a' : Af D.host.F ⊗[D.host.F] D.host.E, a * a' = 1 ∧ a' * a = 1 ∧
      a = finPart D (x : AE D) :=
    ⟨_, _, by rw [← map_mul, Units.mul_inv, map_one], by rw [← map_mul, Units.inv_mul, map_one], rfl⟩
  let X : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨((1 : InfiniteAdeleRing D.host.E), ι a), ((1 : InfiniteAdeleRing D.host.E), ι a'),
      Prod.ext (show (1 : InfiniteAdeleRing D.host.E) * 1 = 1 from mul_one _)
        (show ι a * ι a' = 1 by rw [← map_mul, haa, map_one]),
      Prod.ext (show (1 : InfiniteAdeleRing D.host.E) * 1 = 1 from mul_one _)
        (show ι a' * ι a = 1 by rw [← map_mul, haa', map_one])⟩
  obtain ⟨k, hk⟩ := hX X
  refine ⟨h, hh, k, int_of_val_eq_one ι hι2 _ fun P => ?_⟩
  rw [ι_finPart_pow_mul ι hι1, ← ha]
  have e : ((X ^ h * Neutral.B1.diagUnits D.host.E k : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      AdeleRing (𝓞 D.host.E) D.host.E).2 = ι a ^ h * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  rw [← e]
  exact hk P

end GlobalTheory.FinValAlg

namespace GlobalTheory.FinValAlg

variable {D : D7}

theorem infPart_incA (e : D.host.E) : infPart D (incA D e) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] e := by
  change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem infPart_pairE (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    infPart D (Formalism.L2.Fam.ThC.pairE a b) = a := Formalism.L2.Fam.ThC.fst_pairE a b

theorem finPart_pairE (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (Formalism.L2.Fam.ThC.pairE a b) = b := Formalism.L2.Fam.ThC.snd_pairE a b

theorem pairE_mul_eq_one (z : (AE D)ˣ) :
    Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 * Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 = 1 := by
  refine Formalism.L2.Fam.ThC.ae_ext ?_ ?_
  · rw [map_mul, infPart_pairE, infPart_pairE, ← map_mul, Units.mul_inv]
  · rw [map_mul, finPart_pairE, finPart_pairE, mul_one, map_one]

theorem pairE_mul_eq_one' (z : (AE D)ˣ) :
    Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 * Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 = 1 := by
  refine Formalism.L2.Fam.ThC.ae_ext ?_ ?_
  · rw [map_mul, infPart_pairE, infPart_pairE, ← map_mul, Units.inv_mul]
  · rw [map_mul, finPart_pairE, finPart_pairE, mul_one, map_one]


set_option maxHeartbeats 1000000 in
theorem exists_decomp (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) :
    ∃ h : ℕ, 0 < h ∧ ∃ (k : D.host.Eˣ) (y u : (AE D)ˣ), finPart D (y : AE D) = 1 ∧ Formalism.L2.Pj.FinUnit u ∧
      infPart D (y : AE D) = infPart D (incA D (k : D.host.E)) ∧ x ^ h * Units.map (incA D).toMonoidHom k = y * u := by
  obtain ⟨h, hh, k, h1, h2⟩ := exists_pow_mul_int x
  refine ⟨h, hh, k, ?_⟩
  generalize hz : x ^ h * Units.map (incA D).toMonoidHom k = z at h1 h2
  have hiz : infPart D (z : AE D) = infPart D (incA D (k : D.host.E)) := by
    rw [← hz, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hx, one_pow, one_mul]
    rfl
  have m1 := pairE_mul_eq_one z
  have m2 := pairE_mul_eq_one' z
  obtain ⟨y, hyv, hyi⟩ : ∃ y : (AE D)ˣ, (y : AE D) = Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 ∧
      ((y⁻¹ : (AE D)ˣ) : AE D) = Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 :=
    ⟨⟨_, _, m1, m2⟩, rfl, rfl⟩
  refine ⟨y, y⁻¹ * z, by rw [hyv, finPart_pairE], ⟨?_, ?_, ?_⟩, by rw [hyv, infPart_pairE, hiz], by rw [mul_inv_cancel_left]⟩
  · rw [Units.val_mul, map_mul, hyi, infPart_pairE, ← map_mul, Units.inv_mul, map_one]
  · rw [Units.val_mul, map_mul, hyi, finPart_pairE, one_mul]; exact h1
  · rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul, hyv, finPart_pairE, mul_one]; exact h2

theorem char_eq_prod {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle} (nτ : D.what₂.Tau → ℤ)
    (hn : ∀ τ (x : (AE D)ˣ), finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ nτ τ)
    (y : (AE D)ˣ) (hy : finPart D (y : AE D) = 1) :
    ((χ y : Circle) : ℂ) = ∏ τ, (θ τ (infPart D (y : AE D)) / (‖θ τ (infPart D (y : AE D))‖ : ℂ)) ^ nτ τ := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom hσ
  let wU : D.what₂.Tau → ℂˣ := fun τ => (y.isUnit.map ((θ τ).comp (infPart D))).unit
  have hwU : ∀ τ, ((wU τ : ℂˣ) : ℂ) = θ τ (infPart D (y : AE D)) := fun τ => rfl
  let f : (D.what₂.Tau → ℂ)ˣ →* (AE D)ˣ := Units.map e
  have hf1 : ∀ W, finPart D ((f W : (AE D)ˣ) : AE D) = 1 := fun W => e1 _
  have hf2 : ∀ W τ, θ τ (infPart D ((f W : (AE D)ˣ) : AE D)) = (W : D.what₂.Tau → ℂ) τ := fun W τ => e2 _ τ
  have hy' : y = ∏ τ, f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ))) := by
    rw [← map_prod, ← map_prod, Finset.univ_prod_mulSingle]
    apply Units.ext
    refine GlobalTheory.SplitCharExp.ext_of_chart hσ (by rw [hy, hf1]) fun τ => ?_
    rw [hf2]
    exact (hwU τ).symm
  have hc : ((χ y : Circle) : ℂ) = ∏ τ, ((χ (f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ)))) : Circle) : ℂ) := by
    show Circle.coeHom (χ y) = ∏ τ, Circle.coeHom (χ (f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ)))))
    rw [← map_prod, ← map_prod, ← hy']
  rw [hc]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hs : ∀ τ', θ τ' (infPart D ((f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ))) : (AE D)ˣ) : AE D)) =
      (((Pi.mulSingle τ (wU τ) : D.what₂.Tau → ℂˣ) τ' : ℂˣ) : ℂ) := fun τ' => by rw [hf2]; rfl
  rw [hn τ _ (hf1 _) fun τ' h => by rw [hs, Pi.mulSingle_eq_of_ne h, Units.val_one], hs, Pi.mulSingle_eq_same, hwU]

theorem isAlgebraic_of_infPart_eq_one : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ},
    IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) := by
  intro D θ χ n hθ hχ hr x hx
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ n τ hθ hχ hr
  choose nτ hn2 hn using ha
  have hn' : ∀ τ (x : (AE D)ˣ), finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ nτ τ :=
    fun τ => (hn τ).2 θ hθ
  obtain ⟨h, hh, k, y, u, hy1, hu, hyi, e⟩ := exists_decomp x hx
  obtain ⟨-, -, -, m, hm, hum⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ.1
  have hyalg : IsAlgebraic ℚ ((χ y : Circle) : ℂ) := by
    rw [char_eq_prod hθ nτ hn' y hy1, ← mem_algebraicClosure_iff]
    refine prod_mem fun τ _ => ?_
    rw [mem_algebraicClosure_iff, hyi, infPart_incA, (hθ τ).1]
    exact isAlgebraic_unit_zpow (GlobalTheory.isAlgebraic_embedding_apply _ _) _
  have e2 : χ x ^ (h * m) = χ y ^ m := by
    have := congrArg (fun g => χ g ^ m) e
    simp only [map_mul, mul_pow, hum u hu, mul_one, hχ.2 k, one_pow, map_pow] at this
    rw [pow_mul]
    exact this
  refine IsAlgebraic.of_pow (Nat.mul_pos hh hm) ?_
  rw [← Circle.coe_pow, e2, Circle.coe_pow, ← mem_algebraicClosure_iff]
  exact pow_mem (mem_algebraicClosure_iff.2 hyalg) _

end GlobalTheory.FinValAlg

end

end Reformulated

theorem GlobalTheory.FinValAlg.finite_values_isAlgebraic : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ}, IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) :=
  GlobalTheory.FinValAlg.isAlgebraic_of_infPart_eq_one
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeReadProof

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem phiW_eq {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i))
    (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom) :
    phiW T i σ hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := by
  show T.phiJ _ σ a f _ = _
  rw [CoreJ.phiJ_apply]
  simp only [Core.phiAd, Pi.smul_apply, smul_eq_mul, adel, rdU, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [dictW, castDict] at hx ⊢
  split_ifs with h1
  · ring
  · exact absurd hx h1

theorem heckeReadTie (hSL : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D) (hVF : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D) :
    GlobalTheory.HeckeSupSt.HeckeReadTie := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hlev hgrp hfam hmod hthP ht i σ hσ hV hpin
  intro P p k α Rc hs cq f g hf hg hr h
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hgood : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  obtain ⟨hx, -, -⟩ := exists_witness T i σ hV ht.laws.toLawsM hgood h
  obtain ⟨e, he⟩ := GlobalTheory.T.heckeReading_kernels_match_cosets_through_frame D GlobalTheory.HeckePointLaw.heckePointLaws (hSL D) (hVF D) G Pl0 T0 A T R F κ v₀ hlev hgrp hfam
    hmod hthP ht i σ hσ hV hpin P p k α Rc hs h hx
  have hfin : Finite (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := Finite.of_equiv _ e.symm
  rw [phiW_eq T i σ hV _ g h hx]
  have hr' := hr (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)
  have e1 : toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c g
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) =
      σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * ∑ᶠ C,
        toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) := by
    refine (congrArg toC hr').trans ?_
    have hs1 : σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) = σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) := by
      simp only [hkScal, one_mul, map_mul]
    show σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) * toC (hkVal _ _ _ _ f _) = _
    rw [hs1]
    congr 1
    unfold hkVal
    show (∑ᶠ C, toC (hkTerm _ _ _ _ f _ C)) = _
    refine finsum_congr fun C => ?_
    unfold hkTerm
    split_ifs with h1
    · rfl
    · exact absurd (he C).1 h1
  rw [e1]
  have e2 : ∀ C, (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) =
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) :=
    fun C => (he C).2 _ (he C).1.choose_spec f hf
  have e3 : ∑ᶠ C, (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) =
      (muAt T R i P)⁻¹ ^ k * ∑ a ∈ Rc, phiW T i σ hV (wtA (κ i)) f (h * a) := by
    rw [finsum_comp_equiv e (f := fun a : Rc =>
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (a : GA D (Wc D i))))]
    rw [finsum_eq_sum_of_fintype, Finset.sum_coe_sort Rc
      (fun a => (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * a)), Finset.mul_sum]
  rw [mul_assoc (σ cq) ((muAt T R i P)⁻¹ ^ k), ← e3, ← finsum_congr e2, ← mul_finsum]
  ring

end GlobalTheory.HeckeReadProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutantPermutesFirstRowCosetVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.CosPerm

variable {D : D7}

theorem heisO_smul_fun (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem heisO_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (star f) = star (heisO ψ (negSp S) T w f) := by
  have h := GlobalTheory.CjNeg.heis_negS hψ S T w (star f)
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star f) = f := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hc] at h
  rw [h]; funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem symplO_negSp (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.CjNeg.symplOH_negS]; ring

theorem mem_ann_negSp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Γ : AddSubgroup (WO S T)} {w : WO S T}
    (hw : w ∈ Ann ψ S T Γ) : w ∈ Ann ψ (negSp S) T Γ := by
  have key : ∀ a b : WO S T, ψ (symplO S T a b) = 1 → ψ (symplO (negSp S) T a b) = 1 := fun a b h => by
    rw [symplO_negSp, AddChar.map_neg_eq_inv, h, inv_one]
  exact ⟨fun u hu => key _ _ (hw.1 u hu), fun e he u hu hh => key _ _ (hw.2 e he u hu hh)⟩

end GlobalTheory.CosPerm


open GlobalTheory.CosPerm in
theorem GlobalTheory.CosPerm.cosVec_perm : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ)) ∧ VacG W.ψ _ _ (latRow G i) (star (W.cosVec i κ)) ∧ ∀ w ∈ Ann W.ψ _ _ (latRow G i), w.map (infPart D) = 0 → heisO W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) w (star (W.cosVec i κ)) ∈ Submodule.span ℂ (Set.range fun κ' => (star (W.cosVec i κ') : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) → ℂ)) := by
  intro D hD T L μ0 hL sc G W M hM i hi κ
  obtain ⟨h1, hdep, hfock⟩ := _root_.GlobalTheory.CosDep.cosVec_dep D hD T L μ0 hL sc G W M hM i hi κ
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hth := (GlobalTheory.CjNeg.theta_heis_neg D W.ψ hψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))).1 (star (W.cosVec i κ))
  have hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star (W.cosVec i κ)) = W.cosVec i κ := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hcj] at hth
  refine ⟨h1, hfock, ⟨hth.2.1 hdep.1, fun u hu => ?_, fun e he u hu hh => ?_⟩, ?_⟩
  · rw [heisO_star hψ]; exact congrArg star (hdep.2.1 u hu)
  · rw [heisO_star hψ]; exact congrArg star (hdep.2.2 e he u hu hh)
  intro w hw hfin
  have hw' : w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)) := mem_ann_negSp hw
  obtain ⟨e, he, hthe⟩ := W.cosVec_is
  have hthi := fun κ => hthe i hi κ
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.heisenberg_offPart_vacuumCommutant_acts_by_scalar D hD T L μ0 hL sc G W M hM i hi e he w hw' hfin
  obtain ⟨c₃, h₃⟩ := _root_.GlobalTheory.ThetaEigen.heisO_eigen_of_isThetaAt D W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) e
    (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True)
    (W.vac i) (cosInd e κ) (W.cosVec i κ) ((1 - e - cA D e) • w) c₀ (hthi κ)
    (fun x hx => _root_.GlobalTheory.IdemOffOrth.symplO_compl_half D (G.pS (.chi i 0)) (G.pT (.chi i 0)) G.pl.W0 e he w x (Or.inl hx))
    (fun y hy => _root_.GlobalTheory.IdemOffOrth.symplO_compl_half D (G.pS (.chi i 0)) (G.pT (.chi i 0)) G.pl.W0 e he w y (Or.inr hy)) hc₀
  obtain ⟨c₂, h₂⟩ := _root_.GlobalTheory.CosScalar.conjHalf_heisO_cosVec_smul D hD T L μ0 hL sc G W M hM i hi e he hthi w hw' hfin κ
  obtain ⟨κ', h₁⟩ := _root_.GlobalTheory.CosShift.epart D hD T L μ0 hL sc G W M hM i hi e he hthi w hw' hfin κ
  have hdec : w = e • w + (cA D e • w + (1 - e - cA D e) • w) := by
    rw [← add_smul, ← add_smul, show e + (cA D e + (1 - e - cA D e)) = 1 by ring, one_smul]
  have hne : ∀ a, W.ψ a ≠ 0 := fun a h => by
    have := AddChar.map_add_eq_mul W.ψ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have e1 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := W.ψ) (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
    (cA D e • w) ((1 - e - cA D e) • w) (W.cosVec i κ)
  rw [h₃, heisO_smul_fun, h₂, smul_smul] at e1
  have e1' : heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w + (1 - e - cA D e) • w) (W.cosVec i κ) =
      (W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) ((1 - e - cA D e) • w)))⁻¹ • ((c₃ * c₂) • W.cosVec i κ) := by
    rw [e1, inv_smul_smul₀ (hne _)]
  have e2 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := W.ψ) (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
    (e • w) (cA D e • w + (1 - e - cA D e) • w) (W.cosVec i κ)
  rw [← hdec, e1', heisO_smul_fun, heisO_smul_fun, h₁] at e2
  have hC : heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (W.cosVec i κ) =
      ((W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (e • w) (cA D e • w + (1 - e - cA D e) • w)))⁻¹ *
        ((W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) ((1 - e - cA D e) • w)))⁻¹ * (c₃ * c₂))) • W.cosVec i κ' := by
    rw [← smul_smul, ← smul_smul, e2, inv_smul_smul₀ (hne _)]
  rw [heisO_star hψ]
  change star (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (W.cosVec i κ)) ∈ _
  rw [hC, star_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ', rfl⟩)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPrimFrameGlMulIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.PrimFrameLeft

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]

theorem row_mul_eq_sum (M : Matrix A A k) (Y : Matrix A D k) (i : A) :
    (M * Y).row i = ∑ l, M i l • Y.row l := by
  funext j
  simp [Matrix.mul_apply, Finset.sum_apply, Matrix.row]

theorem span_O_row_mul_le (M : Matrix A A k) (hM : ∀ i j, M i j ∈ 𝒪[k]) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (M * Y).row) ≤ Submodule.span 𝒪[k] (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ (⟨M i l, hM i l⟩ : 𝒪[k]) (Submodule.subset_span ⟨l, rfl⟩)

theorem span_k_row_mul_le (M : Matrix A A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (M * Y).row) ≤ Submodule.span k (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem span_O_row_gl_mul (g : GL A k) (hg : g ∈ KO k A) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (g.val * Y).row) = Submodule.span 𝒪[k] (Set.range Y.row) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  refine le_antisymm (span_O_row_mul_le _ h1 Y) ?_
  have := span_O_row_mul_le _ h2 (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem span_k_row_gl_mul (g : GL A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (g.val * Y).row) = Submodule.span k (Set.range Y.row) := by
  refine le_antisymm (span_k_row_mul_le _ Y) ?_
  have := span_k_row_mul_le (g⁻¹).val (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem mem_matLat_iff_span_le (Λ : Submodule 𝒪[k] (D → k)) (Y : Matrix A D k) :
    Y ∈ matLat A Λ ↔ Submodule.span 𝒪[k] (Set.range Y.row) ≤ Λ := by
  rw [Submodule.span_le, mem_matLat]
  exact ⟨fun h => by rintro _ ⟨i, rfl⟩; exact h i, fun h i => h ⟨i, rfl⟩⟩

theorem isPrimFrame_gl_mul_iff (Λ : Submodule 𝒪[k] (D → k)) (g : GL A k) (hg : g ∈ KO k A)
    (Y : Matrix A D k) : IsPrimFrame Λ (g.val * Y) ↔ IsPrimFrame Λ Y := by
  have hrank : (g.val * Y).rank = Y.rank :=
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  unfold IsPrimFrame
  rw [hrank, mem_matLat_iff_span_le, mem_matLat_iff_span_le, span_O_row_gl_mul g hg, span_k_row_gl_mul]

end GlobalTheory.PrimFrameLeft
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedAbsComplexPowHalfMemSubfieldOfSqrtNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HalfPowField

theorem apow_half_mem_of_sqrt : ∀ {D : D7} (F : Subfield ℂ) (w : Pl D.host.E), ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F → ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ F := by
  intro D F w hs u
  simpa using GlobalTheory.MovedField.apow_half_mem hs u 1

end GlobalTheory.HalfPowField
end
end

