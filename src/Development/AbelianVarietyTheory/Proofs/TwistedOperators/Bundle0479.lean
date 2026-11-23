module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualElementStandardCharSplitPrime
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepRightTranslationMaxCompactSta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeRep

open GlobalTheory.KTypeProj GlobalTheory.Published.AutFin

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem conj_UH (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
  GlobalTheory.Published.AutFin.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) k

theorem fr_mul_inv (τ : D.what₂.Tau) : M.fr τ * (M.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem fr_inv_mul (τ : D.what₂.Tau) : (M.fr τ)⁻¹ * M.fr τ = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem conj_inK (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    GlobalTheory.CuspGK.InK M τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) := by
  refine ⟨conj_UH M τ k, ?_⟩
  have hc : M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) * (M.fr τ)⁻¹ =
      (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK k * (M.fr τ * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
  rw [hc, fr_mul_inv M τ, one_mul, mul_one]
  exact k.2

theorem kAt_one (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) : kAt θ V τ (M.ε τ) (M.fr τ) 1 = 1 := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) * M.fr τ) = 1
  have h1 : Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) = 1 := rfl
  rw [h1, mul_one, fr_inv_mul M τ]
  exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ

theorem kAt_mul (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) (a b : Formalism.REAL.KG (M.ε τ)) :
    kAt θ V τ (M.ε τ) (M.fr τ) (a * b) = kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (a * b) * M.fr τ) =
    atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ) * atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ)
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (conj_UH M τ a) (conj_UH M τ b)]
  have hab : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
  have hsplit : (M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ) =
      (M.fr τ)⁻¹ * Formalism.REAL.toMK a * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK b * M.fr τ := by
    simp only [mul_assoc]
  rw [hsplit, fr_mul_inv M τ, mul_one, hab]
  simp only [mul_assoc]

theorem continuous_kAt (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) :
    Continuous fun k => kAt θ V τ (M.ε τ) (M.fr τ) k := by
  have hK : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hconj : Continuous fun k : Formalism.REAL.KG (M.ε τ) => (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ :=
    (continuous_const.matrix_mul hK).matrix_mul continuous_const
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hconj fun k => conj_UH M τ k

def kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) (hY : KStable θ M Y) (τ : D.what₂.Tau) :
    Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y where
  toFun k := (rTrL (kAt θ V τ (M.ε τ) (M.fr τ) k)).restrict fun f hf => hY τ _ (conj_inK M τ k) f hf
  map_one' := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) 1) = w.1 x
    rw [kAt_one M hθ, mul_one]
  map_mul' a b := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) (a * b)) =
      w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b)
    rw [kAt_mul M hθ, mul_assoc]

theorem isContRep_kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) [FiniteDimensional ℂ Y]
    (hY : KStable θ M Y) (hc : ∀ f ∈ Y, Continuous f) (τ : D.what₂.Tau) : IsContRep (kRep M hθ Y hY τ) := by
  intro ℓ w
  have hℓ : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  refine hℓ.comp (continuous_induced_rng.2 (continuous_pi fun x => ?_))
  show Continuous fun k => (w : GA D V → ℂ) (x * kAt θ V τ (M.ε τ) (M.fr τ) k)
  exact (hc _ w.2).comp (continuous_const.mul (continuous_kAt M hθ τ))

end GlobalTheory.KTypeRep

theorem GlobalTheory.KTypeRep.exists_contRep_types : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y → GlobalTheory.KTypeProj.KStable θ M Y → (∀ f ∈ Y, Continuous f) →
    ∀ τ, ∃ ρ : Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y, GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ T : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ),
        (∀ i, ∀ w ∈ Y, T (GlobalTheory.KTypeProj.rhoK θ M i w) = GlobalTheory.KTypeProj.rhoK θ M i (T w)) →
        ∀ w : Y, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) ρ (T w) := by
  intro D θ V S M hθ Y hfin hY hc τ
  haveI := hfin
  refine ⟨GlobalTheory.KTypeRep.kRep M hθ Y hY τ, GlobalTheory.KTypeRep.isContRep_kRep M hθ Y hY hc τ, ?_⟩
  intro T hT w
  refine GlobalTheory.Published.AutFin.hasTypeAt_of_map θ V τ (M.ε τ) (M.fr τ) _ (T ∘ₗ Y.subtype) (fun k u => ?_) w
  exact hT ⟨(τ, (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ), GlobalTheory.KTypeRep.conj_inK M τ k⟩ u.1 u.2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.HalfDuality

variable {D : D7}

theorem exists_lift (t : Datum.EAf D) : ∃ Z : AE D, infPart D Z = 0 ∧ toEAf D Z = t :=
  ⟨GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm t),
   GlobalTheory.AdForm.infPart_liftFin _, GlobalTheory.AdForm.toEAf_liftFin t⟩

theorem trace_id (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T) :
    toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) :=
  _root_.GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames S T βS βT k y

theorem local_dual (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (e₁ : AE D) (PP : Pl D.host.E)
    (he₁ : Formalism.L2.NTheta.IsIdemAt e₁ PP) :
    ∃ c : Datum.EAf D,
      (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 →
        toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧
      (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c →
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) :=
  _root_.GlobalTheory.SplitDualElt.exists_dual_elt ψ hψ e₁ PP he₁

theorem psi_trace_split (ψ : AddChar (AF D.host.F) ℂ) (a Z Z₁ : AE D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) (a * Z)) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (a * Z₁)) * ψ (Algebra.trace (AF D.host.F) (AE D) (a * (Z - Z₁))) := by
  rw [← AddChar.map_add_eq_mul, ← map_add (f := _), ← mul_add, add_sub_cancel Z₁ Z]

theorem redM_apply_of_mem (PP : Pl D.host.E) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Datum.EAf D)) (i : Fin b) (j : Fin a)
    (h : N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : redM PP N i j = resS D.host.F PP ⟨N i j, h⟩ := by
  simp only [redM]
  exact dif_pos h


set_option maxHeartbeats 800000 in
theorem local_dual_unit (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (e₁ : AE D) (PP : Pl D.host.E)
    (he₁ : Formalism.L2.NTheta.IsIdemAt e₁ PP) (u : Formalism.L2.Herm.intAf D.host.F D.host.E) (hu : resS D.host.F PP u ≠ 0) :
    ∃ c : Datum.EAf D,
      (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 →
        toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧
      (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c * u →
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) := by
  obtain ⟨c, h1, h2⟩ := local_dual ψ hψ e₁ PP he₁
  haveI := PP.isMaximal
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (I := PP.asIdeal) hu
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b
  have hra : resS D.host.F PP (oToS D.host.F D.host.E a) * resS D.host.F PP u = 1 := by
    rw [resS_oToS, ha, mul_comm, hb]
  refine ⟨c * ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D),
    fun Z hZ r hr hZr => ?_, fun Z hZ hZu => ?_⟩
  · refine h1 Z hZ (oToS D.host.F D.host.E a * r) (by rw [map_mul, hr, mul_zero]) ?_
    rw [hZr, MulMemClass.coe_mul, mul_assoc]
  · obtain ⟨Z₁, hZ₁, hZ₁c⟩ := exists_lift (D := D) c
    have hr : resS D.host.F PP (oToS D.host.F D.host.E a * u - 1) = 0 := by
      rw [map_sub, map_mul, hra, map_one, sub_self]
    have h0 := h1 (Z - Z₁) (by rw [map_sub, hZ, hZ₁, sub_zero]) (oToS D.host.F D.host.E a * u - 1) hr (by
      rw [map_sub, hZu, hZ₁c, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, mul_sub, mul_one,
        mul_assoc])
    intro hc
    apply h2 Z₁ hZ₁ hZ₁c
    rw [psi_trace_split ψ _ Z Z₁, h0, mul_one] at hc
    exact hc


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_half_frMapO (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    (e : AE D) (hee : e * e = e) (z : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D))
    (hz : ∀ i j, toEAf D e * z i j = z i j) :
    ∃ y : WO S T, IsHalf e y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapO S T βS βT y = z := by
  choose L hL0 hL using fun t : Datum.EAf D => exists_lift (D := D) t
  let Y : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D) := HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
  refine ⟨Matrix.of fun i j => e * L (Y i j), fun i j => ?_, fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, hee]
  · simp only [Matrix.of_apply, map_mul, hL0, mul_zero]
  · have hz' : toEAf D e • z = z := Matrix.ext fun i j => hz i j
    have h3 : toEAf D e • Y = Y := by
      show toEAf D e • HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val = HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz']
    have hY : (Matrix.of fun i j => e * L (Y i j) : WO S T).map (toEAf D) = Y := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_mul, hL]
      exact congrFun (congrFun h3 i) j
    unfold frMapO
    rw [hY]
    have e1 : HMul.hMul (HMul.hMul (βT⁻¹).val Y) βS.val =
        HMul.hMul (HMul.hMul (HMul.hMul ((βT⁻¹).val) βT.val) z) (HMul.hMul (βS⁻¹).val βS.val) := by
      simp only [Y, Matrix.mul_assoc]
    rw [e1, Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_one]

theorem trace_mul_single {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Datum.EAf D)) (b : Fin n) (a : Fin m) (t0 : Datum.EAf D) :
    Matrix.trace (M * Matrix.single b a t0) = M a b * t0 := by
  rw [Matrix.trace, Finset.sum_eq_single a]
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · intro j _ hj
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ a) h

end GlobalTheory.HalfDuality

set_option maxHeartbeats 1600000 in
theorem GlobalTheory.HalfDuality.exists_dual_half : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  (∃ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ≠ 0) →
  ∃ y : WO (Vc D i) (Wc D i), IsHalf (cA D (cA D e)) y ∧
    (∀ k : WO (Vc D i) (Wc D i), IsHalf (cA D e) k → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) → (∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) = 0) →
      R.ψ (symplO (Vc D i) (Wc D i) k y) = 1) ∧
    R.ψ (symplO (Vc D i) (Wc D i) x y) ≠ 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io hL e he x hx hint hex
  obtain ⟨PP, hPP, hred⟩ := hex
  have hψ : IsStdChar D R.ψ (-1) := hL.2.2.2.2.2.1.std
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  obtain ⟨⟨es, hes, -⟩, -⟩ := he
  obtain ⟨a, b, hab⟩ : ∃ a b, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) a b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hred (Matrix.ext hn)
  have hu : resS D.host.F PP ⟨_, hint a b⟩ ≠ 0 := by
    rw [← GlobalTheory.HalfDuality.redM_apply_of_mem]
    exact hab
  obtain ⟨c₀, h1, h2⟩ := GlobalTheory.HalfDuality.local_dual_unit R.ψ hψ (es PP) PP (hes PP hPP) _ hu
  obtain ⟨y, hyh, hy0, hyz⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) e hee
    (Matrix.single b a (toEAf D e * c₀)) (fun i' j' => by
      rw [Matrix.single_apply]
      split_ifs
      · rw [← mul_assoc, ← map_mul, hee]
      · rw [mul_zero])
  have hinf : ∀ k, infPart D (hO (Vc D i) (Wc D i) y k) = 0 := fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hO, map_sum, map_mul, hy0, mul_zero, Finset.sum_const_zero]
  have hfin : ∀ k, IsHalf (cA D e) k → toEAf D (hO (Vc D i) (Wc D i) y k) =
      c₀ * frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k a b := fun k hk => by
    rw [GlobalTheory.HalfDuality.trace_id _ _ (R.βV i) (R.βW i), hyz, GlobalTheory.HalfDuality.trace_mul_single, mul_comm (toEAf D e) c₀, mul_left_comm,
      mul_comm _ (toEAf D e), GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ hk]
  have hs : ∀ k, R.ψ (symplO (Vc D i) (Wc D i) k y) =
      (R.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * hO (Vc D i) (Wc D i) y k)))⁻¹ := fun k => by
    rw [GlobalTheory.OrientedHeis.symplO_skew y k, AddChar.map_neg_eq_inv]
    rfl
  refine ⟨y, by rw [Formalism.L2.Theta.cA_cA]; exact hyh, fun k hk hki hkr => ?_, ?_⟩
  · rw [hs, h1 _ (hinf k) ⟨_, hki a b⟩ (by rw [← GlobalTheory.HalfDuality.redM_apply_of_mem]; exact congrFun (congrFun (hkr PP hPP) a) b) (hfin k hk), inv_one]
  · rw [hs]
    exact fun h => h2 _ (hinf x) (hfin x hx) (inv_eq_one.1 h)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinOfRest
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaSchrCont

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic
open scoped Matrix

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finSlice (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun w => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), w i)

theorem finSlice_mem {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    finSlice Φ y ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    have : finSlice (pureA F f g) y = f y • g := by
      funext w
      simp only [finSlice, pureA, RingEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ hg
  | zero => exact (SB _).zero_mem
  | add x x' _ _ hx hx' => exact (SB _).add_mem hx hx'
  | smul a x _ hx => exact (SB _).smul_mem a hx

theorem exists_fin_of_rest {f : SInf F κ} {r : (κ → AF F) → ℂ} (hr : Rest (evI F) (⇑f) r) (hf : f ≠ 0) :
    ∃ G ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∀ x : κ → AF F, r x = G fun i => (x i).2 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  refine ⟨(f y)⁻¹ • finSlice (tens (evI F) (⇑f) r) y, Submodule.smul_mem _ _ (finSlice_mem hr.2 y), fun x => ?_⟩
  let z : κ → AF F := fun i => mk (e.symm (y i) - (x i).1) 0
  have hz : At (evI F) z := by
    intro u hu
    funext i
    exact at_mk _ u hu
  have hxz : x + z = fun i => (e.symm (y i), (x i).2) := by
    funext i
    refine Prod.ext ?_ ?_
    · show (x i).1 + (e.symm (y i) - (x i).1) = e.symm (y i)
      abel
    · show (x i).2 + 0 = (x i).2
      exact add_zero _
  have h1 := hr.1 x z hz
  rw [hxz] at h1
  have h2 : (fun i => evI F ((e.symm (y i), (x i).2) : AF F)) = y := by
    funext i
    exact e.apply_symm_apply (y i)
  simp only [Pi.smul_apply, smul_eq_mul, finSlice, tens]
  rw [h2, ← h1]
  field_simp
  rfl

theorem tens_eq_pureA (g : SInf F κ) {r : (κ → AF F) → ℂ} {G : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hG : ∀ x : κ → AF F, r x = G fun i => (x i).2) : tens (evI F) (⇑g) r = pureA F g G := by
  funext x
  simp only [tens, pureA, hG]
  rfl

theorem schr_pureA_eq [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsStd ψ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
    let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
    schr ψ w (pureA F f g) = pureA F (archS f (fun i => q (w.2 i)) (fun i => q (w.1 i))
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)))
      (finS ψ g (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)) := by
  intro q h
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  funext x
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add (f := _), RingHom.map_dotProduct]
        rfl
      rw [e1, map_add (f := _), eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add (f := _), RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

theorem exists_clm_hasSum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (f : SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    Rest (evI F) (⇑f) r → f ≠ 0 → ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ g : SInf F (Fin n × Fin d),
      HasSum (fun ξ : Fin n × Fin d → F => M.co.rho ψ u (tens (evI F) (⇑g) r) (fun i => algebraMap F (AF F) (ξ i))) (T g) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ u f r hr hf
  obtain ⟨G, hG, hrG⟩ := exists_fin_of_rest hr hf
  set w := M.co.e u with hw
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let G' := finS ψ G (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)
  have hG' : G' ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := finS_mem ψ hψ.1 hG _ _ _
  obtain ⟨l, hl, hleq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  obtain ⟨T₀, hT₀⟩ := hl G' hG'
  let A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
    (SchwartzMap.smulLeftCLM ℂ (fun y : Fin n × Fin d → mixedEmbedding.mixedSpace F => eChar ((-trL c) y + -k))).comp
      (SchwartzMap.compSubConstCLM ℂ (-t))
  refine ⟨T₀.comp A, fun g => ?_⟩
  have hΦ : M.co.rho ψ u (tens (evI F) (⇑g) r) = pureA F (A g) G' := by
    rw [tens_eq_pureA g hrG]
    exact schr_pureA_eq ψ hψ w g G
  rw [hΦ]
  have hmem : pureA F (A g) G' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨A g, G', hG', rfl⟩
  convert hasSum_thetaSum F hmem using 1
  rw [ContinuousLinearMap.comp_apply, ← hT₀, hleq _ hmem]

end GlobalTheory.ThetaSchrCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

namespace GlobalTheory.Tow

theorem idemAt_orth {D : D7} {P Q : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b Q) (h : P ≠ Q) : a * b = 0 := by

  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have ha0 := GlobalTheory.PlaceModelSum.infPart_split ha.1
  have hda := (GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 ha0 P).mp ha.2
  have hdb := (GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) Q).mp hb.2
  apply hΦ.ext'
  · rw [map_mul, ha0, zero_mul, map_zero]
  · intro R
    rw [GlobalTheory.IdemSupport.ev_mul, GlobalTheory.IdemSupport.ev_zero]
    by_cases hR : R = P
    · rw [hR, hdb.2.2 P h, mul_zero]
    · rw [hda.2.2 R hR, zero_mul]

theorem idemAt_unique {D : D7} {P : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b P) : a = b := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  exact GlobalTheory.IdemSupport.delta_unique hΦ
    ((GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 (GlobalTheory.PlaceModelSum.infPart_split ha.1) P).mp ha.2)
    ((GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) P).mp hb.2)

theorem idemSum_mul_of_subset {D : D7} {e e₂ : AE D} {P P₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsIdemSum e P) (h₂ : IsIdemSum e₂ P₂) (hP : P ⊆ P₂) : e₂ * e = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨fs, hfs, rfl⟩, -⟩ := h₂
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_

  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem R (hP hR)]
  · rw [idemAt_unique (hfs R (hP hR)) (hes R hR)]
    exact (hes R hR).1.1
  · intro Q hQ hQR
    exact idemAt_orth (hfs Q hQ) (hes R hR) hQR

end GlobalTheory.Tow
end

