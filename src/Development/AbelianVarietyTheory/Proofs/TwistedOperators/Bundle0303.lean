module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0298
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroDiscreteSeriesInfiniteHom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InvTransposeIso

def ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) : GL n A →* GL m A where
  toFun g := ⟨((g⁻¹).1ᵀ).submatrix e.symm e.symm, (g.1ᵀ).submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.submatrix_one_equiv]⟩
  map_one' := Units.ext (by ext i j; simp [Matrix.one_apply])
  map_mul' g h := Units.ext (by
    show (((g * h)⁻¹).1ᵀ).submatrix e.symm e.symm =
      ((g⁻¹).1ᵀ).submatrix e.symm e.symm * ((h⁻¹).1ᵀ).submatrix e.symm e.symm
    rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, ← Units.val_mul, _root_.mul_inv_rev])

theorem ctr_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : (ctr e g).1 = ((g⁻¹).1ᵀ).submatrix e.symm e.symm := rfl

theorem ctr_inv_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ((ctr e g)⁻¹).1 = (g.1ᵀ).submatrix e.symm e.symm := rfl

theorem ctr_ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ctr e.symm (ctr e g) = g :=
  Units.ext (by rw [ctr_val, ctr_inv_val]; ext i j; simp)

theorem key_rel {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (c : A →+* A)
    {H Hi K : Matrix n n A} (hHi : H * Hi = 1) (hK : Hi = -Kᵀ) (g : GL n A)
    (hg : (g.1.map c)ᵀ * H * g.1 = H) :
    (((g⁻¹).1ᵀ).map c)ᵀ * K * (g⁻¹).1ᵀ = K := by
  have hHiH : Hi * H = 1 := mul_eq_one_comm.1 hHi
  have h1 : g.1.map c * (g⁻¹).1.map c = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hY : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H = 1 := by
    calc (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H
        = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * ((g.1.map c)ᵀ * H * g.1) := by rw [hg]
      _ = (g⁻¹).1 * Hi * (g.1.map c * (g⁻¹).1.map c)ᵀ * H * g.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc _ Hi H, hHiH, Matrix.mul_one,
            Units.inv_mul]
  have hY' : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ = Hi := by
    calc _ = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * (H * Hi) := by rw [hHi, Matrix.mul_one]
      _ = Hi := by rw [← Matrix.mul_assoc, hY, Matrix.one_mul]
  have hKt : Kᵀ = -Hi := by rw [hK, neg_neg]
  apply Matrix.transpose_injective
  rw [Matrix.transpose_map]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hKt, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hY']

theorem reindex_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {J : Matrix m m A} {M : Matrix n n A}
    (h : (M.map c)ᵀ * J.submatrix e e * M = J.submatrix e e) :
    ((M.submatrix e.symm e.symm).map c)ᵀ * J * M.submatrix e.symm e.symm = J := by
  have hJ : J = (J.submatrix e e).submatrix e.symm e.symm := by ext i j; simp
  have hM : ((M.submatrix e.symm e.symm).map c)ᵀ = ((M.map c)ᵀ).submatrix e.symm e.symm := rfl
  rw [hM]
  conv_lhs => rw [hJ]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h, ← hJ]

theorem ctr_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {H Hi : Matrix n n A} {J : Matrix m m A} (hHi : H * Hi = 1)
    (hK : Hi = -(Jᵀ.submatrix e e)) (g : GL n A) (hg : Formalism.UG.cT c g.1 * H * g.1 = H) :
    Formalism.UG.cT c (ctr e g).1 * J * (ctr e g).1 = J :=
  reindex_rel c e (key_rel c hHi hK g hg)

theorem inv_rel {K : Type} [Field K] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n K) (B : Matrix m m K) (e : n ≃ m) (h : A⁻¹ = -(Bᵀ.submatrix e e)) (hA : IsUnit A.det) :
    B⁻¹ = -(Aᵀ.submatrix e.symm e.symm) := by
  have h1 : A * -(Bᵀ.submatrix e e) = 1 := by rw [← h]; exact Matrix.mul_nonsing_inv A hA
  have h2 : -(B.submatrix e e) * Aᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.transpose_submatrix, Matrix.transpose_transpose,
      Matrix.transpose_one] at this
    exact this
  have h3 : Aᵀ * -(B.submatrix e e) = 1 := mul_eq_one_comm.1 h2
  have h4 : Aᵀ.submatrix e.symm e.symm * -B = 1 := by
    calc Aᵀ.submatrix e.symm e.symm * -B
        = Aᵀ.submatrix e.symm e.symm * (-(B.submatrix e e)).submatrix e.symm e.symm := by
          congr 1; ext i j; simp
      _ = (Aᵀ * -(B.submatrix e e)).submatrix e.symm e.symm := Matrix.submatrix_mul_equiv _ _ _ _ _
      _ = 1 := by rw [h3, Matrix.submatrix_one_equiv]
  exact Matrix.inv_eq_left_inv (by rw [Matrix.neg_mul, ← Matrix.mul_neg]; exact h4)

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

theorem gram_inv_rel {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    W.gram⁻¹ = -(V.gramᵀ.submatrix e.symm e.symm) :=
  inv_rel V.gram W.gram e h (Formalism.L2.Theta.gram_det_ne V).isUnit

theorem mem_HR {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : ctr e (matHom V g) ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  have hHi : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK : (V.gram⁻¹).map (incA D) = -(((W.gram.map (incA D))ᵀ).submatrix e e) := by
    rw [h]; ext i j; simp
  exact ctr_rel (cA D) e hHi hK (matHom V g) g.2

theorem mem_UJ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (r : GL (Fin V.rank) D.host.E) (hr : r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    ctr e r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  exact ctr_rel _ e (Matrix.mul_nonsing_inv _ hdet) h r hr

def fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V →* GA D W where
  toFun g := (⟨ctr e (matHom V g), mem_HR e h g⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram)
  map_one' := Subtype.ext (by simp only [map_one]; rfl)
  map_mul' g g' := Subtype.ext (by simp only [map_mul]; rfl)

theorem mt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : Formalism.L2.Theta.mt W (fwd e h g) = ((Formalism.L2.Theta.mt V g⁻¹)ᵀ).submatrix e.symm e.symm := by
  show (ctr e (matHom V g)).1 = _
  rw [ctr_val, ← map_inv]; rfl

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

def iso {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V ≃* GA D W :=
  { fwd e h with
    invFun := fwd e.symm (gram_inv_rel e h)
    left_inv := fun g => Subtype.ext (ctr_ctr e g.1)
    right_inv := fun g => Subtype.ext (ctr_ctr e.symm g.1) }

theorem continuous_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    Continuous (fwd e h) := by
  have hv : Continuous fun g : GA D V => (matHom V g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun g : GA D V => ((matHom V g)⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun g : GA D V => (((matHom V g)⁻¹).1ᵀ).submatrix e.symm e.symm
    exact hi.matrix_transpose.matrix_submatrix _ _
  · show Continuous fun g : GA D V => ((matHom V g).1ᵀ).submatrix e.symm e.symm
    exact hv.matrix_transpose.matrix_submatrix _ _

theorem fwd_GQ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (γ : GA D V) (hγ : γ ∈ GQ V) : fwd e h γ ∈ GQ W := by
  obtain ⟨r, hr, hrγ⟩ := (Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈
    HFin (AF D.host.F) D.sp.cm.sig V.gram)
  refine Subgroup.mem_subgroupOf.2 ⟨ctr e r, mem_UJ e h r hr, ?_⟩
  show Formalism.UG.bc (inclR (AF D.host.F)) (ctr e r) = ctr e γ.1
  rw [← hrγ]
  exact Units.ext (by ext i j; rfl)

theorem suppAt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (a : AE D) (g : GA D V) (hg : SuppAt a V g) : SuppAt a W (fwd e h g) := by
  have hYG : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    simp only [Formalism.L2.Theta.mt]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hsub : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1)) := by
    rw [Matrix.mul_sub, hYG, Matrix.mul_one, neg_sub]
  intro i j
  have hij : (Formalism.L2.Theta.mt W (fwd e h g) - 1) i j = (Formalism.L2.Theta.mt V g⁻¹ - 1) (e.symm j) (e.symm i) := by
    rw [mt_fwd]
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.one_apply,
      e.symm.injective.eq_iff, eq_comm]
  rw [hij, hsub, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k (e.symm i)]

theorem det_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).det = (Formalism.L2.Theta.mt V g⁻¹).det := by
  rw [mt_fwd, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

theorem sub_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).submatrix e e = (Formalism.L2.Theta.mt V g⁻¹)ᵀ := by
  rw [mt_fwd]; ext i j; simp

theorem grp_contra : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  intro D T S' e₂ h
  exact ⟨iso e₂ h, continuous_fwd e₂ h, fun γ hγ => fwd_GQ e₂ h γ hγ, sub_fwd e₂ h,
    fun a g hg => suppAt_fwd e₂ h a g hg, det_fwd e₂ h⟩

end GlobalTheory.InvTransposeIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumOneParameterGeneratorCommutators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceTensor.GenPair

theorem exists_pairing {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (G : BoundedContinuousFunction Z ℂ) :
    ∃ L : BoundedContinuousFunction Z ℂ →L[ℂ] ℂ, ∀ F, L F = ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν := by
  have hint : ∀ F : BoundedContinuousFunction Z ℂ, MeasureTheory.Integrable (fun w => F w * (starRingEnd ℂ) (G w)) ν :=
    fun F => (F * star G).integrable ν
  refine ⟨LinearMap.mkContinuous
    { toFun := fun F => ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν
      map_add' := fun F F' => by
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint F) (hint F')
      map_smul' := fun c F => by
        simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ } ((ν Set.univ).toReal * ‖G‖) fun F => ?_, fun F => rfl⟩
  have hb : ∀ w, ‖F w * (starRingEnd ℂ) (G w)‖ ≤ ‖F‖ * ‖G‖ := fun w => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (F.norm_coe_le_norm w) (G.norm_coe_le_norm w) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hb)
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  calc _ ≤ ‖F‖ * ‖G‖ * (ν Set.univ).toReal := by simpa [Measure.real] using this
    _ = _ := by ring

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.DefLift GlobalTheory.DefLift.Gen

theorem blk_sub_vecL {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} (Y : O → Matrix (Fin m) (Fin m) ℂ)
    (X : O → Matrix (Fin n) (Fin n) ℂ) (τ' : O) (u : Matrix (Fin m) (Fin n) ℂ) :
    (GlobalTheory.RealWeil.blk Y (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) X) *ᵥ
                 vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) =
      vecL (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) := by
  funext p
  obtain ⟨⟨i, j⟩, τ⟩ := p
  have key : ∀ (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ)
      (v : (Fin m × Fin n) × O → ℂ), (GlobalTheory.RealWeil.blk b a *ᵥ v) ((i, j), τ) = (b τ * cpt v τ * a τ) i j :=
    fun b a v => by rw [← cpt_blk]; rfl
  have hc : cpt (vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ)) τ = (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) τ := rfl
  rw [Matrix.sub_mulVec, Pi.sub_apply, key, key, hc]
  show _ = (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) τ i j
  by_cases h : τ = τ'
  · subst h
    simp
  · simp [h]

open scoped Classical

variable {D : D7} {θ : InfFam D}

theorem oneP_zero (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : oneP θ V τ X 0 = 1 := by
  have h := GlobalTheory.Mem.Lift.oneP_add hθ hX 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem oneP_inv (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : (oneP θ V τ X t)⁻¹ = oneP θ V τ X (-t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel]
  exact GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX

theorem hasDerivAt_mM (hθ : IsInfFam θ) {S T : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hX : X ∈ lieAt S τ) {Y : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hY : Y ∈ lieAt T τ) (k l : GlobalTheory.RealWeil.Ix S T) :
    HasDerivAt (fun t : ℝ => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t) k l)
      ((GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X) :
        Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) k l) 0 := by
  obtain ⟨⟨i, j⟩, τ₁⟩ := k
  obtain ⟨⟨i', j'⟩, τ₂⟩ := l
  have hS : ∀ t : ℝ, (oneP θ S τ X t)⁻¹ = oneP θ S τ X (-t) := GlobalTheory.PlaceTensor.GenPair.oneP_inv hθ hX
  simp only [mM_apply, hS, GlobalTheory.RealWeil.blk, Matrix.sub_apply, Matrix.blockDiagonal_apply,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h : τ₁ = τ₂
  · subst h
    simp only [if_true]
    have hb := hasDerivAt_comp hθ hY τ₁ i i'
    have ha0 := hasDerivAt_comp hθ hX τ₁ j' j
    have ha : HasDerivAt (fun t : ℝ => Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X t)) j' j)
        ((Pi.single τ X : D.what₂.Tau → _) τ₁ j' j) (-0) := by rw [neg_zero]; exact ha0
    have hT0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt T (oneP θ T τ Y 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]; exact compAt_fin (one_mem _) τ₁
    have hS0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX]; exact compAt_fin (one_mem _) τ₁
    refine (hb.mul (ha.scomp 0 (hasDerivAt_neg 0))).congr_deriv ?_
    simp only [Function.comp_apply, neg_zero, hT0, hS0, Matrix.one_apply]
    split_ifs <;> simp <;> ring
  · simp only [h, if_false, sub_zero]
    exact hasDerivAt_const _ _

theorem exists_generator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (τ : D.what₂.Tau), ∀ X ∈ lieAt S τ, ∀ Y ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (Y * u - u * X) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, oneP θ T τ Y t) f w) (Gn f w) 0) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g, IsThetaFunO ψ S T g → HasDerivAt (fun t : ℝ => ipO μ 𝓕 (om (oneP θ S τ X t, oneP θ T τ Y t) f) g) (ipO μ 𝓕 (Gn f) g) 0 := by
  intro D ψ θ S T χS χT om hW hθ τ X hX Y hY
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hweak : GlobalTheory.Ker.IsWeak ψ S T om := GlobalTheory.Ker.isWeak_of_datum hW
  have hcont : OmCont ψ S T om := hW.om_cont
  have hγc : Continuous fun t : ℝ => (oneP θ S τ X t, oneP θ T τ Y t) :=
    (GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
  have hγa : ∀ s t : ℝ, (oneP θ S τ X (s + t), oneP θ T τ Y (s + t)) =
      (oneP θ S τ X s, oneP θ T τ Y s) * (oneP θ S τ X t, oneP θ T τ Y t) := fun s t => by
    rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, GlobalTheory.Mem.Lift.oneP_add hθ hY]; rfl
  have hγm : ∀ t : ℝ, oneP θ S τ X t ∈ GinfC S ∧ oneP θ T τ Y t ∈ GinfC T := fun t =>
    ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩
  obtain ⟨lam, hlam⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ hσ ψ hψ S T om hweak hcont
    (fun t => (oneP θ S τ X t, oneP θ T τ Y t)) hγc hγa hγm _
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  have h0 : mM θ S T (oneP θ S τ X 0, oneP θ T τ Y 0) = 1 := by
    rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX, GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]
    exact (mM θ S T).map_one
  have hlie := GlobalTheory.Mem.Lift.GenZero.lie_of_path (HM S T)
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X))
    (fun t => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t)) h0 (fun t => mM_unitary hθ _)
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  obtain ⟨Gn, hGn⟩ := GlobalTheory.DefLift.Gen.exists_extension hσ hψ
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) lam
  refine ⟨Gn, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    ⟨GlobalTheory.RealWeil.toB hψ f hf, GlobalTheory.RealWeil.coe_toB hψ f hf⟩
  obtain ⟨hnt, hGF⟩ := hGn F hf
  have hAt : IsThetaFunO ψ S T ((nOp (rhoV hψ σ S T) (HM S T)
      (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
      + lam • F).1 : WO S T → ℂ) := by
    rw [← GlobalTheory.DefLift.Gen.coe_add_smul]
    exact GlobalTheory.OrientedHeis.theta_add hnt (GlobalTheory.OrientedHeis.theta_smul lam hf)
  have hcomm : ∀ (τ' : D.what₂.Tau) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u F.1) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn F.1) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ'
        ((Pi.single τ Y : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) τ' * u -
          u * (Pi.single τ X : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) τ') F.1 := by
    intro τ' u
    have hdt := GlobalTheory.DefLift.Gen.theta_dH hσ hψ F hf
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    have e2 := (hGn _ hdt).2
    have e4 := nOp_add_comm HM_herm HM_det hlie (isHeis_rhoB hσ hψ) lam
      (GlobalTheory.RealWeil.sm_of_theta hσ hψ F hf) (GlobalTheory.RealWeil.sm_of_theta hσ hψ _ hnt)
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    rw [← GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' u, e2, hGF, ← GlobalTheory.DefLift.Gen.coe_dH hσ hψ _ hAt τ' u, e4,
      GlobalTheory.PlaceTensor.GenPair.blk_sub_vecL, GlobalTheory.DefLift.Gen.coe_add_sub]
    exact GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' _
  obtain ⟨u, hu1, hu2⟩ := hlam F hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hGF]; exact hAt
  · intro v
    rw [hcomm, Pi.single_eq_same, Pi.single_eq_same]
  · intro τ' h v
    have hc := hcomm τ' v
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Matrix.zero_mul, Matrix.mul_zero, sub_zero,
      GlobalTheory.DefLift.Gen.dRho_zero hσ hψ F hf] at hc
    exact sub_eq_zero.mp hc
  · intro w
    have h2 : HasDerivAt (fun t => ev _ _ w (u t)) (ev _ _ w (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F)) 0 :=
      ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [ev_apply, hu1] at h2
    rw [hGF]; exact h2
  · intro μ 𝓕 hμ g hg
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
      rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨L, hL⟩ := GlobalTheory.PlaceTensor.GenPair.exists_pairing (μ.restrict 𝓕) (GlobalTheory.RealWeil.toB hψ g hg).1
    have h2 : HasDerivAt (fun t => L (u t).1) (L (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F).1) 0 :=
      ((L.comp (BB ψ S T).subtypeL).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [hL, hu1, GlobalTheory.RealWeil.coe_toB] at h2
    rw [hGF]; exact h2

end GlobalTheory.PlaceTensor.GenPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignatureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWittIndex_le_negative_signature : ∀ {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p → ∀ {r : ℕ} {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}, GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf → r ≤ p := by
  first | exact @GlobalTheory.WittSig.wittIndex_le_neg | exact GlobalTheory.WittSig.wittIndex_le_neg | (intros; apply GlobalTheory.WittSig.wittIndex_le_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryRepEqFiniteSmoothPartTensorDis
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

theorem GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → HasDSComp M π → ∀ hU : IsSubrep π ⊤, IsCopyFinDS (finPartDSSm M hU) M π ⊤ := by
  intro D V S M H _ _ _ π hπ hDS hU
  classical
  obtain ⟨Φ0, hΦ0, hne⟩ := _root_.GlobalTheory.TensorHom.exists_ne_zero_homDS D V S M H π hπ hDS
  obtain ⟨Ψ0, hΨ0, hΨne⟩ := _root_.GlobalTheory.SmoothAvg.exists_smooth_ne_zero D V S M H π hπ.unitary hU ⟨Φ0, hΦ0⟩ (fun h => hne (congrArg Subtype.val h))
  let T : GlobalTheory.PRep.smoothPart (finPartDS M hU) →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H :=
    (homDS M π ⊤).subtype ∘ₗ (GlobalTheory.PRep.smoothPart (finPartDS M hU)).subtype
  have hT : ∀ w, T w ∈ homDS M π ⊤ := fun w => w.1.2
  refine ⟨T, mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => rfl, fun i g w y => (hT w).2 i g y⟩,
    Subtype.val_injective.comp Subtype.val_injective, ?_⟩
  have hinv : ∀ g, ∀ v ∈ Submodule.span ℂ {v | ∃ w y, v = T w y}, π g v ∈ Submodule.span ℂ {v | ∃ w y, v = T w y} := by
    intro g v hv
    refine (Submodule.span_le (p := (Submodule.span ℂ {v | ∃ w y, v = T w y}).comap (π g : H →ₗ[ℂ] H))).2 ?_ hv
    rintro _ ⟨w, y, rfl⟩
    refine Submodule.subset_span ⟨finPartDSSm M hU (toFin V g) w, fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ), ?_⟩
    have e1 : π g (T w y) = π (toInf V g : GA D V) (π (toFin V g : GA D V) (T w y)) := by
      conv_lhs => rw [← toInf_mul_toFin g]
      rw [map_mul]; rfl
    have e2 : π (toFin V g : GA D V) (T w y) = T (finPartDSSm M hU (toFin V g) w) y := rfl
    change π g (T w y) = _
    rw [e1, e2]
    exact GlobalTheory.TrAct.toInf_apply_homDS D V S M H π ⊤ _ (hT _) g y
  rcases hπ.irred.2 _ (isSubrep_topologicalClosure hinv) with h | h
  · exfalso
    refine hΨne (Subtype.ext (ContinuousMultilinearMap.ext fun y => ?_))
    have : T ⟨Ψ0, hΨ0⟩ y ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, y, rfl⟩)
    rw [h, Submodule.mem_bot] at this
    simp only [ZeroMemClass.coe_zero, ContinuousMultilinearMap.zero_apply]
    exact this
  · exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwinerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairThetaLift_factors_through_intertwiner : ∀ (D : D7) (X : ProvA), Inputs D X → CuspAll D X → PairLifts D X := by
  first | exact @GlobalTheory.PairLift.RuleLift.pairLifts | exact GlobalTheory.PairLift.RuleLift.pairLifts | (intros; apply GlobalTheory.PairLift.RuleLift.pairLifts <;> assumption)
end

