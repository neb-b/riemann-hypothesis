module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdCoord

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstTestOfPolarWh
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem isOpen_units_tens {D : D7} (X : HidaSetting D) :
    IsOpen {x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit x} := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let B := Algebra.TensorProduct.basis (Ainf X.B.I.F) (Module.finBasis X.B.I.F X.B.I.E)
  have key : {x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit x} =
      (fun x => (LinearMap.toMatrix B B (Algebra.lmul (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) x)).det) ⁻¹'
        {a | IsUnit a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det]
    constructor
    · intro h; exact h.map (Algebra.lmul (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))
    · intro h
      obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 h).2 1
      exact isUnit_iff_exists_inv.2 ⟨y, hy⟩
  rw [key]
  refine (PI.AprimeInfW.isOpen_units_Ainf X.B.I.F).preimage (Continuous.matrix_det ?_)
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  change Continuous fun x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E => B.coord i (x * B j)
  have hc : Continuous fun v : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E => B.coord i v :=
    IsModuleTopology.continuous_of_linearMap (B.coord i)
  exact hc.comp (continuous_mul_const _)

theorem invNbhd_holds : InvNbhd := by
  intro D X
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : T2Space (MfI X) := inferInstanceAs (T2Space (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
    (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : LocallyCompactSpace (MfI X) := inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) →
    Fin (D.R.rS + 1 + D.R.rS) → (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : SecondCountableTopology (MfI X) := inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) →
    Fin (D.R.rS + 1 + D.R.rS) → (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have hU : IsOpen {M : MfI X | IsUnit M} := by
    have e : {M : MfI X | IsUnit M} = (fun M : MfI X => M.det) ⁻¹' {x | IsUnit x} := by
      ext M; exact Matrix.isUnit_iff_isUnit_det M
    rw [e]
    exact (isOpen_units_tens X).preimage (continuous_id.matrix_det)
  have : LocallyCompactSpace (MfI X)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (MfI X)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : MfI X ≃ₜ (MfI X)ᵐᵒᵖ).symm.isInducing.secondCountableTopology
  have : SecondCountableTopology (MfI X)ˣ := Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hO : MulAction.orbit (MfI X)ˣ (1 : MfI X) = {M : MfI X | IsUnit M} := by
    ext M; constructor
    · rintro ⟨u, rfl⟩; exact ⟨u, by simp [Units.smul_def]⟩
    · rintro ⟨u, rfl⟩; exact ⟨u, by simp [Units.smul_def]⟩
  have hOo : IsOpen (MulAction.orbit (MfI X)ˣ (1 : MfI X)) := hO ▸ hU
  have : LocallyCompactSpace (MulAction.orbit (MfI X)ˣ (1 : MfI X)) :=
    hOo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul (MfI X)ˣ (MulAction.orbit (MfI X)ˣ (1 : MfI X)) :=
    ⟨continuous_induced_rng.2 (by
      change Continuous fun p : (MfI X)ˣ × MulAction.orbit (MfI X)ˣ (1 : MfI X) => ((p.1 : MfI X) * (p.2 : MfI X))
      exact (Units.continuous_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))⟩
  have y1 : (1 : MfI X) ∈ MulAction.orbit (MfI X)ˣ (1 : MfI X) := MulAction.mem_orbit_self _
  have hopen : IsOpenMap (fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) :=
    isOpenMap_smul_of_sigmaCompact _
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : (MfI X)ˣ)
  have hWo : IsOpen (Subtype.val '' ((fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) ''
      interior V)) :=
    hOo.isOpenMap_subtype_val _ (hopen _ isOpen_interior)
  have h1W : (1 : MfI X) ∈ Subtype.val '' ((fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) ''
      interior V) :=
    ⟨⟨1, y1⟩, ⟨1, mem_interior_iff_mem_nhds.2 hV1, one_smul _ _⟩, rfl⟩
  refine ⟨_, hWo.mem_nhds h1W, (fun u : (MfI X)ˣ => ((u⁻¹ : (MfI X)ˣ) : MfI X)) '' V,
    hVc.image Units.continuous_coe_inv, ?_⟩
  rintro b ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨((u⁻¹ : (MfI X)ˣ) : MfI X), ⟨u, interior_subset hu, rfl⟩, ?_⟩
  change ((u⁻¹ : (MfI X)ˣ) : MfI X) * ((u : MfI X) * 1) = 1
  simp

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfStd
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

open Matrix


open scoped Classical in
def expU {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.UJ ε :=
  if h : Formalism.REAL.inUJ ε (NormedSpace.exp M) then ⟨(Matrix.isUnit_exp M).unit, h⟩ else 1

def kap0 {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf) {ι : Type}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (x : EuclideanSpace ℝ ι) : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L x v)) * c⁻¹)

def InStd {n : ℕ} {ε : Fin n → Bool} (S : Finset (Fin n)) (g : Formalism.REAL.UJ ε) : Prop :=
  ∀ i ∉ S, ∀ j, ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) j i = if j = i then 1 else 0

def StdConj {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (u' : D.what₂.Word)
    (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) : Prop :=
  (∀ v, (S v).card = D.R.k ∧ ∀ i ∈ S v, X.B.I.ε v i = true) ∧
  ∀ g : X.B.I.Ginf, X.toInf hb (c * g * c⁻¹) ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') ↔ ∀ v, InStd (S v) (g v)

def LieCompl {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type}
    [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) :
    Prop :=
  (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * L x v = 0 ∧
    ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) ∧
  (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
  ∀ M : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
    (∀ v, (M v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * M v = 0 ∧
      ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) → ∃ x, L x = M

def StdDataEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    ∃ (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) (ι : Type) (_ : Fintype ι)
      (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
      StdConj X hb u' c S ∧ LieCompl X S L

def GrpStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → GrpLim X u' (kap0 X hb c L)

def TupStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a ∧
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → TupJac X u' hT μinf νinf a (kap0 X hb c L)

theorem goodChartEx_of_std (h1 : StdDataEx) (h2 : GrpStd) (h3 : TupStd) : GoodChartEx := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨hb, -⟩ := hP.1
  obtain ⟨c, S, ι, hι, L, hc, hL⟩ := h1 X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨Ω, a, hC, hJ⟩ := h3 X u' ψ hT μinf νinf fibInf hP
  exact ⟨Ω, a, hC, ι, hι, kap0 X hb c L, h2 X u' ψ hT μinf νinf fibInf hP hb c S L hc hL, hJ hb c S L hc hL⟩

theorem inUJ_exp {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0) : Formalism.REAL.inUJ ε (NormedSpace.exp M) := by
  unfold Formalism.REAL.inUJ
  set J := Formalism.REAL.Jm ε with hJdef
  have hJJ : J * J = 1 := Formalism.REAL.Jm_mul_self ε
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨J, J, hJJ, hJJ⟩
  have hMh : Mᴴ = J * (-M) * J := by
    have h1 : Mᴴ * J = -(J * M) := eq_neg_of_add_eq_zero_left hM
    calc Mᴴ = Mᴴ * J * J := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(J * M) * J := by rw [h1]
      _ = J * (-M) * J := by rw [Matrix.mul_neg, Matrix.neg_mul]
  have e1 : NormedSpace.exp (J * (-M) * J) = J * NormedSpace.exp (-M) * J := by
    have h := Matrix.exp_units_conj U (-M)
    exact h
  have e2 : NormedSpace.exp (-M) * NormedSpace.exp M = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl M)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hMh, e1, Matrix.mul_assoc (J * NormedSpace.exp (-M)) J J, hJJ, Matrix.mul_one,
    Matrix.mul_assoc, e2, Matrix.mul_one]

theorem expU_val {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0) :
    (((expU ε M : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp M := by
  unfold expU
  rw [dite_eq_left (inUJ_exp ε M hM)]
  rfl

theorem expU_zero {n : ℕ} (ε : Fin n → Bool) : expU ε 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [expU_val ε 0 (by simp), NormedSpace.exp_zero]
  rfl

theorem toInf_one {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) : X.toInf hb 1 = 1 := by
  have h := PI.AprimeInfU.toInf_mul X hb 1 1
  rw [one_mul] at h
  exact mul_eq_left.mp h.symm

theorem kap0_zero {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf) {ι : Type}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) :
    kap0 X hb c L 0 = 1 := by
  have : (fun v => expU (X.B.I.ε v) (L 0 v)) = 1 := by
    funext v
    rw [map_zero]
    exact expU_zero _
  unfold kap0
  rw [this, mul_one, mul_inv_cancel, toInf_one]

def GrpPiecesStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf
    νinf fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → GrpPieces X u' (kap0 X hb c L)

theorem grpStd_of (h : GrpPiecesStd) : GrpStd := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  exact grpLim_of_pieces X u' _ (h X u' ψ hT μinf νinf fibInf hP hb c S L hc hL)

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPolD
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem gramR_Y0_eq_TI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) :
    gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
  rw [show Y0 X u' = orbM X u' 1 from (one_smul _ _).symm, orbM, gramR_smul, gramR_ratTup]
  rfl

theorem indI_of_gram {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) (Y : TupI X)
    (hY : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _)) :
    Y ∈ IndI X := by
  have e1 := orbM_mem X u' hT hd 1
  have e0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y =
      gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (orbM X u' 1) := by rw [hY, e1.1]
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [e0, e1.1]
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem fib_near (hR : RmulFacts) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) {D : D7} (X : HidaSetting D)
    (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) (a : MfI X) (hunit : IsUnit a)
    (hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X a (Y0 X u')) = (T : Matrix _ _ _))
    (hind : ∀ Y : TupI X, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = (T : Matrix _ _ _) → Y ∈ IndI X) :
    ∃ c : ENNReal, fibInf T = c • X.measG.μGinf.map (fun g => g • rmulT X a (Y0 X u')) := by
  obtain ⟨hmr, hcomp, hsmul, hgram, hcTmul, hcT1, hKm, hrc⟩ := hR X
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hfib := hP.2.2.2.2.2.2
  obtain ⟨hinvT, hlfT⟩ := hF X u' ψ hT μinf νinf fibInf hP T
  set b : MfI X := ↑hunit.unit⁻¹ with hb
  have hab : a * b = 1 := hunit.mul_val_inv
  have hba : b * a = 1 := hunit.val_inv_mul
  have hab' : ∀ Y, rmulT X a (rmulT X b Y) = Y := fun Y => by rw [hcomp, hba, rmulT_one]
  have hba' : ∀ Y, rmulT X b (rmulT X a Y) = Y := fun Y => by rw [hcomp, hab, rmulT_one]
  set ν := (fibInf T).map (rmulT X b) with hν
  have i1 : InvI X ν := by
    intro g
    rw [hν, Measure.map_map (measurable_smul_tupI X g) (hmr b)]
    have : ((fun y => g • y) ∘ rmulT X b) = rmulT X b ∘ (fun y => g • y) := funext fun y => hsmul g b y
    rw [this, ← Measure.map_map (hmr b) (measurable_smul_tupI X g), hinvT g]
  have hS : fibInf T (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1} ∩ IndI X)ᶜ = 0 :=
    hfib.1 T
  have s1 : ν (FbI X u' hT)ᶜ = 0 := by
    rw [hν, Measure.map_apply (hmr b) (measurableSet_FbI X u' hT).compl]
    refine measure_mono_null ?_ hS
    intro y hy hy2
    apply hy
    have hg : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X b y) = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
      rw [hgram, hy2.1, ← hgT, hgram, gramR_Y0_eq_TI X u' hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hcTmul,
        Matrix.mul_assoc, hab, hcT1, Matrix.one_mul, Matrix.mul_one]
    exact ⟨hg, indI_of_gram X u' hT hd _ hg⟩
  have l1 : LFI X ν := by
    intro K hK hKI
    rw [hν, Measure.map_apply (hmr b) (hKm K hK)]
    have hpre : rmulT X b ⁻¹' K = rmulT X a '' K := by
      ext y
      constructor
      · intro hy; exact ⟨rmulT X b y, hy, hab' y⟩
      · rintro ⟨k, hk, rfl⟩; show rmulT X b (rmulT X a k) ∈ K; rw [hba']; exact hk
    rw [hpre]
    have hcl : IsClosed (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
      haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
      exact isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    have hK2 : IsCompact (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
      (hK.image (hrc a)).inter_right hcl
    calc fibInf T (rmulT X a '' K)
        ≤ fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) +
          fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
          measure_le_inter_add_sdiff _ _ _
      _ = fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
          have h0 : fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) = 0 := by
            refine measure_mono_null ?_ hS
            intro y hy hy2
            exact hy.2 hy2.1
          rw [h0, add_zero]
      _ < ⊤ := hlfT _ hK2 (fun y hy => hind y hy.2)
  obtain ⟨c, -, hc⟩ := orbRep_of_witt wittInf_holds hC X u' ψ hT μinf νinf fibInf hP ν i1 s1 l1
  refine ⟨c, ?_⟩
  have e1 : fibInf T = ν.map (rmulT X a) := by
    rw [hν, Measure.map_map (hmr a) (hmr b)]
    have : rmulT X a ∘ rmulT X b = id := funext hab'
    rw [this, Measure.map_id]
  have e2 : (fun g => g • rmulT X a (Y0 X u')) = rmulT X a ∘ orbM X u' :=
    funext fun g => hsmul g a (Y0 X u')
  rw [e1, hc, Measure.map_smul, e2, Measure.map_map (hmr a) (measurable_orbM X u')]
  exact (hmr a).aemeasurable

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RmulFactsHolds
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem rmulFacts_holds : RmulFacts := by
  intro D X
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  have hcont : ∀ a : MfI X, Continuous (rmulT X a) := by
    intro a
    unfold rmulT
    refine continuous_pi fun b => continuous_pi fun i => ?_
    exact continuous_finsetSum _ fun c _ => continuous_const.mul ((continuous_apply i).comp (continuous_apply c))
  refine ⟨fun a => (hcont a).measurable, ?_, ?_, ?_, ?_, ?_, fun K hK => hK.isClosed.measurableSet, hcont⟩
  · intro a b Y
    funext b' i
    simp only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · intro g a Y
    funext b i
    show ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL _ _) : Matrix _ _ _).mulVec (rmulT X a Y b) i =
      ∑ c, a c b * ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL _ _) : Matrix _ _ _).mulVec (Y c) i
    simp only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · intro a Y
    exact sq_gramR_rmul (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J a Y
  · intro a b
    simp only [cTI, Matrix.map_mul, Matrix.transpose_mul]
  · simp only [cTI, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTestC
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem totReal_of {D : D7} (X : HidaSetting D) : ∀ v : InfinitePlace X.B.I.F, v.IsReal :=
  fun v => X.B.I.cm.totReal.isReal v

def tupCoord {D : D7} (X : HidaSetting D) :
    TupI X ≃ₜ EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin X.B.I.n ×
      Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F) :=
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  (Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ =>
    (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F)).trans
      (Homeomorph.piCongrRight fun _ => ainfReal (totReal_of X))).trans (flat4 _ _ _ _)

theorem tupCoord_add {D : D7} (X : HidaSetting D) (x y : TupI X) :
    tupCoord X (x + y) = tupCoord X x + tupCoord X y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [tupCoord, Homeomorph.trans_apply]
  rw [← flatten_four_add]
  congr 1
  funext a i k
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.add_apply]
  rw [tensCoord_add]
  exact ainfReal_add (totReal_of X) _ _

theorem psiInf_addP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (a b : Ainf F) :
    psiInf F ψ (a + b) = psiInf F ψ a * psiInf F ψ b := by
  have h : (pairA F (a + b) 0 : AF F) = pairA F a 0 + pairA F b 0 := by
    show ((a + b, 0) : Ainf F × Af F) = ((a, 0) : Ainf F × Af F) + ((b, 0) : Ainf F × Af F)
    rw [Prod.mk_add_mk, add_zero]
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf]
  rw [h, AddChar.map_add_eq_mul]

theorem psiInf_eq {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) :
    psiInf F ψ = fun x => Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)) :=
  funext hS

theorem continuous_psiInfP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) : Continuous (psiInf F ψ) := by
  rw [psiInf_eq ψ hS]
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp (continuous_apply w))

theorem norm_psiInfP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) (x : Ainf F) : ‖psiInf F ψ x‖ = 1 := by
  rw [hS x]
  have : 2 * (Real.pi : ℂ) * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ) =
      ((2 * Real.pi * ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ) *
        Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem BR_add_leftP {D : D7} (X : HidaSetting D) (x x' y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (x + x') y = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y + BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x' y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem BR_add_rightP {D : D7} (X : HidaSetting D) (x y y' : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x (y + y') = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y + BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem continuous_traceP {D : D7} (X : HidaSetting D) :
    Continuous (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_BR_leftP {D : D7} (X : HidaSetting D) (y : TupI X) : Continuous fun x : TupI X => BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun x : TupI X => ∑ a, Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (∑ i, ∑ j, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf X.B.I.F) X.B.I.cm.sig (x a i) * JR (Ainf X.B.I.F) X.B.I.J i j * y a j)
  exact continuous_finsetSum _ fun a _ => (continuous_traceP X).comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (((continuous_sigRP (Ainf X.B.I.F) X.B.I.cm.sig).comp
      ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul continuous_const)

theorem continuous_BR_rightP {D : D7} (X : HidaSetting D) (x : TupI X) : Continuous fun y : TupI X => BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun y : TupI X => ∑ a, Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (∑ i, ∑ j, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf X.B.I.F) X.B.I.cm.sig (x a i) * JR (Ainf X.B.I.F) X.B.I.J i j * y a j)
  exact continuous_finsetSum _ fun a _ => (continuous_traceP X).comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply a)))

theorem sdTestI_holds : SdTestI := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI := hP.2.2.2.2.1.1
  have hS := hP.2.2.1
  have hpc := continuous_psiInfP ψ hS
  exact ST.testEx_of_homeo μinf _ (tupCoord X) (tupCoord_add X)
    (fun x x' y => by rw [BR_add_leftP, psiInf_addP])
    (fun x y y' => by rw [BR_add_rightP, psiInf_addP])
    (fun x y => norm_psiInfP ψ hS _)
    (fun y => hpc.comp (continuous_BR_leftP X y))
    (fun x => hpc.comp (continuous_BR_rightP X x))

theorem invFib_holds : InvFib := invFib_of (sdInvG_of sdTestI_holds)

end PI.AprimeInfW
end
end

