module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0008

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstFin
section
noncomputable section

namespace PI.AprimeInfW

theorem properOrb_of_compact (hH : MassDataMassesW.HinfCompact) : ProperOrb :=
  properOrb_of_one (properOne_of wittInf_holds hH) invNbhd_holds

theorem pushCont_of_compact (hH : MassDataMassesW.HinfCompact) : PushCont :=
  pushCont_of frame_independent_at_infinity (properOrb_of_compact hH)

theorem pushLFin_of_compact (hH : MassDataMassesW.HinfCompact) : PushLFin :=
  pushLFin_of_proper (properOrb_of_compact hH)

theorem constTest_of_polar_compact (hP : PolarLoc) (hH : MassDataMassesW.HinfCompact) : ConstTest :=
  constTest_of_polar hP (pushCont_of_compact hH)

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMu
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

abbrev KapI {D : D7} (X : HidaSetting D) : Type :=
  Fin (D.R.rS + 1 + D.R.rS) × Fin X.B.I.n ×
    Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F

def betaI {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)) : ℝ :=
  ∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w
    (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w)).re


open Classical in
def matI {D : D7} (X : HidaSetting D) : Matrix (KapI X) (KapI X) ℝ :=
  fun i j => betaI X (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)


open Classical in
def DensMu : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    μinf.map (tupCoord X) = ENNReal.ofReal (Real.sqrt |(matI X).det|) • volume

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLieCompl
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

section Lie

variable {V : Type} [Fintype V] {n : ℕ}

def lieK (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) : Submodule ℝ (V → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
    ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro A B hA hB v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · have e : (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) =
          ((A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * A v) +
            ((B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * B v) := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
      show (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) = 0
      rw [e, (hA v).1, (hB v).1, add_zero]
    · show A v i j + B v i j = 0
      rw [(hA v).2 i hi j hj, (hB v).2 i hi j hj, add_zero]
  smul_mem' := by
    intro c A hA v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · show (c • A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (c • A v) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hA v).1,
        smul_zero]
    · show c • A v i j = 0
      rw [(hA v).2 i hi j hj, smul_zero]

def entL (V : Type) [Fintype V] (n : ℕ) :
    (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] EuclideanSpace ℂ (V × Fin n × Fin n) :=
  ({ toFun := fun M p => M p.1 p.2.1 p.2.2
     invFun := fun f v i j => f (v, i, j)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } : (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] (V × Fin n × Fin n → ℂ)).trans
    ((EuclideanSpace.equiv (V × Fin n × Fin n) ℂ).toLinearEquiv.restrictScalars ℝ).symm

theorem entL_apply (M : V → Matrix (Fin n) (Fin n) ℂ) (p : V × Fin n × Fin n) :
    (EuclideanSpace.equiv (V × Fin n × Fin n) ℂ) (entL V n M) p = M p.1 p.2.1 p.2.2 := by
  simp [entL] <;> rfl

theorem norm_entL_sq (M : V → Matrix (Fin n) (Fin n) ℂ) :
    ‖entL V n M‖ ^ 2 = ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := entL_apply M (v, i, j)
  simp only [EuclideanSpace.equiv] at this
  rw [← this]
  rfl

theorem exists_lieCompl (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)),
      (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧
        ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) ∧
      (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
      ∀ M : V → Matrix (Fin n) (Fin n) ℂ,
        (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) →
          ∃ x, L x = M := by
  set K' : Submodule ℝ (EuclideanSpace ℂ (V × Fin n × Fin n)) := (lieK ε S).map (entL V n).toLinearMap with hK'
  let b := stdOrthonormalBasis ℝ K'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ K')) →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    (entL V n).symm.toLinearMap ∘ₗ K'.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap
  have hLe : ∀ x, entL V n (L x) = (b.repr.symm x : EuclideanSpace ℂ (V × Fin n × Fin n)) := by
    intro x; simp [L]
  have hLK : ∀ x, L x ∈ lieK ε S := by
    intro x
    obtain ⟨M, hM, hMe⟩ := (b.repr.symm x).2
    have : L x = M := by
      apply (entL V n).injective
      rw [hLe]; exact hMe.symm
    rw [this]; exact hM
  refine ⟨Fin (Module.finrank ℝ K'), inferInstance, L, fun x v => hLK x v, fun x => ?_, fun M hM => ?_⟩
  · rw [← norm_entL_sq, hLe]
    exact congrArg (· ^ 2) (b.repr.symm.norm_map x)
  · have hM' : entL V n M ∈ K' := ⟨M, hM, rfl⟩
    refine ⟨b.repr ⟨entL V n M, hM'⟩, ?_⟩
    apply (entL V n).injective
    rw [hLe, LinearIsometryEquiv.symm_apply_apply]

end Lie

def StdConjEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    ∃ (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)), StdConj X hb u' c S

theorem stdDataEx_of (h : StdConjEx) : StdDataEx := by
  intro D X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨c, S, hc⟩ := h X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨ι, hι, L, h1, h2, h3⟩ := exists_lieCompl X.B.I.ε S
  exact ⟨c, S, ι, hι, L, hc, ⟨h1, h2, h3⟩⟩

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibAllP
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem lfFib_at {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) : LFI X (fibInf T) := by
  intro K hK hKU
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨k, -, hkcl, hKk, hkU⟩ := exists_compact_closed_between hK (isOpen_IndI X) hKU
  obtain ⟨f, hf1, hf0, hfc, -⟩ := exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.mpr hKk)
  have hts : tsupport f ⊆ IndI X := by
    refine (closure_minimal ?_ hkcl).trans hkU
    intro y hy
    by_contra h
    exact hy (hf0 (fun h' => h (interior_subset h')))
  have hI := ((hP.2.2.2.2.2.2).2.2 f f.continuous hfc hts).1 T (Set.mem_univ _)
  calc fibInf T K ≤ fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} :=
        measure_mono fun y hy => by
          simp only [Set.mem_ofPred_eq]
          rw [hf1 hy]
          simp
    _ = 1 * fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} := (one_mul _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(fibInf T) :=
        mul_meas_ge_le_lintegral₀ f.continuous.measurable.ennreal_ofReal.aemeasurable 1
    _ < ⊤ := hI.lintegral_lt_top

theorem fibAllT_holds : FibAllT := by
  intro D X u' ψ hT μinf νinf fibInf hP T
  refine ⟨fun g => ?_, lfFib_at X u' ψ hT μinf νinf fibInf hP T⟩
  have hfib := hP.2.2.2.2.2.2
  have h := fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1
    (fibTrans X μinf νinf fibInf hfib g (sdInvG_of sdTestI_holds X u' ψ hT μinf νinf fibInf hP g)) hfib
  exact congrFun h T

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpParts
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Matrix Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
theorem continuous_matExp (n : ℕ) : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
  open scoped Norms.Operator in NormedSpace.exp_continuous

theorem continuous_expU {n : ℕ} (ε : Fin n → Bool) {Y : Type} [TopologicalSpace Y]
    (f : Y → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f)
    (hL : ∀ y, (f y)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * f y = 0) : Continuous (fun y => expU ε (f y)) := by
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · have e : (Units.val ∘ Subtype.val ∘ fun y => expU ε (f y)) = fun y => NormedSpace.exp (f y) :=
      funext fun y => expU_val ε _ (hL y)
    rw [e]
    exact (continuous_matExp n).comp hf
  · have e : (fun x => ((((Subtype.val ∘ fun y => expU ε (f y)) x)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = fun y => NormedSpace.exp (-f y) := by
      funext y
      apply Units.inv_eq_of_mul_eq_one_right
      show (((expU ε (f y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        NormedSpace.exp (-f y) = 1
      rw [expU_val ε _ (hL y), ← Matrix.exp_add_of_commute (f y) (-f y) (Commute.neg_right (Commute.refl (f y))), add_neg_cancel,
        NormedSpace.exp_zero]
    rw [e]
    exact (continuous_matExp n).comp hf.neg

theorem continuous_kap0_of_lieCompl {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (hL : LieCompl X S L) : Continuous (kap0 X hb c L) := by
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hg : Continuous (fun x => ((fun v => expU (X.B.I.ε v) (L x v)) : X.B.I.Ginf)) :=
    continuous_pi fun v => continuous_expU _ (fun x => L x v) ((continuous_apply v).comp hLc)
      (fun x => (hL.1 x v).1)
  exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul hg).mul continuous_const)

def chiOf {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf) {η : Type}
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (y : EuclideanSpace ℝ η) : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L₁ y v)) * c⁻¹)

def BlockLie {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {η : Type}
    [Fintype η]
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) :
    Prop :=
  (∀ y v, (L₁ y v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * L₁ y v = 0 ∧
    ∀ i j, (i ∉ S v ∨ j ∉ S v) → L₁ y v i j = 0) ∧
  (∀ y, ∑ v, ∑ i, ∑ j, ‖L₁ y v i j‖ ^ 2 = ‖y‖ ^ 2) ∧
  ∀ M : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
    (∀ v, (M v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * M v = 0 ∧
      ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0) → ∃ y, L₁ y = M

def BlockEx : Prop := ∀ {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)),
    ∃ (η : Type) (_ : Fintype η)
      (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
      BlockLie X S L₁

def StdCtx {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι η : Type} [Fintype ι] [Fintype η]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) : Prop :=
  (∃ ψ : AddChar (AF X.B.I.F) ℂ, ∃ hT μinf νinf fibInf, PushHyp X u' ψ hT μinf νinf fibInf) ∧
    StdConj X hb u' c S ∧ LieCompl X S L ∧ BlockLie X S L₁

def ChiStab : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∀ y, chiOf X hb c L₁ y ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u')

def GrpDens : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧ ∃ d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt d 0 ∧ d 0 = Formalism.MainNotions.S.AutInst.gaugeU X.B.I ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        X.measG.μGinf ((fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2) '' A) = ∫⁻ p in A, ENNReal.ofReal (d p)

def GrpHaarH : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∀ hS : ∀ y, chiOf X hb c L₁ y ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'),
    ∃ (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) (r : ℝ)
      (e : EuclideanSpace ℝ η → ℝ),
      ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧ 0 < r ∧ ContinuousAt e 0 ∧ 0 < e 0 ∧
      (ν Set.univ).toReal / e 0 = Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) ∧
      ∀ s, 0 < s → s ≤ r → ν ((fun y => (⟨chiOf X hb c L₁ y, hS y⟩ :
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) '' ball 0 s) =
        ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)

def GrpInj : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧
      (∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r,
        (kap0 X hb c L a)⁻¹ * kap0 X hb c L b ∈
          MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') → a = b) ∧
      Set.InjOn (chiOf X hb c L₁) (ball 0 r)

theorem grpPiecesStd_of (h0 : BlockEx) (hS : ChiStab) (hD : GrpDens) (hH : GrpHaarH) (hI : GrpInj) :
    GrpPiecesStd := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  obtain ⟨η, hη, L₁, hB⟩ := h0 X S
  have ctx : StdCtx X u' hb c S L L₁ := ⟨⟨ψ, hT, μinf, νinf, fibInf, hP⟩, hc, hL, hB⟩
  have hst := hS X u' hb c S L L₁ ctx
  obtain ⟨r1, hr1, d, hdc, hd0, hdens⟩ := hD X u' hb c S L L₁ ctx
  obtain ⟨ν, r2, e, hL', hSF, h0', hf, hr2, hec, he0, hvol, hνd⟩ := hH X u' hb c S L L₁ ctx hst
  obtain ⟨r3, hr3, hinj, hχi⟩ := hI X u' hb c S L L₁ ctx
  have hr : 0 < min r1 (min r2 r3) := lt_min hr1 (lt_min hr2 hr3)
  have h1 : min r1 (min r2 r3) ≤ r1 := min_le_left _ _
  have h2 : min r1 (min r2 r3) ≤ r2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min r1 (min r2 r3) ≤ r3 := (min_le_right _ _).trans (min_le_right _ _)
  have hχc : Continuous (fun y => (⟨chiOf X hb c L₁ y, hst y⟩ :
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) := by
    apply Continuous.subtype_mk
    have hLc : Continuous L₁ := L₁.continuous_of_finiteDimensional
    exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul (continuous_pi fun v =>
      continuous_expU _ (fun y => L₁ y v) ((continuous_apply v).comp hLc) (fun y => (hB.1 y v).1))).mul
        continuous_const)
  have hgpos : 0 < Formalism.MainNotions.S.AutInst.gaugeU X.B.I := Finset.prod_pos fun v _ => (hP.2.2.2.1 v).2
  have hdet1 : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).det = 1 := by
    simp [ContinuousLinearMap.det]
  refine ⟨η, hη, fun y => ⟨chiOf X hb c L₁ y, hst y⟩, min r1 (min r2 r3),
    fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2, ball 0 (min r1 (min r2 r3)), d, id,
    fun _ => ContinuousLinearMap.id ℝ _, e, ν, hL', hSF, h0', hf, hr,
    (continuous_kap0_of_lieCompl X hb c S L hL).continuousOn, hχc.continuousOn, ?_, ?_, ?_, ?_, Set.injOn_id _, ?_, ?_, ?_,
    continuousAt_id, ?_, hdc, hec, he0, ?_, ?_⟩
  · intro a ha b hb' hab
    exact hχi (ball_subset_ball h3 ha) (ball_subset_ball h3 hb') (congrArg Subtype.val hab)
  · intro a ha b hb' hm
    exact hinj a (ball_subset_ball h3 ha) b (ball_subset_ball h3 hb') hm
  · intro A hA hAm
    exact hdens A (hA.trans (ball_subset_ball h1)) hAm
  · intro p _
    exact hasFDerivWithinAt_id p _
  · rw [Set.image_id]
  · intro p _
    rfl
  · intro s hs hsr
    exact hνd s hs (hsr.trans h2)
  · simp only [hdet1]
    exact continuousAt_const
  · simp only [hdet1, abs_one, one_mul, id]
    rw [hd0]
    exact hgpos
  · simp only [hdet1, abs_one, one_mul, id]
    rw [hd0, gVal, ← hvol]
    ring


set_option backward.isDefEq.respectTransparency false in
theorem exp_mul_of_mul_eq_zero {n : ℕ} (M P : Matrix (Fin n) (Fin n) ℂ) (hMP : M * P = 0) :
    NormedSpace.exp M * P = P := by
  open scoped Norms.Operator in
  have hs : Summable (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • M ^ k) := NormedSpace.expSeries_summable' (𝕂 := ℚ) M
  rw [NormedSpace.exp_eq_tsum_rat, ← hs.tsum_mul_right P, tsum_eq_single 0]
  · simp
  · intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [smul_mul_assoc, pow_succ, Matrix.mul_assoc, hMP, Matrix.mul_zero, smul_zero]

theorem exp_block_col {n : ℕ} (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) (i : Fin n) (hi : i ∉ S) (j : Fin n) :
    NormedSpace.exp M j i = if j = i then 1 else 0 := by
  have hMP : M * Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) = 0 := by
    ext a b
    rw [Matrix.mul_diagonal]
    by_cases hb : b ∈ S
    · simp [hb]
    · simp [hb, hM a b (Or.inr hb)]
  have h := congrFun (congrFun (exp_mul_of_mul_eq_zero M _ hMP) j) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_apply] at h
  simp only [hi, if_false, mul_one] at h
  rw [h]
  by_cases hji : j = i
  · subst hji
    simp [hi]
  · simp [hji]

theorem chiStab' : ChiStab := by
  intro D X u' hb c S ι η _ _ L L₁ ctx y
  unfold chiOf
  refine (ctx.2.1.2 _).2 fun v i hi j => ?_
  show (((expU (X.B.I.ε v) (L₁ y v) : Formalism.REAL.UJ (X.B.I.ε v)) :
    (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) j i = _
  rw [expU_val _ _ (ctx.2.2.2.1 y v).1]
  exact exp_block_col (S v) _ (ctx.2.2.2.1 y v).2 i hi j

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushTop
section
noncomputable section

namespace PI.AprimeInfW

theorem pushInf_of_pushLFin_of_orbUniq_of_constTest (hL : PushLFin) (hU : OrbUniq) (hC : ConstTest) : PushInf :=
  pushInf_of invPush_holds invFib_holds (lfPush_of detNZ_holds hL) lfFib_holds hU hC

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UnitsOpenTens
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def UnitsOpenTens : Prop := ∀ {D : D7} (X : HidaSetting D), IsOpen {z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit z}

theorem isUnit_det_TI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) :
    IsUnit (TI X u' hT).1.det := by
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem nearFacts_of (hU : UnitsOpenTens) : NearFacts := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hCh
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨hmr, hcomp, hsmul, hgram, hcTmul, hcT1, -, -⟩ := rmulFacts_holds X
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hdetc : ContinuousAt (fun T => (a T).det) (TI X u' hT) :=
    (continuous_id.matrix_det).continuousAt.comp hCh.2.2.1
  have hU1 : {T | IsUnit (a T).det} ∈ 𝓝 (TI X u' hT) :=
    hdetc.preimage_mem_nhds ((hU X).mem_nhds (by
      show IsUnit (a (TI X u' hT)).det
      rw [hCh.2.1, Matrix.det_one]; exact isUnit_one))
  refine ⟨Ω ∩ {T | IsUnit (a T).det}, Set.inter_subset_left, Filter.inter_mem hCh.1 hU1, fun T hT1 =>
    ⟨(Matrix.isUnit_iff_isUnit_det _).2 hT1.2, fun Y hY => ?_⟩⟩
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [hY, ← hCh.2.2.2 T hT1.1, hgram, gramR_Y0_eq_TI X u' hT, Matrix.det_mul, Matrix.det_mul]
  have hc : (cTI X (a T)).det = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf X.B.I.F) X.B.I.cm.sig (a T).det := by
    rw [cTI, Matrix.det_transpose, RingHom.map_det]
    rfl
  rw [hc]
  exact ((hT1.2.map _).mul (isUnit_det_TI X u' hT hd)).mul hT1.2

end PI.AprimeInfW
end
end

