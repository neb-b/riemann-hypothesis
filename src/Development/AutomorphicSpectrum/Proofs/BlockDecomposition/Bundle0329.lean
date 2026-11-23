module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0323
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0325
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl Topology Matrix GroundTheory.Automorphic
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AffglAssembly

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isAutForm_add {φ ψ : Sm E a} (h : IsAutForm φ) (h' : IsAutForm ψ) : IsAutForm (φ + ψ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [h.left, h'.left]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) ?_)
    intro k hk
    have h1 : finRep E a k φ = φ := hk.1
    have h2 : finRep E a k ψ = ψ := hk.2
    change finRep E a k (φ + ψ) = φ + ψ
    rw [map_add (f := _), h1, h2]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C, N, h1⟩ := h.growth g
    obtain ⟨C', N', h2⟩ := h'.growth g
    refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
    have hy := one_le_height y
    have e1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have e2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have hp : 0 ≤ height y ^ N := by positivity
    have hp' : 0 ≤ height y ^ N' := by positivity
    calc ‖(φ + ψ).1 (g * infGL E a y)‖ ≤ ‖φ.1 (g * infGL E a y)‖ + ‖ψ.1 (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (h1 y) (h2 y)
      _ ≤ |C| * height y ^ (N + N') + |C'| * height y ^ (N + N') := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) hp).trans
            (mul_le_mul_of_nonneg_left e1 (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C') hp').trans
            (mul_le_mul_of_nonneg_left e2 (abs_nonneg C'))
      _ = (|C| + |C'|) * height y ^ (N + N') := by ring

theorem isAutForm_smul (c : ℂ) {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (c • φ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change c • φ.1 _ = c • φ.1 _
    rw [h.left]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.level.mem_nhds (by simp)) ?_)
    intro k hk
    have h1 : finRep E a k φ = φ := hk
    change finRep E a k (c • φ) = c • φ
    rw [map_smul, h1]
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C, N, h1⟩ := h.growth g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    change ‖c * φ.1 (g * infGL E a y)‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg c)

def genSub (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))) : Submodule ℂ (Sm E a) where
  carrier := genSpace L ρ J
  zero_mem' := ⟨isAutForm_const (Submodule.zero_mem _), fun k _ => map_zero _, fun g => by
    have e : (fun k : Kinf E a => (cptRep E a k (0 : Sm E a)).1 g) = 0 := by
      funext k; rw [map_zero]; rfl
    rw [e]; exact Submodule.zero_mem _, fun z _ => map_zero z⟩
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨isAutForm_add h1 h1', fun k hk => by rw [map_add (f := _), h2 k hk, h2' k hk], fun g => ?_,
      fun z hz => by rw [map_add (f := _), h4 z hz, h4' z hz, add_zero]⟩
    have e : (fun k : Kinf E a => (cptRep E a k (φ + ψ)).1 g) =
        (fun k : Kinf E a => (cptRep E a k φ).1 g) + fun k : Kinf E a => (cptRep E a k ψ).1 g := by
      funext k; rw [map_add (f := _)]; rfl
    rw [e]; exact Submodule.add_mem _ (h3 g) (h3' g)
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, h4⟩
    refine ⟨isAutForm_smul c h1, fun k hk => by rw [map_smul, h2 k hk], fun g => ?_,
      fun z hz => by rw [map_smul, h4 z hz, smul_zero]⟩
    have e : (fun k : Kinf E a => (cptRep E a k (c • φ)).1 g) =
        c • fun k : Kinf E a => (cptRep E a k φ).1 g := by
      funext k; rw [map_smul]; rfl
    rw [e]; exact Submodule.smul_mem _ c (h3 g)

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_mapInf :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

theorem continuous_mapFin :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

theorem continuous_of_level {φ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ}) : Continuous φ.1 := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hc : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  let f : GA E a → ℂ := fun g =>
    chart φ.1 g₀ (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val)
  have e1 : ∀ᶠ g in 𝓝 g₀, f g = φ.1 g := by
    have hS : {g : GA E a | GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ :=
      ((continuous_mapFin.comp hc).continuousAt).preimage_mem_nhds
        (h.mem_nhds (by simp))
    filter_upwards [hS] with g hg
    have hg' : finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ := hg
    have e2 := congrFun (congrArg Subtype.val hg') (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)))
    have e3 : g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) = g := by
      rw [mul_assoc, infGL_mul_finGL, mul_inv_cancel_left]
    change φ.1 (_ * finGL E a _) = _ at e2
    rw [e3] at e2
    simp only [f]
    rw [chart_val, e2]
  refine ContinuousAt.congr ?_ e1
  have hx : toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val ∈ invSet E a := val_mem_invSet _
  have h1 : ContinuousAt (chart φ.1 g₀) (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ hx).continuousAt
  have h3 : Continuous fun g : GA E a => ((GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) : GL (Fin a) (Cinf E)) :
      Matrix (Fin a) (Fin a) (Cinf E)) := Units.continuous_val.comp (continuous_mapInf.comp hc)
  have h2 : Continuous fun g : GA E a => toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val := h3
  exact ContinuousAt.comp (f := fun g : GA E a => toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) h1 h2.continuousAt

theorem unip_eq_unipGL {R : Type} [CommRing R] {r : ℕ} (x : BlockIx a r → R) :
    unip x = AutomorphicForm.unipGL x := Units.ext rfl

theorem pi_eq_borel (r : ℕ) :
    (MeasurableSpace.pi : MeasurableSpace (BlockIx a r → Ad E)) = borel (BlockIx a r → Ad E) :=
  BorelSpace.measurable_eq

theorem isCuspidal_of_constantTerm {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h0 : ∀ r : ℕ, 0 < r → r < a → ∀ g, ∫ x in AutomorphicForm.unipFundamentalDomain E a r, φ (unip x * g)
      ∂AutomorphicForm.unipMeasure E a r = 0) : IsCuspidal φ := by
  intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
  obtain rfl : inst1 = MeasurableSpace.pi := inst2.measurable_eq.trans (pi_eq_borel r).symm
  have : (AutomorphicForm.unipMeasure E a r).IsAddHaarMeasure := inferInstance
  have hc := Measure.isAddLeftInvariant_eq_smul μ (AutomorphicForm.unipMeasure E a r)
  have : Countable (ratN E a r) := AutomorphicForm.countable_unipLattice (K := E) (n := a) (r := r)
  have hF0 : IsAddFundamentalDomain (ratN E a r) (AutomorphicForm.unipFundamentalDomain E a r) μ :=
    IsAddFundamentalDomain.mono AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain
      (hc ▸ Measure.smul_absolutelyContinuous)
  have hinv : ∀ (ξ : ratN E a r) (x : BlockIx a r → Ad E), φ (unip (ξ +ᵥ x) * g) = φ (unip x * g) := by
    rintro ⟨_, ξ, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (ξ p)) + x) * g) = _
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  rw [hF.setIntegral_eq hF0 hinv, hc, Measure.restrict_smul, integral_smul_nnreal_measure, h0 r hr hr' g, smul_zero]

theorem integrableOn_unip {φ : GA E a → ℂ} (hφ : Continuous φ) (r : ℕ) (g : GA E a) :
    IntegrableOn (fun x => φ (unip x * g)) (AutomorphicForm.unipFundamentalDomain E a r)
      (AutomorphicForm.unipMeasure E a r) := by
  have e : (fun x : BlockIx a r → Ad E => φ (unip x * g)) = fun X => φ (AutomorphicForm.unipGL X * g) :=
    funext fun x => by rw [unip_eq_unipGL]
  rw [e]
  exact AutomorphicForm.integrableOn_constantTerm hφ g

def ctMap (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))) (r : ℕ) :
    genSub L ρ J →ₗ[ℂ] (GA E a → ℂ) where
  toFun ψ g := ∫ x in AutomorphicForm.unipFundamentalDomain E a r, ψ.1.1 (unip x * g)
    ∂AutomorphicForm.unipMeasure E a r
  map_add' ψ ψ' := funext fun g =>
    integral_add (integrableOn_unip (continuous_of_level ψ.2.1.level) r g)
      (integrableOn_unip (continuous_of_level ψ'.2.1.level) r g)
  map_smul' c ψ := funext fun g => integral_smul c _

theorem genFin_step (hC : CuspFin E a) (hT : ∀ r, 0 < r → r < a → CTFin E a r) : GenFin E a := by
  intro L hL W _ _ _ ρ hρ J hJ
  let R := {r : ℕ // 0 < r ∧ r < a}
  have : Finite R := Finite.of_injective (fun r : R => (⟨r.1, r.2.2⟩ : Fin a))
    fun x y h => Subtype.ext (congrArg (fun z : Fin a => z.1) h)
  have ct := fun r : R => hT r.1 r.2.1 r.2.2 L hL W ρ hρ J hJ
  choose V hVf hV using ct
  have : ∀ r, FiniteDimensional ℂ (V r) := hVf
  have hm : ∀ (r : R) (ψ : genSub L ρ J), ctMap L ρ J r.1 ψ ∈ V r := fun r ψ =>
    hV r ψ.1 ψ.2 (AutomorphicForm.unipMeasure E a r.1) (AutomorphicForm.unipFundamentalDomain E a r.1)
      inferInstance AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain
  let Φ : genSub L ρ J →ₗ[ℂ] (∀ r : R, V r) :=
    LinearMap.pi fun r => (ctMap L ρ J r.1).codRestrict (V r) (hm r)
  have hker : FiniteDimensional ℂ (LinearMap.ker Φ) := by
    have hC' := hC L hL W ρ hρ J hJ
    have hle : (LinearMap.ker Φ).map (genSub L ρ J).subtype ≤
        Submodule.span ℂ {φ | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1} := by
      rintro _ ⟨ψ, hψ, rfl⟩
      refine Submodule.subset_span ⟨ψ.2, isCuspidal_of_constantTerm ψ.2.1.left fun r h0 h1 g => ?_⟩
      exact congrFun (congrArg Subtype.val (congrFun (LinearMap.mem_ker.1 hψ) ⟨r, h0, h1⟩)) g
    have : FiniteDimensional ℂ ((LinearMap.ker Φ).map (genSub L ρ J).subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact Module.Finite.equiv
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) (LinearMap.ker Φ)).symm
  have hfin : FiniteDimensional ℂ (genSub L ρ J) := by
    have : Module.Finite ℂ (genSub L ρ J ⧸ LinearMap.ker Φ) := Module.Finite.equiv Φ.quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker Φ)
  rw [show Submodule.span ℂ (genSpace L ρ J) = genSub L ρ J from Submodule.span_eq (genSub L ρ J)]
  exact hfin

theorem genFin_of_chapters :
    (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspFin E a) →
    (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) →
      ∀ r, 0 < r → r < a → CTFin E a r) →
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GenFin E a := by
  intro hC hT E _ _ _ a
  induction a using Nat.strong_induction_on with
  | _ a ih => exact genFin_step (hC E a) (hT E a ih)

end GlobalTheory.CompanionTheory.AffglAssembly

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerMulJG
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.BigCell

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_inG : InG (JJ n) := by
  have hc : (JJ n)ᴴ = -JJ n := by
    unfold JJ
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
  show (JJ n)ᴴ * JJ n * JJ n = JJ n
  rw [hc, Matrix.mul_assoc, JJ_mul_JJ]
  simp

def JG : GR n :=
  ⟨⟨JJ n, -JJ n, by simp [JJ_mul_JJ], by simp [JJ_mul_JJ]⟩, JJ_inG⟩

theorem lower_mul_JG (y : GR n) :
    (mR (y * JG)).toBlocks₂₁ = -(mR y).toBlocks₂₂ := by
  have h : mR (y * JG) = mR y * JJ n := rfl
  rw [h, ← Matrix.fromBlocks_toBlocks (mR y)]
  unfold JJ
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  simp

theorem dense_bigCell₂₂ : ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} := by
  intro n
  have hset : {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} =
      (fun y => y * (JG (n := n))) ⁻¹' {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, lower_mul_JG, Matrix.det_neg]
    constructor
    · intro h
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h
    · intro h h0
      exact h (by rw [h0, mul_zero])
  rw [hset]
  exact (dense_bigCell n).preimage (isOpenMap_mul_right _)

end GlobalTheory.CompanionTheory.BigCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquare
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GodementCoeff

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure]
  [ν.IsMulRightInvariant] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

private theorem integrableOn_and_setIntegral_sq_le_of_isU (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) {s : Set Γ} (hs : MeasurableSet s)
    (hs' : ν s ≠ ⊤) :
    IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν ∧
      ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hcont : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hbd : ∀ g, ‖⟪b, ρ g v⟫_ℂ‖ ≤ ‖b‖ * ‖v‖ := fun g =>
    (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  have hc2 : IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν := by
    refine Measure.integrableOn_of_bounded (M := (‖b‖ * ‖v‖) ^ 2) hs'
      (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd g) 2
  set f : Γ → ℂ := s.indicator (fun g => starRingEnd ℂ ⟪b, ρ g v⟫_ℂ) with hfdef
  have hfm : Measurable f := ((Complex.continuous_conj.comp hcont).measurable).indicator hs
  have hfi : Integrable f ν := by
    refine (integrable_indicator_iff hs).mpr (Measure.integrableOn_of_bounded (M := ‖b‖ * ‖v‖) hs'
      (Complex.continuous_conj.comp hcont).aestronglyMeasurable (ae_of_all _ fun g => ?_))
    rw [Complex.norm_conj]
    exact hbd g
  have hfeq : (fun g => ‖f g‖ ^ 2) = s.indicator (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) := by
    funext g
    by_cases hg : g ∈ s <;> simp [hfdef, hg, norm_inner_symm]
  have hf2 : Integrable (fun g => ‖f g‖ ^ 2) ν := by
    rw [hfeq]
    exact (integrable_indicator_iff hs).mpr hc2
  have hG := GlobalTheory.CompanionTheory.Godement.norm_sq_integral_smul_le ν ρ hρ v hm f hfm hfi hf2
  rw [hfeq, integral_indicator hs] at hG
  have hint : Integrable (fun g => f g • ρ g v) ν :=
    hfi.smul_of_top_left (memLp_top_of_bound (hρ.cont v).aestronglyMeasurable ‖v‖
      (ae_of_all _ fun g => (hρ.norm g v).le))
  set I := ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν with hIdef
  set w := ∫ g, f g • ρ g v ∂ν with hwdef
  have hinner : ⟪b, w⟫_ℂ = (I : ℂ) := by
    have h := (innerSL ℂ b).integral_comp_comm hint
    simp only [innerSL_apply_apply] at h
    rw [hwdef, ← h, hIdef, ← integral_indicator hs, ← integral_complex_ofReal]
    congr 1
    funext g
    by_cases hg : g ∈ s
    · rw [hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem hg, inner_smul_right,
        Complex.conj_mul']
      push_cast
      rfl
    · simp [hfdef, hg]
  have hI0 : 0 ≤ I := setIntegral_nonneg hs fun _ _ => by positivity
  have hM0 : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  have h1 : I ≤ ‖b‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) b w
    rwa [hinner, Complex.norm_real, Real.norm_of_nonneg hI0] at h
  refine ⟨hc2, ?_⟩
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have h2 : I * I ≤ I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
      calc I * I ≤ (‖b‖ * ‖w‖) * (‖b‖ * ‖w‖) := mul_self_le_mul_self hI0 h1
        _ = ‖b‖ ^ 2 * ‖w‖ ^ 2 := by ring
        _ ≤ ‖b‖ ^ 2 * (I * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) := by gcongr
        _ = I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by ring
    exact le_of_mul_le_mul_left h2 hpos

theorem sq_integrable_and_bound (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) :
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
      ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hK : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 :=
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (sq_nonneg _)
  have hcont : Continuous fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 :=
    (continuous_const.inner (hρ.cont v)).norm.pow 2
  have key : ∀ s, MeasurableSet s → ν s ≠ ⊤ → ∫⁻ g in s, ‖‖⟪b, ρ g v⟫_ℂ‖ ^ 2‖ₑ ∂ν ≤
      ENNReal.ofReal ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
    intro s hs hs'
    obtain ⟨hi, hle⟩ := integrableOn_and_setIntegral_sq_le_of_isU ν ρ hρ v hm b hs hs'
    rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
    apply ENNReal.ofReal_le_ofReal
    simpa only [norm_pow, norm_norm] using hle
  have hInt : Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν :=
    integrable_of_forall_fin_meas_le _ ENNReal.ofReal_lt_top hcont.aestronglyMeasurable key
  refine ⟨hInt, ?_⟩
  have hle := lintegral_le_of_forall_fin_meas_le _ key
  rw [← ofReal_integral_norm_eq_lintegral_enorm hInt, ENNReal.ofReal_le_ofReal_iff hK] at hle
  simpa only [norm_pow, norm_norm] using hle

end GlobalTheory.CompanionTheory.GodementCoeff

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureImagePrincipalPosLtTop
section
open GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

theorem measure_image_principal_pos_lt_top :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : k) (m : ℕ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 →
      (∀ x : k, ValuativeRel.valuation k (x) < 1 →
        ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m →
      ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)),
        μ.IsHaarMeasure →
        0 < μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
            ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
              ValuativeRel.valuation k (ϖ ^ m)}) ∧
        μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
            ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
              ValuativeRel.valuation k (ϖ ^ m)}) < ⊤ := by
  intro k _ _ _ _ N ϖ m h0 h1 _ hm _ _ μ hμ
  have ht0 : ϖ ^ m ≠ 0 := pow_ne_zero m h0
  have ht1 : ValuativeRel.valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one' h1 (by omega)
  obtain ⟨hopen, hcomp⟩ := isOpen_isCompact_principal k N (ϖ ^ m) ht0 ht1
  have hone : (1 : GL (Fin N) k) ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (ϖ ^ m)} := by
    intro i j
    simp
  refine ⟨?_, ?_⟩
  · have himg : IsOpenMap (QuotientGroup.mk : GL (Fin N) k → AdGL k N) :=
      QuotientGroup.isOpenMap_coe
    exact (himg _ hopen).measure_pos μ ⟨_, Set.mem_image_of_mem _ hone⟩
  · exact (hcomp.image QuotientGroup.continuous_mk).measure_lt_top

end GlobalTheory.CompanionTheory.PrincipalCongruence
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricLeviUnipotentLower
section
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

theorem factor_Gx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ m ∈ (Gx k e).comap (leviEmb k e), ∃ x ∈ unipRad k e, ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  intro k _ _ _ _ n s d e g hg
  obtain ⟨u, hu, h, hh, rfl⟩ := _root_.GlobalTheory.CompanionTheory.GxSplit.gx_split k n s d e g hg
  obtain ⟨m, hLm, x, hx, c, hc, hdec⟩ := _root_.GlobalTheory.CompanionTheory.KOneFactor.kone_factor k n s d e h hh
  have hm : GlobalTheory.SmGL.leviEmb k e m ∈ PositivityTheory.LowerBoundConstant.Gx k e := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact Subgroup.mem_sup_left hLm
  have hconj : (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m
      ∈ GlobalTheory.SmGL.unipRad k e := by
    have hn := GlobalTheory.SmGL.leviEmb_mem_normalizer k e m⁻¹
    rw [map_inv] at hn
    have h' := (Subgroup.mem_normalizer_iff.mp hn u).mp hu.1
    rwa [inv_inv] at h'
  refine ⟨m, Subgroup.mem_comap.mpr hm,
    (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m * x,
    mul_mem hconj hx.1, c, hc, ?_⟩
  rw [hdec]; group

end GlobalTheory.CompanionTheory.MoyPrasad
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelMorphismCoverCompatStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_level_morphism_cover_compat : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (n : ℕ) (c : WittVector l k) (m : QMor (sW l (B.schFn q) ρ n) (sW l (B.schFn q) ρ (n + 1)) (IdF.span _ c)) (hG : ∀ (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory), stF q ρ n 𝒱 (m.G.obj ⟨T.obj, T.property.1⟩).obj), (∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective (((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j)) → ∀ j, Function.Bijective (((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatCoverGlue.glue | exact GlobalTheory.CompanionTheory.FlatCoverGlue.glue | (intros; apply GlobalTheory.CompanionTheory.FlatCoverGlue.glue <;> assumption)
end

