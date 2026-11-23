module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0014

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEx
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

section Block

variable {V : Type} [Fintype V] {n : ℕ}

def lieB (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) : Submodule ℝ (V → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
    ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro A B hA hB v
    refine ⟨?_, fun i j hij => ?_⟩
    · have e : (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) =
          ((A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * A v) +
            ((B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * B v) := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
      show (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) = 0
      rw [e, (hA v).1, (hB v).1, add_zero]
    · show A v i j + B v i j = 0
      rw [(hA v).2 i j hij, (hB v).2 i j hij, add_zero]
  smul_mem' := by
    intro c A hA v
    refine ⟨?_, fun i j hij => ?_⟩
    · show (c • A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (c • A v) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hA v).1,
        smul_zero]
    · show c • A v i j = 0
      rw [(hA v).2 i j hij, smul_zero]

theorem exists_lieBlock (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) :
    ∃ (η : Type) (_ : Fintype η) (L : EuclideanSpace ℝ η →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)),
      (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧
        ∀ i j, (i ∉ S v ∨ j ∉ S v) → L x v i j = 0) ∧
      (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
      ∀ M : V → Matrix (Fin n) (Fin n) ℂ,
        (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
          ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0) → ∃ x, L x = M := by
  set K' : Submodule ℝ (EuclideanSpace ℂ (V × Fin n × Fin n)) := (lieB ε S).map (entL V n).toLinearMap with hK'
  let b := stdOrthonormalBasis ℝ K'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ K')) →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    (entL V n).symm.toLinearMap ∘ₗ K'.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap
  have hLe : ∀ x, entL V n (L x) = (b.repr.symm x : EuclideanSpace ℂ (V × Fin n × Fin n)) := by
    intro x; simp [L]
  have hLK : ∀ x, L x ∈ lieB ε S := by
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

end Block

theorem blockEx_holds : BlockEx := by
  intro D X S
  obtain ⟨η, hη, L, h1, h2, h3⟩ := exists_lieBlock X.B.I.ε S
  exact ⟨η, hη, L, h1, h2, h3⟩

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuP
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem selfDual_transport {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure V) (χ : V → V → ℂ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (h : SelfDual μ χ) :
    SelfDual (μ.map e) (fun x y => χ (e.symm x) (e.symm y)) := by
  haveI := h.1
  let ea : V ≃+ W := AddEquiv.mk' e.toEquiv he
  let em : V ≃ᵐ W := e.toMeasurableEquiv
  have hm : μ.map e = μ.map em := rfl
  refine ⟨ea.isAddHaarMeasure_map μ e.continuous e.symm.continuous, fun Φ hc hs hI z => ?_⟩
  rw [hm] at hI ⊢
  have hT : ∀ y, ∫ x, Φ x * χ (e.symm x) (e.symm y) ∂(μ.map em) = ∫ x, Φ (e x) * χ x (e.symm y) ∂μ := by
    intro y
    rw [integral_map_equiv]
    simp [em]
  simp only [hT] at hI ⊢
  rw [integrable_map_equiv] at hI
  rw [integral_map_equiv]
  simp only [em, Function.comp_def, Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply] at hI ⊢
  rw [h.2 (fun x => Φ (e x)) (hc.comp e.continuous) (hs.comp_homeomorph e) hI (e.symm z)]
  show Φ (e (-e.symm z)) = Φ (-z)
  rw [show e (-e.symm z) = -z from by
    have := ea.map_neg (e.symm z)
    change e (-e.symm z) = -e (e.symm z) at this
    rw [this, e.apply_symm_apply]]

section Beta

variable {D : D7} (X : HidaSetting D)

theorem tupCoord_symm_add (x y : EuclideanSpace ℝ (KapI X)) :
    (tupCoord X).symm (x + y) = (tupCoord X).symm x + (tupCoord X).symm y := by
  apply (tupCoord X).injective
  rw [tupCoord_add]
  simp

theorem betaI_add_left (x x' y : EuclideanSpace ℝ (KapI X)) : betaI X (x + x') y = betaI X x y + betaI X x' y := by
  simp only [betaI, tupCoord_symm_add, BR_add_leftP]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x') ((tupCoord X).symm y)) w =
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x') ((tupCoord X).symm y) w from rfl,
    map_add, Complex.add_re]

theorem betaI_add_right (x y y' : EuclideanSpace ℝ (KapI X)) : betaI X x (y + y') = betaI X x y + betaI X x y' := by
  simp only [betaI, tupCoord_symm_add, BR_add_rightP]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y')) w =
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y') w from rfl,
    map_add, Complex.add_re]

theorem continuous_betaI_left (y : EuclideanSpace ℝ (KapI X)) : Continuous fun x => betaI X x y :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp
      ((continuous_apply w).comp ((continuous_BR_leftP X _).comp (tupCoord X).symm.continuous)))

theorem continuous_betaI_right (x : EuclideanSpace ℝ (KapI X)) : Continuous fun y => betaI X x y :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp
      ((continuous_apply w).comp ((continuous_BR_rightP X _).comp (tupCoord X).symm.continuous)))

theorem betaI_smul_left (r : ℝ) (x y : EuclideanSpace ℝ (KapI X)) : betaI X (r • x) y = r * betaI X x y :=
  map_real_smul (AddMonoidHom.mk' (fun x => betaI X x y) fun a b => betaI_add_left X a b y)
    (continuous_betaI_left X y) r x

theorem betaI_smul_right (r : ℝ) (x y : EuclideanSpace ℝ (KapI X)) : betaI X x (r • y) = r * betaI X x y :=
  map_real_smul (AddMonoidHom.mk' (fun y => betaI X x y) fun a b => betaI_add_right X x a b)
    (continuous_betaI_right X x) r y

def betaL : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (betaI X) (betaI_add_left X) (fun r x y => betaI_smul_left X r x y) (betaI_add_right X)
    (fun r x y => betaI_smul_right X r x y)

open Classical in
theorem betaI_expand (x y : EuclideanSpace ℝ (KapI X)) : betaI X x y = ∑ i, ∑ j, x i * matI X i j * y j := by
  have h : betaI X x y = betaL X x y := rfl
  rw [h]
  conv_lhs => rw [← (EuclideanSpace.basisFun (KapI X) ℝ).sum_repr x, ← (EuclideanSpace.basisFun (KapI X) ℝ).sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [betaL, LinearMap.mk₂_apply, matI]
  ring

end Beta

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpTop
section
namespace PI.AprimeInfW

theorem expProdU_of_G (h : CayDensG) : ExpProdU := expProdU_of_cayProdU (cayProdU_of_G h)

theorem expProdU_of_hua (h1 : CayDensEx) (h2 : CayValId) : ExpProdU := expProdU_of_G (cayDensG_of h1 h2)

end PI.AprimeInfW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibOrbP
section
noncomputable section

namespace PI.AprimeInfW

theorem fibOrbAt_of (hU : UnitsOpenTens) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) : FibOrbAt := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hCh
  obtain ⟨Ω₁, hΩ₁, hn, hu⟩ := nearFacts_of hU X u' ψ hT μinf νinf fibInf hP Ω a hCh
  exact ⟨Ω₁, hΩ₁, hn, fun T hT1 => fib_near rmulFacts_holds hF hC X u' ψ hT μinf νinf fibInf hP T (a T)
    (hu T hT1).1 (hCh.2.2.2 T (hΩ₁ hT1)) (hu T hT1).2⟩

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FixIffSpan
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S
open scoped TensorProduct Matrix

def wV {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F)
    (b : Fin (D.R.rS + 1 + D.R.rS)) : Fin X.B.I.n → ℂ :=
  (X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (tupH (frameOf X u') b i)

def StabInfV : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (x : X.B.I.Ginf), X.toInf hb x ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') ↔
      ∀ v b, uMat (x v) *ᵥ wV X u' v b = wV X u' v b

def WittBlock : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : NumberField.InfinitePlace X.B.I.F,
    ∃ (S : Finset (Fin X.B.I.n)) (c : Formalism.REAL.UJ (X.B.I.ε v)),
      (S.card = D.R.k ∧ ∀ i ∈ S, X.B.I.ε v i = true) ∧
      Submodule.span ℂ (Set.range fun b => uMat c⁻¹ *ᵥ wV X u' v b) =
        Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin X.B.I.n → ℂ)) '' (↑S)ᶜ)

theorem fix_iff_span {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type} (u : ι → Fin n → ℂ) (S : Finset (Fin n))
    (hspan : Submodule.span ℂ (Set.range u) =
      Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ)) :
    (∀ b, A *ᵥ u b = u b) ↔ ∀ i ∉ S, ∀ j, A j i = if j = i then 1 else 0 := by
  classical
  have hker : ∀ x, A *ᵥ x = x ↔ x ∈ LinearMap.ker (Matrix.toLin' (A - 1)) := by
    intro x
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have e1 : (∀ b, A *ᵥ u b = u b) ↔ Submodule.span ℂ (Set.range u) ≤ LinearMap.ker (Matrix.toLin' (A - 1)) := by
    rw [Submodule.span_le]
    constructor
    · rintro h _ ⟨b, rfl⟩; exact (hker _).1 (h b)
    · intro h b; exact (hker _).2 (h ⟨b, rfl⟩)
  rw [e1, hspan, Submodule.span_le]
  constructor
  · intro h i hi j
    have h1 := (hker _).2 (h ⟨i, hi, rfl⟩)
    rw [Matrix.mulVec_single_one] at h1
    have := congrFun h1 j
    simp only [Matrix.col_apply, Pi.single_apply] at this
    exact this
  · rintro h _ ⟨i, hi, rfl⟩
    refine (hker _).1 ?_
    rw [Matrix.mulVec_single_one]
    funext j
    simp only [Matrix.col_apply, Pi.single_apply]
    exact h i hi j

theorem stdConjEx_of (h1 : StabInfV) (h2 : WittBlock) : StdConjEx := by
  intro D X u' ψ hT μinf νinf fibInf hP hb
  have h2' := h2 X u' ψ hT μinf νinf fibInf hP
  choose S c hS hspan using h2'
  refine ⟨c, S, fun v => hS v, fun g => ?_⟩
  rw [h1 X u' hb (c * g * c⁻¹)]
  refine forall_congr' fun v => ?_
  refine Iff.trans ?_ (fix_iff_span (uMat (g v)) (fun b => uMat (c v)⁻¹ *ᵥ wV X u' v b) (S v) (hspan v))
  refine forall_congr' fun b => ?_
  have hm : uMat ((c * g * c⁻¹) v) = uMat (c v) * uMat (g v) * uMat (c v)⁻¹ := by
    simp [uMat]
  have hci : uMat (c v)⁻¹ * uMat (c v) = 1 := by simp [uMat]
  have hci' : uMat (c v) * uMat (c v)⁻¹ = 1 := by simp [uMat]
  rw [hm]
  constructor
  · intro h
    have h' := congrArg (fun y => uMat (c v)⁻¹ *ᵥ y) h
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hci, Matrix.one_mul] at h'
    rw [Matrix.mulVec_mulVec]
    exact h'
  · intro h
    calc (uMat (c v) * uMat (g v) * uMat (c v)⁻¹) *ᵥ wV X u' v b
        = uMat (c v) *ᵥ (uMat (g v) *ᵥ (uMat (c v)⁻¹ *ᵥ wV X u' v b)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = uMat (c v) *ᵥ (uMat (c v)⁻¹ *ᵥ wV X u' v b) := by rw [h]
      _ = wV X u' v b := by rw [Matrix.mulVec_mulVec, hci', Matrix.one_mulVec]

end PI.AprimeInfW
end
end

