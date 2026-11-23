module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.T2SpaceOfNonarchimedeanLocalField
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.PsiTower
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLieEUnitaryGroupIffOfInvolutive
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.TubeLie


open scoped Matrix.Norms.Operator in
theorem skew_of_mem_lieOf {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : X ∈ lieOf (UH H)) :
    Xᴴ * H + H * X = 0 := by
  have hc : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ) := by
    intro t
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  have key : ∀ t : ℝ, H * NormedSpace.exp (t • X) = NormedSpace.exp (t • -Xᴴ) * H := by
    intro t
    have ht : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := h t
    rw [hc t] at ht
    have e1 : NormedSpace.exp (-((t : ℂ) • Xᴴ)) * NormedSpace.exp ((t : ℂ) • Xᴴ) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Xᴴ)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    have e2 : H * NormedSpace.exp ((t : ℂ) • X) = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H := by
      calc H * NormedSpace.exp ((t : ℂ) • X)
          = (NormedSpace.exp (-((t : ℂ) • Xᴴ)) * NormedSpace.exp ((t : ℂ) • Xᴴ)) * H *
              NormedSpace.exp ((t : ℂ) • X) := by rw [e1, one_mul]
        _ = NormedSpace.exp (-((t : ℂ) • Xᴴ)) *
              (NormedSpace.exp ((t : ℂ) • Xᴴ) * H * NormedSpace.exp ((t : ℂ) • X)) := by
            simp only [mul_assoc]
        _ = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H := by rw [ht]
    rw [← smul_neg, Complex.coe_smul, Complex.coe_smul] at e2
    exact e2
  have d1 : HasDerivAt (fun t : ℝ => H * NormedSpace.exp (t • X))
      (H * (NormedSpace.exp ((0 : ℝ) • X) * X)) 0 :=
    (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul H
  have d2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H)
      (NormedSpace.exp ((0 : ℝ) • -Xᴴ) * -Xᴴ * H) 0 :=
    (hasDerivAt_exp_smul_const (-Xᴴ) (0 : ℝ)).mul_const H
  rw [show (fun t : ℝ => H * NormedSpace.exp (t • X)) =
      (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H) from funext key] at d1
  have hu := d1.unique d2
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hu
  rw [hu, neg_mul, add_neg_cancel]

private theorem conjTranspose_exp_mul_mul_exp_eq_of_skew {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : Xᴴ * H + H * X = 0)
    (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := by
  have hx : H * X = -(Xᴴ * H) := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h
  have hs : SemiconjBy H ((t : ℂ) • X) (-((t : ℂ) • Xᴴ)) := by
    unfold SemiconjBy
    rw [mul_smul_comm, hx, smul_neg, neg_mul, smul_mul_assoc]
  have hc : (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ) := by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℚ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℂ _
  have := hs.exp_neg_mul_mul_exp_eq_self
  rw [neg_neg] at this
  rw [hc]
  exact this

theorem mem_lieOf_of_skew {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : Xᴴ * H + H * X = 0) :
    X ∈ lieOf (UH H) := by
  intro t
  exact conjTranspose_exp_mul_mul_exp_eq_of_skew H X h t

private theorem unrealify_equiv_symm_realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

private theorem equiv_symm_realifyFun_unrealify_eq {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    (WithLp.equiv 2 _).symm (realifyFun (unrealify x)) = x := by
  ext ⟨i, j, b⟩
  cases b <;> simp [unrealify, realifyFun]

private theorem unrealify_map_add {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

private theorem unrealify_map_smul {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

private theorem unrealify_map_zero {m : ℕ} :
    unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem mem_lieE_UH (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0 := by
  have hL : lieOf (UH H) = {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * H + H * X = 0} := by
    ext X
    exact ⟨fun h => skew_of_mem_lieOf H X h, fun h => mem_lieOf_of_skew H X h⟩
  constructor
  · intro hx
    unfold lieE at hx
    rw [hL] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      rw [unrealify_equiv_symm_realifyFun]
      exact hX
    | zero => simp [unrealify_map_zero]
    | add y z _ _ hy hz =>
      rw [unrealify_map_add, Matrix.conjTranspose_add, add_mul, mul_add]
      calc (unrealify y)ᴴ * H + (unrealify z)ᴴ * H + (H * unrealify y + H * unrealify z)
          = ((unrealify y)ᴴ * H + H * unrealify y) + ((unrealify z)ᴴ * H + H * unrealify z) := by
            abel
        _ = 0 := by rw [hy, hz, add_zero]
    | smul c y _ hy =>
      rw [unrealify_map_smul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        smul_mul_assoc, mul_smul_comm, ← smul_add, hy, smul_zero]
  · intro hx
    unfold lieE
    apply Submodule.subset_span
    refine ⟨unrealify x, ?_, equiv_symm_realifyFun_unrealify_eq x⟩
    rw [hL]
    exact hx

theorem mem_lieE_UH_of_sq : ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)),
    H * H = 1 → (x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0) := by
  intro m H x _
  exact mem_lieE_UH m H x

end GlobalTheory.TubeLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RotationInvariantMeasureUnitCircleArc
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal

noncomputable section

namespace GlobalTheory.CircleArc

local instance factTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def par (x : AddCircle (2 * Real.pi)) : ℂ := (AddCircle.toCircle x : Circle)

theorem continuous_par : Continuous par :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

theorem par_injective : Function.Injective par := fun _ _ h =>
  AddCircle.injective_toCircle Real.two_pi_pos.ne' (Circle.ext h)

theorem par_coe (s : ℝ) : par (s : AddCircle (2 * Real.pi)) = Complex.exp (s * Complex.I) := by
  rw [par, AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul, Circle.coe_exp]

theorem par_add (x y) : par (x + y) = par x * par y := by
  rw [par, AddCircle.toCircle_add, Circle.coe_mul]; rfl

theorem norm_par (x) : ‖par x‖ = 1 := Circle.norm_coe _

theorem range_par : Set.range par = {z | ‖z‖ = 1} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact norm_par x
  · intro hz
    refine ⟨(z.arg : ℝ), ?_⟩
    rw [par_coe]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [show ‖z‖ = 1 from hz] at this
    simpa using this

theorem image_ball (r : ℝ) :
    par '' Metric.ball 0 r = (fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 r := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff] at hx
    obtain ⟨s, rfl, hs⟩ := hx
    exact ⟨s, mem_ball_zero_iff.2 hs, (par_coe s).symm⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, ?_, par_coe s⟩
    rw [mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff]
    exact ⟨s, rfl, mem_ball_zero_iff.1 hs⟩

theorem measure_arc : ∀ (τ : Measure ℂ) (ρ : ℝ), τ Set.univ < ⊤ → τ {z | ‖z‖ ≠ 1} = 0 →
    (∀ u : ℂ, ‖u‖ = 1 → τ.map (fun z => u * z) = τ) → 0 < ρ → ρ ≤ Real.pi →
    τ ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) =
      τ Set.univ * ENNReal.ofReal (ρ / Real.pi) := by
  intro τ ρ hfin hsupp hinv hρ hρπ
  haveI : IsFiniteMeasure τ := ⟨hfin⟩
  have hm : MeasurableEmbedding par :=
    (continuous_par.isClosedEmbedding par_injective).measurableEmbedding
  set ν : Measure (AddCircle (2 * Real.pi)) := τ.comap par with hν
  have hνa : ∀ S, ν S = τ (par '' S) := fun S => hm.comap_apply τ S
  haveI : IsFiniteMeasure ν := ⟨by rw [hνa]; exact measure_lt_top _ _⟩
  haveI : ν.IsAddLeftInvariant := by
    constructor
    intro a
    ext S hS
    rw [Measure.map_apply (measurable_const_add a) hS, hνa, hνa]
    conv_rhs => rw [← hinv (par a) (norm_par a)]
    rw [Measure.map_apply (measurable_const_mul _) (hm.measurableSet_image.2 hS)]
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨a + x, hx, par_add a x⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨-a + y, by simpa using hy, ?_⟩
      have h0 : par a ≠ 0 := by
        intro h0
        have := norm_par a
        rw [h0] at this
        simp at this
      apply mul_left_cancel₀ h0
      rw [← par_add, add_neg_cancel_left]
      exact h
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, ν = t • (volume : Measure (AddCircle (2 * Real.pi))) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have hu : τ Set.univ = t * ENNReal.ofReal (2 * Real.pi) := by
    have h1 := hνa Set.univ
    rw [ht, Measure.smul_apply, AddCircle.measure_univ, Set.image_univ, range_par,
      ENNReal.smul_def, smul_eq_mul] at h1
    rw [h1]
    apply measure_congr
    exact (ae_eq_univ.2 hsupp).symm
  rw [← image_ball, ← hνa, hu, ht, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ← measure_congr AddCircle.closedBall_ae_eq_ball, AddCircle.volume_closedBall,
    min_eq_right (by linarith), mul_assoc, ← ENNReal.ofReal_mul Real.two_pi_pos.le]
  congr 2
  have := Real.pi_pos
  field_simp

end GlobalTheory.CircleArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothFunctionalOrbitSmoothVector
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInfOrb

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_rdWord_functional : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (σ : Mat k r → (H →L[ℂ] H))
    (Λ : H →L[ℂ] B), IsURepOn (GG k r) σ → ∀ v : H, IsSmoothVec (k := k) (r := r) σ v →
    SmoothOnH (Hpk k r) (fun g : Mat k r => Λ (σ g v)) ∧
    ∀ ws : List (Mat k r), (∀ X ∈ ws, InLieHpk k r X) → ∀ x ∈ GG k r,
      rdWord ws (fun g : Mat k r => Λ (σ g v)) x = Λ (σ x (dsigW σ ws v)) := by
  intro k r H _ _ _ B _ _ σ Λ hσ v hv
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hg, hF, hE⟩ := hv g₀ hg₀
    refine ⟨U, fun g => Λ (F g), hU, hg, (Λ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hgH
    exact congrArg Λ (hE g hgU hgH)
  · intro ws
    induction ws with
    | nil => intro _ x _; rfl
    | cons X w ih =>
      intro hws x hx
      have hX : InLieHpk k r X := hws X List.mem_cons_self
      have hw : ∀ Y ∈ w, InLieHpk k r Y := fun Y hY => hws Y (List.mem_cons_of_mem _ hY)
      have hd := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv w hw hX
      have h2 := ((Λ.comp (σ x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      have e : (fun t : ℝ => rdWord w (fun g : Mat k r => Λ (σ g v)) (x * NormedSpace.exp ((t : ℂ) • X))) =
          (⇑((Λ.comp (σ x)).restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (dsigW σ w v)) := by
        funext t
        have ht := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX t
        rw [ih hw _ (GlobalTheory.SgInfDD.gg_mul hx ht)]
        simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply]
        rw [hσ.1.2 x hx _ ht]
        rfl
      show deriv _ 0 = _
      rw [e, h2.deriv]
      rfl

end GlobalTheory.SgInfOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDifferentEqLocalGenerator
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

namespace GlobalTheory.LocDiffGen

variable {D : D7}

theorem iF_int (p : PlF D) (a : 𝓞 D.host.F) :
    (D.s.atP p).ιF (a : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
  have h1 : (D.s.atP p).ιF (a : D.host.F) ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [(D.s.atP p).val, map_one]
    exact p.valuation_le_one (K := D.host.F) a
  rw [map_one, Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp), map_one] at h1
  exact (Valuation.mem_integer_iff _ _).2 h1

theorem dual_sub (Z : LocDat D) (p : PlF D) (z : (D.s.atP p).Fp)
    (hz : haveI := (D.s.atP p).ellPrime; ∀ c ∈ 𝒪[(D.s.atP p).Fp],
      ‖Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp (c * z)‖ ≤ 1) :
    Z.δ p * z ∈ 𝒪[(D.s.atP p).Fp] := by
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  obtain ⟨-, hδ, -, hO, hpsi, -⟩ := Z.agree p
  have hx : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * z) ∈ (Z.M p).L.O := by
    rw [← (Z.M p).L.additive_character_dual_ring]
    intro y hy
    rw [hO] at hy
    rw [hpsi]
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * z) * y *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ = y * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z := by
      have e2 : Z.δ p * z * (Z.δ p)⁻¹ = z := by field_simp
      rw [← e2, map_mul (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) (Z.δ p * z) (Z.δ p)⁻¹, e2]
      ring
    rw [e]
    refine (PI.LocDualGen.Top.psi_tower PI.LocDualGen.Psi.addCharKernel (D.s.atP p) _).2 ?_
    rw [map_neg, PI.LocDualGen.Top.tr_smul, map_neg, norm_neg]
    exact hz _ (PI.UnitaryGroupMassFormula.CntFormula.DeltaC.trace_mem (D.s.atP p) hy)
  rw [hO, (D.s.atP p).O_def] at hx
  have hi : IsIntegral 𝒪[(D.s.atP p).Fp] (Z.δ p * z) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective).1 hx
  exact PI.UnitaryGroupMassFormula.CntFormula.DeltaC.mem_of_isIntegral_fp (D.s.atP p) hi

theorem diff_sub (Z : LocDat D) (p : PlF D) (x : 𝓞 D.host.F) (hx : x ∈ differentIdeal ℤ (𝓞 D.host.F)) :
    (Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
  obtain ⟨t, ht, hne, -, hinv⟩ := PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
    (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
    PI.CntNotIntW.small_powers_bound D Z.δ Z.M Z.agree p
  have hB := PI.CntNotIntW.dual_mul_different_integral D t ht x hx
  let w : 𝓞 D.host.F := ⟨_, (mem_integralClosure_iff ℤ D.host.F).2 hB⟩
  have hw : (D.s.atP p).ιF (w : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := iF_int p w
  have hw' : (D.s.atP p).ιF (w : D.host.F) = (D.s.atP p).ιF t * (D.s.atP p).ιF (x : D.host.F) := by
    rw [← map_mul]; rfl
  have ht0 : (D.s.atP p).ιF t ≠ 0 := right_ne_zero_of_mul hne
  have hδ0 : Z.δ p ≠ 0 := left_ne_zero_of_mul hne
  have e : (Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F) =
      (D.s.atP p).ιF (w : D.host.F) * (Z.δ p * (D.s.atP p).ιF t)⁻¹ := by
    rw [hw']; field_simp
  rw [e]
  exact mul_mem hw hinv

theorem dual_glob (Z : LocDat D) (p : PlF D) (t : D.host.F)
    (ht : ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) :
    Z.δ p * (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp] := by
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  haveI := (D.s.atP p).lf
  exact dual_sub Z p _ (fun c hc => trace_dual_local D.host.F p (D.s.atP p).Fp (D.s.atP p).qlCont
    (D.s.atP p).qlFin (D.s.atP p).ιF (D.s.atP p).dense (D.s.atP p).val t ht c hc)

theorem span_different_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D), Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) = Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)} := by
  intro D Z p
  obtain ⟨-, hδ, -, hO, -, -⟩ := Z.agree p
  have hmem : ∀ c ∈ 𝒪[(D.s.atP p).Fp], algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (Z.M p).L.O := by
    intro c hc; rw [hO]; exact PI.CntNotIntW.algMap_mem_O D p c hc
  have hf : ∀ x : 𝓞 D.host.F, (D.s.atP p).ιE (algebraMap D.host.F D.host.E x) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F)) :=
    fun x => (D.s.atP p).compat _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨_, hmem _ (diff_sub Z p x hx)⟩, ?_⟩
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F)) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) = _
    rw [← map_mul]
    show _ = (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F))
    rw [hf]
    congr 1
    field_simp
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set N := Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) with hN
    have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0 := one_ne_zero
    have hIJ : ((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) = 1 := by
      rw [coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := D.host.F) (B := 𝓞 D.host.F)]
      exact inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10)
    have key : ∀ y : D.host.F, y ∈ (((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)) →
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF y) ∈ N := by
      intro y hy
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro m hm n hn
        obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
        have hn' := (FractionalIdeal.mem_dual h10).1 hn
        have ht : ∀ a : 𝓞 D.host.F, ∃ k : ℤ, Algebra.trace ℚ D.host.F (n * a) = k := by
          intro a
          obtain ⟨k, hk⟩ := hn' _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
          exact ⟨k, by rw [← Algebra.traceForm_apply, ← hk]; simp⟩
        have hc := dual_glob Z p n ht
        have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F x * n)) =
            (⟨_, hmem _ hc⟩ : (Z.M p).L.O) • (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F)) := by
          rw [hf, Subring.smul_def]
          show _ = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF n) * _
          rw [← map_mul, map_mul (D.s.atP p).ιF]
          congr 1
          show _ = _ * (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F x)
          ring
        rw [e]
        exact N.smul_mem _ (Submodule.subset_span ⟨x, hx, rfl⟩)
      · intro a b ha hb
        rw [map_add (f := _), mul_add, map_add (f := _)]
        exact N.add_mem ha hb
    have h1 := key 1 (by rw [hIJ]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
    have e1 : Z.δ p * (D.s.atP p).ιF 1 = Z.δ p := by rw [map_one, mul_one]
    rw [e1] at h1
    exact h1

end GlobalTheory.LocDiffGen
end
end

