module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSymBetaA
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymBetaA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem deriv_smul_const_any {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : ℝ → ℂ) (T : E) :
    deriv (fun t => h t • T) 0 = deriv h 0 • T := by
  by_cases hT : T = 0
  · subst hT
    simp
  by_cases hd : DifferentiableAt ℝ h 0
  · exact deriv_smul_const hd T
  · have hnd : ¬ DifferentiableAt ℝ (fun t => h t • T) 0 := by
      intro hd'
      apply hd
      obtain ⟨φ, -, hφ⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.mpr hT)
      have hφT : φ T ≠ 0 := by
        rw [hφ]
        exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hT)
      have he : h = fun t => (φ T)⁻¹ * φ (h t • T) := by
        funext t
        rw [map_smul, smul_eq_mul]
        field_simp
      rw [he]
      exact DifferentiableAt.const_mul ((φ.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd') _
    rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd, zero_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem LdV_smul (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    LdV X (fun g => φ g • T) = fun g => LdV X φ g • T := by
  funext g
  exact deriv_smul_const_any _ T

theorem RdV_smul (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    RdV X (fun g => φ g • T) = fun g => RdV X φ g • T := by
  funext g
  exact deriv_smul_const_any _ T

theorem Rw_smul (v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    Rw v (fun g => φ g • T) = fun g => Rw v φ g • T := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show RdV X (Rw v (fun g => φ g • T)) = fun g => RdV X (Rw v φ) g • T
    rw [ih]
    exact RdV_smul X (Rw v φ) T

theorem dLR_smul (u v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    dLR u v (fun g => φ g • T) = fun g => dLR u v φ g • T := by
  induction u with
  | nil => exact Rw_smul v φ T
  | cons X u ih =>
    show LdV X (dLR u v (fun g => φ g • T)) = fun g => LdV X (dLR u v φ) g • T
    rw [ih]
    exact LdV_smul X (dLR u v φ) T

theorem ccle_scalF {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {A : ℝ} {m : ℕ}
    {f : Mat k r → ℂ} {c : ℝ} (hf : CCle A m f c) : CCle A m (scalF Wp f) c := by
  obtain ⟨hck, hb⟩ := hf
  refine ⟨?_, fun u v hu hv hl g hg => ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hck g₀ hg₀
    refine ⟨U, fun g => f' g • ContinuousLinearMap.id ℂ Wp, hU, hgU, hcd.smul contDiffOn_const,
      fun g hgU' hgG => ?_⟩
    simp only [scalF, heq g hgU' hgG]
  · have h1 := hb u v hu hv hl g hg
    have hsc : dLR u v (scalF Wp f) g = dLR u v f g • ContinuousLinearMap.id ℂ Wp :=
      congrFun (dLR_smul u v f (ContinuousLinearMap.id ℂ Wp)) g
    rw [hsc, norm_smul]
    have hid : ‖ContinuousLinearMap.id ℂ Wp‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hg0 : 0 ≤ gN g ^ A := Real.rpow_nonneg (Real.sqrt_nonneg _) A
    calc gN g ^ A * (‖dLR u v f g‖ * ‖ContinuousLinearMap.id ℂ Wp‖) ≤ gN g ^ A * ‖dLR u v f g‖ := by
          apply mul_le_mul_of_nonneg_left _ hg0
          exact mul_le_of_le_one_right (norm_nonneg _) hid
      _ ≤ c := h1

theorem inCC_scalF {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {A : ℝ} {m : ℕ}
    {f : Mat k r → ℂ} (hf : InCC A m f) : InCC A m (scalF Wp f) := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, ccle_scalF hc⟩

theorem inCC_five_four' {A : ℝ} {f : Mat k r → E} (h : InCC A 5 f) : InCC A 4 f := by
  obtain ⟨c, hck, hb⟩ := h
  refine ⟨c, ?_, fun u v hu hv hl g hg => hb u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hck g₀ hg₀
  exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (by norm_num))), heq⟩

theorem continuousOn_of_ckOn {m : ℕ∞} {f : Mat k r → E} (h : CkOn m (GV k r) f) :
    ContinuousOn f (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := h g₀ hg₀
  have hc : ContinuousAt f' g₀ := hcd.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := GV k r)).congr_of_eventuallyEq ?_ (heq g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin (GV k r) (hU.mem_nhds hgU)] with g hg
  exact heq g hg.2 hg.1

theorem integrable_of_inCC (hInt : GNIntSharp) (hLow : GNLower) (hCl : ClosedG) {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) {f : Mat k r → ℂ} (hf : InCC A 5 f) :
    Integrable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
  obtain ⟨c, hCk, hbd⟩ := hf
  have hb0 : ∀ g ∈ GV k r, ‖f g‖ ≤ c * gN g ^ (-A) := by
    intro g hg
    have h1 := hbd [] [] (by simp) (by simp) (by simp) g hg
    have hgN : 0 < gN g := lt_of_lt_of_le one_pos (hLow k r g hg)
    have hpow : 0 < gN g ^ A := Real.rpow_pos_of_pos hgN A
    rw [Real.rpow_neg hgN.le, ← div_eq_mul_inv, le_div_iff₀ hpow]
    have h2 : gN g ^ A * ‖f g‖ ≤ c := h1
    linarith [mul_comm (gN g ^ A) ‖f g‖]
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := ae_iff.mpr D.haarG.conc
  have hGm : MeasurableSet {g : Mt k r | Matrix.of g ∈ GV k r} :=
    (show IsClosed {g : Mt k r | Matrix.of g ∈ GV k r} from (hCl k r).closed).measurableSet
  have hgNc : Continuous fun g : Mt k r => gN (Matrix.of g) := by
    unfold gN
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
  have hint : Integrable (fun g : Mt k r => gN (Matrix.of g) ^ (-A)) D.μG := by
    refine ⟨(hgNc.measurable.pow_const (-A)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => by
      show (0 : ℝ) ≤ gN (Matrix.of g) ^ (-A)
      unfold gN
      exact Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
    exact hInt k r D.μG A D.haarG hA
  have hcont : ContinuousOn (fun g : Mt k r => f (Matrix.of g)) {g : Mt k r | Matrix.of g ∈ GV k r} :=
    continuousOn_of_ckOn hCk
  have hmeas : AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
    have := hcont.aestronglyMeasurable (μ := D.μG) hGm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {g : Mt k r | Matrix.of g ∈ GV k r}) hae] at this
  refine (hint.const_mul c).mono' hmeas (hae.mono fun g hg => ?_)
  exact hb0 _ hg

theorem volume_normSq_eq (c : ℝ) :
    volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = c} = 0 := by
  have hsub : {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = c} ⊆
      Set.univ ×ˢ Metric.sphere (0 : ℂ) (Real.sqrt c) := by
    rintro ⟨a, z⟩ hz
    simp only [Set.mem_setOf_eq] at hz
    refine ⟨Set.mem_univ _, ?_⟩
    rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.addHaar_sphere, mul_zero]

theorem bcWeight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (by linarith) _)
  · exact le_rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymBetaA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StDiagExists : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)), 1 ≤ k → inWb k r z → 0 < Tz k r z →
    IsCRepOn (UWset k r z) π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → ContinuousOn π (UWset k r z) →
    Formalism.MainNotions.S.IsIrredOn (UWset k r z) π →
    ∃ D : RealPlaceData k r Wp Wp, D.z = z ∧ D.π = π ∧ IsDiag D

def StSchurG : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∃ d : ℝ, IsFdegG D X d

def StPairs : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ d : ℝ, IsFdegG D X d → ∀ a₁ a₂ : ℝ, ∀ u ∈ VflA X a₁, ∀ v ∈ VflA X a₂,
      ∃ C : ℝ, ∀ x ∈ GV k r, ‖mc X u v x‖ ≤ C * gN x ^ (-(min a₁ a₂ - AG k r - 1))

def StBeConv : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ (b : ℝ), AS k r + 1 ≤ b → ∀ u v : X.Hs,
      (∃ C : ℝ, ∀ x ∈ GV k r, ‖mc X u v x‖ ≤ C * gN x ^ (-b)) →
      Integrable (beInt D X u v) (D.μW.prod D.μN)

def StBeEquiv : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ u u' : X.Hs, Integrable (beInt D X u u') (D.μW.prod D.μN) →
      ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r,
        beOp D X (X.σ (m * h) u) u' = psiD D m • (D.π h).comp (beOp D X u u') ∧
        beOp D X u (X.σ (m * h) u') = star (psiD D m) • (beOp D X u u').comp (D.π h⁻¹)

def StRepro : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ d : ℝ, IsFdegG D X d → ∀ u ∈ Vfl X, ∀ v ∈ Vfl X,
      beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG ∧
      beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w) ∂D.μG

def StSmooth : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ φ φ' : Mat k r → ℂ, IsTestG φ → IsTestG φ' → ∀ m : ℕ,
      InCC (X.a - AG k r - 1) m (mc X (sigInt D X φ X.w) (sigInt D X φ' X.w))

def StFrame : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → 0 < Tz k r z →
    ∃ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r z γ

def StInvGroup : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ g ∈ GV k r, gbar k r γ g ∈ GV k r) ∧ (∀ m ∈ Nset k r, gbar k r γ m ∈ Nset k r) ∧
    (∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z) ∧ (∀ u ∈ UUset k r D.z γ, gbar k r γ u ∈ UUset k r D.z γ) ∧
    (∀ g ∈ GV k r, ∀ g' ∈ GV k r, th k r γ (g * g') = th k r γ g' * th k r γ g) ∧
    (∀ g ∈ GV k r, th k r γ (th k r γ g) = g) ∧
    D.μG.map (fun x : Mt k r => fun i j => th k r γ (Matrix.of x) i j) = D.μG ∧
    D.μN.map (fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) = D.μN ∧
    D.μW.map (fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) = D.μW

def StInvChar : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ m ∈ Nset k r, lam k r D.z (gbar k r γ m) = -lam k r D.z m ∧ psiD D (th k r γ m) = psiD D m

def StInvCC : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∃ C : ℝ, ∀ g ∈ GV k r, gN (th k r γ g) ≤ C * gN g) ∧
    ∀ (A : ℝ) (m : ℕ) (F : Mat k r → ℂ), InCC A m F → InCC A m (F ∘ th k r γ)

def StReps : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ (c : Fin r → ℂ) (d : ℂ), (∀ a, c a ≠ 0) → 1 < ‖d‖ →
      (γ * mud k d * γ⁻¹)ᴴ * Hb k * (γ * mud k d * γ⁻¹) = Hb k ∧
      herm (Hpk k r) (embWb k r (γ * mud k d * γ⁻¹) *ᵥ D.z) D.z = -((Tz k r D.z : ℝ) : ℂ) * d ∧
      g0 k r γ c d ∈ GV k r ∧ th k r γ (g0 k r γ c d) = g0 k r γ c d ∧
      ∃ h ∈ UWset k r D.z, ∃ h' ∈ UWset k r D.z, gq D (c, -((Tz k r D.z : ℝ) : ℂ) * d) = h⁻¹ * g0 k r γ c d * h'

def StTransM : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ y ∈ UWset k r D.z, ∃ u₀ ∈ UUset k r D.z γ, th k r γ y = u₀ * y * u₀⁻¹

def StSym : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ (f : Mat k r → ℂ) (q : (Fin r → ℂ) × ℂ), Integrable (fun g : Mt k r => f (Matrix.of g)) D.μG →
      q ∈ Qset D → Tz k r D.z * Tz k r D.z < Complex.normSq q.2 → Ef D (scalF Wp f) q ≠ ∞ →
      JF D (scalF Wp (f ∘ th k r γ)) (gq D q) = JF D (scalF Wp f) (gq D q)

def StSymBeta : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ A : ℝ, AB k r ≤ A → JCont D A → ∀ (f : Mat k r → ℂ) (F' : Mat k r → (Wp →L[ℂ] Wp)),
      InCC A 5 f → InCC A 5 F' → beta D (scalF Wp (f ∘ th k r γ)) F' = beta D (scalF Wp f) F'

def StBetaInf : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ),
    XiExists → AB k r ≤ A → ∀ F F' : Mat k r → (Wq →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' →
      Integrable (Ph D F F') D.μSS → betaInf D F F' = ∫ p, xiTau D (1, 1) p * Ph D F F' p ∂D.μSS

def StDichoG : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0) ∨
    ∃ C : X.Hs ≃ₗᵢ⋆[ℂ] X.Hs, (∀ g ∈ GV k r, ∀ x y : X.Hs, ⟪y, X.σ (th k r γ g) x⟫_ℂ = ⟪C x, X.σ g (C y)⟫_ℂ) ∧
      ∀ h ∈ GV k r, ∀ v : X.Hs, C (X.σ h v) = X.σ (th k r γ h)⁻¹ (C v)

def StDichoW : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : Wp,
      ∫ h : Mt k r, ⟪y, D.π (th k r γ (Matrix.of h)) x⟫_ℂ * star ⟪y', D.π (Matrix.of h) x'⟫_ℂ ∂D.μW = 0) ∨
    ∃ C : Wp ≃ₗᵢ⋆[ℂ] Wp, (∀ h ∈ UWset k r D.z, ∀ x y : Wp, ⟪y, D.π (th k r γ h) x⟫_ℂ = ⟪C x, D.π h (C y)⟫_ℂ) ∧
      ∀ h ∈ UWset k r D.z, ∀ v : Wp, C (D.π h v) = D.π (th k r γ h)⁻¹ (C v)

def StMixed : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    aM k r ≤ X.a → ∀ C : X.Hs ≃ₗᵢ⋆[ℂ] X.Hs,
      (∀ g ∈ GV k r, ∀ x y : X.Hs, ⟪y, X.σ (th k r γ g) x⟫_ℂ = ⟪C x, X.σ g (C y)⟫_ℂ) →
      ∀ u ∈ Vfl X, C u ∈ VflA X (X.a - AG k r - 1)

def ThmM : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∃ l : X.Hs → Wp, IsMultOneMap D X l

def StMFix : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ l : X.Hs → Wp, IsMultOneMap D X l → ∀ d : ℝ, IsFdegG D X d →
      ∀ W' : Mat k r → Wp, AEStronglyMeasurable (fun y : Mt k r => W' (Matrix.of y)) D.μG →
        (∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ x ∈ GV k r, W' (m * h * x) = psiD D m • D.π h (W' x)) →
        (∀ x ∈ GV k r, Integrable (fun y : Mt k r => gN (x⁻¹ * Matrix.of y) ^ (-X.a) * ‖W' (Matrix.of y)‖) D.μG) →
        ∃ c : ℂ, ∀ x ∈ GV k r,
          ∫ y : Mt k r, ((d : ℂ) * star (mc X X.w X.w (Matrix.of y))) • W' (x * Matrix.of y) ∂D.μG = c • l (X.σ x X.w)

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

