module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SmoothVectorHyp
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SmoothVectorHyp

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

structure Hyp (E : Type) [Field E] [NumberField E] (k : ℕ) : Prop where
  cont : Continuous (dmin : GA E k → ℝ)
  pos : ∀ g : GA E k, 0 < dmin g
  rt : ∀ h : GA E k, ∃ B : ℝ, 1 ≤ B ∧ ∀ g, dmin (g * h) ≤ B * dmin g

lemma min_le_of (a b D : ℝ) (hD : 1 ≤ D) (h : a ≤ D * b) : min 1 a ≤ D * min 1 b := by
  rcases le_total 1 b with h1 | h1
  · rw [min_eq_left h1]; exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h1]; exact (min_le_right _ _).trans h

lemma wt_pos (H : Hyp E k) (M : ℕ) (g : GA E k) : 0 < wt M g :=
  pow_pos (lt_min one_pos (H.pos g)) M

lemma wt_le_one (H : Hyp E k) (M : ℕ) (g : GA E k) : wt M g ≤ 1 :=
  pow_le_one₀ (le_min zero_le_one (H.pos g).le) (min_le_left _ _)

lemma wt_cont (H : Hyp E k) (M : ℕ) : Continuous (wt M : GA E k → ℝ) :=
  (continuous_const.min H.cont).pow M

lemma wt_le (H : Hyp E k) (M : ℕ) (g c : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (h : dmin (g * c) ≤ D * dmin g) : wt M (g * c) ≤ D ^ M * wt M g := by
  unfold wt
  rw [← mul_pow]
  exact pow_le_pow_left₀ (le_min zero_le_one (H.pos _).le) (min_le_of _ _ _ hD h) M

def W (H : Hyp E k) (M : ℕ) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M g : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (wt_cont H M)) 1 fun g => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_pos H M g).le]
      exact wt_le_one H M g

lemma ratio_cont (H : Hyp E k) (M : ℕ) (h : GA E k) :
    Continuous fun g : GA E k => ((wt M (g * h) / wt M g : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    (((wt_cont H M).comp (continuous_mul_const h)).div (wt_cont H M) fun g => (wt_pos H M g).ne')

lemma ratio_le (H : Hyp E k) (M : ℕ) (h g : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : dmin (g * h) ≤ D * dmin g) : ‖((wt M (g * h) / wt M g : ℝ) : ℂ)‖ ≤ D ^ M := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (wt_pos H M _).le (wt_pos H M g).le), div_le_iff₀ (wt_pos H M g)]
  exact wt_le H M g h D hD hd

def Q (H : Hyp E k) (M : ℕ) (h : GA E k) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M (g * h) / wt M g : ℝ) : ℂ))
    (ratio_cont H M h) ((H.rt h).choose ^ M) fun g =>
      ratio_le H M h g _ (H.rt h).choose_spec.1 ((H.rt h).choose_spec.2 g)

lemma norm_Q_le (H : Hyp E k) (M : ℕ) (h : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : ∀ g, dmin (g * h) ≤ D * dmin g) : ‖Q H M h‖ ≤ D ^ M :=
  (BoundedContinuousFunction.norm_le (pow_nonneg (zero_le_one.trans hD) M)).mpr fun g =>
    ratio_le H M h g D hD (hd g)

def rho (H : Hyp E k) (M : ℕ) : GA E k →* (XB E k →L[ℂ] XB E k) where
  toFun h := (ContinuousLinearMap.mul ℂ (XB E k) (Q H M h)).comp (Rt E k h)
  map_one' := by
    ext x g
    change ((wt M (g * 1) / wt M g : ℝ) : ℂ) * x (g * 1) = x g
    rw [mul_one, div_self (wt_pos H M g).ne', Complex.ofReal_one, one_mul]
  map_mul' h h' := by
    ext x g
    change ((wt M (g * (h * h')) / wt M g : ℝ) : ℂ) * x (g * (h * h')) =
      ((wt M (g * h) / wt M g : ℝ) : ℂ) * (((wt M (g * h * h') / wt M (g * h) : ℝ) : ℂ) * x (g * h * h'))
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    have := (wt_pos H M (g * h)).ne'
    field_simp

lemma rho_apply (H : Hyp E k) (M : ℕ) (h g : GA E k) (x : XB E k) :
    rho H M h x g = ((wt M (g * h) / wt M g : ℝ) : ℂ) * x (g * h) := rfl

def J (H : Hyp E k) (M : ℕ) : XB E k →L[ℂ] XB E k := ContinuousLinearMap.mul ℂ (XB E k) (W H M)

lemma J_apply (H : Hyp E k) (M : ℕ) (x : XB E k) (g : GA E k) : J H M x g = (wt M g : ℂ) * x g := rfl

lemma inter (H : Hyp E k) (M : ℕ) (h : GA E k) (x : XB E k) : J H M (rho H M h x) = Rt E k h (J H M x) := by
  ext g
  rw [J_apply, rho_apply, Rt_apply, J_apply, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have := (wt_pos H M g).ne'
  field_simp

lemma inj (H : Hyp E k) (M : ℕ) : Function.Injective (J H M) := by
  intro x y hxy
  ext g
  have e := congrArg (fun z : XB E k => z g) hxy
  simp only [J_apply] at e
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (wt_pos H M g).ne') e

variable [_root_.NumberField.IsTotallyComplex E]

lemma smv (H : Hyp E k) (M : ℕ) (x : XB E k) (hx : SmV ((rho H M).comp (infGL E k)) x) :
    SmV (repI E k) (J H M x) := by
  have e : orb (repI E k) (J H M x) = fun A => J H M (orb ((rho H M).comp (infGL E k)) x A) := by
    funext A
    unfold orb
    split_ifs with hA
    · exact (inter H M _ x).symm
    · exact (map_zero (J H M)).symm
  unfold SmV
  rw [e]
  exact hx.continuousLinearMap_comp ((J H M).restrictScalars ℝ)

end SmoothVectorHyp

theorem secondCohomologyBound_of_boundaryBound : H0 → K1 → K2 := by
  intro hH hK E _ _ _ k hk M
  obtain ⟨h1, -, -, -, -, ⟨B, N, -, h6⟩, -⟩ := hH E k
  obtain ⟨kc, kpos, kle, -, kcpt, -⟩ := hK E k hk
  have H : SmoothVectorHyp.Hyp E k := ⟨kc, kpos, fun h => by
    obtain ⟨B, hB, hB'⟩ := kcpt {h} isCompact_singleton
    exact ⟨B, hB, hB' h rfl⟩⟩
  refine ⟨SmoothVectorHyp.rho H M, SmoothVectorHyp.J H M, ⟨fun x g => rfl, SmoothVectorHyp.inter H M, SmoothVectorHyp.inj H M, ?_⟩,
    fun x hx => SmoothVectorHyp.smv H M x hx⟩
  have hne : Nonempty {ξ : Fin k → E // ξ ≠ 0} :=
    ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hk⟩)⟩⟩
  refine ⟨max B 1 ^ M, N * M, pow_nonneg (zero_le_one.trans (le_max_right _ _)) M, fun y x => ?_⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ := ⟨_, rfl⟩
  rw [← hP]
  have hP1 : 1 ≤ P := by
    rw [hP]
    linarith [norm_nonneg (Matrix.of.symm y.val : LieI (InfinitePlace E) k),
      norm_nonneg (Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)]
  have hPinv : 1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖ = P := by
    rw [inv_inv, hP]; ring
  have hD : 1 ≤ max B 1 * P ^ N := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hP1)
  have hDpos : 0 < max B 1 * P ^ N := zero_lt_one.trans_le hD
  have hd : ∀ g, dmin (g * infGL E k y) ≤ max B 1 * P ^ N * dmin g := by
    intro g
    rw [← div_le_iff₀' hDpos]
    show _ ≤ ⨅ ξ : {ξ : Fin k → E // ξ ≠ 0}, ht g ξ.1
    refine le_ciInf fun ξ => ?_
    rw [div_le_iff₀' hDpos]
    calc dmin (g * infGL E k y) ≤ ht (g * infGL E k y) ξ.1 := kle _ _ ξ.2
      _ ≤ B * (1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
          ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖) ^ N *
            ht (g * infGL E k y * infGL E k y⁻¹) ξ.1 := h6 y⁻¹ _ ξ.1 ξ.2
      _ = B * P ^ N * ht g ξ.1 := by
          rw [hPinv, mul_assoc g, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ ≤ max B 1 * P ^ N * ht g ξ.1 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_le_one.trans hP1) _))
            (h1 g ξ.1 ξ.2).le
  change ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖ ≤ _
  calc ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖
        ≤ ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖Rt E k (infGL E k y) x‖ := norm_mul_le _ _
    _ = ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖x‖ := by rw [norm_Rt]
    _ ≤ (max B 1 * P ^ N) ^ M * ‖x‖ :=
        mul_le_mul_of_nonneg_right (SmoothVectorHyp.norm_Q_le H M _ _ hD hd) (norm_nonneg _)
    _ = max B 1 ^ M * P ^ (N * M) * ‖x‖ := by rw [mul_pow, ← pow_mul]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphericalIntegralStep
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SphericalFunctionIntegral

open Formalism.UG GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem le_one (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem mem_Ov (w : Pl E) {x : w.adicCompletion E} (h : x ∈ (ValuativeRel.valuation (w.adicCompletion E)).integer) :
    x ∈ Ov E w :=
  (le_one w x).1 ((Valuation.mem_integer_iff _ _).1 h)

theorem int_KGL (w : Pl E) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : x ∈ KGL w (n := k) := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 hx
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, mem_Ov w (h1 i j)⟩, Matrix.of fun i j => ⟨(x⁻¹ : GL (Fin k) (w.adicCompletion E)).1 i j, mem_Ov w (h2 i j)⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem fix {w : Pl E} {B : Multiset ℂˣ} {φ : XB E k} (h : SatFn w B φ) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : Rt E k (fl k w x) φ = φ := by
  rcases h with rfl | h
  · exact map_zero _
  · exact GlobalTheory.LGrp.mem_fixed.1 h.2.1 x (int_KGL w hx)

variable [_root_.NumberField.IsTotallyComplex E]

theorem step (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k) (g κ : GA E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ)
    (hinf : cInf κ = 1) (hS : ∀ w ∈ S, cLoc w κ = 1)
    (hint : ∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) (T : Finset (Pl E)) :
    ∃ h : GA E k, φ (g * h) = φ g ∧ cInf h = cInf κ ∧ (∀ w, (w ∈ S ∨ w ∈ T) → cLoc w h = cLoc w κ) ∧
      (∀ w, w ∉ S → w ∉ T → cLoc w h = 1) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -⟩ := hG E k
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨1, by rw [mul_one], by rw [map_one, hinf], fun w hw => ?_, fun w _ _ => map_one _⟩
    rcases hw with hw | hw
    · rw [map_one, hS w hw]
    · simp at hw
  | insert w T hwT ih =>
    obtain ⟨h, hf0, hi, hl, ho⟩ := ih
    by_cases hwS : w ∈ S
    · refine ⟨h, hf0, hi, fun v hv => ?_, fun v hv hv' => ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')⟩
      rcases hv with hv | hv
      · exact hl v (Or.inl hv)
      · rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hl v (Or.inl hwS)
        · exact hl v (Or.inr hv)
    · refine ⟨h * fl k w (cLoc w κ), ?_, ?_, fun v hv => ?_, fun v hv hv' => ?_⟩
      · have e := congrArg (fun ψ : XB E k => ψ (g * h)) (hfix w hwS _ (hint w))
        simp only [Rt_apply] at e
        rw [← mul_assoc, e, hf0]
      · rw [map_mul, h3, mul_one, hi]
      · rw [map_mul]
        by_cases hvw : v = w
        · subst hvw
          rw [h4, ho v hwS hwT, one_mul]
        · rw [h5 _ _ _ hvw, mul_one]
          rcases hv with hv | hv
          · exact hl v (Or.inl hv)
          · exact hl v (Or.inr ((Finset.mem_insert.1 hv).resolve_left hvw))
      · have hvw : v ≠ w := fun e => hv' (e ▸ Finset.mem_insert_self w T)
        rw [map_mul, h5 _ _ _ hvw, mul_one]
        exact ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')


open jumpWindows.GeneralLinearEntryConvergence in
theorem sph (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ) :
    SphOff S (φ : GA E k → ℂ) := by
  intro g κ hinf hS hint
  choose H hH using step hG S φ g κ hfix hinf hS hint
  have hT : Tendsto H atTop (𝓝 κ) := by
    refine tendsto_gl κ H (tendsto_entry S κ H (fun T => (hH T).2.1) (fun T => (hH T).2.2.1)
      (fun T => (hH T).2.2.2)) (tendsto_entry S κ⁻¹ (fun T => (H T)⁻¹) (fun T => ?_) (fun T w hw => ?_)
      (fun T w hw hw' => ?_))
    · rw [map_inv, map_inv, (hH T).2.1]
    · rw [map_inv, map_inv, (hH T).2.2.1 w hw]
    · rw [map_inv, (hH T).2.2.2 w hw hw', inv_one]
  have hc : Continuous fun x : GA E k => φ (g * x) := φ.continuous.comp (continuous_const.mul continuous_id)
  have h1 := (hc.tendsto κ).comp hT
  have h2 : Tendsto ((fun x : GA E k => φ (g * x)) ∘ H) atTop (𝓝 (φ g)) := by
    have e : (fun x : GA E k => φ (g * x)) ∘ H = fun _ => φ g := funext fun T => (hH T).1
    rw [e]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end SphericalFunctionIntegral

theorem spherical_function_of : jumpWindows.G0 → jumpWindows.G5 → C0 → K7 → K8 := by
  intro hG0 hG5 hC0 hK7 E _ _ _ k ψ hψ S hcond α φ hgood hsat
  obtain ⟨-, hrt, -, hreg⟩ := hG5 E k ψ hψ
  have hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ :=
    fun w hw x hx => SphericalFunctionIntegral.fix (hsat ⟨w, hw⟩) hx
  have hφ := SphericalFunctionIntegral.sph hG0 S φ hfix
  have hcont := (hreg φ hgood).1
  refine ⟨hφ, fun g κ hinf hS hint => ?_, fun g hg => ⟨fun g₀ hi hS hIn h0 => ?_, fun w hw => ?_⟩⟩
  · have e : Rt E k κ φ = φ := by
      ext x
      simp only [Rt_apply]
      exact hφ x κ hinf hS hint
    rw [← hrt, e]
  · refine hg (jumpWindows.convergence_entries_general_linear hG0 E k S (Wh ψ φ) hcont (fun w hw h hh h0 u => ?_) g g₀ hi hS hIn h0)
    obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    rw [hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) h hh u, h0, zero_mul]
  · obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    obtain ⟨g', hg', e, -, -⟩ := (hC0 E k S).2.2.2.2.2.2 w g
    have h1 := hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) g' hg' (cLoc w g)
    rw [← e] at h1
    rw [h1] at hg
    have h2 := right_ne_zero_of_mul hg
    by_contra hA
    apply h2
    rw [sphericalWhittaker, if_neg hA]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ThetaDecayingFunction
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ThetaDecayingFunction

theorem key {x C1 D : ℝ} {a k : ℕ} (ha : a ≠ 0) (hx : 0 < x) (hC : 0 < C1) (hD : 0 < D) :
    ((D ^ ((k : ℝ)⁻¹) * (x / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹ * x = C1 * D ^ (-(a : ℝ) / k) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hD.le, Real.rpow_inv_natCast_pow (div_nonneg hx.le hC.le) ha,
    show -(a : ℝ) / k = -((k : ℝ)⁻¹ * a) by ring, Real.rpow_neg hD.le]
  have : 0 < D ^ ((k : ℝ)⁻¹ * a) := Real.rpow_pos_of_pos hD _
  field_simp

theorem le_height {x C1 D h : ℝ} {a k : ℕ} (ha : a ≠ 0) (hx : 0 < x) (hC : 0 < C1) (hD : 0 < D)
    (ht : 0 < h / D ^ ((k : ℝ)⁻¹)) (hb : x ≤ C1 * (h / D ^ ((k : ℝ)⁻¹)) ^ a) :
    D ^ ((k : ℝ)⁻¹) * (x / C1) ^ ((a : ℝ)⁻¹) ≤ h := by
  have hDk : 0 < D ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hD _
  have h1 : (x / C1) ^ ((a : ℝ)⁻¹) ≤ h / D ^ ((k : ℝ)⁻¹) := by
    rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (div_nonneg hx.le hC.le) _) ht.le ha,
      Real.rpow_inv_natCast_pow (div_nonneg hx.le hC.le) ha, div_le_iff₀' hC]
    exact hb
  calc _ ≤ D ^ ((k : ℝ)⁻¹) * (h / D ^ ((k : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h1 hDk.le
    _ = h := by field_simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem part1 (hD : D0) (hH : H0) (hG : ThetaSeriesBound) (hk : 1 ≤ k) (φ : GA E k → ℂ) (hφ : Dec φ)
    (Cf : Set (Fin k → Af E)) (hCf : IsCompact Cf) (a : ℕ) (hka : k ≤ a) :
    ∃ (M : ℕ) (C : ℝ), ∀ g : GA E k, (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ ≤
        ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k)) := by
  obtain ⟨M, C, hMC⟩ := hG E k Cf hCf a hka
  obtain ⟨C1, hC1⟩ := hφ a
  refine ⟨M, C * C1, fun g => ?_⟩
  have hDg : 0 < Dt g := (hD E k).1 g
  by_cases h0 : φ g = 0
  · simp [h0]
  have hx : 0 < ‖φ g‖ := norm_pos_iff.2 h0
  have hne : (fun _ : Fin k => (1 : E)) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hk⟩
    simp at this
  have hC1p : 0 < C1 := by
    have h1 := hC1 g _ hne
    have h2 := (hH E k).1 g _ hne
    by_contra hc
    replace hc := not_lt.1 hc
    have : C1 * ht g (fun _ => 1) ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg h2.le _)
    linarith
  have ha : a ≠ 0 := by omega
  have hr : 0 < Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹) :=
    mul_pos (Real.rpow_pos_of_pos hDg _) (Real.rpow_pos_of_pos (div_pos hx hC1p) _)
  have hbound := hMC g _ hr fun ξ hξ => le_height ha hx hC1p hDg ((hH E k).1 g ξ hξ) (hC1 g ξ hξ)
  calc _ ≤ ENNReal.ofReal (C * ((Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹) * ‖φ g‖ₑ := by
        gcongr
    _ = ENNReal.ofReal (C * ((Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹ * ‖φ g‖) := by
        rw [ENNReal.ofReal_mul' (norm_nonneg _), ofReal_norm]
    _ = _ := by rw [mul_assoc, key ha hx hC1p hDg, mul_assoc]

theorem ind_le {C₀ : Set (Fin k → Ad E)} {R : ℝ} (hR : ∀ y ∈ C₀, ‖fun i => pInf E (y i)‖ ≤ R) (M : ℕ)
    (y : Fin k → Ad E) :
    C₀.indicator (fun _ => (1 : ℝ≥0∞)) y ≤ ENNReal.ofReal ((1 + max R 0) ^ M) *
      ENNReal.ofReal (((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
        (fun _ => ((1 + ‖fun i => pInf E (y i)‖) ^ M)⁻¹) fun i => pFin E (y i)) := by
  by_cases hy : y ∈ C₀
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.one_le_ofReal, ← div_eq_mul_inv,
      one_le_div (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith [hR y hy, le_max_left R 0]) M
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

theorem part2 (hD : D0) (hN : N0) (hH : H0) (hG : ThetaSeriesBound) (hk : 1 ≤ k) (φ : GA E k → ℂ) (hφ : Dec φ)
    (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (a : ℕ) (hka : k ≤ a) :
    ∃ C : ℝ, ∀ g : GA E k,
      (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) * ‖φ g‖ₑ ≤
        ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k)) := by
  have hcF : Continuous fun y : Fin k → Ad E => fun i => pFin E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.ContAut.continuous_pFin E).comp (continuous_apply i)
  have hcI : Continuous fun y : Fin k → Ad E => fun i => pInf E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.ContAut.continuous_pInf E).comp (continuous_apply i)
  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn hcI.continuousOn
  obtain ⟨M, C', hC'⟩ := part1 hD hH hG hk φ hφ _ (hC₀.image hcF) a hka
  obtain ⟨-, -, -, -, -, -, -, -, -, hlast⟩ := hN E k k hk le_rfl
  let e : {ξ : Fin k → E // ξ ≠ 0} ≃ RowT E k k :=
    { toFun := fun ξ => ⟨ξ.1, ξ.2, fun i hi => absurd i.2 (by omega)⟩
      invFun := fun ξ => ⟨ξ.1, ξ.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hK : (0 : ℝ) ≤ (1 + max R 0) ^ M := by positivity
  refine ⟨(1 + max R 0) ^ M * C', fun g => ?_⟩
  rw [← e.tsum_eq]
  calc _ = (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, C₀.indicator (fun _ => (1 : ℝ≥0∞))
          ((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val)) * ‖φ g‖ₑ := by
        congr 1
        exact tsum_congr fun ξ => by rw [hlast]; rfl
    _ ≤ (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal ((1 + max R 0) ^ M) * ENNReal.ofReal (
          ((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ :=
        by
        gcongr with ξ
        exact ind_le hR M _
    _ = ENNReal.ofReal ((1 + max R 0) ^ M) * ((∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (
          ((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ) := by
        rw [ENNReal.tsum_mul_left, mul_assoc]
    _ ≤ ENNReal.ofReal ((1 + max R 0) ^ M) * ENNReal.ofReal (C' * Dt g ^ (-(a : ℝ) / k)) :=
        by
        gcongr
        exact hC' g
    _ = _ := by rw [← ENNReal.ofReal_mul hK, mul_assoc]

end ThetaDecayingFunction

theorem theta_decaying_of_bound : D0 → N0 → H0 → ThetaSeriesBound → ThetaDecaying := by
  intro hD hN hH hG E _ _ _ k hk φ hφ
  exact ⟨fun Cf hCf a hka => ThetaDecayingFunction.part1 hD hH hG hk φ hφ Cf hCf a hka,
    fun C₀ hC₀ a hka => ThetaDecayingFunction.part2 hD hN hH hG hk φ hφ C₀ hC₀ a hka⟩

end PositivityTheory.AdelicQuotientData

end
end

