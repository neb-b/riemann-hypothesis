module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ProductBoundOfFactorBounds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CapVal
section
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.CapelliClosureMembership

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h by simp only [Matrix.mul_assoc], hg]
  exact hh

lemma capelliC_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (u : ℂ) :
    ∀ y ∈ S, Capelli.capelliC E u y ∈ S := by
  have hprod : ∀ l : List (Module.End ℂ M), (∀ A ∈ l, ∀ y ∈ S, A y ∈ S) → ∀ y ∈ S, l.prod y ∈ S := by
    intro l
    induction l with
    | nil => intro _ y hy; simpa using hy
    | cons A l ih =>
      intro hl y hy
      rw [List.prod_cons, Module.End.mul_apply]
      exact hl A List.mem_cons_self _ (ih (fun B hB => hl B (List.mem_cons_of_mem _ hB)) y hy)
  intro y hy
  unfold Capelli.capelliC Capelli.cminor
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [LinearMap.smul_apply]
  refine zsmul_mem (hprod _ ?_ y hy) _
  intro A hA
  rw [List.mem_ofFn] at hA
  obtain ⟨j, rfl⟩ := hA
  intro z hz
  unfold Capelli.capEntry
  rw [LinearMap.add_apply]
  refine S.add_mem (hS _ _ z hz) ?_
  split_ifs
  · rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact S.smul_mem _ hz
  · simp

section Clos

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {D : Submodule ℂ H} {V : Submodule ℂ D} {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}


variable (ε σ V) in
def clo : Submodule ℂ H :=
  (Submodule.span ℂ {x : H | ∃ g, inUJ ε g ∧ ∃ v : D, v ∈ V ∧ x = σ g (v : H)}).topologicalClosure

lemma sig_mem_clo (hσ : IsURepOn (UJset ε) σ) {h : Matrix (Fin n) (Fin n) ℂ} (hh : inUJ ε h) {x : H}
    (hx : x ∈ clo V ε σ) : σ h x ∈ clo V ε σ := by
  have hle : Submodule.span ℂ {x : H | ∃ g, inUJ ε g ∧ ∃ v : D, v ∈ V ∧ x = σ g (v : H)} ≤
      (clo V ε σ).comap (σ h : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro y ⟨g, hg, v, hv, rfl⟩
    show σ h (σ g (v : H)) ∈ clo V ε σ
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 h hh g hg]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨h * g, inUJ_mul hh hg, v, hv, rfl⟩)
  have hcl : IsClosed (((clo V ε σ).comap (σ h : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
    (Submodule.isClosed_topologicalClosure _).preimage (σ h).continuous
  exact Submodule.topologicalClosure_minimal _ hle hcl hx

lemma mem_of_hasDerivAt {K : Submodule ℂ H} (hK : IsClosed (K : Set H)) {f : ℝ → H} {f' : H}
    (hf : HasDerivAt f f' 0) (hm : ∀ t, f t ∈ K) : f' ∈ K := by
  refine hK.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hf) (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact Submodule.smul_of_tower_mem K _ (K.sub_mem (hm t) (hm 0))

lemma actM_mem_clo (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) {x : D} (hx : (x : H) ∈ clo V ε σ) : ((actM E X x : D) : H) ∈ clo V ε σ :=
  mem_of_hasDerivAt (Submodule.isClosed_topologicalClosure _) (hD.deriv X hX x)
    fun t => sig_mem_clo hσ (inUJ_exp ε hX t) hx

lemma E_mem_clo (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (a b : Fin n) {x : D}
    (hx : (x : H) ∈ clo V ε σ) : ((E a b x : D) : H) ∈ clo V ε σ := by
  have hs : S7.cpart1 ε (Matrix.single a b 1) + Complex.I • S7.cpart2 ε (Matrix.single a b 1) =
      Matrix.single a b 1 := LemK.ta_cpart_sum ε _
  rw [← SmDerA.actM_single E a b, ← hs, SmDerA.actM_add, SmDerA.actM_smul, LinearMap.add_apply,
    LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul]
  exact add_mem (actM_mem_clo hσ hD (LemK.ta_inG_cpart1 ε _) hx)
    (Submodule.smul_mem _ _ (actM_mem_clo hσ hD (LemK.ta_inG_cpart2 ε _) hx))

end Clos

theorem capVal_main : CapValStatement := by
  intro n ε lam _h H _ _ _ σ D E V T μ ι hσ hD _hV _hcas _hVK hμ hcoef _hHC _hgap _hh _hq ω m hm
  set P : ℂ := ∏ t, (ω + ((LemK.thV lam t : ℝ) : ℂ)) with hP
  set C := Capelli.capelliC E ω with hC
  have hΨ : ∀ g, inUJ ε g → S7.PsiM T μ g = opC σ ι g 1 := by
    intro g hg
    refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun x' => ?_
    obtain ⟨v, rfl⟩ := ι.surjective x
    obtain ⟨v', rfl⟩ := ι.surjective x'
    rw [opC_coef σ ι g 1 v v', ← hcoef g hg v v']
    rfl
  have hval : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((C v : D) : H)⟫_ℂ = P * ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ := by
    intro g hg v v'
    have h1 := S7.psiM_capelli T μ hμ (ω - ((n : ℂ) - 1) / 2) hg
    rw [show ω - ((n : ℂ) - 1) / 2 + ((n : ℂ) - 1) / 2 = ω by ring] at h1
    rw [show Formalism.QuantumDeterminants.capelli ε ω (S7.PsiM T μ) = Formalism.QuantumDeterminants.qdetOp (Formalism.REAL.EabV ε) ω (S7.PsiM T μ)
      from rfl, qdet_opC hσ hD ι hΨ hg ω] at h1
    have h3 : Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (ω - ((n : ℂ) - 1) / 2) = P := by
      unfold Formalism.QuantumDeterminants.capP
      rw [hP]
      refine Finset.prod_congr rfl fun t _ => ?_
      unfold LemK.thV
      push_cast
      ring
    rw [← opC_coef σ ι g C v v', ← mul_one C, h1, h3, hΨ g hg, _root_.smul_apply,
      inner_smul_right, opC_coef]
    rfl
  have hA : ∀ v : V, C v = P • (v : D) := by
    intro v
    set u : D := C v - P • (v : D) with hu
    have horth : ∀ g, inUJ ε g → ∀ v' : V, ⟪((v' : D) : H), σ g (u : H)⟫_ℂ = 0 := by
      intro g hg v'
      rw [hu, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, inner_sub_right,
        inner_smul_right, hval g hg v v', sub_self]
    let S : Submodule ℂ D := (clo V ε σ).comap D.subtype
    have hSE : ∀ a b, ∀ x ∈ S, E a b x ∈ S := fun a b x hx => E_mem_clo hσ hD a b hx
    have hvS : (v : D) ∈ S := by
      show ((v : D) : H) ∈ clo V ε σ
      refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, inUJ_one ε, v, v.2, ?_⟩)
      rw [hσ.1.1]
      rfl
    have huS : u ∈ S := S.sub_mem (capelliC_mem E S hSE ω _ hvS) (S.smul_mem P hvS)
    have hle : clo V ε σ ≤ (innerSL ℂ (u : H)).ker := by
      refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker _)
      rw [Submodule.span_le]
      rintro y ⟨g, hg, w, hw, rfl⟩
      have h0 := horth _ (inUJ_jAdj hg) ⟨w, hw⟩
      have h1 : ⟪σ g (w : H), (u : H)⟫_ℂ = 0 := by
        rw [inner_sig_left hσ hg]
        exact h0
      show innerSL ℂ (u : H) (σ g (w : H)) = 0
      rw [innerSL_apply_apply, ← inner_conj_symm, h1, map_zero]
    have hin : innerSL ℂ (u : H) (u : H) = 0 := hle huS
    rw [innerSL_apply_apply] at hin
    have hu0 : u = 0 := by
      have : (u : H) = 0 := inner_self_eq_zero.mp hin
      exact_mod_cast this
    rw [hu, sub_eq_zero] at hu0
    exact hu0
  have hB : genSub E V ≤ LinearMap.ker (C - P • (1 : Module.End ℂ D)) := by
    refine sInf_le ⟨?_, ?_⟩
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
      exact hA ⟨x, hx⟩
    · intro a b x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hcomm := Capelli.capelliCentral (Module.End ℂ D) n E ω
        ((Capelli.isGlRep_iff_glRelR E).mp hD.glRep) a b
      have hce : C (E a b x) = E a b (C x) := by
        have := congrArg (fun A : Module.End ℂ D => A x) hcomm.eq
        simpa [Module.End.mul_apply] using this.symm
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hx ⊢
      rw [hce, ← map_smul, ← map_sub, hx, map_zero]
  have hm' := hB hm
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hm'
  exact hm'

end ReciprocityTheory.ChartRestriction.DS.Lap.CapelliClosureMembership

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem capVal : CapValStatement := CapelliClosureMembership.capVal_main

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinBFrobConjGe
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem finB_umat_inv {n : ℕ} {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat y⁻¹ = (Formalism.MainNotions.S.umat y)⁻¹ := by
  show ((y⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = _
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem finB_umat_mul {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl

theorem finB_intJ_shift {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (b : ℝ)
    (hI : Integrable (fun y : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y) ^ (-b)) (Formalism.REAL.muG ε))
    (γ : Formalism.REAL.UJ ε) :
    Integrable (fun y : Formalism.REAL.UJ ε => frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b)) (Formalism.REAL.muG ε) ∧
    ∫ y, frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b) ∂(Formalism.REAL.muG ε) =
      ∫ y, frob (Formalism.MainNotions.S.umat y) ^ (-b) ∂(Formalism.REAL.muG ε) := by
  have e : (fun y : Formalism.REAL.UJ ε => frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b)) =
      fun y => (fun y' : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y') ^ (-b)) (γ⁻¹ * y) := by
    funext y
    have h1 : (Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ = (Formalism.MainNotions.S.umat (γ⁻¹ * y))⁻¹ := by
      rw [← finB_umat_inv, ← finB_umat_inv, ← finB_umat_mul, _root_.mul_inv_rev, inv_inv]
    simp only
    rw [h1, finB_frob_inv (unitary_matrix_mem_set ε _)]
  rw [e]
  exact ⟨hI.comp_mul_left γ⁻¹,
    integral_mul_left_eq_self (μ := Formalism.REAL.muG ε) (fun y' : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y') ^ (-b)) γ⁻¹⟩

theorem finB_pair {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} (β : ℝ) (hβ : 0 ≤ β) {Y g : Mat k r}
    (hY : Y ∈ UJset ε) (hg : g ∈ UJset ε) (hYg : Y⁻¹ * g ∈ UJset ε) :
    frob Y ^ (-β) * frob (Y⁻¹ * g) ^ (-β) ≤
      frob g ^ (-(β / 4)) * (frob Y ^ (-(β / 2)) + frob (Y⁻¹ * g) ^ (-(β / 2))) := by
  have hA := finB_one_le hY
  have hB := finB_one_le hYg
  have hG := finB_one_le hg
  have hle := finB_le_mul hY g
  have hAh : 0 ≤ frob Y ^ (-(β / 2)) := Real.rpow_nonneg (by linarith) _
  have hBh : 0 ≤ frob (Y⁻¹ * g) ^ (-(β / 2)) := Real.rpow_nonneg (by linarith) _
  have hGq : 0 ≤ frob g ^ (-(β / 4)) := Real.rpow_nonneg (by linarith) _
  rcases le_total (frob Y) (frob (Y⁻¹ * g)) with h | h
  · calc _ ≤ frob g ^ (-(β / 4)) * frob (Y⁻¹ * g) ^ (-(β / 2)) :=
          S0.DecA.pb_real β _ _ _ hβ hA hB (by linarith) (le_of_le_of_eq hle (mul_comm _ _)) h
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAh) hGq
  · have := S0.DecA.pb_real β (frob (Y⁻¹ * g)) (frob Y) (frob g) hβ hB hA (by linarith) hle h
    rw [mul_comm] at this
    calc _ ≤ frob g ^ (-(β / 4)) * frob Y ^ (-(β / 2)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBh) hGq

theorem finB_one_UH (k r : ℕ) : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem finB_frob_conj_ge {k r : ℕ} {P : Mat k r} (hP : IsUnit P.det) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : Mat k r, c * Formalism.FourierDecayAlt.B.gN g ≤ frob (P * g * P⁻¹) := by
  letI : NormedAddCommGroup (Mat k r) := Matrix.frobeniusNormedAddCommGroup
  have hg : ∀ A : Mat k r, Formalism.FourierDecayAlt.B.gN A = ‖A‖ := by
    intro A
    rw [Matrix.frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_norm_sq, Real.rpow_two]
  have hf : ∀ A : Mat k r, frob A = ‖A‖ := by
    intro A
    rw [Matrix.frobenius_norm_def, frob, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.rpow_two]
  refine ⟨1 / (‖P⁻¹‖ * ‖P‖ + 1), by positivity, fun g => ?_⟩
  have e : g = P⁻¹ * (P * g * P⁻¹) * P := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hP, Matrix.nonsing_inv_mul _ hP,
      Matrix.mul_one]
  have h1 : ‖g‖ ≤ ‖P⁻¹‖ * ‖P * g * P⁻¹‖ * ‖P‖ := by
    conv_lhs => rw [e]
    calc ‖P⁻¹ * (P * g * P⁻¹) * P‖ ≤ ‖P⁻¹ * (P * g * P⁻¹)‖ * ‖P‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖P⁻¹‖ * ‖P * g * P⁻¹‖ * ‖P‖ :=
        mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
  rw [hg, hf, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (P * g * P⁻¹), norm_nonneg P⁻¹, norm_nonneg P,
    mul_nonneg (norm_nonneg P⁻¹) (norm_nonneg P)]

theorem finB_intS (hIS : S0.IntSStatement) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (b : ℝ) (hb : S0.bS k r < b) :
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-b)) (μW.prod μN) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hb0 : 0 ≤ b := by
    have : 0 ≤ S0.bS k r := by unfold S0.bS S0.nS; positivity
    linarith
  obtain ⟨c0, hc0, hcg⟩ := finB_frob_conj_ge hd
  have h1 := hIS k r z μW μN hz hT hW hN 1 (finB_one_UH k r) x hx b hb
  simp only [inv_one, Matrix.one_mul] at h1
  have hae := ae_mem_unitary_nilpotent_product z μW μN hW hN
  have hof : Continuous (fun g : Formalism.QuantumDeterminants.Mt k r => (Matrix.of g : Mat k r)) := S0.Dec.of_cont k r
  have hfc : Continuous (fun M : Mat k r => frob M) := by
    have : (fun M : Mat k r => frob M) = fun M => Formalism.FourierDecayAlt.B.gN M := funext finB_frob_eq
    rw [this]; exact S0.Dec.gN_cont k r
  have hgc : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
    (continuous_const.matrix_mul (((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  refine Integrable.mono' (h1.const_mul (c0 ^ (-b))) ((hfc.comp hgc).measurable.pow_const _).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  have hM : Matrix.of p.1 * Matrix.of p.2 * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    unitary_hermitian_form_mul_mem (unitary_hermitian_form_mul_mem hp.1.1 hp.2.1) hx
  have hg1 := S0.DecA.one_le_gN' hM
  have hge := hcg (Matrix.of p.1 * Matrix.of p.2 * x)
  have hpos : 0 < c0 * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  calc frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-b)
      ≤ (c0 * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hpos hge (by linarith)
    _ = c0 ^ (-b) * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x) ^ (-b) :=
        Real.mul_rpow hc0.le (by linarith)

theorem finB_UJ_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {a b : Mat k r} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := (mir_inUJ_iff ε a).2 ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := (mir_inUJ_iff ε b).2 hb
  show inUJ ε (a * b)
  rw [← mir_inUJ_iff]
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem finB_UJ_closed {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) : IsClosed (UJset ε : Set (Mat k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem finB_gap {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hgap : StepGap ε r h) :
    1 ≤ S7.q0 ε ∧ 0 < h ∧
      4 * max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) <
        aExp ε h - 1 := by
  obtain ⟨h1, h2⟩ := hgap
  have e : min (pOf ε : ℝ) (qOf ε : ℝ) = (S7.q0 ε : ℝ) := by unfold S7.q0; push_cast; rfl
  rw [e] at h2
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmax0 : 0 ≤ max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) :=
    le_max_of_le_left (by positivity)
  refine ⟨?_, ?_, h2⟩
  · by_contra hq
    have hq0 : S7.q0 ε = 0 := by omega
    rw [hq0] at h2
    simp at h2
    have : (0 : ℝ) ≤ max 0 (2 * (r : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) ^ 2) := le_max_left _ _
    linarith
  · have : 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2 := by positivity
    have := le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2) (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotMA
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TransportMapLinear

open ReciprocityTheory.ChartRestriction.DS

section Cls

variable {n : ℕ}

theorem toL2_congr_on_unitary_bis (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ UJset ε, F g = G g) : toL2 ε F = toL2 ε G := by
  have e : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) :=
    funext fun g => h _ (unitary_matrix_mem_set ε g)
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := e ▸ hF
    rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG, MemLp.toLp_eq_toLp_iff]
    exact Filter.EventuallyEq.of_eq e
  · have hG : ¬ MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := e ▸ hF
    rw [toL2_eq_zero_of_not_memLp ε hF, toL2_eq_zero_of_not_memLp ε hG]

theorem exists_lin {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (ε : Fin n → Bool)
    (A : Fin n → Fin n → Module.End ℂ Y) (G : Submodule ℂ Y)
    (L : Y →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (hsm : ∀ f ∈ G, IsSmoothL2 ε (L f))
    (hG : ∀ a b, ∀ f ∈ G, A a b f ∈ G)
    (hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (A a b f) g) :
    ∃ T : Y →ₗ[ℂ] smD ε (rreg ε), (∀ f ∈ G, (T f : L2 ε) = toL2 ε (L f)) ∧
      ∀ a b, ∀ f ∈ G, T (A a b f) = smE ε (rreg ε) a b (T f) := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl G
  let p := G.projectionOnto q hq
  have hpG : ∀ f ∈ G, ((p f : G) : Y) = f := fun f hf => by
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨f, hf⟩)
  have hmem : ∀ f : Y, toL2 ε (L (p f)) ∈ smD ε (rreg ε) := fun f => toL2_mem_smD_of_isSmoothL2 (hsm _ (p f).2)
  have hL2 : ∀ f : Y, MemLp (fun g : Formalism.REAL.UJ ε => L (p f) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    fun f => (hsm _ (p f).2).2 []
  let T : Y →ₗ[ℂ] smD ε (rreg ε) :=
    { toFun := fun f => ⟨toL2 ε (L (p f)), hmem f⟩
      map_add' := fun f g => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [map_add (f := _), Submodule.coe_add, map_add (f := _)]
        exact toL2_add_smooth ε (hL2 f) (hL2 g)
      map_smul' := fun c f => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [map_smul, Submodule.coe_smul, map_smul]
        exact toL2_smul_smooth ε c _ }
  have hT : ∀ f ∈ G, (T f : L2 ε) = toL2 ε (L f) := fun f hf => by
    show toL2 ε (L (p f)) = _
    rw [hpG f hf]
  refine ⟨T, hT, fun a b f hf => ?_⟩
  have e1 : T f = ⟨toL2 ε (L f), toL2_mem_smD_of_isSmoothL2 (hsm f hf)⟩ := Subtype.ext (hT f hf)
  apply Subtype.ext
  rw [hT _ (hG a b f hf), e1, rightDerivative_toL2 (hsm f hf) a b]
  exact toL2_congr_on_unitary_bis ε fun g hg => (hder f hf a b g hg).symm

end Cls

section Lin

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def tMapDL (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : H) :
    (Fin (2 * r + k + 1) → D) →ₗ[ℂ] (Mat k r → ℂ) where
  toFun f := tMapD σ x₁ x₀ w (fun c => ((f c : D) : H))
  map_add' f g := by
    funext x
    simp only [tMapD, coefX, Pi.add_apply, Submodule.coe_add, map_add (f := _), inner_add_right, mul_add,
      Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [tMapD, coefX, Pi.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

end Lin

section Line

universe u

variable {n : ℕ} {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem line (hU : IsKUnitary ε E) (X : Submodule ℂ (Fin n → D)) (Λ : Fin n → ℝ)
    (hXk : ∀ y ∈ X, ∃ S : Submodule ℂ (Fin n → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensVd E) S ∧ y ∈ S)
    (hK2 : ∀ f₁ f₂ : Fin n → D, f₁ ∈ X → f₂ ∈ X → IsKHWVec ε (LemK.tensVd E) Λ f₁ →
      IsKHWVec ε (LemK.tensVd E) Λ f₂ → ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • f₁ + c₂ • f₂ = 0) :
    ∃ ys ∈ X, ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y] (B : Fin n → Fin n → Module.End ℂ Y)
      (ψ : (Fin n → D) →ₗ[ℂ] Y), (∀ a b, ε a = ε b → ∀ x ∈ X, ψ (LemK.tensVd E a b x) = B a b (ψ x)) →
      ∀ y ∈ X.map ψ, IsKHWVec ε B Λ y → ∃ c : ℂ, y = c • ψ ys := by
  classical

  have hlift : ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y] (B : Fin n → Fin n → Module.End ℂ Y)
      (ψ : (Fin n → D) →ₗ[ℂ] Y), (∀ a b, ε a = ε b → ∀ x ∈ X, ψ (LemK.tensVd E a b x) = B a b (ψ x)) →
      ∀ y ∈ X.map ψ, IsKHWVec ε B Λ y → ∃ x ∈ X, IsKHWVec ε (LemK.tensVd E) Λ x ∧ ψ x = y := by
    intro Y _ _ B ψ hψ y hy hyK
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨S, hSX, hfd, hSk, hx₀S⟩ := hXk x₀ hx₀
    obtain ⟨x, hxS, hxK, hx⟩ := LemK.exists_highest_weight_lift_pi hU ψ hfd hSk
      (fun a b hab z hz => hψ a b hab z (hSX hz)) hx₀S hyK
    exact ⟨x, hSX hxS, hxK, hx⟩
  by_cases hex : ∃ ys ∈ X, ys ≠ 0 ∧ IsKHWVec ε (LemK.tensVd E) Λ ys
  · obtain ⟨ys, hys, hys0, hysK⟩ := hex
    refine ⟨ys, hys, fun Y _ _ B ψ hψ y hy hyK => ?_⟩
    obtain ⟨x, hx, hxK, rfl⟩ := hlift Y B ψ hψ y hy hyK
    obtain ⟨c₁, c₂, hc, hsum⟩ := hK2 x ys hx hys hxK hysK
    by_cases h1 : c₁ = 0
    · exfalso
      have h2 : c₂ ≠ 0 := hc.resolve_left (not_not.2 h1)
      rw [h1, zero_smul, zero_add] at hsum
      exact hys0 ((smul_eq_zero.1 hsum).resolve_left h2)
    · refine ⟨-(c₂ / c₁), ?_⟩
      have : x = -(c₂ / c₁) • ys := by
        have h3 : c₁ • x = -(c₂ • ys) := eq_neg_of_add_eq_zero_left hsum
        calc x = c₁⁻¹ • (c₁ • x) := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
          _ = -(c₂ / c₁) • ys := by rw [h3, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      rw [this, map_smul]
  · refine ⟨0, zero_mem _, fun Y _ _ B ψ hψ y hy hyK => ?_⟩
    obtain ⟨x, hx, hxK, rfl⟩ := hlift Y B ψ hψ y hy hyK
    have : x = 0 := by
      by_contra h0
      exact hex ⟨x, hx, h0, hxK⟩
    exact ⟨0, by rw [this, map_zero, zero_smul]⟩

end Line

end ReciprocityTheory.ChartRestriction.DS.Lap.TransportMapLinear
end
end

