module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrandAestronglyMeasurable
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselColumnStepsFunctionalEigen
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quantumMinor_columnSteps_partial (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp]
    [Module ℂ Wp] (k r : ℕ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp)
    (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ) (hE : Formalism.REAL.GlRel E)
    (hp : ∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) →
      (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ =
        (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ)
          else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ
          else 0))
    (w : Fin k → Fin (2 * r + k + 1)) (hw : ∀ i, (w i).val = r + i.val) (j : ℕ) :
    j ≤ r → ∀ (t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)), t = k + j →
      (∀ i, (a i).val = r + i.val) →
      (∀ i, (b i).val = if i.val < k then r + i.val else r + i.val + 1) →
      ∃ c : ℂ, ‖c‖ = (if j = 0 then 1 else τ) ∧ ∀ u v,
        l (Formalism.REAL.qminor E a b u v) = c • l (Formalism.REAL.qminor E w w (u - (j : ℂ)) v) := by
  induction j with
  | zero =>
    intro _ t a b ht ha hb
    obtain rfl : t = k := ht
    have h1 : a = w := funext fun i => Fin.ext (by rw [ha, hw])
    have h2 : b = w := funext fun i => Fin.ext (by rw [hb, hw, if_pos i.isLt])
    refine ⟨1, by simp, fun u v => ?_⟩
    simp [h1, h2]
  | succ j ih =>
    intro hj t a b ht ha hb
    obtain rfl : t = (k + j) + 1 := ht
    obtain ⟨c, hc, hcu⟩ := ih (by omega) (k + j) (fun i => a i.castSucc) (fun i => b i.castSucc) rfl
      (fun i => by simpa using ha i.castSucc) (fun i => by simpa using hb i.castSucc)
    have hai : Function.Injective a := fun x y h => by
      have h' := congrArg Fin.val h
      rw [ha, ha] at h'
      exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y h => by
      have h' := congrArg Fin.val h
      rw [hb, hb] at h'
      exact Fin.ext (by split_ifs at h' <;> omega)
    have hr : ∀ f : Fin (k + j + 1) → Fin (2 * r + k + 1),
        Set.range f = insert (f (Fin.last _)) (Set.range fun i : Fin (k + j) => f i.castSucc) := by
      intro f
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Fin.exists_fin_succ', eq_comm, or_comm]
    have hn : ∀ f : Fin (k + j + 1) → Fin (2 * r + k + 1), Function.Injective f →
        f (Fin.last _) ∉ Set.range fun i : Fin (k + j) => f i.castSucc := by
      rintro f hf ⟨i, hi⟩
      exact (Fin.castSucc_lt_last i).ne (hf hi)
    have hal : (a (Fin.last _)).val = r + (k + j) := by rw [ha]; simp
    have hbl : (b (Fin.last _)).val = r + (k + j) + 1 := by rw [hb]; simp
    have hlt : ∀ i, a i < b (Fin.last _) := fun i => by
      have := i.isLt
      rw [Fin.lt_def, ha, hbl]; omega
    have hq := fun i => hp (a i) (b (Fin.last _)) (hlt i) (by rw [hbl]; omega)
    obtain ⟨e, he, heu⟩ := _root_.GlobalTheory.CapStepCol.cap_step_col M Wp _ (k + j) E l a b (fun i => a i.castSucc)
      (fun i => b i.castSucc) (a (Fin.last _)) (b (Fin.last _))
      (p (a (Fin.last _)) (b (Fin.last _))) hE hai hbi
      (hai.comp (Fin.castSucc_injective _)) (hbi.comp (Fin.castSucc_injective _))
      (hr a) (hn a hai) (hr b) (hn b hbi)
      (by rintro ⟨i, hi⟩; exact (hlt i).ne hi)
      (by
        intro i v
        rw [(hq i).1 v]
        split_ifs with h
        · rw [h]
        · have h0 := (hq i).2
          have hi : (a i).val ≠ r + (k + j) := fun h' => h (Fin.ext (by rw [h', hal]))
          have hi2 := ha i
          rw [hbl, if_neg (by omega), if_neg (by omega)] at h0
          rw [norm_eq_zero.1 h0])
    refine ⟨e * p (a (Fin.last _)) (b (Fin.last _)) * c, ?_, fun u v => ?_⟩
    · have h0 := (hq (Fin.last _)).2
      rw [hal, hbl] at h0
      rw [norm_mul, norm_mul, he, hc, h0]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
        intro h; omega
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
        simp
    · rw [heu, hcu, smul_smul]
      congr 4
      push_cast
      ring

theorem qminor_column_chain : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) = c • l (Formalism.REAL.qminor E (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (u - (r : ℂ)) v) := by
  intro M Wp _ _ _ _ k r E l p τ _ hE hp hr
  have h := quantumMinor_columnSteps_partial M Wp k r E l p τ hE hp
    (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (fun _ => rfl) r le_rfl (r + k)
    (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
    (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
      by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) (Nat.add_comm _ _) (fun _ => rfl) (fun _ => rfl)
  rw [if_neg (by omega)] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSumStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : Mx k r), γ ∈ GG k r → (∀ F F' : Mx k r → (Wq →L[ℂ] Wp), (∀ g ∈ GG k r, F g = F' g) → B.JF D F γ = B.JF D F' γ ∧ (Integrable (JF.integrand D F γ) D.μSS → Integrable (JF.integrand D F' γ) D.μSS)) ∧ (∀ (φ : Mx k r → ℂ) (F : Mx k r → (Wq →L[ℂ] Wp)), (∀ p, D.inSS p → φ (B.sgs p γ) = φ γ) → B.JF D (fun g => φ g • F g) γ = φ γ • B.JF D F γ) ∧ (∀ (ι : Type) [Fintype ι] (F : ι → Mx k r → (Wq →L[ℂ] Wp)), (∀ i, Integrable (JF.integrand D (F i) γ) D.μSS) → B.JF D (fun g => ∑ i, F i g) γ = ∑ i, B.JF D (F i) γ) ∧ ∀ᵐ p ∂D.μSS, D.inSS p := by
  first | exact @GlobalTheory.BesselFunctionBasic.JF_basic | exact GlobalTheory.BesselFunctionBasic.JF_basic | (intros; apply GlobalTheory.BesselFunctionBasic.JF_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreserving
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SParamMeas

open Formalism.QuantumDeterminants

variable {k r : ℕ}

noncomputable def conjInvM (a : B.Mat k r) (x : Mt k r) : Mt k r := a⁻¹ * Matrix.of x * a

theorem meas_mul {α : Type*} [MeasurableSpace α] {f g : α → Mt k r} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.mulM (f x) (g x)) :=
  Formalism.FourierDecayAlt.P.B7.continuous_mulM.measurable.comp (hf.prodMk hg)

theorem meas_inv {α : Type*} [MeasurableSpace α] {f : α → Mt k r} (hf : Measurable f) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.invM (f x)) :=
  Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hf

theorem mp_lmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (lmulM a) μ μ :=
  ⟨meas_mul (f := fun _ => a) measurable_const measurable_id, h.left a ha⟩

theorem mp_rmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (B.rmulF a) μ μ :=
  ⟨meas_mul (g := fun _ => a) measurable_id measurable_const, h.right a ha⟩

theorem mp_inv {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (hU : B2.IsClosedSubgroup U) (h : B.IsHaarOn U μ) :
    MeasurePreserving (B2.invM (k := k) (r := r)) μ μ :=
  ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r U μ hU h⟩

theorem mp_conj {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjM a) μ μ :=
  ⟨meas_mul (g := fun _ => (a⁻¹ : B.Mat k r)) (meas_mul (f := fun _ => a) measurable_const measurable_id)
    measurable_const, Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μ hz hT h a ha⟩

theorem mp_conj_inv {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjInvM a) μ μ := by
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have := mp_conj hz hT h (hW.inv_mem a ha)
  have e : conjM (a⁻¹) = conjInvM a := by
    funext x
    unfold conjM conjInvM
    rw [Matrix.nonsing_inv_nonsing_inv _ (hW.unit a ha)]
  rwa [e] at this

end GlobalTheory.SParamMeas


open GlobalTheory.SParamMeas in
theorem GlobalTheory.sParam_measurePreserving : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → (∀ h₀ ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n₀ ∈ Formalism.QuantumDeterminants.Nset k r, MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 * h₀ : Mx k r) i j), (fun i j => (h₀⁻¹ * Matrix.of p.2 * h₀ * n₀ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (h₀ * Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * n₀ * Matrix.of p.1 * Matrix.of p.2 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN)) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro k r z μW μN hk hz hT hW0 hN0
  have hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW := ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).1 hW0
  have hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN := (GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1.1 hN0
  have := hW0.1
  have := hN0.1
  have cW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have cN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have aW := Formalism.FourierDecayAlt.P.B7.ae_mem hW
  have aN := Formalism.FourierDecayAlt.P.B7.ae_mem hN
  have m1 : Measurable (Prod.fst : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_fst
  have m2 : Measurable (Prod.snd : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_snd
  refine ⟨fun h₀ hh n₀ hn => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mp_rmul hW hh).prod ((mp_rmul hN hn).comp (mp_conj_inv hz hT hN hh))
  · have m3 : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm n₀ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    refine (mp_lmul hW hh).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.lmulM ((Matrix.of a)⁻¹ * n₀ * Matrix.of a) x)
      (meas_mul (meas_mul (meas_mul (meas_inv m1) m3) m1) m2) ?_
    filter_upwards [aW] with a ha
    refine hN.left _ ?_
    have := (Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz _ (cW.inv_mem _ ha) n₀ hn).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ (cW.unit _ ha)] at this
  · refine (mp_inv cW hW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) (B2.invM x))
      (meas_mul (meas_mul m1 (meas_inv m2)) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact ((mp_conj hz hT hN ha).comp (mp_inv cN hN)).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) x)
      (meas_mul (meas_mul m1 m2) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj hz hT hN ha).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) =>
        conjInvM (Matrix.of a) x)
      (meas_mul (meas_mul (meas_inv m1) m2) m1) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj_inv hz hT hN ha).map_eq
  · exact (mp_inv cW hW).prod (mp_inv cN hN)
  · exact (Measure.quasiMeasurePreserving_fst.ae aW).and (Measure.quasiMeasurePreserving_snd.ae aN)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaInfEqIntegralOfIntegrableCoefficient
section
noncomputable section

namespace GlobalTheory.RegularisedIntegral

section

open Matrix MeasureTheory Filter Topology
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem dilate_subst (D : RealPlaceData k r Wp Wq) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SS k r → E} (hf : Integrable f D.μSS) {t : ℝ × ℝ} (h1 : 0 < t.1) (h2 : 0 < t.2) :
    Integrable (fun p => f (dilation₂ t p)) D.μSS ∧
      (∫ p, f (dilation₂ t p) ∂D.μSS) = ((t.1 * t.2) ^ kap k r)⁻¹ • ∫ p, f p ∂D.μSS := by
  have hm := map_measure_dilation_pair_eq_smul (dilation_jacobian_every_setting k r Wp Wq D) h1 h2
  have hf' : Integrable f (D.μSS.map (dilation₂ t)) := by
    rw [hm]
    exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  refine ⟨hf'.comp_measurable (dilation_action_measurable t), ?_⟩
  rw [← integral_map (dilation_action_measurable t).aemeasurable hf'.1, hm, integral_smul_measure, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity), mul_pow, mul_inv]

def kernel (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Bt D F F' q * Complex.exp (Complex.I * (phase D τ q.1 q.2 : ℂ))

variable {D : RealPlaceData k r Wp Wq} {α : ℝ}

theorem betaInfTau_eq_kernel (H : SqIntegrable D α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) :
    betaInfTau D τ F F' = ∫ p, (∫ t : ℝ × ℝ, kernel D F F' τ (p, t)) ∂D.μSS := by
  unfold betaInfTau
  refine integral_congr_ae ?_
  filter_upwards [ae_inSS D] with p hp
  have key := (bracket_calculus H hF hF' hp).2.2.2 (τ.1 * lam k r D.z (Matrix.of p.1.2))
    (-(τ.2 * lam k r D.z' (Matrix.of p.2.2)))
  have e : ∀ t : ℝ × ℝ, τ.1 * t.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * t.2 * lam k r D.z' (Matrix.of p.2.2) =
      τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 := fun t => by ring
  simp only [kernel, phase, Bt_eq D F F' hp, e]
  rw [key, ← mul_assoc, ← Complex.ofReal_mul]
  have : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ * (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹ *
      ((1 + (τ.1 * lam k r D.z (Matrix.of p.1.2)) ^ 2) *
        (1 + (-(τ.2 * lam k r D.z' (Matrix.of p.2.2))) ^ 2)) = 1 := by
    have a1 : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2) ≠ 0 := by positivity
    have a2 : (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2) ≠ 0 := by positivity
    field_simp
  rw [this]
  simp

theorem kernel_slice (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) {t : ℝ × ℝ}
    (h1 : 0 < t.1) (h2 : 0 < t.2) :
    (fun p => kernel D F F' τ (p, t)) =ᵐ[D.μSS] fun p =>
      (D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ) • (xiTau D τ (dilation₂ t p) * Ph D F F' (dilation₂ t p)) := by
  filter_upwards [ae_inSS D] with p hp
  obtain ⟨l1, l2⟩ := lam_dil dilation_unipotent_measure D hp h1 h2
  have l1' : lam k r D.z (Matrix.of (dilation₂ t p).1.2) = t.1 * lam k r D.z (Matrix.of p.1.2) := l1
  have l2' : lam k r D.z' (Matrix.of (dilation₂ t p).2.2) = t.2 * lam k r D.z' (Matrix.of p.2.2) := l2
  unfold kernel xiTau phase
  rw [Bt_eq D F F' hp, l1', l2', Complex.real_smul]
  unfold regBracket
  simp only [mul_assoc]
  ring

theorem kernel_slice_integral (D : RealPlaceData k r Wp Wq) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (τ : ℝ × ℝ)
    (hf : Integrable (fun p => xiTau D τ p * Ph D F F' p) D.μSS) (t : ℝ × ℝ) :
    Integrable (fun p => kernel D F F' τ (p, t)) D.μSS ∧
      (∫ p, kernel D F F' τ (p, t) ∂D.μSS) =
        ((D.χ t.1 * D.χ t.2 : ℝ) : ℂ) * ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS ∧
      (∫ p, ‖kernel D F F' τ (p, t)‖ ∂D.μSS) =
        |D.χ t.1| * |D.χ t.2| * ∫ p, ‖xiTau D τ p * Ph D F F' p‖ ∂D.μSS := by
  by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
  · have h1 : 0 < t.1 := lt_trans (by norm_num) ht.1.1
    have h2 : 0 < t.2 := lt_trans (by norm_num) ht.2.1
    have e := kernel_slice D F F' τ h1 h2
    obtain ⟨i1, s1⟩ := dilate_subst D hf h1 h2
    obtain ⟨-, s2⟩ := dilate_subst D hf.norm h1 h2
    have hpos : 0 < (t.1 * t.2) ^ kap k r := by positivity
    refine ⟨(i1.smul (D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ)).congr e.symm, ?_, ?_⟩
    · rw [integral_congr_ae e, integral_smul, s1, smul_smul, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one,
        Complex.real_smul]
    · have e' : (fun p => ‖kernel D F F' τ (p, t)‖) =ᵐ[D.μSS] fun p =>
          (|D.χ t.1| * |D.χ t.2| * (t.1 * t.2) ^ kap k r) * ‖xiTau D τ (dilation₂ t p) * Ph D F F' (dilation₂ t p)‖ := by
        filter_upwards [e] with p hp
        rw [hp, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hpos]
      rw [integral_congr_ae e', integral_const_mul, s2, smul_eq_mul, ← mul_assoc, mul_assoc _ _ (_⁻¹),
        mul_inv_cancel₀ hpos.ne', mul_one]
  · have hz : D.χ t.1 * D.χ t.2 = 0 := by
      by_cases h1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
      · have h2 : t.2 ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h => ht ⟨h1, h⟩
        rw [cutoff_vanishes_outside_interval D h2, mul_zero]
      · rw [cutoff_vanishes_outside_interval D h1, zero_mul]
    have e : ∀ p, kernel D F F' τ (p, t) = 0 := fun p => by
      unfold kernel
      rw [Bt_zero D F F' p ht, zero_mul]
    rw [← abs_mul, hz]
    simp [e]

theorem betaInfTau_eq_integral (hα : AB k r ≤ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (hcF : InCC α 4 F)
    (hcF' : InCC α 4 F') (hΦ : Integrable (Ph D F F') D.μSS) (τ : ℝ × ℝ) :
    betaInfTau D τ F F' = ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS := by
  obtain ⟨c, hc⟩ := hcF
  obtain ⟨c', hc'⟩ := hcF'
  have hF := admissible_weighted_of_bound hc
  have hF' := admissible_weighted_of_bound hc'
  have H := sqIntegrable_of_threshold D hα
  have := sigmaFinite_μSS D
  have hξ : Continuous (xiTau D τ) := by
    unfold xiTau
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul (first_eigenvalue_continuous D)).sub (continuous_const.mul (continuous_lambda_second_coordinate D)))))
  have hf : Integrable (fun p => xiTau D τ p * Ph D F F' p) D.μSS := by
    refine hΦ.norm.mono' (hξ.aestronglyMeasurable.mul hΦ.1) (Eventually.of_forall fun p => ?_)
    unfold xiTau
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hs := kernel_slice_integral D τ hf
  have hmeas : AEStronglyMeasurable (kernel D F F' τ) (D.μSS.prod volume) := by
    unfold kernel
    refine ((cutBracket_measurable H hF hF').mul (Continuous.stronglyMeasurable ?_)).aestronglyMeasurable
    have hp : Continuous fun q : SS k r × (ℝ × ℝ) => phase D τ q.1 q.2 :=
      (phase_continuous D).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hp))
  have hχ : Integrable D.χ := by
    by_contra h
    have := D.χ_int
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hK : Integrable (kernel D F F' τ) (D.μSS.prod volume) := by
    refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun t => (hs t).1, ?_⟩
    simp only [fun t => (hs t).2.2]
    refine Integrable.mul_const ?_ _
    rw [Measure.volume_eq_prod]
    exact hχ.abs.mul_prod hχ.abs
  rw [betaInfTau_eq_kernel H hF hF', integral_integral_swap (f := fun p t => kernel D F F' τ (p, t)) hK]
  simp only [fun t => (hs t).2.1]
  rw [integral_mul_const, integral_cutoff_product_eq_one, one_mul]

end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem betaInf_eq_integral :
    ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
      [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
      [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)),
      B.AB k r ≤ A → B.InCC A 4 F → Integrable (B.Ph D F F) D.μSS →
      B.betaInf D F F = ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hF hΦ => betaInfTau_eq_integral hA hF hF hΦ (1, 1)

end GlobalTheory.RegularisedIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimir
section
open Formalism.REAL

namespace GlobalTheory

theorem comatrix_last_row_inverts_casimir
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ)
    (hE : GlRel E) (hdet : ∀ w v, qdet E w v = (∏ j, (w + m j)) • v)
    (hOm : ∀ y b, Om y b = ∑ c, E c b (y c)) :
    ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V),
      (∀ u x, K u ((u - 0) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧
      ∀ u v, K u (PiLp.single 2 (Fin.last n) v) =
        qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) v := by
  let Q : ℂ → Fin (n + 1) → Module.End ℂ V := fun u l =>
    (((-1 : ℤ) ^ (n + (l : ℕ)) : ℤ) : Module.End ℂ V) *
      qminor E Fin.castSucc (Fin.succAbove l) (u - 1)
  let K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V) := fun u =>
    ∑ l, (Q u l) ∘ₗ (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) l)
  have hK : ∀ u x, K u x = ∑ l, Q u l (x l) := by
    intro u x
    simp only [K, LinearMap.sum_apply, LinearMap.comp_apply, PiLp.projₗ_apply]
  refine ⟨K, fun u x => ?_, fun u v => ?_⟩
  · have h1 : ∀ l, ((u - 0) • x + Om x) l = ∑ c, Tm E u c l (x c) := by
      intro l
      simp only [Tm, sub_zero, PiLp.add_apply, PiLp.smul_apply, hOm, LinearMap.add_apply,
        Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single l]
      · simp
      · intro c _ hc
        simp [hc]
      · simp
    rw [hK]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [h1, map_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ c, ∑ l, Q u l (Tm E u c l (x c)) =
        (if c = Fin.last n then qdet E u else 0 : Module.End ℂ V) (x c) := by
      intro c
      rw [← capelli_comatrix_last_row _ n E hE u c, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Q, Module.End.mul_apply]
    simp only [h2]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [hdet]
    · intro c _ hc
      simp [hc]
    · simp
  · rw [hK, Finset.sum_eq_single (Fin.last n)]
    · have h3 : qminor E Fin.castSucc Fin.castSucc (u - 1) =
          qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) := by
        simp only [qdet, qminor, Tm, id, Fin.castSucc_inj]
      have h4 : ((-1 : ℤ) ^ (n + n)) = 1 := by
        rw [← two_mul, pow_mul]; simp
      simp only [Q, Fin.succAbove_last, h3, Fin.val_last, h4, Int.cast_one, one_mul,
        PiLp.single_eq_same]
    · intro c _ hc
      simp [PiLp.single_eq_of_ne, hc]
    · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesPropertiesStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedAction_discreteSeries_properties : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ X, PI.UpqRep.InLieHpk k r X → (∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧ HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) 0) ∧ (∀ v ∈ R.sm, ∀ g ∈ GG k r, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (g * X * g⁻¹) (R.σ g v)) ∧ (∀ v, R.KFin v → R.KFin (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) ∧ (∀ v ∈ R.TK, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.TK) ∧ (∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, PI.UpqRep.dsig (k := k) (r := r) R.σ X w⟫_ℂ) := by
  first | exact @GlobalTheory.DerivedAction.derived_action | exact GlobalTheory.DerivedAction.derived_action | (intros; apply GlobalTheory.DerivedAction.derived_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsKTypeNonzeroBesselStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_K_type_nonzero_bessel : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), R.IsDS ε mu → IsBes R z π l → NzOn R l → ∃ v ∈ R.TK, l v ≠ 0 := by
  first | exact @GlobalTheory.bessel_nonzero_on_translates | exact GlobalTheory.bessel_nonzero_on_translates | (intros; apply GlobalTheory.bessel_nonzero_on_translates <;> assumption)
end

