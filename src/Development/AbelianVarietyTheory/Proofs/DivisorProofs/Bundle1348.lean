module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockRepEquivFirst
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DiagCell

theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : Type}
    [Fintype t] [DecidableEq t]
    (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL t R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    have hj := j.isLt
    have hz := h0 b hb
    omega
  · have hi := i.isLt
    have hz := h0 a ha
    omega

theorem eq_one_of_mem_unipRad_single {R : Type} [CommRing R] {β : Type} [Fintype β] [LinearOrder β]
    {n : β → ℕ} {t : Type} [Fintype t] [DecidableEq t] (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) {g : GL t R} (hg : g ∈ unipRad R e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

end GlobalTheory.DiagCell

namespace GlobalTheory.DiagCell

theorem cellFunctor_diag_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : Type} [Fintype m] [DecidableEq m] (b : SizeMatrix (Two (Fin 1) m) (Two (Fin 1) m)),
    b.1 false true = 0 → b.1 true false = 0 →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k (Two (Fin 1) m)) W), IsSmooth ρ →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j),
      Nonempty ((cellFunctor f g ρ).Equiv ρ) := by
  intro k _ _ _ _ m _ _ b h01 h10 W _ _ ρ hsm
  have hrz : ∀ i j, j ≠ i → b.1 i j = 0 := by
    intro i j hj
    cases i <;> cases j <;> simp_all
  have hcz : ∀ j i, i ≠ j → b.1 i j = 0 := fun j i hi => hrz i j (Ne.symm hi)
  have hcard : ∀ i, Fintype.card (Fin (b.1 i i)) = Fintype.card (Two (Fin 1) m i) := by
    intro i
    have r := b.2.1 i
    rw [Fintype.sum_bool] at r
    cases i <;> simp_all
  let E : ∀ i, Fin (b.1 i i) ≃ Two (Fin 1) m i := fun i => Fintype.equivOfCardEq (hcard i)
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i := fun i =>
    (OneBlockCell.valEquiv (n := fun j => b.1 i j) i rfl (fun j hj => hrz i j hj)).trans (E i)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j := fun j =>
    (OneBlockCell.valEquiv (n := fun i => b.1 i j) j rfl (fun i hi => hcz j i hi)).trans (E j)
  refine ⟨f, g, ?_⟩
  have hbot : twKer ρ (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (Two (Fin 1) m)) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) i (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      OneBlockCell.deltaHalf_eq_one_of_single i (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      OneBlockCell.deltaHalf_eq_one_of_single j (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) j (fun i hi => hcz j i hi) (x j)
  have hfg : ∀ i (t : Fin (b.1 i i)), f i ⟨i, t⟩ = g i ⟨i, t⟩ := fun i t => rfl
  have hγ : ∀ (p : relParab k g),
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) =
        (p : Levi k (Two (Fin 1) m)) := by
    intro p
    funext i
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f i).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f i).surjective y
    have ha : a = i := by
      by_contra hne
      have h1 := hrz i a hne
      have h2 := t.2
      omega
    have ha' : a' = i := by
      by_contra hne
      have h1 := hrz i a' hne
      have h2 := s.2
      omega
    subst ha
    subst ha'
    have hsame (z : Levi k (fun j => Fin (b.1 a' j))) (u v : Fin (b.1 a' a')) :
        (leviEmb k (f a') z : Matrix _ _ k) (f a' ⟨a', u⟩) (f a' ⟨a', v⟩) =
          (z a' : Matrix _ _ k) u v := by
      simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
    rw [hsame, hfg, hfg]
    rfl
  let Ψ : W ≃ₗ[ℂ] Jacquet ρ (relUnip k f) := (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk u := fun u => rfl
  let τ := (twist ((relJac f ρ).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) = Ψ (ρ p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ, hγ p]
    simp only [inv_one, Units.val_one, one_smul]
  let F : ρ.IntertwiningMap (cellFunctor f g ρ) :=
    { toFun := fun u => ⟨⟨fun x => Ψ (ρ x u), fun p x => by
          show Ψ (ρ (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : ρ x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ (ρ (y * x) u) = Ψ (ρ y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ (ρ x (ρ h u)) = Ψ (ρ (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ (ρ 1 u) = Ψ (ρ 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ (ρ x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

end GlobalTheory.DiagCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementInfinitePoints
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.LeviArch
open GlobalTheory.LeviPlane
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.LeviArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormCutoffLogWeightLowerBound
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeightLevi

open Complex ComplexConjugate Filter

theorem deriv_zero_of_eqOn {χ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {c : ℝ}
    (h : ∀ s ∈ U, χ s = c) : ∀ s ∈ U, deriv χ s = 0 ∧ deriv (deriv χ) s = 0 := by
  have h1 : ∀ s ∈ U, deriv χ s = 0 := fun s hs => by
    have e : χ =ᶠ[𝓝 s] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hs) h
    rw [e.deriv_eq]; simp
  intro s hs
  refine ⟨h1 s hs, ?_⟩
  have e : deriv χ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := Filter.eventually_of_mem (hU.mem_nhds hs) h1
  rw [e.deriv_eq]; simp

theorem hasDerivAt_logShift {δ s : ℝ} (hs : 0 < s + δ) :
    HasDerivAt (fun s => Real.log ((s + δ) / 2)) (s + δ)⁻¹ s := by
  have h1 : HasDerivAt (fun s : ℝ => (s + δ) / 2) (1 / 2) s :=
    ((hasDerivAt_id' s).add_const δ).div_const 2
  convert h1.log (by positivity) using 1
  field_simp

theorem hasDerivAt_cutLog {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {δ s : ℝ} (hs : 0 < s + δ) :
    HasDerivAt (fun s => χ s * Real.log ((s + δ) / 2))
      (deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹) s := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  exact (hd s).hasDerivAt.mul (hasDerivAt_logShift hs)

theorem derivs_cutLog {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {δ t : ℝ} (ht : 0 < t + δ) :
    deriv (fun s => χ s * Real.log ((s + δ) / 2)) t =
        deriv χ t * Real.log ((t + δ) / 2) + χ t * (t + δ)⁻¹ ∧
      deriv (deriv (fun s => χ s * Real.log ((s + δ) / 2))) t =
        deriv (deriv χ) t * Real.log ((t + δ) / 2) + 2 * deriv χ t * (t + δ)⁻¹ -
          χ t * ((t + δ)⁻¹) ^ 2 := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hd2 : Differentiable ℝ (deriv χ) :=
    (contDiff_infty_iff_deriv.1 hχ).2.differentiable (by simp)
  have hU : Set.Ioi (-δ) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have e : deriv (fun s => χ s * Real.log ((s + δ) / 2)) =ᶠ[𝓝 t]
      fun s => deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹ :=
    Filter.eventually_of_mem hU fun s hs =>
      (hasDerivAt_cutLog hχ (by simp only [Set.mem_Ioi] at hs; linarith)).deriv
  refine ⟨(hasDerivAt_cutLog hχ ht).deriv, ?_⟩
  rw [e.deriv_eq]
  have hinv : HasDerivAt (fun s => (s + δ)⁻¹) (-1 / (t + δ) ^ 2) t :=
    ((hasDerivAt_id' t).add_const δ).inv ht.ne'
  have h : HasDerivAt (fun s => deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹) _ t :=
    ((hd2 t).hasDerivAt.mul (hasDerivAt_logShift ht)).add ((hd t).hasDerivAt.mul hinv)
  rw [h.deriv]
  field_simp
  ring

theorem cutLog_bounds (χ : ℝ → ℝ) (A : ℝ) (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (h1 : ∀ t, t ≤ 1 / 4 → χ t = 1) (h0 : ∀ t, 1 ≤ t → χ t = 0) (hA1 : ∀ t, |deriv χ t| ≤ A)
    (hA2 : ∀ t, |deriv (deriv χ) t| ≤ A) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    -(13 * A + 20) ≤ deriv (fun s => χ s * Real.log ((s + δ) / 2)) t ∧
      -(13 * A + 20) ≤ deriv (fun s => χ s * Real.log ((s + δ) / 2)) t +
        t * deriv (deriv (fun s => χ s * Real.log ((s + δ) / 2))) t := by
  have htd : 0 < t + δ := by linarith
  obtain ⟨e1, e2⟩ := derivs_cutLog hχ htd
  rw [e1, e2]
  have hA : 0 ≤ A := (abs_nonneg _).trans (hA1 0)
  set L := Real.log ((t + δ) / 2)
  set u := (t + δ)⁻¹ with hu_def
  have hu : 0 < u := inv_pos.2 htd
  have htu : t * u ≤ 1 := by
    rw [hu_def, ← div_eq_mul_inv, div_le_one htd]; linarith
  have htu0 : 0 ≤ t * u := mul_nonneg ht hu.le
  have hc0 := h01 t
  have hpos : 0 ≤ χ t * u * (1 - t * u) :=
    mul_nonneg (mul_nonneg hc0.1 hu.le) (by linarith)
  have hexp : deriv χ t * L + χ t * u + t * (deriv (deriv χ) t * L + 2 * deriv χ t * u - χ t * u ^ 2) =
      deriv χ t * L + t * (deriv (deriv χ) t * L) + 2 * (deriv χ t * (t * u)) +
        χ t * u * (1 - t * u) := by ring
  rw [hexp]
  by_cases hc : t < 1 / 4 ∨ 1 < t
  · have hz : deriv χ t = 0 ∧ deriv (deriv χ) t = 0 := by
      rcases hc with hc | hc
      · exact deriv_zero_of_eqOn isOpen_Iio (fun s hs => h1 s (le_of_lt hs)) t hc
      · exact deriv_zero_of_eqOn isOpen_Ioi (fun s hs => h0 s (le_of_lt hs)) t hc
    rw [hz.1, hz.2]
    have : 0 ≤ χ t * u := mul_nonneg hc0.1 hu.le
    constructor <;> nlinarith
  · push_neg at hc
    have hx1 : (t + δ) / 2 ≤ 1 := by linarith
    have hx0 : 1 / 8 ≤ (t + δ) / 2 := by linarith
    have hL0 : L ≤ 0 := Real.log_nonpos (by linarith) hx1
    have hl8 : Real.log (1 / 8) = -(3 * Real.log 2) := by
      rw [show (1 : ℝ) / 8 = ((2 : ℝ) ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
    have hL1 : -3 ≤ L := by
      have := Real.log_le_log (by norm_num) hx0
      have := Real.log_two_lt_d9
      linarith
    have hLabs : |L| ≤ 3 := abs_le.2 ⟨hL1, by linarith⟩
    have b1 : -(3 * A) ≤ deriv χ t * L := by
      have : |deriv χ t * L| ≤ A * 3 := by
        rw [abs_mul]; exact mul_le_mul (hA1 t) hLabs (abs_nonneg _) hA
      linarith [neg_abs_le (deriv χ t * L)]
    have b2 : -(3 * A) ≤ t * (deriv (deriv χ) t * L) := by
      have : |t * (deriv (deriv χ) t * L)| ≤ 1 * (A * 3) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht]
        exact mul_le_mul (by linarith) (mul_le_mul (hA2 t) hLabs (abs_nonneg _) hA)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
      linarith [neg_abs_le (t * (deriv (deriv χ) t * L))]
    have b3 : -A ≤ deriv χ t * (t * u) := by
      have : |deriv χ t * (t * u)| ≤ A * 1 := by
        rw [abs_mul, abs_of_nonneg htu0]
        exact mul_le_mul (hA1 t) htu htu0 hA
      linarith [neg_abs_le (deriv χ t * (t * u))]
    have : 0 ≤ χ t * u := mul_nonneg hc0.1 hu.le
    constructor <;> nlinarith

theorem normSq_sum_conj_mul_le {n : ℕ} (a b : Fin n → ℂ) :
    Complex.normSq (∑ m, conj (a m) * b m) ≤
      (∑ m, Complex.normSq (a m)) * ∑ m, Complex.normSq (b m) := by
  have h1 : ‖∑ m, conj (a m) * b m‖ ≤ ∑ m, ‖a m‖ * ‖b m‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ => by
      rw [norm_mul, Complex.norm_conj]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun m => ‖a m‖) (fun m => ‖b m‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ m, conj (a m) * b m‖ ^ 2 ≤ (∑ m, ‖a m‖ * ‖b m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem levi_cutLog_lower : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) →
    (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) →
    (∀ t, |deriv (deriv χ) t| ≤ A) → ∀ (n : ℕ) (ρ δ : ℝ), 0 < ρ → 0 < δ → δ ≤ 1 →
    ∀ (z : V n) (ξ : Fin n → ℂ), -((13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) ≤
      (leviV n (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ))
        z ξ).re := by
  intro χ A hχ h01 h1 h0 hA1 hA2 n ρ δ hρ hδ hδ1 z ξ
  set k : ℝ → ℝ := fun s => χ s * Real.log ((s + δ) / 2) with hk
  let L : Fin n → V n →L[ℂ] ℂ := fun j => ((ρ : ℂ)⁻¹) • EuclideanSpace.proj j
  have hLapp : ∀ j y, L j y = (ρ : ℂ)⁻¹ * y j := fun j y => by simp [L]
  set v : V n → ℝ := fun y => ∑ j, Complex.normSq (L j y) with hvdef
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hv : ∀ y : V n, ‖y‖ ^ 2 / ρ ^ 2 = v y := by
    intro y
    simp only [hvdef, hLapp, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal,
      EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    field_simp
  have hfun : (fun w : V n => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ))
      = fun w => ((k (v w) : ℝ) : ℂ) := by
    funext w; rw [hv w]
  rw [hfun]
  have hLc : ∀ j, ContDiffAt ℂ 2 (fun y => L j y) z := fun j => (L j).contDiff.contDiffAt
  have hu : ∀ j, ContDiffAt ℝ 2 (fun y => Complex.normSq (L j y)) z := fun j =>
    H.contDiffAt_normSq_comp (hLc j)
  have hvC : ContDiffAt ℝ 2 v z := ContDiffAt.sum fun j _ => hu j
  have ht0 : 0 ≤ v z := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hkC : ContDiffAt ℝ 2 k (v z) := by
    have hχ2 : ContDiffAt ℝ 2 χ (v z) := hχ.contDiffAt.of_le (by norm_cast)
    exact hχ2.mul (((contDiffAt_id.add contDiffAt_const).div_const (2 : ℝ)).log
      (by simp only [id]; positivity))
  rw [H.leviChain n k v z ξ hvC hkC]
  have hwdL : ∀ j m, wd n m (fun y => L j y) z = (ρ : ℂ)⁻¹ * (if j = m then 1 else 0) := by
    intro j m
    rw [wd_of_differentiableAt (L j).differentiableAt, (L j).fderiv, hLapp]
    simp [bas, PiLp.single_apply]
  have hLevi : leviV n (fun y => ((v y : ℝ) : ℂ)) z ξ =
      ((∑ j, Complex.normSq ((ρ : ℂ)⁻¹ * ξ j) : ℝ) : ℂ) := by
    rw [show (fun y => ((v y : ℝ) : ℂ)) = fun y => ((∑ j, Complex.normSq (L j y) : ℝ) : ℂ) from rfl,
      H.leviV_ofReal_sum hu, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.leviV_normSq_comp (hLc j)]
    simp [hwdL]
  have hwd : ∀ m, wd n m (fun y => ((v y : ℝ) : ℂ)) z = (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) := by
    intro m
    rw [show (fun y => ((v y : ℝ) : ℂ)) = fun y => ((∑ j, Complex.normSq (L j y) : ℝ) : ℂ) from rfl,
      H.wd_ofReal_sum (fun j => (hu j).differentiableAt (by simp))]
    refine (Finset.sum_congr rfl fun j _ => by rw [H.wd_normSq_comp (hLc j), hwdL]).trans ?_
    simp [hLapp]
  rw [hLevi]
  simp only [hwd]
  set P := ∑ j, Complex.normSq ((ρ : ℂ)⁻¹ * ξ j) with hP
  set N := Complex.normSq (∑ m, (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) * ξ m) with hN
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hNt : N ≤ v z * P := by
    have e : ∑ m, (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) * ξ m =
        ∑ m, conj ((ρ : ℂ)⁻¹ * z m) * ((ρ : ℂ)⁻¹ * ξ m) :=
      Finset.sum_congr rfl fun m _ => by ring
    have ev : v z = ∑ m, Complex.normSq ((ρ : ℂ)⁻¹ * z m) :=
      Finset.sum_congr rfl fun m _ => by rw [hLapp]
    rw [hN, e, ev, hP]
    exact normSq_sum_conj_mul_le _ _
  have hPe : (13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 = (13 * A + 20) * P := by
    rw [hP, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    field_simp
  rw [hPe]
  obtain ⟨b1, b2⟩ := cutLog_bounds χ A hχ h01 h1 h0 hA1 hA2 hδ hδ1 ht0
  by_cases hs : 0 ≤ deriv (deriv k) (v z)
  · have := mul_le_mul_of_nonneg_right b1 hP0
    have := mul_nonneg hs hN0
    nlinarith
  · push_neg at hs
    have h3 : deriv (deriv k) (v z) * (v z * P) ≤ deriv (deriv k) (v z) * N :=
      mul_le_mul_of_nonpos_left hNt hs.le
    have := mul_le_mul_of_nonneg_right b2 hP0
    nlinarith

end GlobalTheory.PeakWeightLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvAt0.PolD

variable {F : Type} [Field F] [NumberField F]

def linL {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ
      ∑ i, (LinearMap.mulRight ℝ (b i)) ∘ₗ LinearMap.proj i)

theorem linL_apply {κ : Type} [Fintype κ] (b x : κ → mixedEmbedding.mixedSpace F) :
    linL b x = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * b i) := by
  simp [linL]

def lin {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) (x : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * b i) : ℝ) : ℂ)

theorem lin_hasTemperateGrowth {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) :
    (lin b).HasTemperateGrowth := by
  have e : lin b = ⇑(Complex.ofRealCLM.comp (linL b)) := by
    funext x; simp [lin, linL_apply]
  rw [e]
  exact (Complex.ofRealCLM.comp (linL b)).hasTemperateGrowth

def mulOp {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →L[ℂ] SInf F κ :=
  SchwartzMap.smulLeftCLM ℂ (lin b)

theorem mulOp_apply {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (x : κ → mixedEmbedding.mixedSpace F) : mulOp b f x = lin b x * f x := by
  simp [mulOp, SchwartzMap.smulLeftCLM_apply_apply (lin_hasTemperateGrowth b)]

def dOp {κ : Type} [Fintype κ] (a b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →L[ℂ] SInf F κ :=
  LineDeriv.lineDerivOpCLM ℂ (SInf F κ) a - ((2 * Real.pi * Complex.I : ℂ)) • mulOp b

theorem dOp_apply {κ : Type} [Fintype κ] (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (x : κ → mixedEmbedding.mixedSpace F) :
    dOp a b f x = fderiv ℝ f x a - 2 * Real.pi * Complex.I * lin b x * f x := by
  simp [dOp, mulOp_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

def arc {κ : Type} (c : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (c i)

def liftA (v : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v)

theorem evI_liftA (v : mixedEmbedding.mixedSpace F) : evI F (liftA v) = v := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v) = v
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply v

theorem smul_liftA {c : AF F} (hc : evI F c = 0) (v : mixedEmbedding.mixedSpace F) : c • liftA v = 0 := by
  have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hc)
  have key : ∀ x y : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F, x.1 = 0 → y.2 = 0 → x * y = 0 :=
    fun x y hx hy => Prod.ext (by simp [hx]) (by simp [hy])
  exact key c (liftA v) h1 rfl

variable {n d d₁ : ℕ}

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def GaussD {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (g : SInf F (Fin n × Fin d)) : Prop :=
  ∃ ε : InfinitePlace F → ℤˣ, ∀ u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    dOp (arc (M.co.e u').1) (arc (M.co.e u').2) g = Complex.I • dOp (arc (M.co.e u).1) (arc (M.co.e u).2) g

end GlobalTheory.ThK.EvAt0.PolD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetAdelicGLExistsCompactDecompositionStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : Set (AdelicGLn.AdelicGL E a)), IsCompact ω → ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) → ∀ t : ℝ, 0 < t → ∃ (Ω : Set (GL (Fin a) (Cinf E))) (Kf : Set (GL (Fin a) (Af E))), IsCompact Ω ∧ IsCompact Kf ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, ∀ k ∈ maxCompact (K := E) (n := a), ∃ c ∈ Ω, ∃ f ∈ Kf, b * infGL E a d * k = infGL E a (d * c) * finGL E a f := by
  first | exact @GlobalTheory.SiegelSetGL.exists_compact_decomp | exact GlobalTheory.SiegelSetGL.exists_compact_decomp | (intros; apply GlobalTheory.SiegelSetGL.exists_compact_decomp <;> assumption)
end

