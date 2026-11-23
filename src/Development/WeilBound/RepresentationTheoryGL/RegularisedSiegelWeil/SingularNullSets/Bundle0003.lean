module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0001
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LmajASeq
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Convex.Cone.Extension

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKB
section
namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cj_smul {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (r : R) (M : Matrix m p R) :
    cj s (r • M) = s r • cj s M := by
  ext i j; simp [cj]

theorem map_cj {R S : Type} [CommRing R] [CommRing S] (σ : R →+* R) (s : S →+* S) (π : R →+* S)
    (h : ∀ x, π (σ x) = s (π x)) {m p : Type} (M : Matrix m p R) : (cj σ M).map π = cj s (M.map π) := by
  ext i j; simp [cj, h]

theorem det_jacobi {R : Type} [CommRing R] (σ : R →+* R) (a b0 c d b : Matrix n n R)
    (R1 : a * cj σ d - b0 * cj σ c = 1) (R2 : c * cj σ d = d * cj σ c) (hb : cj σ b = b) :
    (fromBlocks a (a * b + b0) c (d + c * b)).det * (cj σ (d + c * b)).det = (d + c * b).det := by
  have hu : cj σ (d + c * b) = cj σ d + b * cj σ c := by rw [cj_add, cj_mul, hb]
  have e : fromBlocks a (a * b + b0) c (d + c * b) * fromBlocks (cj σ (d + c * b)) 0 (-cj σ c) 1 =
      fromBlocks 1 (a * b + b0) 0 (d + c * b) := by
    rw [fromBlocks_multiply, hu]
    congr 1
    · rw [← R1]; noncomm_ring
    · simp
    · calc c * (cj σ d + b * cj σ c) + (d + c * b) * -cj σ c = c * cj σ d - d * cj σ c := by noncomm_ring
        _ = 0 := by rw [R2, sub_self]
    · simp
  have := congrArg Matrix.det e
  rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] at this
  simpa using this

theorem core {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (𝔭 : Ideal R) [h𝔭 : 𝔭.IsMaximal]
    (h2 : IsUnit (2 : R)) (hU : ∀ x, x ∉ 𝔭 → σ x ∉ 𝔭 → IsUnit x) (a b0 c d : Matrix n n R)
    (R1 : a * cj σ d - b0 * cj σ c = 1) (R2 : c * cj σ d = d * cj σ c) (R3 : d * cj σ a - c * cj σ b0 = 1) :
    ∃ b : Matrix n n R, cj σ b = b ∧ IsUnit (d + c * b).det := by
  letI : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  set π : R →+* R ⧸ 𝔭 := Ideal.Quotient.mk 𝔭 with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  set lift : R ⧸ 𝔭 → R := Function.surjInv hsurj with hlift
  have hl : ∀ y, π (lift y) = y := Function.surjInv_eq hsurj
  have hXY : c * (-cj σ b0) + d * cj σ a = 1 := by rw [← R3]; noncomm_ring
  have hXY' : c.map π * (-cj σ b0).map π + d.map π * (cj σ a).map π = 1 := by
    have := congrArg π.mapMatrix hXY
    simpa only [map_add (f := _), map_mul, map_one, RingHom.mapMatrix_apply] using this
  have key : ∃ b : Matrix n n R, cj σ b = b ∧ (d + c * b).det ∉ 𝔭 := by
    have hdet : ∀ b : Matrix n n R, ((d + c * b).map π).det ≠ 0 → (d + c * b).det ∉ 𝔭 := by
      intro b hb hm
      apply hb
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hm
      rw [← hm, RingHom.map_det]; rfl
    by_cases hst : ∀ x ∈ 𝔭, σ x ∈ 𝔭
    · set s : R ⧸ 𝔭 →+* R ⧸ 𝔭 := Ideal.quotientMap 𝔭 σ (fun x hx => hst x hx) with hs
      have hsπ : ∀ x, π (σ x) = s (π x) := fun x => (Ideal.quotientMap_mk).symm
      have hss : ∀ y, s (s y) = y := by
        intro y; obtain ⟨x, rfl⟩ := hsurj y; rw [← hsπ, ← hsπ, hσ]
      have hlag : c.map π * cj s (d.map π) = d.map π * cj s (c.map π) := by
        rw [← map_cj σ s π hsπ, ← map_cj σ s π hsπ]
        have := congrArg π.mapMatrix R2
        simpa only [map_mul, RingHom.mapMatrix_apply] using this
      obtain ⟨B, hBh, hBd⟩ := fieldA s hss _ _ _ _ hXY' hlag
      set B' := B.map lift with hB'
      refine ⟨(↑h2.unit⁻¹ : R) • (B' + cj σ B'), ?_, hdet _ ?_⟩
      · have hinv : σ (↑h2.unit⁻¹ : R) = ↑h2.unit⁻¹ := by
          have e1 : σ (↑h2.unit⁻¹ : R) * 2 = 1 := by
            have : σ ((↑h2.unit⁻¹ : R) * 2) = 1 := by
              rw [show (↑h2.unit⁻¹ : R) * 2 = ↑h2.unit⁻¹ * ↑h2.unit from rfl, Units.inv_mul, map_one]
            rwa [map_mul, map_ofNat] at this
          calc σ (↑h2.unit⁻¹ : R) = σ (↑h2.unit⁻¹ : R) * (2 * ↑h2.unit⁻¹) := by
                rw [show (2 : R) * ↑h2.unit⁻¹ = ↑h2.unit * ↑h2.unit⁻¹ from rfl, Units.mul_inv, mul_one]
            _ = ↑h2.unit⁻¹ := by rw [← mul_assoc, e1, one_mul]
        rw [cj_smul, cj_add, cj_cj σ hσ, hinv, add_comm]
      · have hmap : ((↑h2.unit⁻¹ : R) • (B' + cj σ B')).map π = B := by
          ext i j
          have hij := congrFun (congrFun hBh i) j
          rw [cj_apply] at hij
          have h2π : π (↑h2.unit⁻¹ : R) * 2 = 1 := by
            rw [← map_ofNat π 2, ← map_mul, show (↑h2.unit⁻¹ : R) * 2 = ↑h2.unit⁻¹ * ↑h2.unit from rfl,
              Units.inv_mul, map_one]
          simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_mul, map_add (f := _), cj_apply,
            hB', hsπ, hl, hij]
          linear_combination (B i j) * h2π
        have : (d + c * ((↑h2.unit⁻¹ : R) • (B' + cj σ B'))).map π = d.map π + c.map π * B := by
          rw [← hmap]; simp [Matrix.map_add (f := _), Matrix.map_mul]
        rw [this]; exact hBd
    · push_neg at hst
      obtain ⟨y, hy, hσy⟩ := hst
      obtain ⟨r, i, hi, hri⟩ := h𝔭.exists_inv hσy
      obtain ⟨B, hBd⟩ := fieldB _ _ _ _ hXY'
      set B' := B.map lift with hB'
      set x := r * σ y with hx
      have hπx : π x = 1 := by
        have : π (x + i) = 1 := by rw [hx, hri, map_one]
        rwa [map_add, (Ideal.Quotient.eq_zero_iff_mem).2 hi, add_zero] at this
      have hπσx : π (σ x) = 0 := by
        rw [hx, map_mul, hσ, map_mul, (Ideal.Quotient.eq_zero_iff_mem).2 hy, mul_zero]
      refine ⟨x • B' + cj σ (x • B'), ?_, hdet _ ?_⟩
      · rw [cj_add, cj_cj σ hσ, add_comm]
      · have hmap : (x • B' + cj σ (x • B')).map π = B := by
          ext i j
          simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cj_apply, map_add (f := _), map_mul,
            hπx, hπσx, hB', hl]
          ring
        have : (d + c * (x • B' + cj σ (x • B'))).map π = d.map π + c.map π * B := by
          rw [← hmap]; simp [Matrix.map_add (f := _), Matrix.map_mul]
        rw [this]; exact hBd
  obtain ⟨b, hb, hb𝔭⟩ := key
  refine ⟨b, hb, hU _ hb𝔭 fun hσ𝔭 => hb𝔭 ?_⟩
  rw [← det_jacobi σ a b0 c d b R1 R2 hb, det_cj]
  exact Ideal.mul_mem_left _ _ hσ𝔭

end PositivityTheory.Rg.Rsw.L.LGenK
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorA
section
noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

open Metric
open scoped ContDiff

theorem schMajor {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}
    (f : Fin k → SchwartzMap V ℂ) :
    ∃ F₀ : SchwartzMap V ℂ, (∀ y, 0 ≤ (F₀ y).re ∧ (F₀ y).im = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : V → ℂ, c.HasTemperateGrowth ∧ HasCompactSupport c ∧
        ∀ i y, ‖f i y‖ * ‖1 - c y‖ ≤ ε * (F₀ y).re := by
  classical
  set e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean with he
  set q : V → ℝ := fun y => ‖e y‖ ^ 2 with hqdef
  have hqy : ∀ y, q y = ‖e y‖ ^ 2 := fun y => rfl
  have hq0 : ∀ y, 0 ≤ q y := fun y => by rw [hqy]; positivity
  have hq : q.HasTemperateGrowth :=
    (Function.hasTemperateGrowth_norm_sq (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))).comp
      e.hasTemperateGrowth
  have hq_upper : ∃ (k : ℕ) (C : ℝ), ∀ y, ‖y‖ ≤ C * (1 + ‖q y‖) ^ k := by
    refine ⟨1, ‖(e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)‖, fun y => ?_⟩
    have h1 : ‖y‖ ≤ ‖(e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)‖ * ‖e y‖ := by
      have := (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V).le_opNorm (e y)
      simpa using this
    have h2 : ‖e y‖ ≤ 1 + ‖q y‖ := by
      rw [Real.norm_of_nonneg (hq0 y), hqy]
      nlinarith [sq_nonneg (‖e y‖ - 1), norm_nonneg (e y)]
    rw [pow_one]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have hqA : ∀ y, q y ≤ ‖(e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))‖ ^ 2 * ‖y‖ ^ 2 := by
    intro y
    rw [hqy, ← mul_pow]
    have := (e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))).le_opNorm y
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using this) 2
  obtain ⟨b, hb0, hbs, hbε⟩ := lmajASeq f q hq0 _ (sq_nonneg _) hqA
  obtain ⟨h, hh0, hhb⟩ := lmajASeqSchwartz b hb0 hbs
  set F₀ : SchwartzMap V ℂ := SchwartzMap.compCLM ℝ hq hq_upper h with hF₀
  have hF : ∀ y, F₀ y = h (q y) := fun y => rfl
  refine ⟨F₀, fun y => by rw [hF]; exact hh0 _, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hbε ε hε
  let β : ContDiffBump (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
    ⟨(N : ℝ) + 1, (N : ℝ) + 2, by positivity, by linarith⟩
  set c : V → ℂ := fun y => ((β (e y) : ℝ) : ℂ) with hc
  have hcd : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp ((β.contDiff).comp e.contDiff)
  have hcs : HasCompactSupport c :=
    (β.hasCompactSupport.comp_homeomorph e.toHomeomorph).comp_left Complex.ofReal_zero
  refine ⟨c, hcs.hasTemperateGrowth hcd, hcs, fun i y => ?_⟩
  have hF0 : 0 ≤ (F₀ y).re := by rw [hF]; exact (hh0 _).1
  by_cases hy : ‖e y‖ ≤ (N : ℝ) + 1
  · have hβ : β (e y) = 1 :=
      β.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hy)
    have hc1 : c y = 1 := by simp [hc, hβ]
    rw [hc1, sub_self, norm_zero, mul_zero]
    exact mul_nonneg hε.le hF0
  · push Not at hy
    have hqN : (N : ℝ) ≤ q y := by
      rw [hqy]
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have h1c : ‖1 - c y‖ ≤ 1 := by
      have : (1 : ℂ) - c y = ((1 - β (e y) : ℝ) : ℂ) := by simp [hc]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [β.nonneg (x := e y), β.le_one (x := e y)]
    have hqn : |q y - (⌊q y⌋₊ : ℝ)| ≤ 1 := by
      have h1 := Nat.floor_le (hq0 y)
      have h2 := Nat.lt_floor_add_one (q y)
      rw [abs_le]; constructor <;> linarith
    calc ‖f i y‖ * ‖1 - c y‖ ≤ ‖f i y‖ := mul_le_of_le_one_right (norm_nonneg _) h1c
      _ ≤ ε * b ⌊q y⌋₊ := hN i y hqN
      _ ≤ ε * (F₀ y).re := by rw [hF]; exact mul_le_mul_of_nonneg_left (hhb _ _ hqn) hε.le

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExtB
section
noncomputable section

open Set MeasureTheory CompactlySupported

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X]

theorem est {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {G h : X → ℂ}
    (hG : Integrable G μ) (hh : Integrable h μ) {C : ℝ} (hoff : ∀ x ∉ K, G x - h x = 0)
    (hon : ∀ x ∈ K, ‖G x - h x‖ ≤ C) : ‖∫ x, G x ∂μ - ∫ x, h x ∂μ‖ ≤ C * μ.real K := by
  rw [← integral_sub hG hh, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun x hx => hoff x hx)]
  exact norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hon

variable [BorelSpace X]

theorem uniq (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    (ν ν' : Measure X) [IsFiniteMeasureOnCompacts ν] [IsFiniteMeasureOnCompacts ν']
    (heq : ∀ f ∈ A, ∫ x, f x ∂ν = ∫ x, f x ∂ν') (g : C_c(X, ℝ)) : ∫ x, g x ∂ν = ∫ x, g x ∂ν' := by
  obtain ⟨b, hbA, -, hb1⟩ := hbump (tsupport g) g.hasCompactSupport
  obtain ⟨B, hB⟩ := (hA b hbA).1.bounded_above_of_compact_support (hA b hbA).2
  have hK : IsCompact (tsupport b) := (hA b hbA).2
  have hbK : ∀ x ∉ tsupport b, b x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  let G : X → ℂ := fun x => (g x : ℂ)
  have hG : Continuous G := Complex.continuous_ofReal.comp g.continuous
  have hGc : HasCompactSupport G := g.hasCompactSupport.comp_left Complex.ofReal_zero
  have hGb : ∀ x, G x ≠ 0 → b x = 1 := fun x hx =>
    hb1 x (subset_tsupport _ (by simpa [G, Function.mem_support] using hx))
  have hGK : ∀ x ∉ tsupport b, G x = 0 := by
    intro x hx
    by_contra h0
    have := hGb x h0
    rw [hbK x hx] at this
    exact zero_ne_one this
  have key : ∫ x, G x ∂ν - ∫ x, G x ∂ν' = 0 := by
    apply zero_of_le _ (B * (ν.real (tsupport b) + ν'.real (tsupport b)))
    intro ε hε
    obtain ⟨h, hhA, hh⟩ := approx A (fun f hf => (hA f hf).1) hmul hstar hsep hK hbA hbK hG hGb hε
    have hoff : ∀ x ∉ tsupport b, G x - h x = 0 := by
      intro x hx
      have := hh x
      rw [hbK x hx, norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] at this
      rw [this, sub_self]
    have hon : ∀ x ∈ tsupport b, ‖G x - h x‖ ≤ ε * B := by
      intro x _
      rw [norm_sub_rev]
      exact (hh x).trans (mul_le_mul_of_nonneg_left (hB x) hε.le)
    have hGi : ∀ μ : Measure X, IsFiniteMeasureOnCompacts μ → Integrable G μ :=
      fun μ _ => hG.integrable_of_hasCompactSupport hGc
    have hhi : ∀ μ : Measure X, IsFiniteMeasureOnCompacts μ → Integrable h μ :=
      fun μ _ => (hA h hhA).1.integrable_of_hasCompactSupport (hA h hhA).2
    have e1 := est hK (hGi ν inferInstance) (hhi ν inferInstance) hoff hon
    have e2 := est hK (hGi ν' inferInstance) (hhi ν' inferInstance) hoff hon
    have : ∫ x, G x ∂ν - ∫ x, G x ∂ν' = (∫ x, G x ∂ν - ∫ x, h x ∂ν) - (∫ x, G x ∂ν' - ∫ x, h x ∂ν') := by
      rw [heq h hhA]; ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    nlinarith [e1, e2]
  have h2 : ((∫ x, g x ∂ν : ℝ) : ℂ) = ((∫ x, g x ∂ν' : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    exact sub_eq_zero.mp key
  exact_mod_cast h2

theorem uniq' [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    (ν ν' : Measure X) (hν : IsFiniteMeasureOnCompacts ν) (hν' : IsFiniteMeasureOnCompacts ν')
    (heq : ∀ f ∈ A, ∫ x, f x ∂ν = ∫ x, f x ∂ν') : ν = ν' :=
  Measure.ext_of_integral_eq_on_compactlySupported (uniq A hA hmul hstar hsep hbump ν ν' heq)

end PositivityTheory.Rg.Rsw.L.LPosExt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExtC
section
noncomputable section

open Set MeasureTheory CompactlySupported

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X]

def AR (A : Submodule ℂ (X → ℂ)) : Submodule ℝ (X → ℂ) where
  carrier := {f | f ∈ A ∧ ∀ x, (f x).im = 0}
  add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨A.add_mem ha hb, fun x => by simp [ha' x, hb' x]⟩
  zero_mem' := ⟨A.zero_mem, fun x => by simp⟩
  smul_mem' c f := fun ⟨hf, hf'⟩ => ⟨by
      have : c • f = (c : ℂ) • f := by ext x; simp [Complex.real_smul]
      rw [this]; exact A.smul_mem _ hf, fun x => by simp [hf' x]⟩

def reC (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f) :
    AR A →ₗ[ℝ] C_c(X, ℝ) where
  toFun f := ⟨⟨fun x => (f.1 x).re, Complex.continuous_re.comp (hA _ f.2.1).1⟩,
    (hA _ f.2.1).2.comp_left Complex.zero_re⟩
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

theorem reC_inj (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f) :
    Function.Injective (reC A hA) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  have h := congrArg (fun u : C_c(X, ℝ) => u x) hfg
  simp only [reC, LinearMap.coe_mk, AddHom.coe_mk] at h
  exact Complex.ext h ((f.2.2 x).trans (g.2.2 x).symm)

def reL (A : Submodule ℂ (X → ℂ)) (L : A →ₗ[ℂ] ℂ) : AR A →ₗ[ℝ] ℝ where
  toFun f := (L ⟨f.1, f.2.1⟩).re
  map_add' f g := by
    have : (⟨(f + g).1, (f + g).2.1⟩ : A) = ⟨f.1, f.2.1⟩ + ⟨g.1, g.2.1⟩ := rfl
    simp only [this, map_add (f := _), Complex.add_re]
  map_smul' c f := by
    have : (⟨(c • f).1, (c • f).2.1⟩ : A) = (c : ℂ) • ⟨f.1, f.2.1⟩ := by
      apply Subtype.ext; ext x; simp [Complex.real_smul]
    simp only [this, map_smul, smul_eq_mul, Complex.re_ofReal_mul, RingHom.id_apply]

theorem dom (A : Submodule ℂ (X → ℂ))
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    {y : X → ℝ} (hy : Continuous y) (hyc : HasCompactSupport y) :
    ∃ b ∈ A, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x, 0 ≤ M * (b x).re + y x ∧ 0 ≤ M * (b x).re - y x := by
  obtain ⟨b, hbA, hb0, hb1⟩ := hbump (tsupport y) hyc
  obtain ⟨C, hC⟩ := hy.bounded_above_of_compact_support hyc
  refine ⟨b, hbA, hb0, max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport y
  · rw [hb1 x hx, Complex.one_re, mul_one]
    have := hC x
    rw [Real.norm_eq_abs] at this
    constructor <;> linarith [abs_le.mp this, le_max_left C 0]
  · rw [image_eq_zero_of_notMem_tsupport hx]
    have := mul_nonneg (le_max_right C 0) (hb0 x).1
    constructor <;> linarith

end PositivityTheory.Rg.Rsw.L.LPosExt
end
end

