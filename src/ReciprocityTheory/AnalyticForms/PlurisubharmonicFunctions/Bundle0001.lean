module

public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog
section
namespace ReciprocityTheory.AnForm.A

open Complex Filter Topology

noncomputable section

variable {D : ℕ}

theorem hessC_congr' {φ ψ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    hessC φ z = hessC ψ z := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ :=
    h.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq
  have h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := h1.fderiv_eq
  ext i j
  simp only [hessC, h2]

theorem hessC_eq_zero_of_re_bilin (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (B : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ)
    (hB : ∀ v u, fderiv ℝ (fderiv ℝ φ) z v u = (B v u).re) : hessC φ z = 0 := by
  ext i j
  simp only [hessC, hB, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Matrix.zero_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf
  simp

theorem hessC_add' (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  have hφ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ φ w :=
    (hφ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hψ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ ψ w :=
    (hψ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hE : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w :=
    (hφ'.and hψ').mono fun w hw => fderiv_add hw.1 hw.2
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdψ : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) z =
      fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z := by
    rw [hE.fderiv_eq]
    exact fderiv_add hdφ hdψ
  ext i j
  simp only [hessC, h2, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring

private lemma fderiv_re_apply_lemma (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hg : DifferentiableAt ℂ g z) (v : Fin D → ℂ) :
    fderiv ℝ (fun w => (g w).re) z v = (fderiv ℂ g z v).re := by
  have h : HasFDerivAt (fun w => (g w).re)
      (Complex.reCLM.comp ((fderiv ℂ g z).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hg.hasFDerivAt.restrictScalars ℝ)
  rw [h.fderiv]
  rfl

theorem fderiv_fderiv_re_analytic (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z)
    (v u : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fun w => (G w).re)) z v u = (fderiv ℂ (fderiv ℂ G) z v u).re := by
  have hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)
  have hdΦ : DifferentiableAt ℝ (fderiv ℝ (fun w => (G w).re)) z :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ G w := hG.eventually_analyticAt
  have hE : (fun w => fderiv ℝ (fun w => (G w).re) w u) =ᶠ[𝓝 z]
      fun w => (fderiv ℂ G w u).re :=
    hA.mono fun w hw => fderiv_re_apply_lemma G w hw.differentiableAt u
  have hdG : DifferentiableAt ℂ (fun w => fderiv ℂ G w u) z :=
    (hG.fderiv.differentiableAt).clm_apply (differentiableAt_const u)
  have h1 : fderiv ℝ (fderiv ℝ (fun w => (G w).re)) z v u =
      fderiv ℝ (fun w => fderiv ℝ (fun w => (G w).re) w u) z v := by
    rw [fderiv_clm_apply hdΦ (differentiableAt_const u)]
    simp
  have h2 : fderiv ℂ (fun w => fderiv ℂ G w u) z v = fderiv ℂ (fderiv ℂ G) z v u := by
    rw [fderiv_clm_apply (hG.fderiv.differentiableAt) (differentiableAt_const u)]
    simp
  rw [h1, hE.fderiv_eq, fderiv_re_apply_lemma _ z hdG v, h2]

theorem hessC_re_analytic' (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => (G w).re) z = 0 := hessC_eq_zero_of_re_bilin _ z _ (fderiv_fderiv_re_analytic G z hG)

theorem hessC_add_re_analytic' (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by
  have hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)
  rw [hessC_add' φ _ z hφ hΦ, hessC_re_analytic' G z hG, add_zero]

theorem exists_re_analytic_eq_log_norm (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticAt ℂ G z ∧
      (fun w => Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => (G w).re := by
  refine ⟨fun w => Complex.log (g w / g z) + Complex.log (g z), ?_, ?_⟩
  · refine AnalyticAt.add ?_ analyticAt_const
    refine (hg.div analyticAt_const hz).clog ?_
    show g z / g z ∈ Complex.slitPlane
    rw [div_self hz]
    exact Complex.one_mem_slitPlane
  · filter_upwards [hg.continuousAt.eventually_ne hz] with w hw
    simp only [Complex.add_re, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 hz)]
    ring

theorem hessC_log_norm' (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by
  obtain ⟨G, hG, hEq⟩ := exists_re_analytic_eq_log_norm g z hg hz
  rw [hessC_congr' hEq]
  exact hessC_re_analytic' G z hG

theorem hessC_add_log_norm' (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by
  obtain ⟨G, hG, hEq⟩ := exists_re_analytic_eq_log_norm g z hg hz
  have h2 : (fun w => φ w + Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => φ w + (G w).re :=
    hEq.mono fun w hw => by simp only [hw]
  rw [hessC_congr' h2]
  exact hessC_add_re_analytic' φ G z hφ hG

end

end ReciprocityTheory.AnForm.A
end

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory

open scoped ContDiff

noncomputable section

def hypIncl {n : ℕ} (w : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons (0 : ℂ) w

theorem hypIncl_zero {n : ℕ} (w : Fin n → ℂ) : hypIncl w 0 = 0 := rfl

def PoincareLelongData {n : ℕ} (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) : Prop :=
  IsOpen U ∧ ContDiff ℝ 3 v ∧ HasCompactSupport v ∧ tsupport v ⊆ U ∧
    ∀ k, ContDiffOn ℝ ∞ (φ k) U

def densV {n : ℕ} (v : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) : ℝ :=
  maDens (D := n + 1) (Fin.cons v φ) z

def densHyp {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (w : Fin n → ℂ) : ℝ :=
  maDens (D := n) (fun k => φ k ∘ hypIncl) w

def PoincareLelongHyperplane : Prop :=
  ∀ (n : ℕ) (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ), PoincareLelongData U v φ →
    Integrable (fun z => Real.log ‖z 0‖ * densV v φ z) volume ∧
    Integrable (fun w => v (hypIncl w) * densHyp φ w) volume ∧
    ∫ z, Real.log ‖z 0‖ * densV v φ z = ∫ w, v (hypIncl w) * densHyp φ w

def PoincareLelongUnitPower : Prop :=
  ∀ (n : ℕ) (m : ℤ) (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (u : (Fin (n + 1) → ℂ) → ℂ), PoincareLelongData U v φ →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    Integrable (fun z => Real.log ‖z 0 ^ m * u z‖ * densV v φ z) volume ∧
    ∫ z, Real.log ‖z 0 ^ m * u z‖ * densV v φ z = (m : ℝ) * ∫ w, v (hypIncl w) * densHyp φ w

def hypInclAt {n : ℕ} (i : Fin (n + 1)) (w : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) i 0 w

def densHypAt {n : ℕ} (i : Fin (n + 1)) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (w : Fin n → ℂ) : ℝ :=
  maDens (D := n) (fun k => φ k ∘ hypInclAt i) w

def PoincareLelongNormalCrossing : Prop :=
  ∀ (n : ℕ) (m : Fin (n + 1) → ℤ) (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (u : (Fin (n + 1) → ℂ) → ℂ), PoincareLelongData U v φ →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    Integrable (fun z => Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z) volume ∧
    ∫ z, Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z =
      ∑ i, (m i : ℝ) * ∫ w, v (hypInclAt i w) * densHypAt i φ w

theorem hypInclAt_zero {n : ℕ} (w : Fin n → ℂ) : hypInclAt 0 w = hypIncl w := by
  funext j
  simp [hypInclAt, hypIncl, Fin.insertNth_zero']

end

end ReciprocityTheory.AnForm.A
end

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory
open scoped Laplacian

noncomputable section

def ddcDens (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * Δ u z

def ddcCoordDens {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  (2 / Real.pi) * ReciprocityTheory.AnForm.levi u z (Pi.single j 1)

def GreenParamFiberStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u → ∀ p : E,
    Integrable (fun z : ℂ => Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z) ∧
      ∫ z : ℂ, Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z = 2 * Real.pi * u (0, p)

def GreenParamStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1)
        ((volume : Measure ℂ).prod μ) ∧
      ∫ q : ℂ × E, Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1 ∂((volume : Measure ℂ).prod μ)
        = 2 * Real.pi * ∫ p : E, u (0, p) ∂μ

def GreenCoordStatement : Prop :=
  ∀ (D : ℕ) (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) ∧
      ∫ z : Fin (D + 1) → ℂ, Real.log ‖z j‖ * ddcCoordDens j u z =
        ∫ w : Fin D → ℂ, u (Fin.insertNth j 0 w)

def GreenMixedStatement : Prop :=
  ∀ (D : ℕ) (j a b : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    (a, b) ≠ (j, j) →
    Integrable (fun z : Fin (D + 1) → ℂ => (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b) ∧
      ∫ z : Fin (D + 1) → ℂ, (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b = 0

end

end ReciprocityTheory.AnForm.A
end

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology
open scoped ContDiff

noncomputable section

variable {D : ℕ}

def IsPsh (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) : Prop :=
  UpperSemicontinuousOn φ U ∧
    ∀ z w : Fin D → ℂ, (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ U) →
      CircleIntegrable (fun ζ : ℂ => φ (z + ζ • w)) 0 1 ∧
        φ z ≤ Real.circleAverage (fun ζ : ℂ => φ (z + ζ • w)) 0 1

def IsLeviPsh (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ U ∧ ∀ z ∈ U, ∀ w : Fin D → ℂ, 0 ≤ levi φ z w

def IsPsh_iff_isLeviPshStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U →
    (IsPsh U φ ↔ IsLeviPsh U φ)

def IsPsh_locallyIntegrableStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U → IsPsh U φ →
    LocallyIntegrableOn φ U volume

def IsPsh_supStatement : Prop :=
  ∀ (D : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (U : Set (Fin D → ℂ))
    (u : ι → (Fin D → ℂ) → ℝ), IsOpen U → (∀ j, IsPsh U (u j)) →
    IsPsh U (fun z => Finset.univ.sup' Finset.univ_nonempty (fun j => u j z))

def SubMeanPolydiscStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ),
    IsOpen U → IsPsh U φ → 0 < t → closedBall z t ⊆ U →
    IntegrableOn φ (closedBall z t) volume ∧ φ z ≤ ⨍ x in closedBall z t, φ x

def coordDiv (S : Finset (Fin D)) : Set (Fin D → ℂ) :=
  {z | ∃ i ∈ S, z i = 0}


open Classical in
def limsupExt (U A : Set (Fin D → ℂ)) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  by
    classical
    exact if z ∈ A then limsup v (𝓝[U \ A] z) else v z

def PshExtensionStatement : Prop :=
  ∀ (D : ℕ) (S : Finset (Fin D)) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (C : ℝ),
    IsOpen U → U ⊆ ball 0 1 → ContinuousOn u (U \ coordDiv S) → IsPsh (U \ coordDiv S) u →
    (∀ z ∈ U \ coordDiv S, u z ≤ C * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹)) →
    (∀ K : Set (Fin D → ℂ), IsCompact K → K ⊆ U → BddAbove (u '' (K \ coordDiv S))) ∧
      ∀ κ : ℝ, IsPsh U (limsupExt U (coordDiv S) (fun z => max (u z) (-κ)))

def polyMax (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' closedBall z t)

def PolyMaxLogConvexStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (R : ℝ),
    IsOpen U → IsPsh U φ → 0 < R → closedBall z R ⊆ U →
    ConvexOn ℝ (Set.Iic (Real.log R)) (fun s => polyMax φ z (Real.exp s)) ∧
      MonotoneOn (polyMax φ z) (Set.Ioc 0 R) ∧
      (∀ t, 0 ≤ t → t ≤ R → ∃ x ∈ closedBall z t, φ x = polyMax φ z t) ∧
      Tendsto (polyMax φ z) (𝓝[>] 0) (𝓝 (φ z))

structure Mollifier (D : ℕ) where

  toFun : (Fin D → ℂ) → ℝ
  contDiff : ContDiff ℝ ∞ toFun
  nonneg : ∀ w, 0 ≤ toFun w
  support_subset : Function.support toFun ⊆ ball 0 1
  integral_eq_one : ∫ w, toFun w = 1
  circle_inv : ∀ (c : ℂ) (w : Fin D → ℂ), ‖c‖ = 1 → toFun (c • w) = toFun w

def MollifierInhabitStatement : Prop := ∀ D : ℕ, Nonempty (Mollifier D)

def Mollifier.scaled (ρ : Mollifier D) (ε : ℝ) (w : Fin D → ℂ) : ℝ :=
  (ε ^ (2 * D))⁻¹ * ρ.toFun (ε⁻¹ • w)

def molli (ρ : Mollifier D) (ε : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  ∫ w, ρ.scaled ε w * φ (z - w)

def shrink (U : Set (Fin D → ℂ)) (ε : ℝ) : Set (Fin D → ℂ) :=
  {z | closedBall z ε ⊆ U}

def MollifyStatement : Prop :=
  ∀ (D : ℕ) (ρ : Mollifier D) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ),
    IsOpen U → IsPsh U φ →
    (∀ ε, 0 < ε → IsOpen (shrink U ε) ∧ ContDiffOn ℝ ∞ (molli ρ ε φ) (shrink U ε) ∧
        IsPsh (shrink U ε) (molli ρ ε φ) ∧
        ∀ z ∈ shrink U ε, φ z ≤ molli ρ ε φ z ∧ molli ρ ε φ z ≤ polyMax φ z ε) ∧
      (∀ z ∈ U, Tendsto (fun ε => molli ρ ε φ z) (𝓝[>] 0) (𝓝 (φ z)))

def MollificationSecondOrder : Prop :=
  ∀ (D : ℕ) (ρ : Mollifier D) (U K : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ),
    IsOpen U → ContDiffOn ℝ 3 φ U → IsCompact K → K ⊆ U →
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → ∀ z ∈ K, z ∈ shrink U ε ∧
      |molli ρ ε φ z - φ z| ≤ C * ε ∧
      ‖fderiv ℝ (molli ρ ε φ) z - fderiv ℝ φ z‖ ≤ C * ε ∧
      ‖fderiv ℝ (fderiv ℝ (molli ρ ε φ)) z - fderiv ℝ (fderiv ℝ φ) z‖ ≤ C * ε

def kθ : ℝ → ℝ :=
  (⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)).normed volume

def tmax {ι : Type*} [Fintype ι] [Nonempty ι] (t : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty t

def regMax {ι : Type*} [Fintype ι] [Nonempty ι] (η : ℝ) (t : ι → ℝ) : ℝ :=
  ∫ h : ι → ℝ, tmax (fun j => t j + η * h j) * ∏ j, kθ (h j)

def RegMaxStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι],
    (∀ η : ℝ, 0 < η →
      ContDiff ℝ ∞ (regMax (ι := ι) η) ∧ ConvexOn ℝ Set.univ (regMax (ι := ι) η) ∧
      Monotone (regMax (ι := ι) η) ∧
      (∀ t : ι → ℝ, tmax t ≤ regMax η t ∧ regMax η t ≤ tmax t + η / 2) ∧
      (∀ (t : ι → ℝ) i, (∀ j, j ≠ i → t j + η ≤ t i) → regMax η t = t i) ∧
      (∀ (t : ι → ℝ) j k (s : ℝ), k ≠ j → t j + η ≤ t k → s + η ≤ t k →
        regMax η (Function.update t j s) = regMax η t) ∧
      (∀ (t : ι → ℝ) (c : ℝ), regMax η (fun j => t j + c) = regMax η t + c) ∧
      (∀ t : ι → ℝ, ∑ j, fderiv ℝ (regMax (ι := ι) η) t (Pi.single j 1) = 1)) ∧
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ (t : ι → ℝ) (i j : ι),
      |fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t (Pi.single i 1) (Pi.single j 1)| ≤ C / η

def RegMaxLeviStatement : Prop :=
  ∀ (D : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (η : ℝ) (U : Set (Fin D → ℂ))
    (u : ι → (Fin D → ℂ) → ℝ), IsOpen U → 0 < η → (∀ j, ContDiffOn ℝ 2 (u j) U) →
    ∀ z ∈ U, ∀ (w : Fin D → ℂ) (g : ℝ), (∀ j, g ≤ levi (u j) z w) →
      g ≤ levi (fun x => regMax η (fun j => u j x)) z w

end

end ReciprocityTheory.AnForm.A
end

