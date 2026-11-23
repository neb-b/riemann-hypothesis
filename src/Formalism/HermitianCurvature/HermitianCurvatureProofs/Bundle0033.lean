module

public import Mathlib
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Mathlib.Topology.Algebra.MvPolynomial
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open PI.UpqRep

namespace TranslationBesselVanishing

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : hᴴ * Hpk k r * h = Hpk k r) (hg : gᴴ * Hpk k r * g = Hpk k r) :
    (h * g)ᴴ * Hpk k r * (h * g) = Hpk k r := by
  calc (h * g)ᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hh, hg]

theorem sigma_mul {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : hᴴ * Hpk k r * h = Hpk k r) (hg : gᴴ * Hpk k r * g = Hpk k r) :
    σ (h * g) = (σ h).comp (σ g) := by
  obtain ⟨P, hP, hDS⟩ := hds
  have hmul := hDS.2.2.1.1.2
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hsP : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hPu
  have hPs : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp hPu
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hsP
  have hJ : Jm ε = P * Hpk k r * star P := by
    rw [← hP.1.2, ← Matrix.star_eq_conjTranspose]
    calc Jm ε = (P * star P) * Jm ε * (P * star P) := by rw [hPs, Matrix.one_mul, Matrix.mul_one]
      _ = P * (star P * Jm ε * P) * star P := by simp only [Matrix.mul_assoc]
  have memJ : ∀ x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      xᴴ * Hpk k r * x = Hpk k r → P * x * P⁻¹ ∈ UJset ε := by
    intro x hx
    have hx' : star x * Hpk k r * x = Hpk k r := by rw [Matrix.star_eq_conjTranspose]; exact hx
    show (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε
    rw [hinv, hJ, ← Matrix.star_eq_conjTranspose]
    calc star (P * x * star P) * (P * Hpk k r * star P) * (P * x * star P)
        = P * (star x * (star P * P) * Hpk k r * (star P * P) * x) * star P := by
          simp only [star_mul, star_star, Matrix.mul_assoc]
      _ = P * (star x * Hpk k r * x) * star P := by simp only [hsP, Matrix.mul_one]
      _ = P * Hpk k r * star P := by rw [hx']
  have key : ∀ x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P⁻¹ * (P * x * P⁻¹) * P = x := by
    intro x
    rw [hinv]
    calc star P * (P * x * star P) * P = (star P * P) * x * (star P * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hsP, Matrix.one_mul, Matrix.mul_one]
  have hprod : (P * h * P⁻¹) * (P * g * P⁻¹) = P * (h * g) * P⁻¹ := by
    rw [hinv]
    calc P * h * star P * (P * g * star P) = P * h * (star P * P) * g * star P := by
          simp only [Matrix.mul_assoc]
      _ = P * (h * g) * star P := by rw [hsP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h1 := hmul (P * h * P⁻¹) (memJ h hh) (P * g * P⁻¹) (memJ g hg)
  dsimp only at h1
  rw [hprod, key, key, key] at h1
  exact h1

theorem smooth_add {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {x y : H}
    (hx : x ∈ smoothVecs (k := k) (r := r) σ) (hy : y ∈ smoothVecs (k := k) (r := r) σ) :
    x + y ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g (x + y))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g x) from hx) g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hGe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g y) from hy) g₀ hg₀
  refine ⟨U ∩ V, fun g => F g + G g, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
  simp only [map_add (f := _), hFe g hg.1 hgl, hGe g hg.2 hgl]

theorem smooth_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (c : ℂ) {x : H}
    (hx : x ∈ smoothVecs (k := k) (r := r) σ) : c • x ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g (c • x))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g x) from hx) g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgl => ?_⟩
  simp only [map_smul, hFe g hg hgl]

theorem smooth_zero {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} :
    (0 : H) ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g 0)
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => by simp⟩

def mulRightCLM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ]
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => h * g
      map_add' := fun a b => Matrix.add_mul a b g
      map_smul' := fun c a => by simp [Matrix.smul_mul] }

theorem smooth_translate {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    σ g v ∈ smoothVecs (k := k) (r := r) σ := by
  intro h0 hh0
  obtain ⟨U, F, hU, hmem, hF, hEq⟩ := hv (h0 * g) (uh_mul hh0 hg)
  refine ⟨(mulRightCLM g) ⁻¹' U, fun h => F (h * g), hU.preimage (mulRightCLM g).continuous, hmem,
    hF.comp (mulRightCLM g).contDiff.contDiffOn (fun h hh => hh), ?_⟩
  intro h hhU hh
  have e := (hEq (h * g) hhU (uh_mul hh hg)).symm
  show σ h (σ g v) = F (h * g)
  rw [e]
  show σ h (σ g v) = σ (h * g) v
  rw [sigma_mul hds hh hg]
  rfl

end TranslationBesselVanishing


open TranslationBesselVanishing in
theorem bessel_ne_zero_of_cyclic_orbit : Formalism.FourierDecayAlt.ThreeDimData.DDNzOfCyc := by
  intro hCyc hKF k r ε lam H _ _ _ σ w0 Wp _ _ z c π hlam hds hlow Bm hB hzero x hx
  obtain ⟨hadd, -, -, C, Ws, hWs, hbd⟩ := hB
  have hw0 : w0 ∈ smoothVecs (k := k) (r := r) σ :=
    PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth hKF k r ε lam H σ w0 hlam hds hlow
  by_contra hne
  have hpos : 0 < ‖Bm x‖ := norm_pos_iff.mpr hne
  have h2 : 0 < 2 * (|C| + 1) := by positivity
  set δ : ℝ := ‖Bm x‖ / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := div_pos hpos h2
  obtain ⟨N, cc, g, hg, hsum⟩ := hCyc k r ε lam H σ w0 hlam hds hlow x hx Ws hWs δ hδ
  set y : H := ∑ i, cc i • σ (g i) w0 with hy
  have hysm : y ∈ smoothVecs (k := k) (r := r) σ :=
    Finset.sum_induction _ (· ∈ smoothVecs (k := k) (r := r) σ) (fun a b ha hb => smooth_add ha hb)
      smooth_zero (fun i _ => smooth_smul _ (smooth_translate hds hw0 (hg i)))
  have hyDD : y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0 :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g i, hg i, rfl⟩))
  have hxy : x - y ∈ smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ y]
    exact smooth_add hx (smooth_smul _ hysm)
  have hsplit : Bm x = Bm (x - y) + Bm y := by
    rw [← hadd _ hxy _ hysm, sub_add_cancel]
  have hBy : Bm y = 0 := hzero y hyDD
  have hb := hbd (x - y) hxy
  have hS0 : 0 ≤ (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp ha
    exact norm_nonneg _
  have hlt : ‖Bm x‖ < ‖Bm x‖ :=
    calc ‖Bm x‖ = ‖Bm (x - y)‖ := by rw [hsplit, hBy, add_zero]
      _ ≤ C * (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum := hb
      _ ≤ |C| * (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hsum.le (abs_nonneg C)
      _ < ‖Bm x‖ := by
          rw [hδdef, ← mul_div_assoc, div_lt_iff₀ h2]
          nlinarith [abs_nonneg C, hpos]
  exact lt_irrefl _ hlt

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselScaling
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.BesselScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem haar_smul {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (c : ℝ≥0) (hc : 0 < c) :
    IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.conc, smul_zero]
  · intro a ha
    have hcont : Continuous (lmulM a : Mt k r → Mt k r) := by
      unfold lmulM
      exact (continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h.left a ha]
  · intro a ha
    have hcont : Continuous (rmulF a) := by
      unfold rmulF
      exact (continuous_id (X := Mat k r)).matrix_mul continuous_const
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h.right a ha]
  · intro K hK
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  · intro h0
    apply h.ne_zero
    have h1 : (c • μ) Set.univ = 0 := by rw [h0]; rfl
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (by exact_mod_cast h2 : c = 0) hc.ne'
    · exact Measure.measure_univ_eq_zero.mp h2

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def scaleG (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) : RealPlaceData k r Wp Wq :=
  { D with μG := c • D.μG, haarG := haar_smul D.haarG c hc }

theorem iteratedDeriv_two_const_mul (c : ℂ) (f : ℝ → ℂ) :
    iteratedDeriv 2 (fun x => c * f x) = fun x => c * iteratedDeriv 2 f x := by
  have h2 : ∀ g : ℝ → ℂ, iteratedDeriv 2 g = deriv (deriv g) := by
    intro g
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h2, deriv_const_mul_field', deriv_const_mul_field']

theorem oneMinusDD_const_mul (c : ℂ) (h : ℝ → ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * h a b) t₁ t₂ = c * oneMinusDD h t₁ t₂ := by
  simp only [oneMinusDD, iteratedDeriv_two_const_mul, ← mul_sub]

variable [FiniteDimensional ℂ Wq]

theorem ph_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) :
    Ph (scaleG D c hc) F F' p = ((c : ℝ) : ℂ) * Ph D F F' p := by
  have hμ : (scaleG D c hc).μG = c • D.μG := rfl
  unfold Ph
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  try rfl

theorem betaInf_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    betaInf (scaleG D c hc) F F' = ((c : ℝ) : ℂ) * betaInf D F F' := by
  have hreg : ∀ p, regBracket (scaleG D c hc) F F' p =
      fun a b => ((c : ℝ) : ℂ) * regBracket D F F' p a b := by
    intro p
    funext a b
    have hχ : (scaleG D c hc).χ = D.χ := rfl
    simp only [regBracket]
    rw [ph_scale, hχ]
    ring
  have hz : (scaleG D c hc).z = D.z := rfl
  have hz' : (scaleG D c hc).z' = D.z' := rfl
  have hS : (scaleG D c hc).μSS = D.μSS := rfl
  unfold betaInf betaInfTau
  simp only [hreg, hz, hz', hS, oneMinusDD_const_mul, mul_assoc, integral_const_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring
end

theorem anyFromNorm : LemmaBNorm → IntNormB → LemmaBAny := by
  intro hN hB k r Wp Wq _ _ _ _ _ _ D A hA
  obtain ⟨c, ⟨hc, hF⟩, -⟩ := hB k r Wp Wq D
  have hF' : IntFormula (scaleG D c hc) := hF
  obtain ⟨h1, h2, h3, h4⟩ := hN k r Wp Wq (scaleG D c hc) A hA hF'
  refine ⟨c, hc, hF, h1, ?_, ?_, h4⟩
  · intro F F' hF1 hF2
    have hb : beta (scaleG D c hc) F F' = beta D F F' := rfl
    rw [← hb, h2 F F' hF1 hF2, betaInf_scale]
  · intro UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4 hIC
    exact h3 UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4
      (fun p hp T hT i j hij hj => (hIC p hp T hT i j hij hj).smul_measure_nnreal)

end Formalism.FourierDecayAlt.P.BesselScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem lemma_b_from_xi_of_parts : Formalism.FourierDecayAlt.B2.LemmaBFromXiFromParts := by
  intro hC hJ hD hI hB hX
  have hN : LemmaBNorm := by
    intro k r Wp Wq _ _ _ _ _ _ D A hA hF
    exact hC hX k r Wp Wq D A hA hF (hJ k r Wp Wq D) (hD k r Wp Wq D) (hI k r Wp Wq D A hA)
  exact ⟨hN, Formalism.FourierDecayAlt.P.BesselScaling.anyFromNorm hN hB⟩

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.BesselScaling

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem lemmaBFromXi_of : ConjInvAll → DilJacAll → CCIntAll → IntNormB → LemmaBFromXi :=
  Formalism.FourierDecayAlt.P.lemma_b_from_xi_of_parts (fun hX => Formalism.FourierDecayAlt.P.bessel_lemma_closed_form hX Formalism.FourierDecayAlt.P.lemma_B_of_components
            Formalism.FourierDecayAlt.P.clause_of_regularized_limit Formalism.FourierDecayAlt.P.adjointness_polynomially_bounded)

end Formalism.FourierDecayAlt.P.BesselScaling
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellOpenDomain

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem qdom_open (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (QDom k r z z') := by
  have h1 : IsOpen {q : (Fin r → ℂ) × ℂ | ∀ a, q.1 a ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
  have h2 : IsOpen {q : (Fin r → ℂ) × ℂ | Tz k r z * Tz k r z' < Complex.normSq q.2} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  exact h1.inter h2

theorem c_apply (n : ℕ) (a : Fin r) (s : Set ((Fin r → ℂ) × ℂ)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => q.1 a) s :=
  ((contDiff_apply ℝ (fun _ => ℂ) a).comp contDiff_fst).contDiffOn

theorem c_inv (z z' : Fin (2 * r + k + 1) → ℂ) (n : ℕ) (a : Fin r) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => (star (q.1 a))⁻¹) (QDom k r z z') := by
  have h0 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => q.1 a) :=
    (contDiff_apply ℝ (fun _ => ℂ) a).comp contDiff_fst
  have hc : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => star (q.1 a)) :=
    Complex.conjCLE.contDiff.comp h0
  exact hc.contDiffOn.inv (fun q hq => star_ne_zero.2 ((show (∀ a, q.1 a ≠ 0) ∧ _ from hq).1 a))

theorem mu_entry (D : RealPlaceData k r Wp Wq) (n : ℕ) (a b : Fin (k + 1)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => D.μsec q.2 a b) (QDom k r D.z D.z') := by
  have hle : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  exact ((D.sec.1 a b).of_le hle).comp (s := QDom k r D.z D.z') contDiff_snd.contDiffOn fun q hq => hq.2

theorem gq_contDiffOn (D : RealPlaceData k r Wp Wq) (n : ℕ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q => gq D q) (QDom k r D.z D.z') := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => bigCell k r q.1 (D.μsec q.2) i j) _
  unfold bigCell
  split_ifs <;> first
    | exact contDiffOn_const
    | exact c_apply n _ _
    | exact c_inv D.z D.z' n _
    | exact mu_entry D n _ _

end Formalism.FourierDecayAlt.P.BigCellOpenDomain

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bessel_smooth_of_parts : Formalism.FourierDecayAlt.JF.JqSmoothOfParts := by
  intro hW hGD k r Wp Wq _ _ _ _ _ _ D A m F hT hF
  have hg := BigCellOpenDomain.gq_contDiffOn D m
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hG := hGD k r Wp Wq D q hq
  obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 (gq D q) ⟨WordKeyIdentity.glev0 hG.1, hG.2⟩
  refine ⟨QDom k r D.z D.z' ∩ (fun q => gq D q) ⁻¹' U,
    hg.continuousOn.isOpen_inter_preimage (BigCellOpenDomain.qdom_open D.z D.z') hU, ⟨hq, hgU⟩, ?_⟩
  have hcomp : ContDiffOn ℝ (m : WithTop ℕ∞) (F' ∘ fun q => gq D q)
      (QDom k r D.z D.z' ∩ (QDom k r D.z D.z' ∩ (fun q => gq D q) ⁻¹' U)) :=
    hc.comp (hg.mono Set.inter_subset_left) fun x hx => hx.2.2
  refine hcomp.congr fun x hx => ?_
  exact he _ hx.2.2 (WordKeyIdentity.glev0 (hGD k r Wp Wq D x hx.1).1)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem gf_cont (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous fun g : B.Mat k r => Gf k r z z' g := by
  obtain ⟨q, _, hq⟩ := P.gram_function_polynomial k r z z'
  have h1 : Continuous fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ) := by
    have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) =
        fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
    rw [e]
    refine (MvPolynomial.continuous_eval q).comp ?_
    refine continuous_pi fun i => ?_
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · simp only [Sum.elim_inl]; exact continuous_id.matrix_elem a b
    · simp only [Sum.elim_inr]; exact continuous_star.comp (continuous_id.matrix_elem a b)
  have := Complex.continuous_re.comp h1
  refine this.congr fun g => ?_
  simp

end ops

end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

namespace Formalism.FourierDecayAlt.P

open DifferentialOperatorClasses

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CasimirEigenvalueCoefficients
section
open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Qb1

variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]

theorem ckOn_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (h : CkOn m (GV k r) f) : CkOn m (GV k r) f' := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  exact ⟨U, F, a, b, c, fun g hg hgG => (he g hgG).symm.trans (d g hg hgG)⟩

variable {σ : Mx k r → (Vs →L[ℂ] Vs)}

theorem lie1 (Z : Mx k r) : inLie k r (hpart1 (Hpk k r) Z) := Qx2.hpart1_lie Z

theorem lie2 (Z : Mx k r) : inLie k r (hpart2 (Hpk k r) Z) := Qx2.hpart2_lie Z

end Qb1

end Formalism.FourierDecayAlt.P
end
end

