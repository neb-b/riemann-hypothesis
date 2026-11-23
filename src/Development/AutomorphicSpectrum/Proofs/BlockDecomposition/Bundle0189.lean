module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0181
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SchemeDescendsToSubalgebra
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSubValueZeroRapidDecay
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSumStatement
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summable_majorant_lattice_sum : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) {C : Set (GL ι 𝔸[k])} (hC : IsCompact C), ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → k,
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)‖ ≤ u ξ := by
  first | exact @GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC | exact GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC | (intros; apply GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfContinuousOn
section
noncomputable section

open MeasureTheory Matrix Finset PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open scoped ContDiff ComplexConjugate InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WeightIbp

variable {n : ℕ}

theorem isOpen_invertible : IsOpen (GLs n) := by
  have h : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

theorem val_mem_invertible (y : G n) : y.val ∈ GLs n := by
  have h : y.val.det * (y⁻¹ : G n).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one h

theorem integrable_of_continuousOn (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] {W : Type} [NormedAddCommGroup W] (F : Mat n → W) (hF : ContinuousOn F (GLs n)) (hc : Cpt F) :
    Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hc
  have hcont : Continuous fun y : G n => F y.val :=
    hF.comp_continuous Units.continuous_val val_mem_invertible
  have hK : IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1 R
  have hsupp : HasCompactSupport fun y : G n => F y.val := by
    refine HasCompactSupport.intro hK fun y hy => ?_
    exact hR _ (val_mem_invertible y) (not_le.1 hy)
  exact hcont.integrable_of_hasCompactSupport hsupp

theorem fderiv_eq_zero_far (hL : LgFacts) {φ : Mat n → ℝ} {R : ℝ} (hR : ∀ y ∈ GLs n, R < lg y → φ y = 0)
    {y : Mat n} (hy : y ∈ GLs n) (hl : R < lg y) : fderiv ℝ φ y = 0 := by
  have hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n) := (hL n).2.2.2.1.continuousOn
  have hU : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R) := hlg.isOpen_inter_preimage isOpen_invertible isOpen_Ioi
  have he : φ =ᶠ[nhds y] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hy, hl⟩) fun z hz => hR z hz.1 hz.2
  rw [he.fderiv_eq]
  exact fderiv_const_apply 0

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem Rd_weight_inner {f h : Mat n → V} {φ : Mat n → ℝ} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (hφ : ContDiffOn ℝ ∞ φ (GLs n)) (X : Mat n) {y : Mat n} (hy : y ∈ GLs n) :
    Rd X (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y =
      (φ y : ℂ) * ⟪h y, Rd X f y⟫_ℂ + (φ y : ℂ) * ⟪Rd X h y, f y⟫_ℂ +
        (fderiv ℝ φ y (y * X) : ℂ) * ⟪h y, f y⟫_ℂ := by
  have hn := isOpen_invertible.mem_nhds hy
  have hfd : HasFDerivAt f (fderiv ℝ f y) y :=
    ((hf.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hhd : HasFDerivAt h (fderiv ℝ h y) y :=
    ((hh.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hφd : HasFDerivAt φ (fderiv ℝ φ y) y :=
    ((hφ.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hi := hhd.inner ℂ hfd
  have ho := Complex.ofRealCLM.hasFDerivAt.comp y hφd
  have hm := ho.mul hi
  have := hm.fderiv
  have key : fderiv ℝ (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y (y * X) =
      (φ y : ℂ) * fderivInnerCLM ℂ (h y, f y) (fderiv ℝ h y (y * X), fderiv ℝ f y (y * X)) +
        ⟪h y, f y⟫_ℂ * (fderiv ℝ φ y (y * X) : ℂ) := by
    have e : (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) = (⇑Complex.ofRealCLM ∘ φ * fun t => ⟪h t, f t⟫_ℂ) := rfl
    rw [e]
    erw [this]
    rfl
  simp only [Rd]
  rw [key, fderivInnerCLM_apply]
  ring

theorem weight_ibp : RCalc → LgFacts → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f h : Mat n → V) (φ : Mat n → ℝ), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → ContDiffOn ℝ ∞ φ (GLs n) → Cpt φ → ∀ X : Mat n, ∫ y : G n, (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ ∂μ = -(∫ y : G n, (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ ∂μ) - ∫ y : G n, (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ ∂μ := by
  intro hR hL n _ _ μ _ V _ _ f h φ hf hh hφ hc X
  obtain ⟨R, hRφ⟩ := id hc
  have hφc : ContinuousOn (fun y => (φ y : ℂ)) (GLs n) :=
    Complex.continuous_ofReal.comp_continuousOn hφ.continuousOn
  have hFs : ContDiffOn ℝ ∞ (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) (GLs n) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ).mul (hh.inner ℂ hf)
  have hFc : Cpt (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) :=
    ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩
  have h0 := (hR n).2.2 μ ℂ _ hFs hFc X
  have hRf := ((hR n).1 V f hf).1 X
  have hRh := ((hR n).1 V h hh).1 X
  have iA : Integrable (fun y : G n => (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ) μ :=
    integrable_of_continuousOn hL μ (fun z => (φ z : ℂ) * ⟪h z, Rd X f z⟫_ℂ)
      (hφc.mul (hh.continuousOn.inner hRf.continuousOn)) ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩
  have iB : Integrable (fun y : G n => (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ) μ :=
    integrable_of_continuousOn hL μ (fun z => (φ z : ℂ) * ⟪Rd X h z, f z⟫_ℂ)
      (hφc.mul (hRh.continuousOn.inner hf.continuousOn)) ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩
  have hdc : ContinuousOn (fun y : Mat n => ((fderiv ℝ φ y (y * X) : ℝ) : ℂ)) (GLs n) := by
    have h1 : ContinuousOn (fderiv ℝ φ) (GLs n) :=
      hφ.continuousOn_fderiv_of_isOpen isOpen_invertible (by simp)
    have h2 : ContinuousOn (fun y : Mat n => y * X) (GLs n) :=
      (continuous_id.matrix_mul continuous_const).continuousOn
    exact Complex.continuous_ofReal.comp_continuousOn (h1.clm_apply h2)
  have iC : Integrable (fun y : G n => (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ) μ :=
    integrable_of_continuousOn hL μ (fun z => (fderiv ℝ φ z (z * X) : ℂ) * ⟪h z, f z⟫_ℂ)
      (hdc.mul (hh.continuousOn.inner hf.continuousOn))
      ⟨R, fun y hy hl => by simp [fderiv_eq_zero_far hL hRφ hy hl]⟩
  have hsum : ∫ y : G n, Rd X (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y.val ∂μ =
      (∫ y : G n, (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ ∂μ) +
        (∫ y : G n, (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ ∂μ) +
        ∫ y : G n, (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ ∂μ := by
    have e := integral_add (iA.add iB) iC
    simp only [Pi.add_apply] at e
    rw [← integral_add iA iB, ← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact Rd_weight_inner hf hh hφ X (val_mem_invertible y)
  rw [h0] at hsum
  linear_combination -hsum

end GlobalTheory.CompanionTheory.WeightIbp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDSSkImpUpqRep
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiscreteSeries

theorem isDS_sk_imp_upqRep (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ :=
  fun h => h

end GlobalTheory.CompanionTheory.DiscreteSeries
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

def gconv (g g' : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t, g t * g' (r - t)

theorem gconv_comm (g g' : ℝ → ℝ) : gconv g g' = gconv g' g := by
  funext r
  unfold gconv
  rw [← integral_sub_left_eq_self (fun t => g t * g' (r - t)) volume r]
  simp [mul_comm]

variable {n : ℕ}

def KReg {V : Type} [NormedAddCommGroup V] (k : Mat n → V) : Prop :=
  ContinuousOn k (GLs n) ∧ ∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0

theorem inv_mem_GLs {y : Mat n} (hy : y ∈ GLs n) : y⁻¹ ∈ GLs n := by
  have : y.det ≠ 0 := hy
  change (y⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero this

section
variable [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)

theorem isMult_of_fintype {ι : Type} [Fintype ι] {k : Mat n → (E.V →L[ℂ] E.V)} {val : Inf n → ℂ} {T : ℝ}
    (c : ι → ℂ) (w : ι → List (Bool × ℕ)) (g : ι → ℝ → ℝ) (ks : ι → Mat n → (E.V →L[ℂ] E.V))
    (h1 : ∀ i, IsBump (g i) T ∧ IsKer μ E (w i) (g i) (ks i)) (h2 : ∀ y ∈ GLs n, k y = ∑ i, c i • ks i y)
    (h3 : ∀ χ, val χ = ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ)) : IsMult μ E k val T := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, c ∘ e.symm, w ∘ e.symm, g ∘ e.symm, ks ∘ e.symm, fun i => h1 _, fun y hy => ?_, fun χ => ?_⟩
  · rw [h2 y hy]
    exact (Equiv.sum_comp e.symm (fun i => c i • ks i y)).symm
  · rw [h3 χ]
    exact (Equiv.sum_comp e.symm (fun i => c i * zVal (w i) χ * coshT (g i) (cas χ))).symm
end

theorem zVal_append (w w' : List (Bool × ℕ)) (χ : Inf n) : zVal (w ++ w') χ = zVal w χ * zVal w' χ := by
  simp [zVal]

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def EpowT (s : Bool) : ℕ → Fin n → Fin n → (Mat n → V) → (Mat n → V)
  | 0, a, b => fun f => if a = b then f else 0
  | m + 1, a, b => fun f => ∑ c, Eu s c a (EpowT s m c b f)

def gelT (s : Bool) (m : ℕ) (f : Mat n → V) : Mat n → V := ∑ a, EpowT s m a a f

end Ops

section Alg

variable {A : Type} [Ring A]

noncomputable def Epw (e : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0, a, b => if a = b then 1 else 0
  | m + 1, a, b => ∑ c, e a c * Epw e m c b

def trE (e : Fin n → Fin n → A) (m : ℕ) : A := ∑ a, Epw e m a a

noncomputable def bco (N : A) (τ : ℕ → A) : ℕ → ℕ → A
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => N * bco N τ m 0 - τ m
  | m + 1, j + 1 => bco N τ m j + N * bco N τ m (j + 1)

noncomputable def phiSeq (N : A) (τ : ℕ → A) (m : ℕ) : A :=
  τ m - ∑ j : Fin m, bco N τ m j * phiSeq N τ j
termination_by m
decreasing_by exact j.isLt

end Alg

def gser (c : Fin n → ℂ) : PowerSeries ℂ := PowerSeries.mk (GlobalTheory.Dec.gelfVal c)

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPiStatement
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearChange_mem_schwartzBruhatPi : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]), ltr A F ∈ schwartzBruhatPi (K := k) (ι := ι) := by
  first | exact @GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | exact GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | (intros; apply GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapQdetEtr
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliMap

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

theorem map_Tm (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) :
    φ (Formalism.REAL.Tm X u a b) = Formalism.REAL.Tm (fun a b => φ (X a b)) u a b := by
  unfold Formalism.REAL.Tm
  split_ifs <;> simp

theorem map_qminor (φ : A →ₐ[ℂ] B) {n t : ℕ} (X : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) :
    φ (Formalism.REAL.qminor X a b u) = Formalism.REAL.qminor (fun a b => φ (X a b)) a b u := by
  unfold Formalism.REAL.qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext k
  exact map_Tm φ X _ _ _

theorem map_qdet (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun a b => φ (X a b)) u := by
  unfold Formalism.REAL.qdet
  exact map_qminor φ X id id u

theorem map_epow (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    φ (Formalism.REAL.epow X k a b) = Formalism.REAL.epow (fun a b => φ (X a b)) k a b := by
  induction k generalizing a b with
  | zero => by_cases h : a = b <;> simp [Formalism.REAL.epow, h]
  | succ m ih => simp [Formalism.REAL.epow, map_sum, map_mul, ih, apply_ite]

theorem map_etr (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (k : ℕ) :
    φ (Formalism.REAL.etr X k) = Formalism.REAL.etr (fun a b => φ (X a b)) k := by
  unfold Formalism.REAL.etr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl (fun a _ => map_epow φ X k a a)

theorem map_qdet_etr : ∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (n : ℕ) (X : Fin n → Fin n → A) (u : ℂ) (k : ℕ),
    φ (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun a b => φ (X a b)) u ∧
      φ (Formalism.REAL.etr X k) = Formalism.REAL.etr (fun a b => φ (X a b)) k := by
  intro A B _ _ _ _ φ n X u k
  exact ⟨map_qdet φ X u, map_etr φ X k⟩

end GlobalTheory.CompanionTheory.CapelliMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Ix (n : ℕ) := Bool × Fin n × Fin n

def hm (p : Ix n) : Mat n :=
  if p.1 then Matrix.single p.2.1 p.2.2 1 + Matrix.single p.2.2 p.2.1 1
  else Matrix.single p.2.1 p.2.2 Complex.I - Matrix.single p.2.2 p.2.1 Complex.I

def sk (p : Ix n) : Mat n :=
  if p.1 then Matrix.single p.2.1 p.2.2 1 - Matrix.single p.2.2 p.2.1 1
  else Matrix.single p.2.1 p.2.2 Complex.I + Matrix.single p.2.2 p.2.1 Complex.I

section Calc

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

def Rr (X : Mat n) (f : Mat n → W) : Mat n → W := fun g => fderiv ℝ f g (g * X)

def Sm (u : ℝ → Mat n → W) : Prop := ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)

def dt (u : ℝ → Mat n → W) : ℝ → Mat n → W := fun s y => deriv (fun r => u r y) s

def Rt (X : Mat n) (u : ℝ → Mat n → W) : ℝ → Mat n → W := fun s => Rr X (u s)

def dens (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) : ℝ :=
  ‖dt u s y‖ ^ 2 + (1 / 4) * ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 + ‖u s y‖ ^ 2

end Calc

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := by ext g; simp [GLs]
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  exact this.ne_zero

end GlobalTheory.CompanionTheory.WaveSpd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpread
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.NoethApprox

theorem schemeModels : GlobalTheory.SpreadingModels.SchemeModels := by
  intro R _ Y f h₁ h₂ h₃
  obtain ⟨R₀, i, φ, Y₀, f₀, π, a, b, c, d, e⟩ := GlobalTheory.SpreadScheme.hasModel (V := R) f
  exact ⟨R₀, i, φ, Y₀, f₀, π, a, b, d, c, e⟩

end GlobalTheory.CompanionTheory.NoethApprox
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSubValueZeroRapidDecayStatement
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sub_value_zero_rapid_decay : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) (r : ℕ), ∃ M : ℝ, ∀ h ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaC F (scalC (moduleSection w t) * h) - F 0‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  first | exact @GlobalTheory.CompanionTheory.EisThCDecay.exists_norm_thetaC_sub_le | exact GlobalTheory.CompanionTheory.EisThCDecay.exists_norm_thetaC_sub_le | (intros; apply GlobalTheory.CompanionTheory.EisThCDecay.exists_norm_thetaC_sub_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitActGlRel
section
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.SmoothVecMod

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothVecGl

theorem unitAct_glRel : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ),
    Formalism.REAL.GlRel (fun a b => GlobalTheory.SmoothVecMod.unitAct hσ a b) := by
  intro n ε H _ _ σ hσ
  have key : ∀ a b (u : smoothVec ε σ), ∀ g ∈ UJset ε,
      σ g (unitAct hσ a b u) = EabV ε a b (fun g => σ g u) g :=
    fun a b u g hg => rep_eabV hσ u.2 a b hg
  intro a b c d
  ext u
  have h := eabGlV_of (rdLinV_of vector_right_derivative_extends)
    (rdBracketV_of vector_right_derivative_extends (rdSmoothV_of vector_right_derivative_extends)) (rdSmoothV_of vector_right_derivative_extends)
    n ε H (fun g => σ g u) a b c d 1 u.2 inUJ_one
  rw [← eabV_congr (key c d u) a b inUJ_one, ← eabV_congr (key a b u) c d inUJ_one] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
  rw [unitAct_coe hσ a b, unitAct_coe hσ c d (unitAct hσ a b u), h]
  split_ifs <;> simp [unitAct_coe]

end GlobalTheory.CompanionTheory.SmoothVecGl
end
end

