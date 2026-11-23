module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistence
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RdEqFderiv
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ZJoint

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem isOpen_dom (n : ℕ) : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) :=
  isOpen_univ.prod (isOpen_GLs n)

def Pres (Φ : (Mat n → V) → (Mat n → V)) : Prop :=
  ∀ U : ℝ → Mat n → V, ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) →
    ContDiffOn ℝ ∞ (Function.uncurry fun t => Φ (U t)) (Set.univ ×ˢ GLs n)

theorem rd_eq_fderiv (U : ℝ → Mat n → V)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) {t : ℝ} {g : Mat n}
    (hg : g ∈ GLs n) (X : Mat n) :
    Rd X (U t) g = fderiv ℝ (Function.uncurry U) (t, g) ((0 : ℝ), g * X) := by
  have hd : DifferentiableAt ℝ (Function.uncurry U) (t, g) :=
    (hU.contDiffAt ((isOpen_dom n).mem_nhds ⟨Set.mem_univ _, hg⟩)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun x : Mat n => (t, x)) (ContinuousLinearMap.inr ℝ ℝ (Mat n)) g :=
    hasFDerivAt_prodMk_right t g
  have h2 : HasFDerivAt (U t)
      ((fderiv ℝ (Function.uncurry U) (t, g)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n))) g :=
    HasFDerivAt.comp g (f := fun x : Mat n => (t, x)) (g := Function.uncurry U) hd.hasFDerivAt hi
  simp [Rd, h2.fderiv]

theorem pres_Rd (X : Mat n) : Pres (V := V) (Rd X) := by
  intro U hU
  have h1 := hU.fderiv_of_isOpen (m := ∞) (isOpen_dom n) (by simp)
  let L : Mat n →ₗ[ℝ] Mat n := LinearMap.mulRight ℝ X
  have hL : ContDiff ℝ ∞ (fun x : Mat n => x * X) := (L.toContinuousLinearMap).contDiff
  have hl : ContDiff ℝ ∞ (fun p : ℝ × Mat n => ((0 : ℝ), p.2 * X)) :=
    contDiff_const.prodMk (hL.comp contDiff_snd)
  refine (h1.clm_apply hl.contDiffOn).congr ?_
  rintro ⟨t, g⟩ ⟨-, hg⟩
  exact rd_eq_fderiv U hU hg X

theorem Pres.add {Φ Ψ : (Mat n → V) → (Mat n → V)} (h : Pres Φ) (k : Pres Ψ) :
    Pres (fun f => Φ f + Ψ f) :=
  fun U hU => (h U hU).add (k U hU)

theorem Pres.smul {Φ : (Mat n → V) → (Mat n → V)} (c : ℂ) (h : Pres Φ) :
    Pres (fun f => c • Φ f) :=
  fun U hU => (h U hU).const_smul c

theorem Pres.comp {Φ Ψ : (Mat n → V) → (Mat n → V)} (h : Pres Φ) (k : Pres Ψ) :
    Pres (fun f => Φ (Ψ f)) :=
  fun U hU => h (fun t => Ψ (U t)) (k U hU)

theorem pres_sum {ι : Type} (s : Finset ι) (Φ : ι → (Mat n → V) → (Mat n → V))
    (h : ∀ i, Pres (Φ i)) : Pres (fun f => ∑ i ∈ s, Φ i f) := by
  intro U hU
  have e : (Function.uncurry fun t => ∑ i ∈ s, Φ i (U t)) =
      fun p => ∑ i ∈ s, (Function.uncurry fun t => Φ i (U t)) p := by
    funext p
    simp [Function.uncurry, Finset.sum_apply]
  rw [e]
  exact ContDiffOn.sum fun i _ => h i U hU

theorem pres_Eu (s : Bool) (a b : Fin n) : Pres (V := V) (Eu s a b) :=
  Pres.smul (1 / 2 : ℂ) ((pres_Rd _).add (Pres.smul _ (pres_Rd _)))

theorem pres_Epow (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Pres (V := V) (Epow s m a b) := by
  induction m with
  | zero =>
    intro a b U hU
    by_cases hab : a = b
    · simpa [Epow, hab] using hU
    · have e : (Function.uncurry fun t => Epow (V := V) s 0 a b (U t)) = fun _ => 0 := by
        funext p
        simp [Epow, hab, Function.uncurry]
      rw [e]
      exact contDiffOn_const
  | succ m ih =>
    intro a b
    exact pres_sum Finset.univ (fun c f => Eu s a c (Epow s m c b f))
      fun c => (pres_Eu s a c).comp (ih c b)

theorem pres_gel (s : Bool) (m : ℕ) : Pres (V := V) (gel (n := n) s m) :=
  pres_sum Finset.univ (fun a f => Epow s m a a f) fun a => pres_Epow s m a a

theorem pres_zOp (w : List (Bool × ℕ)) : Pres (V := V) (zOp (n := n) w) := by
  induction w with
  | nil => exact fun U hU => hU
  | cons p w ih => exact (pres_gel p.1 p.2).comp ih

theorem zOp_joint (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (U : ℝ → Mat n → V)
    (w : List (Bool × ℕ)) (h : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t => zOp w (U t)) (Set.univ ×ˢ GLs n) :=
  pres_zOp w U h

end GlobalTheory.CompanionTheory.WaveMult.ZJoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableG
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Word

variable {n : ℕ}

section Defs

variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

structure Cl (K : Mat n → Mat n → L) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry K) (GLs n ×ˢ GLs n)
  supp : ∃ R, ∀ x ∈ GLs n, ∀ y ∈ GLs n, R + lg x < lg y → K x y = 0

def kK (k : Mat n → L) : Mat n → Mat n → L := fun x y => k (x⁻¹ * y)

def Iop {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace (G n)] (μ : Measure (G n))
    (K : Mat n → Mat n → (V →L[ℂ] V)) (φ : Mat n → V) : Mat n → V :=
  fun x => ∫ y : G n, K x y.val (φ y.val) ∂μ

end Defs

section ClB
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

end ClB

section Lem
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

theorem contDiff_ent (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff

theorem contDiffOn_invMul : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) := by
  have hinv : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹) (GLs n ×ˢ GLs n) :=
    (ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero.restrict_scalars ℝ).comp (f := Prod.fst) contDiff_fst.contDiffOn
      fun p hp => hp.1
  refine contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  refine ContDiffOn.sum fun c _ => ContDiffOn.mul ?_ ?_
  · exact (contDiff_ent a c).comp_contDiffOn hinv
  · exact ((contDiff_ent c b).comp contDiff_snd).contDiffOn

theorem cl_kK (hL : LgFacts) {k : Mat n → L} (hk : ContDiffOn ℝ ∞ k (GLs n)) {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → k y = 0) : Cl (kK k) := by
  refine ⟨hk.comp contDiffOn_invMul fun p hp => GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveMult.inv_mem_GLs hp.1) hp.2,
    R, fun x hx y hy hl => ?_⟩
  have hz := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveMult.inv_mem_GLs hx) hy
  refine hR _ hz ?_
  have h := (hL n).1 x hx _ hz
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hx)] at h
  linarith

end Lem

section Lem2
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

end Lem2

section Lem3
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

end Lem3

section Basic
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

end Basic

section Pairs

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

variable {μ} {φ : Mat n → V}

theorem act_eq_Iop (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V) {x : Mat n} (hx : x ∈ GLs n) :
    act μ E k f x = Iop μ (kK k) f x := by
  let xG : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx
  have hv : xG.val = x := rfl
  have hdet : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have h := integral_mul_left_eq_self (μ := μ) (fun y : G n => k (x⁻¹ * y.val) (f y.val)) xG
  simp only [Iop, kK, act]
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [Units.val_mul, hv, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]

end Pairs

end GlobalTheory.CompanionTheory.WaveK.Word
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOrthCptZero
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

variable {n : ℕ}

theorem isOpen_GLs_dens (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne.preimage h

theorem mul_unitary_mem_GLs {y : Mat n} (hy : y ∈ GLs n) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    y * k.1 ∈ GLs n := by
  have h1 : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have h2 : k.1.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse h1
  have h3 : y.det ≠ 0 := hy
  change (y * k.1).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h3 h2

theorem inner_rho_inv (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) (a v : E.V) :
    ⟪E.ρ k⁻¹ a, v⟫_ℂ = ⟪a, E.ρ k v⟫_ℂ := by
  let L : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩
  have h1 : E.ρ k (E.ρ k⁻¹ a) = a := by
    have : (E.ρ k * E.ρ k⁻¹) a = a := by
      rw [← map_mul, mul_inv_cancel, map_one]; rfl
    simpa using this
  have h2 := L.inner_map_map (E.ρ k⁻¹ a) v
  have h3 : L (E.ρ k⁻¹ a) = a := h1
  have h4 : L v = E.ρ k v := rfl
  rw [h3, h4] at h2
  exact h2.symm

theorem section_orth_cpt_zero : KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (A : Mat n → E.V), ContinuousOn A (GLs n) →
    (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, A (y * k₂.1) = E.ρ k₂⁻¹ (A y)) →
    (∀ h ∈ CE E, Cpt h → ∫ y : G n, ⟪A y.val, h y.val⟫_ℂ ∂μ = 0) → ∀ y ∈ GLs n, A y = 0 := by
  intro hK n _ _ μ _ E A hA hEq hOrth y hy
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  let e : E.V := A y
  let κ : Mat n → (E.V →L[ℂ] E.V) := fun z => (innerSL ℂ (A z)).smulRight e
  have hκ : ∀ z v, κ z v = ⟪A z, v⟫_ℂ • e := fun z v => by simp [κ]
  have hcont : ContinuousOn κ (GLs n) := by
    have h1 : Continuous fun a : E.V => (innerSL ℂ a).smulRight e :=
      ((ContinuousLinearMap.smulRightL ℂ E.V E.V).flip e).continuous.comp (innerSL ℂ).continuous
    exact h1.comp_continuousOn hA
  have hequi : ∀ z ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, κ (z * k₂.1) = κ z * E.ρ k₂ := by
    intro z hz k₂
    ext v
    rw [ContinuousLinearMap.mul_apply, hκ, hκ, hEq z hz k₂, inner_rho_inv]
  have hact : ∀ f ∈ CE E, Cpt f → (∀ z ∈ GLs n, z ∉ GLs n → f z = 0) → act μ E κ f 1 = 0 := by
    intro f hf hc _
    have h0 := hOrth f hf hc
    unfold act
    simp only [one_mul, hκ]
    rw [integral_smul_const, h0, zero_smul]
  have hz := hK n μ E κ (GLs n) (isOpen_GLs_dens n) subset_rfl
    (fun z hz k => mul_unitary_mem_GLs hz k) hcont hequi hact y hy
  have h1 : ⟪A y, A y⟫_ℂ • e = 0 := by
    rw [← hκ, hz]; rfl
  rcases smul_eq_zero.1 h1 with h | h
  · exact inner_self_eq_zero.1 h
  · exact h

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommute
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SmCalc

section Generic

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {u : ℝ → E → W} {O : Set E}

theorem hasFDerivAt_unc (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y)) (s, y) :=
  ((hu.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
    (by simp)).hasFDerivAt

theorem hasDerivAt_line (s : ℝ) (y : E) :
    HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : E)) s :=
  (hasDerivAt_id s).prodMk (hasDerivAt_const s y)

theorem deriv_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    deriv (fun r => u r y) s = fderiv ℝ (Function.uncurry u) (s, y) ((1 : ℝ), (0 : E)) := by
  have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s
    (hasFDerivAt_unc hO hu s hy) (hasDerivAt_line s y)
  exact h2.deriv

theorem fderiv_slice_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O)
    (v : E) : fderiv ℝ (u s) y v = fderiv ℝ (Function.uncurry u) (s, y) ((0 : ℝ), v) := by
  have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
    hasFDerivAt_prodMk_right s y
  have h2 := HasFDerivAt.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) y
    (hasFDerivAt_unc hO hu s hy) h1
  have h3 : HasFDerivAt (u s) ((fderiv ℝ (Function.uncurry u) (s, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)) y := h2
  simp [h3.fderiv]

theorem fd_smooth (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ O) :=
  hu.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)

theorem smooth_deriv (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => deriv (fun r => u r y) s) (Set.univ ×ˢ O) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((1 : ℝ), (0 : E))) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply contDiffOn_const
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact deriv_eq hO hu s hy

theorem smooth_field (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {V : E → E} (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => fderiv ℝ (u s) y (V y)) (Set.univ ×ˢ O) := by
  have h0 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), V p.2)) :=
    contDiff_const.prodMk (hV.comp contDiff_snd)
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((0 : ℝ), V p.2)) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply h0.contDiffOn
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact fderiv_slice_eq hO hu s hy _

theorem smooth_slice (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) :
    ContDiffOn ℝ ∞ (u s) O := by
  have h1 : ContDiff ℝ ∞ (fun z : E => (s, z)) := contDiff_const.prodMk contDiff_id
  exact ContDiffOn.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) hu
    h1.contDiffOn (fun z hz => ⟨Set.mem_univ _, hz⟩)

theorem smooth_line (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {y : E} (hy : y ∈ O) : ContDiff ℝ ∞ fun s => u s y := by
  have h1 : ContDiff ℝ ∞ (fun r : ℝ => (r, y)) := contDiff_id.prodMk contDiff_const
  have h2 := ContDiffOn.comp (s := Set.univ) (g := Function.uncurry u)
    (f := fun r : ℝ => (r, y)) hu h1.contDiffOn (fun _ _ => ⟨Set.mem_univ _, hy⟩)
  exact contDiffOn_univ.1 h2

theorem deriv_fderiv_comm (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (v : E) (s : ℝ) {y : E}
    (hy : y ∈ O) :
    deriv (fun r => fderiv ℝ (u r) y v) s =
      fderiv ℝ (fun z => deriv (fun r => u r z) s) y v := by
  have hm : (s, y) ∈ (Set.univ : Set ℝ) ×ˢ O := ⟨Set.mem_univ _, hy⟩
  have hn := (isOpen_univ.prod hO).mem_nhds hm
  have hF : ContDiffAt ℝ ∞ (Function.uncurry u) (s, y) := hu.contDiffAt hn
  have hG : HasFDerivAt (fderiv ℝ (Function.uncurry u))
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)) (s, y) :=
    (((fd_smooth hO hu).contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hsym : IsSymmSndFDerivAt ℝ (Function.uncurry u) (s, y) :=
    hF.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hL : HasDerivAt (fun r => fderiv ℝ (u r) y v)
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y) ((1 : ℝ), (0 : E)) ((0 : ℝ), v)) s := by
    have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s hG (hasDerivAt_line s y)
    have h3 := ((ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)).hasFDerivAt).comp_hasDerivAt s h2
    have he : (fun r => fderiv ℝ (u r) y v) = (⇑(ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)) ∘
        (fderiv ℝ (Function.uncurry u)) ∘ fun r : ℝ => (r, y)) := by
      funext r
      simpa using fderiv_slice_eq hO hu r hy v
    rw [he]
    simpa using h3
  have hR : HasFDerivAt (fun z => deriv (fun r => u r z) s)
      ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).comp
        ((fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ E))) y := by
    have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
      hasFDerivAt_prodMk_right s y
    have h2 := HasFDerivAt.comp (f := fun z : E => (s, z)) y hG h1
    have h3 := ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).hasFDerivAt).comp y h2
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hy] with z hz
    simpa using deriv_eq hO hu s hz
  rw [hL.deriv, hR.fderiv]
  simpa using hsym.eq ((1 : ℝ), (0 : E)) ((0 : ℝ), v)

end Generic

theorem contDiff_mulRight {n : ℕ} (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff

end SmCalc

theorem sm_calculus : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (u : ℝ → Mat n → W), Sm u → Sm (dt u) ∧ (∀ X : Mat n, Sm (Rt X u)) ∧
      (∀ s, ContDiffOn ℝ ∞ (u s) (GLs n)) ∧ (∀ y ∈ GLs n, ContDiff ℝ ∞ fun s => u s y) ∧
      ∀ (X : Mat n) (s : ℝ), ∀ y ∈ GLs n, dt (Rt X u) s y = Rr X (dt u s) y :=
  fun _ hu => ⟨SmCalc.smooth_deriv isOpen_GLs hu,
    fun X => SmCalc.smooth_field isOpen_GLs hu (SmCalc.contDiff_mulRight X),
    SmCalc.smooth_slice hu, fun _ hy => SmCalc.smooth_line hu hy,
    fun _ s _ hy => SmCalc.deriv_fderiv_comm isOpen_GLs hu _ s hy⟩

end GlobalTheory.CompanionTheory.WaveSpd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WvAlg
section
namespace GlobalTheory.CompanionTheory.WaveFc

open PositivityTheory.RgBcC.Fc

theorem wvAlg : WvAlg := by
  intro c N t y
  have hsq : ((y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = y := by
    rw [← Complex.cpow_nat_mul]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : Even 2 := ⟨1, rfl⟩
    have h0 : Even 0 := ⟨0, rfl⟩
    simp only [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj, h2, h0, if_true, hsq, pow_zero, one_mul]
    first
      | ring
      | (simp [hsq]; ring_nf)
      | simp [hsq]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · intro j
    simp only [PositivityTheory.RgBcC.Fc.wv]
    rw [pow_succ (1 + y ^ 2) N, mul_inv]
    push_cast
    ring

end GlobalTheory.CompanionTheory.WaveFc
end

