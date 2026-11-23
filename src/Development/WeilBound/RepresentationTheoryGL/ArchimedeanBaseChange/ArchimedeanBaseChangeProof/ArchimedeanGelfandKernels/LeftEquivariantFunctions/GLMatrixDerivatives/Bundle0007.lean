module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdcC
section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulLL (a : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

theorem hb_conj_back' (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) :
    (k.1)ᴴ * (k.1 * X * (k.1)ᴴ) * k.1 = X := by
  rw [show (k.1)ᴴ * (k.1 * X * (k.1)ᴴ) * k.1 = (k.1)ᴴ * (((k.1 * X * (k.1)ᴴ)) * k.1) by simp only [Matrix.mul_assoc],
    hb_conj_back]

theorem kapEquiv : KapEquiv := by
  intro n lam E Fr ε ι S Γ T h k hk hkK
  have hopen := isOpen_GLs (n := n)
  have hkd : ∀ y ∈ GLs n, DifferentiableAt ℝ k y := fun y hy =>
    (hk.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hy)
  have hcont := hk.continuousOn_fderiv_of_isOpen hopen (by simp)
  refine ⟨?_, ?_, ?_⟩
  · unfold kapL
    apply continuousOn_finsetSum
    intro p _
    apply continuousOn_const.mul
    apply ContinuousOn.add
    · unfold Ld
      exact (hcont.clm_apply (mulLL (hb p)).continuous.continuousOn).neg
    · exact continuousOn_const.mul hk.continuousOn
  · unfold kapR
    apply continuousOn_finsetSum
    intro p _
    apply ContinuousOn.add
    · unfold Rd
      exact (hcont.clm_apply (mulRL (hb p)).continuous.continuousOn).neg.mul continuousOn_const
    · exact (hk.continuousOn.mul continuousOn_const).mul continuousOn_const
  · intro y hy k₂
    set Φ : (E.V →L[ℂ] E.V) →L[ℝ] (E.V →L[ℂ] E.V) :=
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂)).restrictScalars ℝ with hΦ
    have hyk : y * k₂.1 ∈ GLs n := mem_GLs_mul hy (unit_mem k₂)
    have hEq : (fun z => k (z * k₂.1)) =ᶠ[nhds y] fun z => Φ (k z) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      rw [hkK z hz k₂]
      rfl
    have hD : ∀ Z, fderiv ℝ k (y * k₂.1) (Z * k₂.1) = fderiv ℝ k y Z * E.ρ k₂ := fun Z =>
      fderiv_right k k₂.1 y Φ (hkd _ hyk) (hkd y hy) hEq Z
    constructor
    · have hLd : ∀ X, Ld X k (y * k₂.1) = Ld X k y * E.ρ k₂ := by
        intro X
        unfold Ld
        rw [show X * (y * k₂.1) = (X * y) * k₂.1 by rw [Matrix.mul_assoc], hD, neg_mul]
      unfold kapL
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hLd, hkK y hy k₂]
      simp only [mul_assoc, add_mul]
    · set Y : Fin n × Fin n → Mat n := fun p => k₂.1 * hb p * (k₂.1)ᴴ with hYdef
      have hRd : ∀ p, Rd (hb p) k (y * k₂.1) = Rd (Y p) k y * E.ρ k₂ := by
        intro p
        unfold Rd
        rw [show y * k₂.1 * hb p = (y * Y p) * k₂.1 by
          simp only [hYdef, Matrix.mul_assoc, unit_star_mul, Matrix.mul_one], hD]
      have hε : ∀ p, E.ρ k₂ * ε (hb p) = ε (Y p) * E.ρ k₂ := by
        intro p
        rw [eps_rho h k₂ (Y p) (conj_herm _ _ (hb_herm p)), hYdef]
        dsimp only
        rw [hb_conj_back']
      have hF : ∀ p, E.ρ k₂ * fderiv ℝ Fr 1 (hb p) = fderiv ℝ Fr 1 (Y p) * E.ρ k₂ := by
        intro p
        have := dFr_conj h k₂ (Y p)
        rw [hYdef, hb_conj_back] at this
        rw [this, ← mul_assoc, ← mul_assoc, rho_mul_inv, one_mul]
      let B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V) := LinearMap.mk₂ ℝ
        (fun H H' => -(fderiv ℝ k y (y * H')) * ε H + k y * ε H * fderiv ℝ Fr 1 H')
        (fun H₁ H₂ H' => by simp only [map_add (f := _), mul_add, add_mul]; abel)
        (fun c H H' => by simp only [map_smul, mul_smul_comm, smul_mul_assoc, smul_add])
        (fun H H₁ H₂ => by simp only [Matrix.mul_add, map_add (f := _), neg_add, add_mul, mul_add]; abel)
        (fun c H H' => by
          simp only [Matrix.mul_smul, map_smul, neg_smul, smul_mul_assoc, mul_smul_comm, smul_add, ← smul_neg])
      have hkapR : kapR ε Fr k y = ∑ p, B (hb p) (hb p) := rfl
      have hterm : ∀ p, -(Rd (hb p) k (y * k₂.1)) * ε (hb p) + k (y * k₂.1) * ε (hb p) * fderiv ℝ Fr 1 (hb p) =
          B (Y p) (Y p) * E.ρ k₂ := by
        intro p
        rw [hRd, hkK y hy k₂]
        show -(Rd (Y p) k y * E.ρ k₂) * ε (hb p) + k y * E.ρ k₂ * ε (hb p) * fderiv ℝ Fr 1 (hb p) =
          (-(fderiv ℝ k y (y * Y p)) * ε (Y p) + k y * ε (Y p) * fderiv ℝ Fr 1 (Y p)) * E.ρ k₂
        rw [neg_mul, mul_assoc (Rd (Y p) k y), hε, mul_assoc (k y), hε, mul_assoc (k y), mul_assoc (ε (Y p)), hF]
        simp only [Rd, add_mul, neg_mul, mul_assoc]
      unfold kapR
      rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_mul]
      congr 1
      rw [basis_inv B k₂]
      rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfDC
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.DCc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem dc_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) :
    Set.EqOn (DC ε Fr f) (DC ε Fr f') U := by
  intro x hx
  have hev : f =ᶠ[𝓝 x] f' := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
  simp only [DC, Rd, hev.fderiv_eq, h hx]

theorem cont_partial {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (u : ℝ → Mat n → V)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)) (x : Mat n) (hx : x ∈ GLs n) (X : Mat n) :
    Continuous (fun t => u t x) ∧ Continuous (fun t => Rd X (u t) x) := by
  have hs : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod (isOpen_GLs n)
  have hc : ContinuousOn (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ GLs n) :=
    hu.continuousOn_fderiv_of_isOpen hs (by simp)
  have key : ∀ t, fderiv ℝ (u t) x =
      (fderiv ℝ (Function.uncurry u) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n)) := by
    intro t
    have hd : DifferentiableAt ℝ (Function.uncurry u) (t, x) :=
      (hu.differentiableOn (by simp)).differentiableAt (hs.mem_nhds ⟨Set.mem_univ _, hx⟩)
    exact (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  have hline : Continuous fun t : ℝ => ((t, x) : ℝ × Mat n) := continuous_id.prodMk continuous_const
  constructor
  · exact hu.continuousOn.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)
  · simp only [Rd, key, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact (hc.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)).clm_apply continuous_const

theorem bump_cpt (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T) : HasCompactSupport fun t => (g t : ℂ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) ?_
  intro t ht
  simp only [Complex.ofReal_eq_zero]
  exact hgb.2.2 t (by simpa [Real.norm_eq_abs, not_le] using ht)

theorem int_bump {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T)
    (φ : ℝ → V) (hφ : Continuous φ) : Integrable fun t => (g t : ℂ) • φ t := by
  refine ((Complex.continuous_ofReal.comp hgb.1.continuous).smul hφ).integrable_of_hasCompactSupport ?_
  exact (bump_cpt g T hgb).smul_right

theorem param_dc {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) (u : ℝ → Mat n → V)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)) (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T)
    (hRd : ∀ X, ∀ x ∈ GLs n, Rd X (fun x' => ∫ t, (g t : ℂ) • u t x') x = ∫ t, (g t : ℂ) • Rd X (u t) x)
    (x : Mat n) (hx : x ∈ GLs n) :
    ∫ t, (g t : ℂ) • DC ε Fr (u t) x = DC ε Fr (fun x' => ∫ t, (g t : ℂ) • u t x') x := by
  have hc := fun X => cont_partial u hu x hx X
  have ia : ∀ X, Integrable (fun t => (g t : ℂ) • Rd X (u t) x) := fun X => int_bump g T hgb _ (hc X).2
  have ib : Integrable (fun t => (g t : ℂ) • u t x) := int_bump g T hgb _ (hc 0).1
  have iab : ∀ p : Fin n × Fin n, Integrable (fun t => (g t : ℂ) • Rd (hb p) (u t) x +
      (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x)) :=
    fun p => (ia _).add ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib)
  have hpt : ∀ t, (g t : ℂ) • DC ε Fr (u t) x = ∑ p : Fin n × Fin n, ε (hb p)
      ((g t : ℂ) • Rd (hb p) (u t) x + (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x)) := by
    intro t
    simp only [DC, Finset.smul_sum, map_add (f := _), map_smul, smul_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum _ (fun p _ => (ε (hb p)).integrable_comp (iab p))]
  simp only [DC, hRd _ x hx]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [(ε (hb p)).integral_comp_comm (iab p),
    integral_add (ia _) ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib),
    (fderiv ℝ Fr 1 (hb p)).integral_comp_comm ib]

end PositivityTheory.RgBcC.LfSt.ChainPf.DCc
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HasDerivAtFderivLine
section
noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbFr

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs' : IsOpen (GLs n) :=
  isOpen_compl_singleton.preimage (contDiff_det (n := n)).continuous

theorem line_mem (X : Mat n) : ∀ᶠ t : ℝ in 𝓝 0, 1 + t • X ∈ GLs n := det_line_ne X

theorem hasDerivAt_fderiv_line {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : Mat n → Z} {x : Mat n}
    (hF : DifferentiableAt ℝ F x) (v : Mat n) : HasDerivAt (fun t : ℝ => F (x + t • v)) (fderiv ℝ F x v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simp only [id, one_smul] at h
    exact h
  exact hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

theorem diffAt_of {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : Mat n → Z} (hF : ContDiffOn ℝ ∞ F (GLs n))
    {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ F x :=
  ((hF.contDiffAt (isOpen_GLs'.mem_nhds hx)).differentiableAt (by simp))

theorem one_mem : (1 : Mat n) ∈ GLs n := by simp [GLs]

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem hasDerivAt_Fr_line (h : CxData lam E Fr ε ι S Γ T) (Y : Mat n) :
    HasDerivAt (fun t : ℝ => Fr (1 + t • Y)) (fderiv ℝ Fr 1 Y) 0 :=
  hasDerivAt_fderiv_line (diffAt_of h.smooth one_mem) Y

theorem conjT_line {X : Mat n} (hX : X.IsHermitian) (t : ℝ) : (1 + t • X)ᴴ = 1 + t • X := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hX.eq]
  simp

theorem frComm_at (h : CxData lam E Fr ε ι S Γ T) {X H : Mat n} (hX : X.IsHermitian) (hH : H.IsHermitian) :
    fderiv ℝ Fr 1 X * ε H = ε H * fderiv ℝ Fr 1 X - ε (X * H + H * X) ∧ Γ * fderiv ℝ Fr 1 X = fderiv ℝ Fr 1 X * Γ := by
  have hF := hasDerivAt_Fr_line h X
  constructor
  · set εc : Mat n →L[ℝ] (E.V →L[ℂ] E.V) := LinearMap.toContinuousLinearMap ε
    have hM : HasDerivAt (fun t : ℝ => (1 + t • X) * H * (1 + t • X)) (X * H + H * X) 0 := by
      have := hasDerivAt_matmul (hasDerivAt_matmul (hasDerivAt_line X) (hasDerivAt_const (0 : ℝ) H)) (hasDerivAt_line X)
      refine this.congr_deriv ?_
      simp
    have hE : HasDerivAt (fun t : ℝ => ε ((1 + t • X) * H * (1 + t • X))) (ε (X * H + H * X)) 0 :=
      εc.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hM
    have hR := hF.mul hE
    have hL := hF.const_mul (ε H)
    have e : ∀ᶠ t : ℝ in 𝓝 0, ε H * Fr (1 + t • X) = Fr (1 + t • X) * ε ((1 + t • X) * H * (1 + t • X)) := by
      filter_upwards [line_mem X] with t ht
      have := h.frε _ ht H hH
      rwa [conjT_line hX] at this
    have hL' := hL.congr_of_eventuallyEq (e.mono fun t ht => ht.symm)
    have u := hL'.unique hR
    simp only [zero_smul, add_zero, h.one, one_mul, Matrix.mul_one] at u
    rw [u]; abel
  · have hL := hF.const_mul Γ
    have hR := hF.mul_const Γ
    have e : ∀ᶠ t : ℝ in 𝓝 0, Γ * Fr (1 + t • X) = Fr (1 + t • X) * Γ := by
      filter_upwards [line_mem X] with t ht
      exact h.ΓFr _ ht
    exact (hL.congr_of_eventuallyEq (e.mono fun t ht => ht.symm)).unique hR

end

theorem frComm : FrComm := fun _ _ _ _ _ _ _ _ _ h _X _H hX hH => frComm_at h hX hH

end PositivityTheory.RgBcC.LfSt.Kchain.KbFr
end
end

