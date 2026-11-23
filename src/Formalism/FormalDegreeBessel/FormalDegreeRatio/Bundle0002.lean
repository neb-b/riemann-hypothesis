module

public import Formalism.FormalDegreeBessel.Bundle0001
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

@[expose] public section

-- bundled from Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.QuantumDeterminants

namespace BesselUnipotentEquiv

variable {k r : ℕ}

theorem continuous_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (lmulM (k := k) (r := r) a) := by
  first
  | exact (continuous_const.matrix_mul continuous_id : Continuous fun x : Mt k r => a * Matrix.of x)
  | exact continuous_pi fun i => continuous_pi fun j => by
      simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
      fun_prop

def lmulEquiv (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left a (Matrix.of x) ha
  right_inv x := Matrix.mul_nonsing_inv_cancel_left a (Matrix.of x) ha
  measurable_toFun := (continuous_lmulM a).measurable
  measurable_invFun := (continuous_lmulM a⁻¹).measurable

theorem psi_one (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z) :
    psi k r z c 1 = 1 := by
  have h : ell k r z 1 = 0 := by
    unfold ell
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with h'
    · rw [Matrix.one_apply_ne]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [Matrix.one_mulVec]
      exact hz _ (Or.inl (by simp [eI]))
  simp [psi, h]

theorem star_psi_inv (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z)
    (n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hn : n ∈ Nset k r) :
    star (psi k r z c n⁻¹) = psi k r z c n := by
  have hinv := (unipotent_subgroup_holds k r).2.2 n hn
  have hu := WeylGroupFacts.isUnit_of_uh hn.1
  have h1 : psi k r z c n⁻¹ * psi k r z c n = 1 := by
    rw [← (additive_character_holds k r z c hz n⁻¹ hinv).1 n hn, Matrix.nonsing_inv_mul _ hu, psi_one z c hz]
  have h2 : star (psi k r z c n⁻¹) * psi k r z c n⁻¹ = 1 := by
    rw [Complex.star_def, Complex.conj_mul', (additive_character_holds k r z c hz n⁻¹ hinv).2]
    simp
  calc star (psi k r z c n⁻¹) = star (psi k r z c n⁻¹) * (psi k r z c n⁻¹ * psi k r z c n) := by
        rw [h1, mul_one]
    _ = psi k r z c n := by rw [← mul_assoc, h2, one_mul]

theorem coe_lmulEquiv (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    ⇑(lmulEquiv (k := k) (r := r) a ha) = lmulM a := rfl

theorem of_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) :
    Matrix.of (lmulM a x) = a * Matrix.of x := rfl

end BesselUnipotentEquiv

open BesselUnipotentEquiv in
theorem bessel_unipotent_equiv_holds : BesselNEquiv := by
  intro Wp Wq _ _ _ _ _ _ k r z z' c π π' μW μN μW' _ _ _ F hz hz' hNc hinvN g n₀ hn₀ n₀' hn₀'
  have hinv' : n₀'⁻¹ ∈ Nset k r := (unipotent_subgroup_holds k r).2.2 n₀' hn₀'
  have hu0 : IsUnit n₀.det := WeylGroupFacts.isUnit_of_uh hn₀.1
  have hu0' : IsUnit n₀'.det := WeylGroupFacts.isUnit_of_uh hn₀'.1
  have hui' : IsUnit (n₀'⁻¹).det := WeylGroupFacts.isUnit_of_uh hinv'.1
  let e1 := lmulEquiv (k := k) (r := r) n₀ hu0
  let e2 := lmulEquiv (k := k) (r := r) n₀'⁻¹ hui'
  let Φ := ((MeasurableEquiv.refl (Mt k r)).prodCongr e1).prodCongr
    ((MeasurableEquiv.refl (Mt k r)).prodCongr e2)
  have hΦapp : ∀ q : (Mt k r × Mt k r) × (Mt k r × Mt k r),
      Φ q = ((q.1.1, lmulM n₀ q.1.2), (q.2.1, lmulM n₀'⁻¹ q.2.2)) := fun q => rfl
  have hp1 : MeasurePreserving e1 μN μN :=
    ⟨e1.measurable, by rw [coe_lmulEquiv]; exact hinvN n₀ hn₀⟩
  have hp2 : MeasurePreserving e2 μN μN :=
    ⟨e2.measurable, by rw [coe_lmulEquiv]; exact hinvN n₀'⁻¹ hinv'⟩
  have hpΦ : MeasurePreserving Φ ((μW.prod μN).prod (μW'.prod μN))
      ((μW.prod μN).prod (μW'.prod μN)) :=
    ((MeasurePreserving.id μW).prod hp1).prod ((MeasurePreserving.id μW').prod hp2)
  have haeN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := ae_iff.2 hNc
  have hae1 : ∀ᵐ q ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of q.1.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae haeN)
  have hae2 : ∀ᵐ q ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of q.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae haeN)
  have key : ∀ h m h' m' : Mt k r, Matrix.of m ∈ Nset k r → Matrix.of m' ∈ Nset k r →
      (psi k r z c (n₀ * Matrix.of m) * star (psi k r z' c (n₀'⁻¹ * Matrix.of m'))) •
        ((π (Matrix.of h)).comp ((F ((Matrix.of h)⁻¹ * (n₀ * Matrix.of m)⁻¹ * (n₀ * g * n₀') *
          (n₀'⁻¹ * Matrix.of m') * Matrix.of h')).comp (π' (Matrix.of h')⁻¹))) =
      (psi k r z c n₀ * psi k r z' c n₀') •
        ((psi k r z c (Matrix.of m) * star (psi k r z' c (Matrix.of m'))) •
          ((π (Matrix.of h)).comp ((F ((Matrix.of h)⁻¹ * (Matrix.of m)⁻¹ * g *
            Matrix.of m' * Matrix.of h')).comp (π' (Matrix.of h')⁻¹)))) := by
    intro h m h' m' hm hm'
    have hmat : (Matrix.of h)⁻¹ * (n₀ * Matrix.of m)⁻¹ * (n₀ * g * n₀') *
        (n₀'⁻¹ * Matrix.of m') * Matrix.of h' =
        (Matrix.of h)⁻¹ * (Matrix.of m)⁻¹ * g * Matrix.of m' * Matrix.of h' := by
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu0, Matrix.mul_nonsing_inv_cancel_left _ _ hu0']
    rw [hmat, smul_smul]
    congr 1
    rw [(additive_character_holds k r z c hz n₀ hn₀).1 _ hm, (additive_character_holds k r z' c hz' _ hinv').1 _ hm',
      star_mul', star_psi_inv z' c hz' n₀' hn₀']
    ring
  unfold besselJ
  rw [← hpΦ.integral_comp', ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hae1, hae2] with q hm hm'
  rw [hΦapp]
  simp only [of_lmulM]
  exact key q.1.1 q.1.2 q.2.1 q.2.2 hm hm'

end Formalism.QuantumDeterminants
end
end

-- bundled from Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.QuantumDeterminants

namespace BesselUnitaryEquiv

variable {k r : ℕ}

theorem continuous_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (lmulM (k := k) (r := r) a) := by
  unfold lmulM
  first
  | fun_prop
  | exact continuous_const.matrix_mul continuous_id
  | continuity

theorem continuous_conjM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (conjM (k := k) (r := r) a) := by
  unfold conjM
  first
  | fun_prop
  | exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  | continuity

def lmulE (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv x := by
    have : a⁻¹ * (a * Matrix.of x) = Matrix.of x := Matrix.nonsing_inv_mul_cancel_left _ _ ha
    exact this
  right_inv x := by
    have : a * (a⁻¹ * Matrix.of x) = Matrix.of x := Matrix.mul_nonsing_inv_cancel_left _ _ ha
    exact this
  measurable_toFun := (continuous_lmulM a).measurable
  measurable_invFun := (continuous_lmulM a⁻¹).measurable

def conjE (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    Mt k r ≃ᵐ Mt k r where
  toFun := conjM a
  invFun := conjM a⁻¹
  left_inv x := by
    have : a⁻¹ * (a * Matrix.of x * a⁻¹) * a⁻¹⁻¹ = Matrix.of x := by
      simp only [Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha,
        Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ ha]
    exact this
  right_inv x := by
    have : a * (a⁻¹ * Matrix.of x * a⁻¹⁻¹) * a⁻¹ = Matrix.of x := by
      simp only [Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha,
        Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ ha]
    exact this
  measurable_toFun := (continuous_conjM a).measurable
  measurable_invFun := (continuous_conjM a⁻¹).measurable

theorem integral_transfer {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    (f : α → α) (hf : MeasurePreserving f μ μ) (hfe : MeasurableEmbedding f)
    (L : E ≃L[ℂ] F) (I₀ : α → E) (I₁ : α → F)
    (h : ∀ᵐ p ∂μ, I₁ (f p) = L (I₀ p)) : ∫ p, I₁ p ∂μ = L (∫ p, I₀ p ∂μ) := by
  rw [← hf.integral_comp hfe I₁, integral_congr_ae h]
  exact L.integral_comp_comm I₀

theorem rep_inv {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℕ}
    {U : Set (Matrix (Fin m) (Fin m) ℂ)} {π : Matrix (Fin m) (Fin m) ℂ → (W →L[ℂ] W)}
    (hπ : IsCRepOn U π) {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ U) (hb : b ∈ U)
    (hab : a * b = 1) (x : W) : π a (π b x) = x := by
  unfold IsCRepOn at hπ
  rw [← ContinuousLinearMap.comp_apply, ← hπ.2 a ha b hb, hab, hπ.1]
  try rfl

end BesselUnitaryEquiv

open BesselUnitaryEquiv in
theorem bessel_unitary_equiv_holds : BesselUEquiv := by
  intro Wp Wq _ _ _ _ _ _ k r z z' c π π' μW μN μW' _ _ _ F hz hz' hN hW hW' hWl hW'l hNc hπ hπ'
    g h₀ hh₀ h₀' hh₀'
  have hu₀ := WeylGroupFacts.isUnit_of_uh hh₀.1
  have hu₀' := WeylGroupFacts.isUnit_of_uh hh₀'.1
  have hi₀ : h₀⁻¹ ∈ UWset k r z := WeylGroupFacts.uw_inv hh₀
  have hi₀' : h₀'⁻¹ ∈ UWset k r z' := WeylGroupFacts.uw_inv hh₀'
  have hui₀' : IsUnit (h₀'⁻¹).det := WeylGroupFacts.isUnit_of_uh hi₀'.1

  let Φ : (Mt k r × Mt k r) × (Mt k r × Mt k r) ≃ᵐ (Mt k r × Mt k r) × (Mt k r × Mt k r) :=
    ((lmulE h₀ hu₀).prodCongr (conjE h₀ hu₀)).prodCongr
      ((lmulE h₀'⁻¹ hui₀').prodCongr (conjE h₀'⁻¹ hui₀'))
  have hΦe : MeasurableEmbedding (Prod.map (Prod.map (lmulM h₀) (conjM h₀))
      (Prod.map (lmulM h₀'⁻¹) (conjM h₀'⁻¹)) :
        (Mt k r × Mt k r) × (Mt k r × Mt k r) → (Mt k r × Mt k r) × (Mt k r × Mt k r)) :=
    Φ.measurableEmbedding
  have hΦ : MeasurePreserving (Prod.map (Prod.map (lmulM h₀) (conjM h₀))
      (Prod.map (lmulM h₀'⁻¹) (conjM h₀'⁻¹)) :
        (Mt k r × Mt k r) × (Mt k r × Mt k r) → (Mt k r × Mt k r) × (Mt k r × Mt k r))
      ((μW.prod μN).prod (μW'.prod μN)) ((μW.prod μN).prod (μW'.prod μN)) := by
    refine MeasurePreserving.prod (MeasurePreserving.prod ?_ ?_) (MeasurePreserving.prod ?_ ?_)
    · exact ⟨(lmulE h₀ hu₀).measurable, hWl h₀ hh₀⟩
    · exact ⟨(conjE h₀ hu₀).measurable, hNc h₀ (Or.inl hh₀)⟩
    · exact ⟨(lmulE h₀'⁻¹ hui₀').measurable, hW'l _ hi₀'⟩
    · exact ⟨(conjE h₀'⁻¹ hui₀').measurable, hNc _ (Or.inr hi₀')⟩

  have aW : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.2 hW
  have aW' : ∀ᵐ x ∂μW', Matrix.of x ∈ UWset k r z' := ae_iff.2 hW'
  have aN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := ae_iff.2 hN
  have q11 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of p.1.1 ∈ UWset k r z :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_fst).ae aW
  have q12 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_fst).ae aN
  have q21 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of p.2.1 ∈ UWset k r z' :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd).ae aW'
  have q22 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae aN

  let e₂ : Wp ≃L[ℂ] Wp := ContinuousLinearEquiv.equivOfInverse (π h₀) (π h₀⁻¹)
    (fun x => rep_inv hπ hi₀ hh₀ (Matrix.nonsing_inv_mul _ hu₀) x)
    (fun x => rep_inv hπ hh₀ hi₀ (Matrix.mul_nonsing_inv _ hu₀) x)
  let e₁ : Wq ≃L[ℂ] Wq := ContinuousLinearEquiv.equivOfInverse (π' h₀'⁻¹) (π' h₀')
    (fun x => rep_inv hπ' hh₀' hi₀' (Matrix.mul_nonsing_inv _ hu₀') x)
    (fun x => rep_inv hπ' hi₀' hh₀' (Matrix.nonsing_inv_mul _ hu₀') x)
  let L : (Wq →L[ℂ] Wp) ≃L[ℂ] (Wq →L[ℂ] Wp) := e₁.arrowCongr e₂
  have hL : ∀ X : Wq →L[ℂ] Wp, L X = (π h₀).comp (X.comp (π' h₀')) := by
    intro X; ext y; rfl
  rw [← hL]
  unfold besselJ
  refine integral_transfer _ hΦ hΦe L _ _ ?_
  filter_upwards [q11, q12, q21, q22] with p hK hM hK' hM'
  obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := p
  rw [hL]
  set K : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of a
  set M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of b
  set K' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of a'
  set M' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of b'
  have ep : psi k r z c (h₀ * M * h₀⁻¹) = psi k r z c M := by
    unfold psi; rw [(unitary_weyl_normal_holds k r z hz h₀ hh₀ M hM).2]
  have ep' : psi k r z' c (h₀'⁻¹ * M' * h₀'⁻¹⁻¹) = psi k r z' c M' := by
    unfold psi; rw [(unitary_weyl_normal_holds k r z' hz' h₀'⁻¹ hi₀' M' hM').2]
  have earg : (h₀ * K)⁻¹ * (h₀ * M * h₀⁻¹)⁻¹ * (h₀ * g * h₀') * (h₀'⁻¹ * M' * h₀'⁻¹⁻¹) *
      (h₀'⁻¹ * K') = K⁻¹ * M⁻¹ * g * M' * K' := by
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu₀,
      Matrix.nonsing_inv_nonsing_inv _ hu₀', Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu₀, Matrix.mul_nonsing_inv_cancel_left _ _ hu₀']
  have eπ : π (h₀ * K) = (π h₀).comp (π K) := hπ.2 h₀ hh₀ K hK
  have einv : (h₀'⁻¹ * K')⁻¹ = K'⁻¹ * h₀' := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu₀']
  have eπ' : π' (K'⁻¹ * h₀') = (π' K'⁻¹).comp (π' h₀') := hπ'.2 _ (WeylGroupFacts.uw_inv hK') _ hh₀'
  show (psi k r z c (h₀ * M * h₀⁻¹) * star (psi k r z' c (h₀'⁻¹ * M' * h₀'⁻¹⁻¹))) •
      ((π (h₀ * K)).comp ((F ((h₀ * K)⁻¹ * (h₀ * M * h₀⁻¹)⁻¹ * (h₀ * g * h₀') *
        (h₀'⁻¹ * M' * h₀'⁻¹⁻¹) * (h₀'⁻¹ * K'))).comp (π' (h₀'⁻¹ * K')⁻¹))) =
    (π h₀).comp (((psi k r z c M * star (psi k r z' c M')) •
      ((π K).comp ((F (K⁻¹ * M⁻¹ * g * M' * K')).comp (π' K'⁻¹)))).comp (π' h₀'))
  rw [ep, ep', earg, eπ, einv, eπ']
  ext y
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul]

end Formalism.QuantumDeterminants
end
end

