module

public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfChart
section
noncomputable section

open Matrix Filter Topology
open scoped NNReal

namespace Formalism.IndefR.Tow.SobPf

namespace Chart

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem norm_le_sum (X : Matrix (Fin n) (Fin n) ℂ) : ‖X‖ ≤ ∑ i, ∑ j, ‖X i j‖ := by
  rw [Matrix.linfty_opNorm_def]
  have : ((Finset.univ).sup fun i => ∑ j, ‖X i j‖₊) ≤ ∑ i, ∑ j, ‖X i j‖₊ :=
    Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊) (fun _ _ => zero_le) (Finset.mem_univ i)
  calc _ ≤ ((∑ i, ∑ j, ‖X i j‖₊ : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 this
    _ = _ := by push_cast; rfl

def lieSub (G : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := lieG G
  add_mem' := by
    intro X Y hX hY
    have hX' : Xᴴ * G + G * X = 0 := hX
    have hY' : Yᴴ * G + G * Y = 0 := hY
    show (X + Y)ᴴ * G + G * (X + Y) = 0
    rw [conjTranspose_add, add_mul, mul_add]
    calc _ = (Xᴴ * G + G * X) + (Yᴴ * G + G * Y) := by abel
      _ = 0 := by rw [hX', hY', add_zero]
  zero_mem' := zero_mem_lieG G
  smul_mem' := by
    intro c X hX
    have h := CCRuleCW.lie_smul G X hX c
    rw [Complex.coe_smul] at h
    exact h

theorem sobChart_holds : SobChart := by
  intro n G s _
  classical
  let L := lieSub G
  let d := Module.finrank ℝ L
  let b := Module.finBasis ℝ L
  let Y : Fin d → Matrix (Fin n) (Fin n) ℂ := fun i => (b i : Matrix (Fin n) (Fin n) ℂ)
  have hY : ∀ i, Y i ∈ lieG G := fun i => (b i).2
  refine ⟨d, Y, hY, ?_⟩
  let ψ : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := L.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : ∀ t, ψ t = lin Y t := by
    intro t
    simp [ψ, lin_apply, Y, Module.Basis.equivFun_symm_apply]
    try rfl
  have hinj : LinearMap.ker ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp b.equivFun.symm.injective
  obtain ⟨Q0, hQ0⟩ := ψ.exists_leftInverse_of_injective hinj
  let Q : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap Q0
  have hQψ : ∀ t, Q (ψ t) = t := fun t => LinearMap.congr_fun hQ0 t
  have hback : ∀ X ∈ lieG G, ψ (Q X) = X := by
    intro X hX
    have e : X = ψ (b.equivFun ⟨X, hX⟩) := by simp [ψ]
    rw [e, hQψ]
  let f : (Fin d → ℝ) → (Fin d → ℝ) := fun t => Q (cay (oneProd Y t))
  have hcay : HasStrictFDerivAt (cay : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (oneProd Y 0) := by
    rw [oneProd_zero]; exact hasStrictFDerivAt_cay
  have hΦ := hcay.comp (0 : Fin d → ℝ) (hasStrictFDerivAt_oneProd Y)
  have hf := Q.hasStrictFDerivAt.comp (0 : Fin d → ℝ) hΦ
  have hf' : HasStrictFDerivAt f
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))) 0 := by
    refine hf.congr_fderiv ?_
    ext1 t
    change Q (lin Y t) = t
    rw [← hψ]
    exact hQψ t
  have hmap := hf'.map_nhds_eq_of_equiv
  have hcay1 : cay (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [cay]
  have hf0 : f 0 = 0 := by
    show Q (cay (oneProd Y 0)) = 0
    rw [oneProd_zero, hcay1, map_zero]
  rw [hf0] at hmap
  intro ε hε
  have hcont : ContinuousAt (oneProd Y) 0 := (hasStrictFDerivAt_oneProd Y).continuousAt
  have hUnit : {t : Fin d → ℝ | IsUnit (oneProd Y t + 1)} ∈ 𝓝 (0 : Fin d → ℝ) := by
    have hc : ContinuousAt (fun t => oneProd Y t + 1) 0 := hcont.add continuousAt_const
    have h2 : IsUnit (oneProd Y 0 + 1) := by rw [oneProd_zero]; exact isUnit_two
    exact hc.preimage_mem_nhds (Units.isOpen.mem_nhds h2)
  have hB : Metric.ball (0 : Fin d → ℝ) ε ∩ {t | IsUnit (oneProd Y t + 1)} ∈ 𝓝 (0 : Fin d → ℝ) :=
    Filter.inter_mem (Metric.ball_mem_nhds 0 hε) hUnit
  have hfB : f '' (Metric.ball (0 : Fin d → ℝ) ε ∩ {t | IsUnit (oneProd Y t + 1)}) ∈ 𝓝 (0 : Fin d → ℝ) := by
    rw [← hmap]; exact Filter.image_mem_map hB
  have hk : ContinuousAt (fun g => Q (cay g)) (1 : Matrix (Fin n) (Fin n) ℂ) :=
    Q.continuous.continuousAt.comp hasStrictFDerivAt_cay.continuousAt
  have hN : {g : Matrix (Fin n) (Fin n) ℂ | Q (cay g) ∈
      f '' (Metric.ball (0 : Fin d → ℝ) ε ∩ {t | IsUnit (oneProd Y t + 1)})} ∩ {g | IsUnit (g + 1)} ∈
      𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) := by
    refine Filter.inter_mem ?_ ?_
    · refine hk.preimage_mem_nhds ?_
      show _ ∈ 𝓝 (Q (cay 1))
      rw [hcay1, map_zero]
      exact hfB
    · have hc : ContinuousAt (fun g : Matrix (Fin n) (Fin n) ℂ => g + 1) 1 :=
        continuousAt_id.add continuousAt_const
      exact hc.preimage_mem_nhds (Units.isOpen.mem_nhds isUnit_two)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN
  have hδ : 0 < r / ((n : ℝ) * n + 1) := by positivity
  refine ⟨r / ((n : ℝ) * n + 1), hδ, ?_⟩
  intro g hg hgd
  have hnorm : ‖g - 1‖ < r := by
    calc ‖g - 1‖ ≤ ∑ i, ∑ j, ‖(g - 1) i j‖ := norm_le_sum _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, r / ((n : ℝ) * n + 1) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [Matrix.sub_apply]; exact (hgd i j).le
      _ = (n : ℝ) * n * (r / ((n : ℝ) * n + 1)) := by simp [Finset.sum_const, mul_assoc]
      _ < r := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hgN := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hnorm)
  obtain ⟨⟨t, ⟨htB, htU⟩, hft⟩, hgU⟩ := hgN
  refine ⟨t, fun i => ?_, ?_⟩
  · have h1 := norm_le_pi_norm t i
    have h2 := mem_ball_zero_iff.1 htB
    rw [Real.norm_eq_abs] at h1
    linarith
  · have e1 : cay (oneProd Y t) = cay g := calc
      cay (oneProd Y t) = ψ (Q (cay (oneProd Y t))) :=
          (hback _ (cay_mem G _ (oneProd_mem G Y hY t) htU)).symm
      _ = ψ (Q (cay g)) := congrArg ψ hft
      _ = cay g := hback _ (cay_mem G g hg hgU)
    exact (cay_inj htU hgU e1).symm

end Chart

theorem sobChart_holds : SobChart := Chart.sobChart_holds

end Formalism.IndefR.Tow.SobPf

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ContOnPIterAvgTerm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexOrder

namespace Formalism.IndefR.Tow.SobPf.Avg

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def hcFun (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : (Fin n → Fin n → ℂ) → ℂ) (w : H)
    (u : Matrix (Fin n) (Fin n) ℂ) {d d' : ℕ} (Z : Fin (d + d') → Matrix (Fin n) (Fin n) ℂ) (j : ℕ)
    (q : (Fin (d + d') → ℝ) × (Fin n → Fin n → ℂ)) : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) H :=
  (p q.2 • (π u).restrictScalars ℝ).compContinuousMultilinearMap
    ((iteratedFDeriv ℝ j (fun r => π (oneProd Z r) w) q.1).compContinuousLinearMap (fun _ => appL d d'))

set_option maxHeartbeats 1000000 in
theorem continuous_hcFun {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : (Fin n → Fin n → ℂ) → ℂ} {w : H}
    (u : Matrix (Fin n) (Fin n) ℂ) {d d' : ℕ} {Z : Fin (d + d') → Matrix (Fin n) (Fin n) ℂ}
    (hp : Continuous p) (hGZ : ContDiff ℝ ∞ fun r => π (oneProd Z r) w) (j : ℕ) :
    Continuous (hcFun π p w u Z j) := by
  have hM : Continuous fun q : (Fin (d + d') → ℝ) × (Fin n → Fin n → ℂ) =>
      (iteratedFDeriv ℝ j (fun r => π (oneProd Z r) w) q.1).compContinuousLinearMap
        (fun _ : Fin j => appL d d') :=
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => appL d d')).continuous.comp
      ((hGZ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp continuous_fst)
  have hL : Continuous fun q : (Fin (d + d') → ℝ) × (Fin n → Fin n → ℂ) =>
      p q.2 • (π u).restrictScalars ℝ :=
    (hp.comp continuous_snd).smul continuous_const
  have h := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => Fin d → ℝ) H H).continuous.comp
    hL).clm_apply hM
  unfold hcFun
  simpa using h


set_option maxHeartbeats 1000000 in
theorem contOn_pIter_avgTerm (h4 : SobChart) {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s)
    {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hπ : IsGRep G π) {w : H} (hw : SmoothVec (lieG G) π w)
    {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) {d : ℕ} {Xs : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (hXs : ∀ i, Xs i ∈ lieG G) (j : ℕ) :
    ContinuousOn (fun q : (Fin d → ℝ) × (Fin n → Fin n → ℂ) => pIter (avgTerm π p w Xs) j q.1 q.2)
      (Set.univ ×ˢ Kset G s) := by
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    have h1 := hs.2.2.det_pos.ne'
    rw [Matrix.det_mul] at h1
    exact left_ne_zero_of_mul h1
  obtain ⟨d', Y, hY, hch⟩ := h4 G s hs
  intro q0 hq0
  obtain ⟨t0, k0⟩ := q0
  have hk0 : Matrix.of k0 ∈ KAt G s := hq0.2
  obtain ⟨u, hu_eq⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ, u = Matrix.of k0 := ⟨_, rfl⟩
  have hu : u ∈ Formalism.QuantumDeterminants.UH G := by rw [hu_eq]; exact hk0.1
  have hdu : IsUnit u.det := by
    have h : uᴴ * G * u = G := hu
    have h' := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul] at h'
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h'
    exact hG.ne_zero h'.symm
  have hA : ∀ i, Fin.append (fun i => u⁻¹ * Xs i * u) Y i ∈ lieG G :=
    append_mem_lieG (fun i => conj_mem_lieG hG hu (hXs i)) hY
  have hc := continuous_hcFun (π := π) (w := w) u (Z := Fin.append (fun i => u⁻¹ * Xs i * u) Y) hp
    (contDiff_orbit hw hA) j
  have hk0' : Matrix.of k0 = u * oneProd Y 0 := by rw [oneProd_zero, mul_one, hu_eq]
  have hval : ∀ (t : Fin d → ℝ) (k : Fin n → Fin n → ℂ) (s' : Fin d' → ℝ), Matrix.of k = u * oneProd Y s' →
      pIter (avgTerm π p w Xs) j t k =
        hcFun π p w u (Fin.append (fun i => u⁻¹ * Xs i * u) Y) j (Fin.append t s', k) :=
    fun t k s' hk => pIter_avgTerm hG hπ hw hXs hY hu s' hk j t
  refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
  obtain ⟨η, hη, hHc⟩ := Metric.continuous_iff.1 hc (Fin.append t0 0, k0) ε hε
  obtain ⟨δ, hδ, hchδ⟩ := hch η hη
  have hV : IsOpen {k : Fin n → Fin n → ℂ |
      ∀ i j, ‖(u⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ} := by
    have hcont : ∀ i j, Continuous fun k : Fin n → Fin n → ℂ =>
        ‖(u⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ := fun i j =>
      (((continuous_const.matrix_mul
        (continuous_id' : Continuous fun k : Fin n → Fin n → ℂ => Matrix.of k)).matrix_elem i j).sub
          continuous_const).norm
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt (hcont i j) continuous_const
  have hk0V : ∀ i j, ‖(u⁻¹ * Matrix.of k0) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ := by
    intro i j
    rw [← hu_eq, Matrix.nonsing_inv_mul _ hdu, sub_self, norm_zero]
    exact hδ
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hV k0 hk0V
  refine ⟨min η ρ, lt_min hη hρ, fun {x} hx hdx => ?_⟩
  obtain ⟨t, k⟩ := x
  rw [Prod.dist_eq] at hdx
  have hd1 : dist t t0 < η := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hdx (min_le_left _ _))
  have hd2 : dist k k0 < ρ := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hdx (min_le_right _ _))
  have hd3 : dist k k0 < η := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hdx (min_le_left _ _))
  have hkV := hρV (Metric.mem_ball.2 hd2)
  have hkK : Matrix.of k ∈ KAt G s := hx.2
  have hg : u⁻¹ * Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := mul_mem_UH₂ G _ (inv_mem_UH hG hu) _ hkK.1
  obtain ⟨s', hs', hgs⟩ := hchδ _ hg hkV
  have hks : Matrix.of k = u * oneProd Y s' := by
    rw [← hgs, Matrix.mul_nonsing_inv_cancel_left _ _ hdu]
  dsimp only
  rw [hval t k s' hks, hval t0 k0 0 hk0']
  apply hHc
  rw [Prod.dist_eq]
  refine max_lt ?_ hd3
  rw [dist_pi_lt_iff hη]
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left]
    exact lt_of_le_of_lt (dist_le_pi_dist t t0 i) hd1
  · simp only [Fin.append_right, Pi.zero_apply]
    rw [Real.dist_eq, sub_zero]
    exact hs' i

end Formalism.IndefR.Tow.SobPf.Avg

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.TotalDegreeBindLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace KFin

variable {n : ℕ}

def KS (G s : Matrix (Fin n) (Fin n) ℂ) : Set (Fin n → Fin n → ℂ) := {k | Matrix.of k ∈ KAt G s}

theorem isCompact_KS {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCompact (KS G s) := isCompact_KAt hs

section Int

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuousOn_avg {G s : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) (w : H) :
    ContinuousOn (fun k => p k • π (Matrix.of k) w) (KS G s) := by

  have hmaps : Set.MapsTo (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s) (Formalism.QuantumDeterminants.UH G) :=
    fun k hk => (show Matrix.of k ∈ Formalism.QuantumDeterminants.UH G ∧ Matrix.of k * s = s * Matrix.of k from hk).1
  have hof : ContinuousOn (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s) :=
    continuous_id.continuousOn
  have h1 : ContinuousOn (fun k : Fin n → Fin n → ℂ => π (Matrix.of k) w) (KS G s) :=
    (hπ.2.2.2 w).comp hof hmaps
  exact hp.continuousOn.smul h1

theorem integrable_avg {G s : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hs : IsCartanInv G s) (hπ : IsGRep G π) {μ : Measure (Fin n → Fin n → ℂ)} (hμ : IsHaarK G s μ)
    {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) (w : H) :
    Integrable (fun k => p k • π (Matrix.of k) w) μ := by

  haveI := hμ.1
  have hae : ∀ᵐ k ∂μ, k ∈ KS G s := hμ.2.1
  have h := (continuousOn_avg (s := s) hπ hp w).integrableOn_compact (μ := μ) (isCompact_KS hs)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h

end Int

abbrev Var (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def subst (A : Matrix (Fin n) (Fin n) ℂ) : Var n → MvPolynomial (Var n) ℂ
  | Sum.inl ij => ∑ l, MvPolynomial.C (A ij.1 l) * MvPolynomial.X (Sum.inl (l, ij.2))
  | Sum.inr ij => ∑ l, MvPolynomial.C (starRingEnd ℂ (A ij.1 l)) * MvPolynomial.X (Sum.inr (l, ij.2))

theorem evalMatrix_bind₁_mulLeft (A : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (Var n) ℂ) (k : Fin n → Fin n → ℂ) :
    evP (MvPolynomial.bind₁ (subst A) q) k = evP q (Matrix.of.symm (A * Matrix.of k)) := by

  induction q using MvPolynomial.induction_on
  next a =>
    simp [evP]
  next p r hp hr =>
    simp only [evP, map_add (f := _)] at hp hr ⊢
    rw [hp, hr]
  next p v hp =>
    simp only [evP, map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.eval_X] at hp ⊢
    rw [hp]
    congr 1
    rcases v with ⟨i, j⟩ | ⟨i, j⟩
    · simp [subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C, map_sum]

theorem totalDegree_subst (A : Matrix (Fin n) (Fin n) ℂ) (v : Var n) : (subst A v).totalDegree ≤ 1 := by

  rcases v with ij | ij <;>
  · simp only [subst]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp

theorem totalDegree_bind_le (A : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (Var n) ℂ) :
    (MvPolynomial.bind₁ (subst A) q).totalDegree ≤ q.totalDegree := by

  conv_lhs => rw [q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul le_rfl (totalDegree_subst A i))) ?_
  simp only [mul_one]
  exact MvPolynomial.le_totalDegree hm

def Mon (n N : ℕ) : Set (Var n →₀ ℕ) := {m | (m.sum fun _ e => e) ≤ N}

theorem finite_Mon (n N : ℕ) : (Mon n N).Finite := by

  refine (Set.finite_range (fun f : Var n → Fin (N + 1) =>
    Finsupp.equivFunOnFinite.symm (fun v => (f v : ℕ)))).subset ?_
  intro m hm
  have hm' : ∑ v ∈ m.support, m v ≤ N := hm
  have hle : ∀ v, m v ≤ N := by
    intro v
    by_cases hv : v ∈ m.support
    · exact le_trans (Finset.single_le_sum (f := fun v => m v) (fun _ _ => Nat.zero_le _) hv) hm'
    · have h0 : m v = 0 := by simpa using hv
      rw [h0]; exact Nat.zero_le _
  refine ⟨fun v => ⟨m v, Nat.lt_succ_of_le (hle v)⟩, ?_⟩
  ext v
  simp

theorem evalMatrix_eq_sum_monomial (q : MvPolynomial (Var n) ℂ) (k : Fin n → Fin n → ℂ) :
    evP q k = ∑ m ∈ q.support, q.coeff m * evP (MvPolynomial.monomial m 1) k := by

  simp only [evP]
  conv_lhs => rw [q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show MvPolynomial.monomial m (q.coeff m) =
      MvPolynomial.C (q.coeff m) * MvPolynomial.monomial m (1 : ℂ) by
    rw [MvPolynomial.C_mul_monomial, mul_one], map_mul, MvPolynomial.eval_C]

end KFin

end Formalism.IndefR.Tow.SobPf

end
end

