module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerF

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecBound
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

theorem sL_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n, ‖sL Q y‖ ≤ C * ‖F0 p q e y‖ := by
  have hK := isCompact_KR (n := n)
  have hs : Continuous (sL Q) := hL.cont Q
  have hF : Continuous (F0 (n := n) p q e) := continuous_weight_factor hD p q e
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hs.continuousOn
  have hne : ((KR n : Subgroup (GR n)) : Set (GR n)).Nonempty := ⟨1, (KR n).one_mem⟩
  obtain ⟨k0, -, hmin⟩ := hK.exists_isMinOn hne hF.norm.continuousOn
  set δ := ‖F0 p q e k0‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (weight_factor_ne_zero hD p q e k0)
  refine ⟨max B 0 / δ, div_nonneg (le_max_right _ _) hδ.le, fun y => ?_⟩
  obtain ⟨u, k, hu, hk, rfl⟩ := hI n y
  have hmk : δ ≤ ‖F0 p q e k‖ := hmin hk
  calc ‖sL Q (u * k)‖ = ‖F0 p q e u‖ * ‖sL Q k‖ := by rw [hL.law Q u k hu, norm_mul]
    _ ≤ ‖F0 p q e u‖ * max B 0 :=
        mul_le_mul_of_nonneg_left ((hB k hk).trans (le_max_left _ _)) (norm_nonneg _)
    _ = (max B 0 / δ) * (‖F0 p q e u‖ * δ) := by field_simp
    _ ≤ (max B 0 / δ) * (‖F0 p q e u‖ * ‖F0 p q e k‖) := by gcongr
    _ = (max B 0 / δ) * ‖F0 p q e (u * k)‖ := by rw [((hM n p q e).1 u k hk).1, norm_mul]

theorem rpow_le_add {a x₁ x₂ s : ℝ} (ha : 0 < a) (h₁ : x₁ ≤ s) (h₂ : s ≤ x₂) : a ^ s ≤ a ^ x₁ + a ^ x₂ := by
  rcases le_total 1 a with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h h₂).trans (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge ha h h₁).trans (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _))

section Glob

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem Ht_pos (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (x : G) : 0 < (Ht x : ℝ) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).1]
  exact mul_pos hr (hLoc_pos hD y)

theorem sec_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G, ‖sec Q x‖ ≤ C * ‖sec 1 x‖ := by
  obtain ⟨C, hC0, hC⟩ := sL_bound hI hM hD hL Q
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).2 Q, (h y).2 1, hL.vac y, norm_mul, norm_mul]
  calc ‖S‖ * ‖sL Q y‖ ≤ ‖S‖ * (C * ‖F0 p q e y‖) := mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    _ = C * (‖S‖ * ‖F0 p q e y‖) := by ring

theorem norm_hz (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (z : ℂ) (Q : PX m n) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ = (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ := by
  unfold hz
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (Ht_pos hD hG x), Complex.sub_re]

end Glob

end PositivityTheory.Rg.Sw.AbsSt.Far
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerN
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDN

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem gs_norm (c : ℝ) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ = Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) := by
  rw [gs, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]

theorem continuous_gs (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  unfold gs
  fun_prop

theorem integrable_poly_gs (P : PX m n) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => ‖evX P x‖ * ‖gs c x‖) := by
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  obtain ⟨Cp, k, hCp, hP⟩ := poly_bound P
  obtain ⟨Cd, hCd, hdec⟩ := decay k c hc r
  refine Integrable.mono' ((integrable_one_add_norm (E := Fin m → Fin n → ℂ) (μ := volume)
    (r := r) (by rw [hr]; linarith)).const_mul (Cp * Cd))
    (((continuous_evX P).norm.mul (continuous_gs c).norm).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hg : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
    rw [gs_norm]
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (sq_norm_le_sum x) hc.le))
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (Cp * (1 + ‖x‖) ^ k) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul (hP x) hg (norm_nonneg _) (by positivity)
    _ = Cp * ((1 + ‖x‖) ^ k * Real.exp (-(c * ‖x‖ ^ 2))) := by ring
    _ ≤ Cp * (Cd * (1 + ‖x‖) ^ (-r)) := mul_le_mul_of_nonneg_left (hdec _ hx0) hCp
    _ = Cp * Cd * (1 + ‖x‖) ^ (-r) := by ring

def trH (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, C (H i j) * Qp ε j i

theorem evX_trH (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (trH ε H) x = (H * gramX ε x).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [trH, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX, evX, map_sum, map_mul,
    MvPolynomial.eval_C]

theorem evX_DN (ε : Fin m → Bool) (t : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (x : Fin m → Fin n → ℂ) :
    evX (DN ε t H R) x = Complex.I * t * (H * gramX ε x).trace * evX R x := by
  have h : evX (DN ε t H R) x = (Complex.I * t) * evX (trH ε H) x * evX R x := by
    simp only [DN, trH, evX, map_mul, MvPolynomial.eval_C]
  rw [h, evX_trH]

theorem continuous_gramX (ε : Fin m → Bool) : Continuous (gramX (n := n) ε) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_evX _

private theorem norm_evX_gs_exp_trace_eq_of_isHermitian (ε : Fin m → Bool) (c t : ℝ) (P : PX m n)
    {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) (x : Fin m → Fin n → ℂ) :
    ‖evX P x * gs c x * Complex.exp (Complex.I * t * (B * gramX ε x).trace)‖ =
      ‖evX P x‖ * ‖gs c x‖ := by
  rw [norm_mul, norm_mul, norm_phase t _ (trace_im ε x hB), mul_one]
private theorem continuous_evX_gs_exp_trace (ε : Fin m → Bool) (c t : ℝ) (P : PX m n)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun x : Fin m → Fin n → ℂ =>
      evX P x * gs c x * Complex.exp (Complex.I * t * (B * gramX ε x).trace) :=
  ((continuous_evX P).mul (continuous_gs c)).mul (Complex.continuous_exp.comp
    (continuous_const.mul (continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace))
private theorem isHermitian_add_real_smul {b H : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (hH : H.IsHermitian) (σ : ℝ) : (b + (σ : ℂ) • H).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_add, conjTranspose_smul, hb.eq, hH.eq, Complex.star_def, Complex.conj_ofReal]

theorem hasDerivAt_secN (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) (R : PX m n)
    {b H : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (hH : H.IsHermitian) (s : ℝ) :
    HasDerivAt (fun σ : ℝ => secN ε c t R (b + (σ : ℂ) • H)) (secN ε c t (DN ε t H R) (b + (s : ℂ) • H)) s := by
  have hB : ∀ σ : ℝ, (b + (σ : ℂ) • H).IsHermitian := fun σ => isHermitian_add_real_smul hb hH σ
  have hd : ∀ (x : Fin m → Fin n → ℂ) (σ : ℝ),
      HasDerivAt (fun τ : ℝ => evX R x * gs c x *
          Complex.exp (Complex.I * t * ((b + (τ : ℂ) • H) * gramX ε x).trace))
        (evX (DN ε t H R) x * gs c x *
          Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace)) σ := by
    intro x σ
    have htr : ∀ τ : ℝ, ((b + (τ : ℂ) • H) * gramX ε x).trace =
        (b * gramX ε x).trace + (τ : ℂ) * (H * gramX ε x).trace := by
      intro τ
      rw [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    simp only [htr]
    have h1 : HasDerivAt (fun τ : ℝ => Complex.I * t * ((b * gramX ε x).trace +
        (τ : ℂ) * (H * gramX ε x).trace)) (Complex.I * t * (H * gramX ε x).trace) σ := by
      refine (((((hasDerivAt_id σ).ofReal_comp).mul_const ((H * gramX ε x).trace)).const_add
        ((b * gramX ε x).trace)).const_mul (Complex.I * t)).congr_deriv ?_
      simp
    refine (h1.cexp.const_mul (evX R x * gs c x)).congr_deriv ?_
    rw [evX_DN]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℝ)
    (F := fun σ : ℝ => fun x => evX R x * gs c x *
      Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace))
    (F' := fun σ : ℝ => fun x => evX (DN ε t H R) x * gs c x *
      Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace))
    (x₀ := s) (s := Set.univ) (bound := fun x => ‖evX (DN ε t H R) x‖ * ‖gs c x‖)
    Filter.univ_mem
    (Eventually.of_forall fun σ => (continuous_evX_gs_exp_trace ε c t R _).aestronglyMeasurable)
    (Integrable.mono' (integrable_poly_gs R hc) (continuous_evX_gs_exp_trace ε c t R _).aestronglyMeasurable
      (Eventually.of_forall fun x => (norm_evX_gs_exp_trace_eq_of_isHermitian ε c t R (hB s) x).le))
    (continuous_evX_gs_exp_trace ε c t _ _).aestronglyMeasurable
    (Eventually.of_forall fun x σ _ => (norm_evX_gs_exp_trace_eq_of_isHermitian ε c t _ (hB σ) x).le)
    (integrable_poly_gs _ hc)
    (Eventually.of_forall fun x σ _ => hd x σ)
  exact key.2

theorem sec_along {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
    {ρ : GR n → PX m n →ₗ[ℂ] PX m n} (hL : LocData ε c t p q e sL ρ) {C : ℂ}
    (hcell : ∀ P (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sL P g = C * secN ε c t P b)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) {f : ℝ → GR n} (hf : ∀ σ : ℝ, mR (f σ) = nU ((σ : ℂ) • H))
    {y₁ w : GR n} {b : Matrix (Fin n) (Fin n) ℂ} (hy₁ : IsUp y₁) (hb : b.IsHermitian) (hw : mR w = JJ n * nU b)
    (P : PX m n) (σ : ℝ) : sL P (y₁ * w * f σ) = F0 p q e y₁ * (C * secN ε c t P (b + (σ : ℂ) • H)) := by
  have hfw : mR (w * f σ) = JJ n * nU (b + (σ : ℂ) • H) := by
    rw [mR_mul, hw, hf, Matrix.mul_assoc, nU_mul_nU]
  have hbσ : (b + (σ : ℂ) • H).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_add, conjTranspose_smul, hb.eq, hH.eq, Complex.star_def, Complex.conj_ofReal]
  rw [mul_assoc, hL.law P y₁ (w * f σ) hy₁, hcell P (w * f σ) _ hbσ hfw]

end PositivityTheory.Rg.Sw.AbsSt.SDN

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.DF PositivityTheory.Rg.Sw.AbsSt.SDN

theorem nDer : NDer := by
  intro m n ε c t p q e sL ρ hL R H hH f hf g hg s
  obtain ⟨y₁, w, b, hy₁, hb, hw, rfl⟩ := cell_dec g hg
  obtain ⟨C, -, hcell⟩ := hL.cell
  have hfun : (fun σ : ℝ => sL R (y₁ * w * f σ)) =
      fun σ : ℝ => F0 p q e y₁ * (C * secN ε c t R (b + (σ : ℂ) • H)) :=
    funext fun σ => sec_along hL hcell hH hf hy₁ hb hw R σ
  rw [hfun, sec_along hL hcell hH hf hy₁ hb hw (DN ε t H R) s]
  exact ((hasDerivAt_secN ε hL.cpos t R hb hH s).const_mul C).const_mul _

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerT
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {n : ℕ}

theorem herm_smul {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : ((σ : ℂ) • H).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hH.eq]
  simp

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hb.eq]

def nGU (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := nU ((σ : ℂ) • H)
  inv := nU (-((σ : ℂ) • H))
  val_inv := by rw [nU_mul_nU, add_neg_cancel, nU_zero]
  inv_val := by rw [nU_mul_nU, neg_add_cancel, nU_zero]

def nG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : GR n := ⟨nGU H σ, inG_nU (herm_smul hH σ)⟩

theorem mR_nG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : mR (nG hH σ) = nU ((σ : ℂ) • H) := rfl

theorem cont_nG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : Continuous (nG hH) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun σ : ℝ => fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) ((σ : ℂ) • H) 0 1
    exact Continuous.matrix_fromBlocks continuous_const ((Complex.continuous_ofReal).smul continuous_const)
      continuous_const continuous_const
  · show Continuous fun σ : ℝ => fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-((σ : ℂ) • H)) 0 1
    exact Continuous.matrix_fromBlocks continuous_const ((Complex.continuous_ofReal).smul continuous_const).neg
      continuous_const continuous_const

theorem nG_zero {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : nG hH 0 = 1 := by
  apply DF.ext_mR
  rw [mR_nG, DF.mR_one]
  simp [DF.nU_zero]

def eH (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp ((σ : ℂ) • H)

theorem eH_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : eH H (-σ) = NormedSpace.exp (-((σ : ℂ) • H)) := by
  simp [eH, neg_smul]

theorem eH_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : eH H σ * eH H (-σ) = 1 := by
  rw [eH_neg]
  unfold eH
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((σ : ℂ) • H)).neg_right, add_neg_cancel]
  simp

theorem eH_neg_mul (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : eH H (-σ) * eH H σ = 1 := by
  rw [eH_neg]
  unfold eH
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((σ : ℂ) • H)).neg_left, neg_add_cancel]
  simp

theorem eH_herm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : (eH H σ)ᴴ = eH H σ := by
  rw [eH, ← Matrix.exp_conjTranspose, (herm_smul hH σ).eq]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem cont_eH (H : Matrix (Fin n) (Fin n) ℂ) : Continuous (eH H) :=
  NormedSpace.exp_continuous.comp ((Complex.continuous_ofReal).smul continuous_const)

def mGU (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks (eH H σ) 0 0 (eH H (-σ))
  inv := fromBlocks (eH H (-σ)) 0 0 (eH H σ)
  val_inv := by rw [fromBlocks_multiply]; simp [eH_mul_neg, eH_neg_mul, fromBlocks_one]
  inv_val := by rw [fromBlocks_multiply]; simp [eH_mul_neg, eH_neg_mul, fromBlocks_one]

theorem inG_mGU {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) :
    InG (fromBlocks (eH H σ) 0 0 (eH H (-σ))) := by
  unfold InG JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [eH_herm hH, eH_mul_neg, eH_neg_mul]

def mG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : GR n := ⟨mGU H σ, inG_mGU hH σ⟩

theorem mR_mG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) :
    mR (mG hH σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H))) := by
  rw [← eH_neg]
  rfl

theorem cont_mG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : Continuous (mG hH) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  have h1 := cont_eH H
  have h2 : Continuous fun σ : ℝ => eH H (-σ) := h1.comp continuous_neg
  constructor
  · exact Continuous.matrix_fromBlocks h1 continuous_const continuous_const h2
  · exact Continuous.matrix_fromBlocks h2 continuous_const continuous_const h1

theorem mG_zero {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : mG hH 0 = 1 := by
  apply DF.ext_mR
  rw [mR_mG, DF.mR_one]
  simp [Matrix.fromBlocks_one]

theorem unif_family (S D : GR n → ℂ) (hS : Continuous S) (hD : Continuous D) (f : ℝ → GR n) (hf : Continuous f)
    (hf0 : f 0 = 1)
    (hd : ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∀ s : ℝ, HasDerivAt (fun σ : ℝ => S (g * f σ)) (D (g * f s)) s)
    (y : GR n) : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(S ((k : GR n) * y * f s) - S ((k : GR n) * y)) / s - D ((k : GR n) * y)‖ ≤ δ := by
  intro δ hδ
  have hcontD : Continuous fun p : GR n × ℝ => D (p.1 * f p.2) :=
    hD.comp (continuous_fst.mul (hf.comp continuous_snd))
  have ftc : ∀ s : ℝ, ∀ g : GR n, S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ) := by
    intro s
    have hcl : IsClosed {g : GR n | S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ)} := by
      apply isClosed_eq
      · exact (hS.comp (continuous_id.mul continuous_const)).sub hS
      · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun g σ => D (g * f σ)) hcontD 0 s
    have hsub : {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} ⊆
        {g : GR n | S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ)} := by
      intro g hg
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := fun σ => S (g * f σ)) (f' := fun σ => D (g * f σ)) (fun x _ => hd g hg x)
        ((hD.comp (continuous_const.mul hf)).intervalIntegrable 0 s)
      simp only [hf0, mul_one] at h
      exact h.symm
    intro g
    have h := hcl.closure_subset_iff.mpr hsub
    rw [DF.dense_cell.closure_eq] at h
    exact h (Set.mem_univ g)
  have htube : ∀ᶠ σ in 𝓝 (0:ℝ), ∀ k ∈ (Set.univ : Set (KR n)),
      ‖D ((k : GR n) * y * f σ) - D ((k : GR n) * y)‖ < δ := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro k _
    have hc : Continuous fun p : ℝ × KR n => ‖D ((p.2 : GR n) * y * f p.1) - D ((p.2 : GR n) * y)‖ :=
      ((hD.comp (((continuous_subtype_val.comp continuous_snd).mul continuous_const).mul
        (hf.comp continuous_fst))).sub
        (hD.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_const))).norm
    have h0 : ‖D ((k : GR n) * y * f 0) - D ((k : GR n) * y)‖ < δ := by simp [hf0, hδ]
    exact Filter.eventually_of_mem ((hc.isOpen_preimage _ isOpen_Iio).mem_nhds h0) (fun z hz => hz)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp htube
  refine ⟨η, hη, fun s hs hsη k => ?_⟩
  set g := (k : GR n) * y with hg
  rw [ftc s g]
  have hint : IntervalIntegrable (fun σ => D (g * f σ)) MeasureTheory.volume 0 s :=
    (hD.comp (continuous_const.mul hf)).intervalIntegrable 0 s
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have key : (∫ σ in (0:ℝ)..s, D (g * f σ)) / s - D g = (∫ σ in (0:ℝ)..s, (D (g * f σ) - D g)) / s := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, sub_div, mul_div_cancel_left₀ _ hs']
  have hb : ‖∫ σ in (0:ℝ)..s, (D (g * f σ) - D g)‖ ≤ δ * |s - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : |x| ≤ |s| := by
      rcases Set.mem_uIoc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le_abs h2 (by linarith)
      · rw [abs_of_nonpos h2, abs_of_neg (by linarith)]
        linarith
    have hx2 : dist x 0 < η := by
      rw [dist_zero_right, Real.norm_eq_abs]
      linarith
    exact (hball hx2 k (Set.mem_univ _)).le
  have hs0 : (0:ℝ) < ‖(s:ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_pos.mpr hs
  rw [key, norm_div, div_le_iff₀ hs0]
  calc _ ≤ δ * |s - 0| := hb
    _ = δ * ‖(s:ℂ)‖ := by rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]

end PositivityTheory.Rg.Sw.AbsSt.SD

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SD

theorem secDer_of (hN : NDer) (hM : MDer) : SecDer := by
  intro m n ε c t p q e sL ρ hL R _ y H hH
  refine ⟨⟨nG hH, unif_family (sL R) (sL (DN ε t H R)) (hL.cont R) (hL.cont _) (nG hH) (cont_nG hH) (nG_zero hH)
    (fun g hg s => hN m n ε c t p q e sL ρ hL R H hH (nG hH) (mR_nG hH) g hg s) y⟩,
    ⟨mG hH, unif_family (sL R) (sL (DM ε c H R)) (hL.cont R) (hL.cont _) (mG hH) (cont_mG hH) (mG_zero hH)
    (fun g hg s => hM m n ε c t p q e sL ρ hL R H hH (mG hH) (mR_mG hH) g hg s) y⟩⟩

end PositivityTheory.Rg.Sw.AbsSt
end
end

