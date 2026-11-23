module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0095
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0097
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0098

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MapInvMEq
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem gN_cont : Continuous (fun g : Mx k r => B.gN g) := by
  unfold B.gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp (continuous_apply_apply i j))

theorem gNpow_inCC (hNI : NormInv) (b : ℝ) (hb : b ≠ 0) :
    B.InCC b 0 (fun g : B.Mat k r => ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
  have hpos : ∀ g ∈ B.GV k r, 0 < B.gN g := fun g hg => lt_of_lt_of_le one_pos ((hNI k r).2 g hg).2
  have hf : ContinuousOn (fun g : Mx k r => ((B.gN g ^ (-b) : ℝ) : ℂ)) (B.GV k r) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact gN_cont.continuousOn.rpow_const (fun g hg => Or.inl (hpos g hg).ne')
  refine ⟨1, ckOn_zero_of_contOn _ hf, ?_⟩
  intro uu vv _ _ hlen g hg
  have hu : uu = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hv : vv = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hu; subst hv
  show B.gN g ^ b * ‖((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ ≤ 1
  have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
  rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hgN _)]
  have := rpow_bound (B.gN g) 1 b hgN hb
  simpa using this

def invP (p : B.SS k r) : B.SS k r :=
  ((B2.invM p.1.1, B2.invM p.1.2), (B2.invM p.2.1, B2.invM p.2.2))

theorem map_invM_eq {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : B.IsHaarOn U μ) : μ.map B2.invM = μ := Formalism.FourierDecayAlt.P.haar_measure_inversion k r U μ hU hμ

theorem ae_of_haarB {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by
  rw [ae_iff]; exact hμ.conc

theorem ae_SS {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] :
    ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r ∧
      Matrix.of p.2.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' ∧ Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW := ae_of_haarB D.haarW
  have hN := ae_of_haarB D.haarN
  have hW' := ae_of_haarB D.haarW'
  have e1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have e2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have e3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have e4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem map_invP {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] :
    D.μSS.map invP = D.μSS := by
  have hm := B2x1.invM_meas (k := k) (r := r)
  have hW := map_invM_eq (weyl_subgroup_closed k r D.z) D.haarW
  have hN := map_invM_eq (unipotent_radical_closed k r) D.haarN
  have hW' := map_invM_eq (weyl_subgroup_closed k r D.z') D.haarW'
  show ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)).map
      (Prod.map (Prod.map B2.invM B2.invM) (Prod.map B2.invM B2.invM)) = (D.μW.prod D.μN).prod (D.μW'.prod D.μN)
  rw [← Measure.map_prod_map _ _ (hm.prodMap hm) (hm.prodMap hm), ← Measure.map_prod_map _ _ hm hm,
    ← Measure.map_prod_map _ _ hm hm, hW, hN, hW']

theorem la_fin (hNI : NormInv) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] {b : ℝ} (hb : JF.TransportedAlt k r b 0) (hb0 : b ≠ 0)
    {γ : B.Mat k r} (hγ : γ ∈ JF.Om k r D.z D.z') :
    ∫⁻ p, ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ
      ∂D.μSS < ⊤ := by
  set F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun g => ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) with hF
  have hJC := Formalism.FourierDecayAlt.P.bessel_integral_converges k r ℂ ℂ (triv D) b F hb (gNpow_inCC hNI b hb0)
  obtain ⟨bb, hbb, hbd⟩ := hJC.2 {γ} isCompact_singleton (Set.singleton_subset_iff.mpr hγ)
  set G : B.SS k r → ℝ≥0∞ := fun p => ‖B.gN (B.sgs p γ) ^ (-b)‖ₑ with hG
  have h1 : ∫⁻ p, G p ∂D.μSS < ⊤ := by
    calc ∫⁻ p, G p ∂D.μSS ≤ ∫⁻ p, ‖bb p‖ₑ ∂D.μSS := by
          apply lintegral_mono_ae
          filter_upwards [hbd γ rfl] with p hp
          have e : ‖B.gN (B.sgs p γ) ^ (-b)‖ = ‖B.rho (triv D) p F γ‖ := by
            rw [rho_triv]; simp [hF]
          simp only [hG]
          rw [← ofReal_norm, ← ofReal_norm, e]
          exact ENNReal.ofReal_le_ofReal (hp.trans (Real.le_norm_self _))
      _ < ⊤ := hbb.hasFiniteIntegral
  have hinv : ∀ᵐ p ∂D.μSS, invP (invP p) = p ∧
      G (invP p) = ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ *
        (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ := by
    filter_upwards [ae_SS D] with p hp
    have u1 := (weyl_subgroup_closed k r D.z).unit _ hp.1
    have u2 := (unipotent_radical_closed k r).unit _ hp.2.1
    have u3 := (weyl_subgroup_closed k r D.z').unit _ hp.2.2.1
    have u4 := (unipotent_radical_closed k r).unit _ hp.2.2.2
    have ii : ∀ x : Formalism.QuantumDeterminants.Mt k r, IsUnit (Matrix.of x).det → B2.invM (B2.invM x) = x := by
      intro x hx
      show (((Matrix.of x)⁻¹)⁻¹ : B.Mat k r) = Matrix.of x
      exact Matrix.nonsing_inv_nonsing_inv _ hx
    refine ⟨?_, ?_⟩
    · simp only [invP]
      rw [ii _ u1, ii _ u2, ii _ u3, ii _ u4]
    · simp only [hG, invP, B.sgs]
      have j1 : (Matrix.of (B2.invM p.1.1))⁻¹ = Matrix.of p.1.1 := ii _ u1
      have j2 : (Matrix.of (B2.invM p.1.2))⁻¹ = Matrix.of p.1.2 := ii _ u2
      rw [j1, j2]
      rfl
  calc ∫⁻ p, ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ
        ∂D.μSS = ∫⁻ p, G (invP p) ∂D.μSS := lintegral_congr_ae (hinv.mono fun p hp => hp.2.symm)
    _ = ∫⁻ p, G (invP p) ∂(D.μSS.map invP) := by rw [map_invP D]
    _ ≤ ∫⁻ p, G (invP (invP p)) ∂D.μSS := by
      have hm := B2x1.invM_meas (k := k) (r := r)
      have hinvP : Measurable (invP (k := k) (r := r)) :=
        (hm.prodMap hm).prodMap (hm.prodMap hm)
      exact lintegral_map_le (fun p => G (invP p)) hinvP.aemeasurable
    _ = ∫⁻ p, G p ∂D.μSS := lintegral_congr_ae (hinv.mono fun p hp => by show G (invP (invP p)) = G p; rw [hp.1])
    _ < ⊤ := h1

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCLim
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def Hh (Y : Finset H) (κ : H → H → ℂ) (hat : Fin f → ℂ → H → H → ℂ) (σ : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, hat v (σ v) h h'

theorem eventually_norm_gt (v : Fin f) (a : ℝ) : ∀ᶠ x in crystallineComparison.atInfAll f, a < ‖x v‖ := by
  have h : ∀ᶠ x in Filter.comap (fun x : crystallineComparison.V f => ‖x v‖) atTop, a < ‖x v‖ :=
    (Filter.eventually_gt_atTop a).comap _
  unfold crystallineComparison.atInfAll
  exact Filter.mem_iInf_of_mem v h

theorem eventually_good (σ : crystallineComparison.V f) : ∀ᶠ x in crystallineComparison.atInfAll f, Good x ∧ Good (x + σ) := by
  have h1 : ∀ v, ∀ᶠ x in crystallineComparison.atInfAll f, x v ≠ 0 ∧ x v + σ v ≠ 0 := by
    intro v
    filter_upwards [eventually_norm_gt v ‖σ v‖] with x hx
    constructor
    · intro h
      rw [h, norm_zero] at hx
      exact absurd hx (not_lt.mpr (norm_nonneg _))
    · intro h
      have e : x v = -σ v := eq_neg_of_add_eq_zero_left h
      rw [e, norm_neg] at hx
      exact lt_irrefl _ hx
  filter_upwards [Filter.eventually_all.mpr h1] with x hx
  exact ⟨fun v => (hx v).1, fun v => (hx v).2⟩

theorem tendsto_coord (v : Fin f) : Tendsto (fun x : crystallineComparison.V f => x v) (crystallineComparison.atInfAll f) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, Filter.tendsto_comap_iff]
  exact Filter.tendsto_comap.mono_left (iInf_le (fun v => Filter.comap (fun x : crystallineComparison.V f => ‖x v‖) atTop) v)

theorem phiG_tendsto (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ)
    (hat : Fin f → ℂ → H → H → ℂ)
    (hlim : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => K v (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hat v σ h h'))) (σ : crystallineComparison.V f) :
    Tendsto (fun x => phiG Y κ K x (x + σ)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)) := by
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun x => phi Y κ K x (x + σ)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)))
  · filter_upwards [eventually_good σ] with x hx
    rw [phiG, if_pos hx]
  · unfold phi Hh
    refine tendsto_finsetSum _ (fun h hh => tendsto_finsetSum _ (fun h' hh' => ?_))
    refine Tendsto.const_mul _ ?_
    refine tendsto_finsetProd _ (fun v _ => ?_)
    exact (hlim v h hh h' hh' (σ v)).comp (tendsto_coord v)

theorem phiG_conj_tendsto (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (K : Fin f → H × ℂ → H × ℂ → ℂ)
    (hat : Fin f → ℂ → H → H → ℂ)
    (hlim : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => conj (K v (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hat v σ h h'))) (σ : crystallineComparison.V f) :
    Tendsto (fun x => conj (phiG Y κ K (x + σ) x)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)) := by
  have hherm : ∀ h ∈ Y, ∀ h' ∈ Y, conj (κ h' h) = κ h h' := by
    intro h hh h' hh'
    have := hκ.1.apply ⟨h, hh⟩ ⟨h', hh'⟩
    simp only [Matrix.of_apply] at this
    exact this
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun x => ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, conj (K v (h', x v + σ v) (h, x v)))
    (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)))
  · filter_upwards [eventually_good σ] with x hx
    symm
    rw [phiG, if_pos ⟨hx.2, hx.1⟩, phi]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_prod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun h' hh' => ?_))
    rw [hherm h hh h' hh']
    rfl
  · unfold Hh
    refine tendsto_finsetSum _ (fun h hh => tendsto_finsetSum _ (fun h' hh' => ?_))
    refine Tendsto.const_mul _ ?_
    refine tendsto_finsetProd _ (fun v _ => ?_)
    exact (hlim v h hh h' hh' (σ v)).comp (tendsto_coord v)

section mean

variable (Λ : AddSubgroup (crystallineComparison.V f)) (LIM : (Λ → ℂ) → ℂ)

end mean

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PlMonoConst
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section poly

variable {A : Type} [Ring A] [Algebra ℂ A]

def PolyLe (t : ℕ) (f : ℂ → A) : Prop :=
  ∃ C : Fin t → A, ∀ u, f u = ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l

theorem pl_congr {t : ℕ} {f g : ℂ → A} (h : ∀ u, f u = g u) (hf : PolyLe t f) : PolyLe t g := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun u => by rw [← h u]; exact hC u⟩

theorem pl_zero (t : ℕ) : PolyLe t (fun _ => (0 : A)) := ⟨0, fun u => by simp⟩

theorem pl_add {t : ℕ} {f g : ℂ → A} (hf : PolyLe t f) (hg : PolyLe t g) : PolyLe t (fun u => f u + g u) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun u => ?_⟩
  dsimp only
  rw [hC, hD, ← Finset.sum_add_distrib]
  simp only [Pi.add_apply, mul_add]

theorem pl_sum {t : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ → A) (hf : ∀ i ∈ s, PolyLe t (f i)) :
    PolyLe t (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact pl_congr (fun u => by simp) (pl_zero t)
  | insert i s hi ih =>
    exact pl_congr (fun u => by simp [Finset.sum_insert hi])
      (pl_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem pl_lmul {t : ℕ} {f : ℂ → A} (c : A) (hf : PolyLe t f) : PolyLe t (fun u => c * f u) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨fun l => c * C l, fun u => ?_⟩
  dsimp only
  rw [hC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => Algebra.left_comm _ _ _

theorem pl_mono {t : ℕ} {f : ℂ → A} (hf : PolyLe t f) : PolyLe (t + 1) f := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨Fin.snoc (α := fun _ => A) C 0, fun u => ?_⟩
  rw [hC, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem pl_mulu {t : ℕ} {f : ℂ → A} (hf : PolyLe t f) : PolyLe (t + 1) (fun u => f u * algebraMap ℂ A u) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨Fin.cons (α := fun _ => A) 0 C, fun u => ?_⟩
  dsimp only
  rw [hC, Fin.sum_univ_succ, Finset.sum_mul]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, Fin.val_succ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, pow_succ]

theorem pl_mono_const (t : ℕ) (x : A) : PolyLe (t + 1) (fun u => algebraMap ℂ A (u ^ t) * x) := by
  refine ⟨Fin.snoc (α := fun _ => A) 0 x, fun u => ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem prod_poly : ∀ (t : ℕ) (c δ : Fin t → ℂ) (F : Fin t → A),
    PolyLe t (fun u => (List.ofFn fun k => algebraMap ℂ A ((u + c k) * δ k) + F k).prod -
      algebraMap ℂ A (u ^ t * ∏ k, δ k)) := by
  intro t
  induction t with
  | zero =>
    intro c δ F
    exact ⟨Fin.elim0, fun u => by simp⟩
  | succ t ih =>
    intro c δ F
    obtain ⟨C, hC⟩ := ih (fun k => c k.succ) (fun k => δ k.succ) (fun k => F k.succ)
    let Q : ℂ → A := fun u => ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
    have hQpl : PolyLe t Q := ⟨C, fun u => rfl⟩
    have hR : ∀ u, (List.ofFn fun k : Fin t => algebraMap ℂ A ((u + c k.succ) * δ k.succ) + F k.succ).prod =
        algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) + Q u := by
      intro u
      show _ = _ + ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
      have h := hC u
      dsimp only at h
      rw [← h]
      abel
    refine pl_congr (f := fun u => algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) +
        ((algebraMap ℂ A (c 0 * δ 0) + F 0) * Q u + algebraMap ℂ A (u ^ t) *
          ((algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (∏ k : Fin t, δ k.succ)))) ?_
      (pl_add (pl_lmul _ (pl_mulu hQpl)) (pl_add (pl_mono (pl_lmul _ hQpl)) (pl_mono_const t _)))
    intro u
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [hR u]
    have e1 : algebraMap ℂ A (u * δ 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ (t + 1) * (δ 0 * ∏ k : Fin t, δ k.succ)) := by
      rw [← map_mul]
      congr 1
      ring
    have e2 : algebraMap ℂ A (u * δ 0) * Q u = algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) := by
      rw [← Algebra.commutes, ← mul_assoc, ← map_mul, mul_comm (δ 0) u]
    have e3 : (algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ t) * ((algebraMap ℂ A (c 0 * δ 0) + F 0) *
          algebraMap ℂ A (∏ k : Fin t, δ k.succ)) := by
      rw [map_mul (algebraMap ℂ A) (u ^ t), Algebra.left_comm]
    rw [add_mul u (c 0) (δ 0), map_add (f := _), add_assoc,
      mul_add (algebraMap ℂ A (u * δ 0) + (algebraMap ℂ A (c 0 * δ 0) + F 0)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (Q u), e1, e2, e3]
    abel

theorem qminor_poly {n t : ℕ} (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (s0 : ℂ) :
    PolyLe t (fun u => qminor E a b (u + s0) - algebraMap ℂ A (u ^ t *
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0))) := by
  classical
  refine pl_congr (f := fun u => ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
      ((List.ofFn fun k : Fin t => algebraMap ℂ A ((u + (s0 - (k : ℂ))) *
          (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k)).prod -
        algebraMap ℂ A (u ^ t * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0)))) ?_
    (pl_sum _ _ fun σ _ => pl_lmul _ (prod_poly t _ _ _))
  intro u
  have hT : ∀ (σ : Equiv.Perm (Fin t)) (k : Fin t), Tm E (u + s0 - (k : ℂ)) (a (σ k)) (b k) =
      algebraMap ℂ A ((u + (s0 - (k : ℂ))) * (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k) := by
    intro σ k
    unfold Tm
    split_ifs <;> simp [add_sub_assoc]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · unfold qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hT]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [mul_left_comm (u ^ t) (((Equiv.Perm.sign σ : ℤ) : ℂ)),
        map_mul (algebraMap ℂ A) (((Equiv.Perm.sign σ : ℤ) : ℂ)), map_intCast]

end poly

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

