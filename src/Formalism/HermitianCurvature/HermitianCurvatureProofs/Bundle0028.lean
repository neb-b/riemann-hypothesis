module

public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralZeroFrequencyInvariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0025
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeEqualityFromTestFunctions
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragingVanishes
section
open Formalism.FourierDecayAlt Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.GeometricRayBounds

theorem exists_dir {ι : Type*} (S : Finset ι) (c : ι → ℂ) (hc : ∀ i ∈ S, c i ≠ 0) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ i ∈ S, (c i * u).re ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ S.image (fun i => (c i).re / (c i).im) := by
    first
    | exact Infinite.exists_not_mem_finset _
    | exact Infinite.exists_notMem_finset _
  refine ⟨1 + (t : ℂ) * Complex.I, ?_, fun i hi => ?_⟩
  · intro h
    have h1 := congrArg Complex.re h
    simp at h1
  · intro h0
    have h0' : (c i).re = (c i).im * t := by
      simp at h0
      linarith
    by_cases him : (c i).im = 0
    · exact hc i hi (Complex.ext (by rw [h0', him, zero_mul, Complex.zero_re])
        (by rw [him, Complex.zero_im]))
    · exact ht (Finset.mem_image.2 ⟨i, hi, by rw [h0']; exact mul_div_cancel_left₀ t him⟩)

theorem p_sum_le {V : Type*} [AddCommGroup V] [Module ℂ V] (p : Seminorm ℂ V) {ι : Type*} (S : Finset ι)
    (f : ι → V) : p (∑ i ∈ S, f i) ≤ ∑ i ∈ S, p (f i) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (map_add_le_add p _ _).trans (add_le_add_right ih _)

theorem nexp (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x

theorem geom_bound (q : ℂ) (hq : ‖q‖ = 1) (hq1 : q ≠ 1) (M : ℕ) :
    ‖∑ m ∈ range M, q ^ m‖ ≤ 2 / ‖q - 1‖ := by
  have hne : 0 < ‖q - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hq1)
  rw [geom_sum_eq hq1, norm_div]
  apply div_le_div_of_nonneg_right _ hne.le
  calc ‖q ^ M - 1‖ ≤ ‖q ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [norm_pow, hq, one_pow, norm_one]
      norm_num

theorem exp_ne_one {x : ℝ} (h0 : x ≠ 0) (h1 : |x| < 2 * Real.pi) :
    Complex.exp (Complex.I * (x : ℂ)) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have h2 := congrArg Complex.im hn
  simp at h2
  have hx : x = n * (2 * Real.pi) := by linarith
  have hpi := Real.pi_pos
  rw [hx, abs_lt] at h1
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · have h3 : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn0
    nlinarith
  · subst hn0
    simp at hx
    exact h0 hx
  · have h3 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith

end Formalism.FourierDecayAlt.P.GeometricRayBounds

namespace Formalism.FourierDecayAlt.P

open GeometricRayBounds

theorem averaging_vanishes : C6.AveragingZero := by
  intro β hβ V _ _ p s w a C' x₁ hw H j0
  classical
  set c : Fin s → ℂ := fun j => β * (w j - w j0) with hcdef
  have hc : ∀ j ∈ Finset.univ.erase j0, c j ≠ 0 := by
    intro j hj
    have hj' : j ≠ j0 := Finset.ne_of_mem_erase hj
    exact mul_ne_zero hβ (sub_ne_zero.2 fun h => hj' (hw h))
  obtain ⟨u, hu0, hu⟩ := exists_dir (Finset.univ.erase j0) c hc
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hsum0 : 0 ≤ ∑ j, |(c j * u).re| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set K0 : ℝ := 1 + ∑ j, |(c j * u).re| with hK0
  have hK0pos : 0 < K0 := by linarith
  set t : ℝ := Real.pi / K0 with ht
  have htpos : 0 < t := div_pos Real.pi_pos hK0pos
  have hphase : ∀ j, |t * (c j * u).re| < 2 * Real.pi := by
    intro j
    have hle : |(c j * u).re| ≤ ∑ j, |(c j * u).re| :=
      Finset.single_le_sum (f := fun j => |(c j * u).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    rw [abs_mul, abs_of_pos htpos, ht, div_mul_eq_mul_div, div_lt_iff₀ hK0pos]
    nlinarith [Real.pi_pos]
  set q : Fin s → ℂ := fun j => Complex.exp (Complex.I * ((t * (c j * u).re : ℝ) : ℂ)) with hqdef
  have hq1 : ∀ j ∈ Finset.univ.erase j0, q j ≠ 1 := fun j hj =>
    exp_ne_one (mul_ne_zero htpos.ne' (hu j hj)) (hphase j)
  have hqn : ∀ j, ‖q j‖ = 1 := fun j => nexp _
  have hpsi : ∀ j (x : ℂ), G.psi β (-(w j0) * x) * G.psi β (w j * x) =
      Complex.exp (Complex.I * (((c j * x).re : ℝ) : ℂ)) := by
    intro j x
    rw [show c j * x = β * (-(w j0) * x) + β * (w j * x) by simp only [hcdef]; ring, Complex.add_re,
      Complex.ofReal_add, mul_add, Complex.exp_add]
    rfl
  have hpsin : ∀ x : ℂ, ‖G.psi β x‖ = 1 := fun x => nexp _
  set Kc : ℝ := ∑ j ∈ Finset.univ.erase j0, 2 / ‖q j - 1‖ * p (a j) with hKc
  have hC' : 0 ≤ C' := by
    obtain ⟨N, hN⟩ := exists_nat_gt (|x₁| / ‖u‖ + 1)
    have hq0 : 0 ≤ |x₁| / ‖u‖ := div_nonneg (abs_nonneg _) hunorm.le
    have hNu : 0 < (N : ℝ) * ‖u‖ := mul_pos (by linarith) hunorm
    have hx : x₁ ≤ ‖((N : ℝ) : ℂ) * u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
      have h2 := (div_lt_iff₀ hunorm).1 (by linarith : |x₁| / ‖u‖ < N)
      linarith [le_abs_self x₁]
    have h1 := (apply_nonneg p _).trans (H _ hx)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)] at h1
    exact (div_nonneg_iff.1 h1).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hNu))
  have hmain : ∀ N : ℕ, 0 < N → x₁ ≤ N * ‖u‖ → p (a j0) ≤ (C' / ‖u‖ + Kc) / N := by
    intro N hN hx₁
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    set x : ℕ → ℂ := fun m => (((N : ℝ) + m * t : ℝ) : ℂ) * u with hxdef
    have hxn : ∀ m : ℕ, (N : ℝ) * ‖u‖ ≤ ‖x m‖ := by
      intro m
      have hmt : 0 ≤ (m : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) htpos.le
      simp only [hxdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) hmt)]
      gcongr
      linarith
    have hT : ∀ m : ℕ, p (∑ j, G.psi β (w j * x m) • a j) ≤ C' / (N * ‖u‖) := by
      intro m
      calc _ ≤ C' / ‖x m‖ := H _ (hx₁.trans (hxn m))
        _ ≤ C' / (N * ‖u‖) := div_le_div_of_nonneg_left hC' (mul_pos hNpos hunorm) (hxn m)
    set coef : Fin s → ℂ := fun j =>
      ∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) * G.psi β (w j * x m) with hcoef
    have hid : ∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j =
        ∑ j, coef j • a j := by
      simp only [Finset.smul_sum, smul_smul, hcoef, Finset.sum_smul]
      exact Finset.sum_comm
    have hc0 : coef j0 = N := by
      have h0 : c j0 = 0 := by simp only [hcdef, sub_self, mul_zero]
      simp only [hcoef, hpsi, h0, zero_mul, Complex.zero_re, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hcj : ∀ j ∈ Finset.univ.erase j0, ‖coef j‖ ≤ 2 / ‖q j - 1‖ := by
      intro j hj
      have hterm : ∀ m : ℕ, G.psi β (-(w j0) * x m) * G.psi β (w j * x m) =
          Complex.exp (Complex.I * (((N : ℝ) * (c j * u).re : ℝ) : ℂ)) * q j ^ m := by
        intro m
        rw [hpsi, show c j * x m = (((N : ℝ) + m * t : ℝ) : ℂ) * (c j * u) by simp only [hxdef]; ring,
          Complex.re_ofReal_mul]
        simp only [hqdef]
        rw [← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp only [hcoef, hterm, ← Finset.mul_sum, norm_mul, nexp, one_mul]
      exact geom_bound (q j) (hqn j) (hq1 j hj) N
    have hsplit : ∑ j, coef j • a j = coef j0 • a j0 + ∑ j ∈ Finset.univ.erase j0, coef j • a j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j0)).symm
    have hpa : (N : ℝ) * p (a j0) ≤ N * (C' / (N * ‖u‖)) + Kc := by
      have e1 : (N : ℝ) * p (a j0) = p (coef j0 • a j0) := by
        rw [hc0, map_smul_eq_mul]
        simp
      rw [e1]
      have e2 : coef j0 • a j0 =
          (∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j) -
            ∑ j ∈ Finset.univ.erase j0, coef j • a j := by
        rw [hid, hsplit]
        abel
      rw [e2]
      refine (map_sub_le_add p _ _).trans (add_le_add ?_ ?_)
      · refine (p_sum_le p _ _).trans ?_
        calc ∑ m ∈ Finset.range N, p (G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j)
            = ∑ m ∈ Finset.range N, p (∑ j, G.psi β (w j * x m) • a j) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [map_smul_eq_mul, hpsin, one_mul]
          _ ≤ ∑ m ∈ Finset.range N, C' / (N * ‖u‖) := Finset.sum_le_sum fun m _ => hT m
          _ = N * (C' / (N * ‖u‖)) := by simp
      · refine (p_sum_le p _ _).trans ?_
        refine Finset.sum_le_sum fun j hj => ?_
        rw [map_smul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcj j hj) (apply_nonneg p _)
    have e3 : (N : ℝ) * (C' / (N * ‖u‖)) = C' / ‖u‖ := by
      field_simp
    rw [e3] at hpa
    rw [le_div_iff₀ hNpos]
    linarith
  have hnn := apply_nonneg p (a j0)
  by_contra hne
  have hδ : 0 < p (a j0) := lt_of_le_of_ne hnn (Ne.symm hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (|x₁| / ‖u‖) ((C' / ‖u‖ + Kc) / p (a j0)))
  have hN1 : |x₁| / ‖u‖ < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : (C' / ‖u‖ + Kc) / p (a j0) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hunorm.le) hN1
  have hx₁ : x₁ ≤ N * ‖u‖ := by
    have h2 := (div_lt_iff₀ hunorm).1 hN1
    linarith [le_abs_self x₁]
  have hb := hmain N (by exact_mod_cast hNpos) hx₁
  rw [div_lt_iff₀ hδ] at hN2
  rw [le_div_iff₀ hNpos] at hb
  nlinarith

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellInversePair

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have hu := WeylGroupFacts.isUnit_of_uh hh.1
  have key : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨WeylGroupFacts.uh_inv hh.1, fun a => ⟨key _ (hh.2.1 a).1, key _ (hh.2.1 a).2⟩, key _ hh.2.2⟩

def invP (p : SS k r) : SS k r :=
  ((((Matrix.of p.1.1 : Mat k r)⁻¹ : Mat k r),
      ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * (Matrix.of p.1.1 : Mat k r) : Mat k r)),
    (((Matrix.of p.2.1 : Mat k r)⁻¹ : Mat k r),
      ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 : Mat k r)⁻¹ * (Matrix.of p.2.1 : Mat k r) : Mat k r)))

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem invP_inSS (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : D.inSS (invP p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hu1 := WeylGroupFacts.isUnit_of_uh h1.1
  have hu3 := WeylGroupFacts.isUnit_of_uh h3.1
  refine ⟨uw_inv h1, ?_, uw_inv h3, ?_⟩
  · have := (uWNormal k r D.z D.z_mem (Matrix.of p.1.1)⁻¹ (uw_inv h1) _ (WeylGroupFacts.mem_n_inv h2)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu1] at this
  · have := (uWNormal k r D.z' D.z'_mem (Matrix.of p.2.1)⁻¹ (uw_inv h3) _ (WeylGroupFacts.mem_n_inv h4)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu3] at this

theorem sgs_invP (p : SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : Mat k r).det) (hp2 : IsUnit (Matrix.of p.1.2 : Mat k r).det)
    (hp3 : IsUnit (Matrix.of p.2.1 : Mat k r).det) (hp4 : IsUnit (Matrix.of p.2.2 : Mat k r).det) (x : Mat k r) :
    sgs (invP p) (sgs p x) = x := by
  show (Matrix.of p.1.1 : Mat k r)⁻¹⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ *
      Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * x *
      Matrix.of p.2.2 * Matrix.of p.2.1) * ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 : Mat k r)⁻¹ *
      Matrix.of p.2.1) * (Matrix.of p.2.1 : Mat k r)⁻¹ = x
  generalize (Matrix.of p.1.1 : Mat k r) = A at hp1 ⊢
  generalize (Matrix.of p.1.2 : Mat k r) = B at hp2 ⊢
  generalize (Matrix.of p.2.1 : Mat k r) = C at hp3 ⊢
  generalize (Matrix.of p.2.2 : Mat k r) = D at hp4 ⊢
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv A hp1,
    Matrix.nonsing_inv_nonsing_inv B hp2]
  simp only [mul_assoc, Matrix.mul_nonsing_inv_cancel_left, Matrix.nonsing_inv_mul_cancel_left,
    Matrix.mul_nonsing_inv, hp1, hp2, hp3, hp4, mul_one]

end Formalism.FourierDecayAlt.P.BigCellInversePair

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EqOfContinuousOffZero
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

theorem isClosed_nonneg_complex : IsClosed {z : ℂ | 0 ≤ z} := by
  have h : {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.le_def, Complex.zero_re, Complex.zero_im]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  rw [h]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)

theorem integral_nonneg_complex {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ ∫ a, f a ∂ν := by
  have hre : ∀ a, f a = ((f a).re : ℂ) := fun a => by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact ((Complex.le_def.mp (h a)).2).symm
  have hf : (fun a => f a) = fun a => ((f a).re : ℂ) := funext hre
  rw [hf]
  first
  | rw [integral_complex_ofReal]
  | rw [integral_ofReal]
  | rw [← RCLike.ofReal_eq_complex_ofReal, integral_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun a => (Complex.le_def.mp (h a)).1)

theorem continuous_fsv (s : ℂ) : Continuous (fsv s) := by
  unfold fsv
  exact ((continuous_const.mul continuous_id).sub
    (continuous_const.mul Complex.continuous_conj)).cexp

theorem nonneg_of_continuous {φ : ℂ → ℂ} (hc : Continuous φ) (h : ∀ t, t ≠ 0 → 0 ≤ φ t) :
    ∀ t, 0 ≤ φ t := by
  have hcl : IsClosed {t | 0 ≤ φ t} := isClosed_nonneg_complex.preimage hc
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {t | 0 ≤ φ t} := fun t ht => h t ht
  have hcl2 := hcl.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at hcl2
  intro t
  exact hcl2 (Set.mem_univ t)

theorem eq_of_continuous_off_zero {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, t ≠ 0 → f t = g t) : f = g := hf.ext_on (dense_compl_singleton (0 : ℂ)) hg (fun t ht => h t ht)

theorem update_mem_OmX {m : ℕ} {c : Fin m → ℂ} (hc : c ∈ OmX m) (l : Fin m) {t : ℂ} (ht : t ≠ 0) :
    Function.update c l t ∈ OmX m := by
  intro j
  rcases eq_or_ne j l with rfl | hj
  · simpa using ht
  · rw [Function.update_of_ne hj]
    exact hc j

theorem nonneg_all_levels {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hTI : TopIdent (S := S) P z z' π π' μ L st K l0) (hTN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hSI : SliceIn (S := S) P z z' π π' L st K l0) (hSD : StepDens (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) :
    ∀ (n : ℕ) (i : Fin (P.r + 1)), i.val + n = P.r → ∀ c ∈ OmX P.r,
      ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → 0 ≤ RRform L st μ i w x x c := by
  intro n
  induction n with
  | zero =>
    intro i hi c hc x hx
    have hi' : i = Fin.last P.r := Fin.ext (by simpa using hi)
    subst hi'
    rw [(hTI w hw x x hx hx c hc).2]
    exact integral_nonneg_complex μ _ (fun g => hTN w hw x hx c hc (Matrix.of g))
  | succ n ih =>
    intro i hi c hc x hx
    have hlt : i.val < P.r := by omega
    obtain ⟨l, rfl⟩ : ∃ l : Fin P.r, l.castSucc = i := ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    obtain ⟨φ, hφc, hφ, -, hint⟩ := hSD w hw l x x hx hx c hc
    rw [← hint]
    apply integral_nonneg_complex
    apply nonneg_of_continuous hφc
    intro t ht
    rw [hφ t ht]
    unfold ph
    apply mul_nonneg
    · exact Complex.zero_le_real.mpr (by positivity)
    · have hn : (l.succ).val + n = P.r := by
        simp only [Fin.coe_castSucc] at hi
        simp only [Fin.val_succ]
        omega
      exact ih l.succ hn _ (update_mem_OmX hc l ht) _ (hSI w hw l x hx)

theorem thmPFromStepsAll : ThmPFromStepsAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K l0
  intro hTI hTN hTT hSI hSD hST hFS w hw
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy c hc
    refine ⟨(hTI w hw x y hx hy c hc).1, ?_, ?_⟩
    · intro s Wv Wv' h1 h2
      obtain ⟨hK, hD⟩ := hTT w hw s Wv Wv' h1 h2 x y hx hy c hc
      rw [(hTI w hw _ y hK hy c hc).2]
      congr 1
      funext g
      rw [hD]
    · exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw 0
        (Fin.last P.r) (by simp) c hc x hx
  · intro l x y hx hy c hc
    obtain ⟨φ, hφc, hφ, hC, -⟩ := hSD w hw l x y hx hy c hc
    refine ⟨φ, hφc, hφ, hC, ?_⟩
    intro s Wv Wv' h1 h2
    obtain ⟨hK, hT⟩ := hST w hw l s Wv Wv' h1 h2 x y hx hy c hc
    obtain ⟨ψ, hψc, hψ, -, hψint⟩ := hSD w hw l _ y hK hy c hc
    rw [← hψint]
    congr 1
    apply eq_of_continuous_off_zero ((continuous_fsv s).mul hφc) hψc
    intro t ht
    show fsv s t * φ t = ψ t
    rw [hψ t ht, hT t ht, hφ t ht]
  · intro i c hc
    refine ⟨hFS w hw i c hc, ?_⟩
    intro x hx
    have hxK : InK (K i) x := fun a => (Submodule.mem_pi.mp hx) a (Set.mem_univ a)
    exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw (P.r - i.val) i
      (by omega) c hc x hxK

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaBOfComponents
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.B

theorem lemma_B_of_components : Formalism.FourierDecayAlt.B.LemmaB :=
  bessel_lemma_from_reductions bilinear_form_continuity ae_equality_from_test_functions fatou_lemma_in_parameter matrix_coefficient_linear dilation_matrix_coefficient
    bessel_function_trivial_index regularized_beta_bound_continuity_sesquilinear regularised_average_identity unfolding_identity_of_integration_formula orbital_integral_ae_convergence_continuity
    dilation_identity_of_jacobian phase_function_adjoint regularised_pairing_via_phase assemble_equality_identity adjointness_of_bessel_transform

theorem b_lemmaBClosed_of : Formalism.FourierDecayAlt.B.XiExists → Formalism.FourierDecayAlt.B.LemmaBClosed := fun hX =>
  bessel_lemma_closed_form hX lemma_B_of_components clause_of_regularized_limit adjointness_polynomially_bounded

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNormalization
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BesselCapelliCommutation

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

variable {k r : ℕ}

theorem psi_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) : psi k r z c 1 = 1 := by
  have heI : ∀ (a : Fin r) (h : (a : ℕ) + 1 < r), eI k r a ≠ eI k r ⟨a + 1, h⟩ := by
    intro a h he
    have := congrArg Fin.val he
    simp [eI] at this
  have hz' : ∀ a : Fin r, z (eI k r a) = 0 := fun a => hz _ (Or.inl (by simp [eI]))
  simp [psi, ell, Matrix.one_apply_ne, heI, hz']

end Formalism.FourierDecayAlt.P.BesselCapelliCommutation

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

