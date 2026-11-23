module

public import Formalism.HermitianCurvature.StatementJ
public import Formalism.HermitianCurvature.StatementFr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0018
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0016
public import Formalism.HermitianCurvature.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0011
public import Formalism.HermitianCurvature.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0017
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplitPrimeToDifferent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevToThreshold
section
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Jx10

theorem pull {α X : Type} [DecidableEq X] (η : α → X) (F : Finset α) (k : X → X → ℂ)
    (h : A5.IsPSD (F.image η) k) : A5.IsPSD F (fun x y => k (η x) (η y)) := by
  unfold Formalism.FourierDecayAlt.A5.IsPSD at h ⊢
  intro a
  show (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).im = 0 ∧
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).re
  set b : X → ℂ := fun u => ∑ z ∈ F.filter (fun z => η z = u), a z with hb
  have hmaps : ∀ x ∈ F, η x ∈ F.image η := fun x hx => Finset.mem_image_of_mem η hx
  have rhs : ∀ u v, b u * conj (b v) * k u v =
      ∑ x ∈ F.filter (fun z => η z = u), ∑ y ∈ F.filter (fun z => η z = v),
        a x * conj (a y) * k (η x) (η y) := by
    intro u v
    simp only [hb]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have h1 := (Finset.mem_filter.mp hx).2
    have h2 := (Finset.mem_filter.mp hy).2
    rw [h1, h2] <;> ring
  have key : (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)) =
      ∑ u ∈ F.image η, ∑ v ∈ F.image η, b u * conj (b v) * k u v := by
    simp_rw [rhs]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
  rw [key]
  exact h b

theorem inter_of_module (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E)
    (hL : ∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
      algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) (t : E)
    (h : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ S6.locAt E P L) : t ∈ L := by
  by_contra ht
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _), add_mul] at ha hb ⊢
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, mul_assoc] at ha ⊢
        exact hL c _ ha }
  have hI : I ≠ ⊤ := by
    intro hI
    apply ht
    have h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := by
      rw [hI]
      exact Submodule.mem_top
    have h2 : algebraMap (𝓞 (maximalRealSubfield E)) E 1 * t ∈ L := h1
    simpa using h2
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨a, haP, haL⟩ := h P hP
  exact haP (hIP haL)

end Formalism.FourierDecayAlt.P.Jx10

namespace Formalism.FourierDecayAlt.P


open Classical in
theorem local_kernel_psd : Formalism.FourierDecayAlt.J.LocalKernelPSD := by
  intro hag hgram K _ _ _ R ψ hLD α η Y
  rw [(hag α Y _).1, ← (hag α Y _).2]
  exact Jx10.pull η Y (A5.Kp R ψ) (hgram K R ψ hLD (Y.image η))

theorem intersection_of_local : Formalism.FourierDecayAlt.J.IntersectionOfLocal := by
  intro E _ _ _ L hL t
  obtain ⟨hL1, -⟩ := hL
  constructor
  · intro ht P hP
    unfold Formalism.FourierDecayAlt.S6.locAt
    rw [Set.mem_setOf_eq]
    refine ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1), ?_⟩
    rw [map_one, one_mul]
    exact ht
  · intro h
    exact Jx10.inter_of_module E L hL1 t h

theorem lattice_of_local : Formalism.FourierDecayAlt.J.LatticeOfLocal := by
  intro E _ _ _ L hL Q _ pl M hcov hM
  have hint := intersection_of_local E L hL
  ext t
  rw [AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, hint]
  constructor
  · intro h p
    rw [hM]
    intro P _ hP
    exact h P hP
  · intro h P hP
    obtain ⟨p, hp⟩ := hcov P hP
    exact (hM p t).mp (h p) P hp hP

theorem pull_lattice_typed : Formalism.FourierDecayAlt.J.PullLatticeTyped := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u α ψ η Θ hR hu t
  rw [hT E g ν s hg hpd P hP hgP K o σ hσ t]
  show (u : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t ∈ R ↔ _
  rw [hR, hu]
  have e : (((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) : K × K) *
      (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t =
      (σ t / (g : K), (-1) ^ s * σ (IsCMField.complexConj E t) / (g : K)) := by
    ext
    · simp [div_eq_mul_inv, mul_comm]
    · simp [div_eq_mul_inv]; ring
  rw [e]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2RmatrixTranspose
section
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr4

section

variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem free_one (c : S) : FreeOf c (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

theorem free_zero (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _

theorem free_mul {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x * y) :=
  fun i j => (hx i j).mul_right (hy i j)

theorem free_add {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x + y) :=
  fun i j => (hx i j).add_right (hy i j)

theorem free_sub {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x - y) :=
  fun i j => (hx i j).sub_right (hy i j)

theorem free_neg {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) : FreeOf c (-x) :=
  fun i j => (hx i j).neg_right

theorem free_smul {c : S} {x : SlopeTestRemainingChoices S A} (k : ℂ) (hx : FreeOf c x) : FreeOf c (k • x) :=
  fun i j => (hx i j).smul_right k

theorem free_pow {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (n : ℕ) : FreeOf c (x ^ n) :=
  fun i j => (hx i j).pow_right n

theorem free_star [StarRing A] {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) : FreeOf c (star x) := by
  intro i j
  have h := (hx j i).star_star
  rwa [Wd1.star_eU] at h

theorem free_io (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * io x = io x * eU c i j
  ext u v
  unfold io
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Wd1.eU_apply]
  split_ifs <;> simp

theorem free_eU {a c : S} (hc : c ≠ a) (k l : Fin 2) : FreeOf c (eU a k l : SlopeTestRemainingChoices S A) :=
  fun i j => Wd1.eU_comm_of_ne hc i j k l

theorem freeOf2_mul {c : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) (hN : FreeOf2 c N) : FreeOf2 c (M * N) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact free_add (free_mul (hM _ _) (hN _ _)) (free_mul (hM _ _) (hN _ _))

theorem freeOf2_transpose {c : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) : FreeOf2 c Mᵀ :=
  fun i j => hM j i

theorem freeOf2_matrix_entries {c : S} {x y z w : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) (hz : FreeOf c z)
    (hw : FreeOf c w) : FreeOf2 c !![x, y; z, w] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact hx
  · exact hy
  · exact hz
  · exact hw

theorem freeOf2_one (c : S) : FreeOf2 c (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq]; exact free_one c
  · rw [Matrix.one_apply_ne h]; exact free_zero c

theorem freeOf2_rmatrix {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  unfold Rh0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))

theorem freeOf2_rmatrix_transpose {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  unfold Rht0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))

theorem freeOf2_lift (c : S) (M : M2 A) : FreeOf2 c (lift0 M : M2 (SlopeTestRemainingChoices S A)) :=
  fun i j => free_io c (M i j)

end

section

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem free_l (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.l L Y) :=
  free_add (free_io c _) (free_mul (free_io c _) (h.2.2.2.2.2.2.2.2 Y))

theorem free_d (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) : FreeOf c (f.d L) :=
  free_mul (free_pow (free_io c _) _) h.2.2.2.2.2.2.1

theorem free_di (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) : FreeOf c (f.di L) :=
  free_mul h.2.2.2.2.2.2.2.1 (free_pow (free_io c _) _)

theorem free_m (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.m L Y) :=
  free_mul (free_mul (free_di L h) (free_star (free_l L h _))) (free_d L h)

theorem free_DD {f : FrameData S A} {c : S} (h : f.Free c) (Y Ya : ℂ) : FreeOf c (f.DD Y Ya) :=
  free_smul _ (free_sub (h.2.2.2.2.2.2.2.2 Y) (h.2.2.2.2.2.2.2.2 Ya))

theorem free_tz (L : LevelData A r) (c : S) : FreeOf c (tz L : SlopeTestRemainingChoices S A) := free_io c _

theorem plus_free (L : LevelData A r) {f : FrameData S A} {a c : S} (hc : c ≠ a) (h : f.Free c) (Ya : ℂ) :
    (f.plus L a Ya).Free c := by
  obtain ⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩ := id h
  have z := free_zero (A := A) c
  have o := free_one (A := A) c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact free_mul hRR (Wd1.ins_free hc _ (hTT Ya))
  · exact fun Y => freeOf2_mul (hTT Y) (freeOf2_rmatrix hc _)
  · exact free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _))
      (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_l L h Ya)) (free_io c _)))) hF
  · exact free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_l L h Ya)) (free_io c _))
      (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))
  · exact fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))
  · exact free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))
  · exact fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (free_add (free_sub (hee Y) (free_DD h Y Ya)) (free_tz L c))
      (free_neg (free_smul _ o)) z (free_mul (free_mul (hxi _) (hee Y)) (hx _)))

theorem minus_free (L : LevelData A r) {f : FrameData S A} {b c : S} (hc : c ≠ b) (h : f.Free c) (Yb : ℂ) :
    (f.minus L b Yb).Free c := by
  obtain ⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩ := id h
  have z := free_zero (A := A) c
  have o := free_one (A := A) c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact free_mul hRR (Wd1.ins_free hc _ (freeOf2_transpose (hTT Yb)))
  · exact fun Y => freeOf2_mul (freeOf2_rmatrix_transpose hc _) (hTT Y)
  · exact free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _))
      (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_m L h Yb)) (free_io c _)))) hF
  · exact free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_m L h Yb)) (free_io c _))
      (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))
  · exact fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))
  · exact free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))
  · exact fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (hee Y) z (free_neg (free_smul _ (free_mul (hxi _) (hxi _))))
      (free_add (free_sub (free_mul (free_mul (hxi _) (hee Y)) (hx _)) (free_DD h Y Yb)) (free_tz L c)))

theorem start_free (st : Start A) (c : S) : (st.frame : FrameData S A).Free c :=
  ⟨free_one c, fun _ => freeOf2_lift c _, free_one c, free_one c, fun _ => free_io c _, fun _ => free_io c _,
    free_one c, free_one c, fun _ => free_io c _⟩

end

end Formalism.FourierDecayAlt.P.Fr4

namespace Formalism.FourierDecayAlt.P

theorem frame_free_of_new_position : Formalism.FourierDecayAlt.Fr.FrameFree := by
  intro A S _ _ _ _ _ _ r L st w c
  induction w with
  | nil => intro _; exact Fr4.start_free st c
  | cons l w ih =>
    intro hc
    rw [List.map_cons, List.mem_cons, not_or] at hc
    have h := ih hc.2
    show (if l.plus then (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt else (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt).Free c
    split_ifs
    · exact Fr4.plus_free L hc.1 h l.pt
    · exact Fr4.minus_free L hc.1 h l.pt

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ImCircleIntegral
section
open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem continuousOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContinuousOn (bet α) (Hh TT) := by
  exact (contDiffOn_bet hα).continuousOn

theorem cont_vert (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    Continuous fun θ : ℝ => bet α (x0 TT + (θ : ℂ) * I) := by
  exact (continuousOn_bet hα).comp_continuous (by fun_prop) (vert_mem hTT)

theorem im_circleIntegral (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    (circleIntegral α 0 (TT + 1)).im = ∫ θ in (0 : ℝ)..2 * Real.pi, (bet α (x0 TT + (θ : ℂ) * I)).re := by
  have hint : IntervalIntegrable (fun θ : ℝ => I * bet α (x0 TT + (θ : ℂ) * I)) MeasureTheory.volume
      0 (2 * Real.pi) :=
    (continuous_const.mul (cont_vert hTT hα)).intervalIntegrable _ _
  rw [circleIntegral_eq hTT, ← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1
  funext θ
  simp [Complex.mul_im]

theorem th_top (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    th TT α (x0 TT + 2 * Real.pi * I) = 2 * (circleIntegral α 0 (TT + 1)).im := by
  rw [im_circleIntegral hTT hα]
  have hw : x0 TT + 2 * Real.pi * I - x0 TT = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
  have harg : ∀ t : ℝ, x0 TT + (t : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * I) =
      x0 TT + ((2 * Real.pi * t : ℝ) : ℂ) * I := by
    intro t; push_cast; ring
  have him : ∀ z : ℂ, (z * (((2 * Real.pi : ℝ) : ℂ) * I)).im = 2 * Real.pi * z.re := by
    intro z
    simp [Complex.mul_im, Complex.mul_re]
    ring
  simp only [th, prim, hw, om_apply, harg, him]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (f := fun θ : ℝ => (bet α (x0 TT + (θ : ℂ) * I)).re)
      (by positivity : (2 * Real.pi) ≠ 0)]
  simp only [mul_zero, mul_one, smul_eq_mul]
  have hpi : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc (2 * Real.pi), hpi, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeSummability
section
open MeasureTheory Set Finset Function

noncomputable section

namespace Formalism.FourierDecayAlt.P.LatticeSummability

open Formalism.FourierDecayAlt.crystallineComparison

theorem mfac_nonneg (K : ℕ) {L : ℝ} (hL : 0 ≤ L) (a : ℝ) (ha : 0 ≤ a) : 0 ≤ mfac K L a := by
  unfold mfac
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (by positivity)

theorem mfac_anti (K : ℕ) {L : ℝ} (hL : 0 < L) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    mfac K L b' ≤ mfac K L b := by
  unfold mfac
  by_cases hb0 : b = 0
  · rw [if_pos hb0]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hb'0 : b' ≠ 0 := by linarith
    rw [if_neg hb0, if_neg hb'0]
    refine min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hL.le (by linarith)) ?_ K)
    exact div_le_div_of_nonneg_left hL.le hbpos hbb

end Formalism.FourierDecayAlt.P.LatticeSummability
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting
section
namespace Formalism.FourierDecayAlt.P

theorem lattice_facts_general : Formalism.FourierDecayAlt.S6.LatticesGeneral :=
  assemble_lattice_facts degreeFacts_statement different_power_conj_stable
    unramRelative twistedLatticeBetween twistedLatticeIndex dual_lattice_subset
    traceDualGe scaledIdealNorm covolumeIndex

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionGivesUniformBoundsForm
section
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix

namespace Formalism.FourierDecayAlt.P.Jx6

end Formalism.FourierDecayAlt.P.Jx6

namespace Formalism.FourierDecayAlt.P

open Jx6

theorem form_gives_theorem_A : Formalism.FourierDecayAlt.J.FormGivesMain := by
  intro hM P _ B hPos he hKV h2A hF hMass hform hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩ := hPos
  have hn : 0 < B.n0c := a33
  have hen : 0 < B.e1 * B.n0c := mul_pos he hn
  have key := hM P { B with supdens := B.e1, KtopV := B.KV / (B.e1 * B.n0c) }
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, he.le, a35⟩ h2A hF
    (by
      constructor
      · show B.KV ≤ B.e1 * B.n0c * (B.KV / (B.e1 * B.n0c))
        rw [mul_div_cancel₀ _ hen.ne']
      · show 0 ≤ B.KV / (B.e1 * B.n0c)
        exact div_nonneg hKV hen.le)
    hMass
    (by show B.e1 ≤ B.e1; exact le_refl _)
    (by
      show B.c0 * B.c0' * (B.KV / (B.e1 * B.n0c)) ≤ (1 + B.δ) * B.IntN
      rw [← mul_div_assoc, div_le_iff₀ hen]
      have e : (1 + B.δ) * B.e1 * (B.n0c * B.IntN) = (1 + B.δ) * B.IntN * (B.e1 * B.n0c) := by ring
      linarith)
    hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  exact key

end Formalism.FourierDecayAlt.P
end

