module

public import Formalism.LocalToGlobal.CharacterGerms.RowTiePLogSt
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0020
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePOActLog
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OActLog

open PartialDerivEval LogEx

variable {C : Type} [Field C] [CharZero C] {d : ℕ}

theorem ev_zero_pt {n : ℕ} (g : PS C 1 d) : ev (n := n) ![(0 : Pt C n d)] g = MvPowerSeries.C (constantCoeff g) := by
  have hz : (fun p : Fin 1 × Fin d => (![0] : Fin 1 → Pt C n d) p.1 p.2) = 0 := by
    funext p
    obtain ⟨k, b⟩ := p
    fin_cases k
    rfl
  rw [ev, hz, subst_zero_eq_C_constantCoeff, map_C]
  simp

theorem cc_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv (R := C) i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem add_zero_of (G : FGLaw C d) (Q : PS C 1 d)
    (hQ : ev (n := 2) ![G.F] Q = ev (n := 2) ![pt C d 0] Q + ev (n := 2) ![pt C d 1] Q)
    (hlin : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) Q = 0) (hc : constantCoeff Q = 0) : Q = 0 := by
  classical
  let A : Matrix (Fin d) (Fin d) (PS C 1 d) := Matrix.of fun k b =>
    ev (n := 1) ![pt C d 0, 0] (pderiv (R := C) ((1 : Fin 2), k) (G.F b))
  let u : Fin d → PS C 1 d := fun b => pderiv (R := C) ((0 : Fin 1), b) Q
  have hX (k b : Fin d) :
      pderiv (R := C) ((0 : Fin 1), k) (pt C d 0 b) = if k = b then 1 else 0 := by
    by_cases h : k = b
    · subst b
      simp [pt]
    · rw [ite_eq_right h]
      exact pderiv_X_of_ne (by simpa using Ne.symm h)
  have hA : (constantCoeff : PS C 1 d →+* C).mapMatrix A = 1 := by
    ext k b
    have hz := constant_zero_zero_point (pt C (n := 1) d 0) (coordinate_point_constantCoeff 0)
    have h := congrArg (pderiv (R := C) ((0 : Fin 1), k)) (G.unit b)
    change pderiv ((0 : Fin 1), k) (ev ![0, pt C d 0] (G.F b)) =
      pderiv ((0 : Fin 1), k) (pt C d 0 b) at h
    rw [ev, Formalism.G.LogCR.pderiv_subst
      (a := fun p : Fin 2 × Fin d => (![0, pt C d 0] : Fin 2 → Pt C 1 d) p.1 p.2)
      (fun p => hz p.1 p.2),
      Fintype.sum_prod_type, Fin.sum_univ_two] at h
    change (∑ j, ev ![0, pt C d 0] (pderiv ((0 : Fin 2), j) (G.F b)) *
        pderiv ((0 : Fin 1), k) (0 : PS C 1 d)) +
      (∑ j, ev ![0, pt C d 0] (pderiv ((1 : Fin 2), j) (G.F b)) *
        pderiv ((0 : Fin 1), k) (pt C d 0 j)) = _ at h
    simp only [map_zero, mul_zero, Finset.sum_const_zero, zero_add, hX, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    have hcc := congrArg constantCoeff h
    rw [constantCoeff_ev hz, apply_ite constantCoeff, map_one, map_zero] at hcc
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, A, Matrix.of_apply, Matrix.one_apply,
      constantCoeff_ev constant_zero_first_zero] using hcc
  have hdet : IsUnit A.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hA, Matrix.det_one]
    exact isUnit_one
  have hchain (P : Pt C 2 d) (hP : ∀ j, constantCoeff (P j) = 0) (q : Fin 2 × Fin d) :
      pderiv q (ev ![P] Q) = ∑ b, ev ![P] (u b) * pderiv q (P b) := by
    unfold ev
    rw [Formalism.G.LogCR.pderiv_subst
      (a := fun p : Fin 1 × Fin d => (![P] : Fin 1 → Pt C 2 d) p.1 p.2)
      (fun p => z0_1 P hP p.1 p.2) Q q,
      Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  have hrow : A.mulVec u = 0 := by
    funext k
    have h0 : pderiv ((1 : Fin 2), k) (ev ![pt C d 0] Q) = 0 := by
      rw [hchain _ (coordinate_point_constantCoeff 0)]
      exact Finset.sum_eq_zero fun b _ => by simp [pt]
    have h1 : pderiv ((1 : Fin 2), k) (ev ![pt C d 1] Q) = ev ![pt C d 1] (u k) := by
      rw [hchain _ (coordinate_point_constantCoeff 1), Finset.sum_eq_single k]
      · simp [pt]
      · intro b _ hb
        rw [show pt C d 1 b = X ((1 : Fin 2), b) from rfl, pderiv_X_of_ne (by simp [hb]), mul_zero]
      · simp
    have D := congrArg (fun g => ev (n := 1) ![pt C d 0, 0] (pderiv (R := C) ((1 : Fin 2), k) g)) hQ
    rw [map_add (f := _), h0, h1, zero_add, hchain G.F G.const] at D
    rw [ev_sum constant_zero_first_zero] at D
    simp only [Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_mul constant_zero_first_zero, eval_group_law_at_zero G] at D
    rw [eval_eval_single (z0_1 (pt C d 1) (coordinate_point_constantCoeff 1)) constant_zero_first_zero (a' := (0 : Pt C 1 d)) (fun j => ev_X constant_zero_first_zero 1 j), ev_zero_pt,
      show u k = pderiv ((0 : Fin 1), k) Q from rfl, cc_pderiv, hlin k, map_zero] at D
    change (∑ b, A k b * u b) = 0
    change (∑ b, u b * A k b) = 0 at D
    simpa only [mul_comm (A k _) (u _)] using D
  have hd : u = 0 := by
    have h := congrArg (fun v => (A⁻¹).mulVec v) hrow
    change (A⁻¹).mulVec (A.mulVec u) = (A⁻¹).mulVec 0 at h
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  apply pderiv.ext
  · intro q
    obtain ⟨q1, q2⟩ := q
    fin_cases q1
    rw [map_zero]
    exact congrFun hd q2
  · rw [hc, map_zero]

def linM (φ : Pt C 1 d) (i j : Fin d) : C := coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)

theorem linN_coeff {lg : Pt C 1 d} (hlin : LinN lg) (j b : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), b) 1) (lg j) = if b = j then 1 else 0 := by
  rw [hlin j _ (by rw [Finsupp.degree_single]), coeff_X]
  by_cases h : b = j
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro e
    exact h (congrArg Prod.snd ((Finsupp.single_left_inj one_ne_zero).mp e))

theorem log_endo (G : FGLaw C d) (lg : Pt C 1 d) (hlin : LinN lg)
    (hadd : ∀ i, ev (n := 2) ![addOf G.F (pt C d 0) (pt C d 1)] (lg i) =
      ev (n := 2) ![pt C d 0] (lg i) + ev (n := 2) ![pt C d 1] (lg i))
    (φ : Pt C 1 d) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hφ : comp1 φ (addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1)) =
      addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1)))
    (i : Fin d) : comp1 lg φ i = ∑ j, MvPowerSeries.C (linM φ i j) * lg j := by
  have haddF : addOf G.F (pt C d 0) (pt C d 1) = (G.F : Pt C 2 d) := funext fun j => eval_points_two (G.F j)
  have hF : ∀ j, ev (n := 2) ![G.F] (lg j) = ev (n := 2) ![pt C d 0] (lg j) + ev (n := 2) ![pt C d 1] (lg j) := by
    intro j; rw [← haddF]; exact hadd j
  have hφ1 : Z0 (![φ] : Fin 1 → Pt C 1 d) := z0_1 φ hφ0
  have hFz : Z0 (![G.F] : Fin 1 → Pt C 2 d) := z0_1 G.F G.const
  have hP0 : Z0 (![pt C d 0] : Fin 1 → Pt C 2 d) := z0_1 _ (coordinate_point_constantCoeff 0)
  have hP1 : Z0 (![pt C d 1] : Fin 1 → Pt C 2 d) := z0_1 _ (coordinate_point_constantCoeff 1)
  set A : Pt C 2 d := comp1 φ (pt C (n := 2) d 0) with hA
  set B : Pt C 2 d := comp1 φ (pt C (n := 2) d 1) with hB
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => const_ev hP0 (hφ0 j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j => const_ev hP1 (hφ0 j)
  have hAB : Z0 (![A, B] : Fin 2 → Pt C 2 d) := by
    intro k j; fin_cases k
    · exact hA0 j
    · exact hB0 j

  have hlgAB : ∀ j, ev (n := 2) ![addOf G.F A B] (lg j) = ev (n := 2) ![A] (lg j) + ev (n := 2) ![B] (lg j) := by
    intro j
    have h := congrArg (ev (n := 2) ![A, B]) (hF j)
    have hFc : ∀ k, constantCoeff (G.F k) = 0 := G.const
    rw [ev_add hAB, eval_eval_single hFz hAB (a' := addOf G.F A B) (fun k => rfl),
      eval_eval_single hP0 hAB (a' := A) (fun k => ev_X hAB 0 k),
      eval_eval_single hP1 hAB (a' := B) (fun k => ev_X hAB 1 k)] at h
    exact h

  have hcomp : ev (n := 2) ![G.F] (comp1 lg φ i) =
      ev (n := 2) ![pt C d 0] (comp1 lg φ i) + ev (n := 2) ![pt C d 1] (comp1 lg φ i) := by
    have e1 : ev (n := 2) ![G.F] (comp1 lg φ i) = ev (n := 2) ![comp1 φ G.F] (lg i) :=
      eval_eval_single hφ1 hFz (a' := comp1 φ G.F) (fun k => rfl) (lg i)
    have e2 : comp1 φ G.F = addOf G.F A B :=
      calc comp1 φ G.F = comp1 φ (addOf G.F (pt C d 0) (pt C d 1)) := by rw [haddF]
        _ = addOf G.F A B := hφ
    have e3 : ev (n := 2) ![pt C d 0] (comp1 lg φ i) = ev (n := 2) ![A] (lg i) :=
      eval_eval_single hφ1 hP0 (a' := A) (fun k => rfl) (lg i)
    have e4 : ev (n := 2) ![pt C d 1] (comp1 lg φ i) = ev (n := 2) ![B] (lg i) :=
      eval_eval_single hφ1 hP1 (a' := B) (fun k => rfl) (lg i)
    rw [e1, e2, e3, e4, hlgAB]
  have hQ := add_zero_of G (comp1 lg φ i - ∑ j, MvPowerSeries.C (linM φ i j) * lg j) (by
      rw [ev_sub hFz, ev_sub hP0, ev_sub hP1, ev_sum hFz, ev_sum hP0, ev_sum hP1, hcomp]
      simp only [Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_mul hFz, Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_mul hP0, Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_mul hP1,
        Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_C, hF, mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro k
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [coeff_C_mul, linN_coeff hlin, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← cc_pderiv, show comp1 lg φ i = ev ![φ] (lg i) from rfl]
      have hchain :
          pderiv ((0 : Fin 1), k) (ev ![φ] (lg i)) =
            ∑ b, ev ![φ] (pderiv ((0 : Fin 1), b) (lg i)) * pderiv ((0 : Fin 1), k) (φ b) := by
        unfold ev
        rw [Formalism.G.LogCR.pderiv_subst
          (a := fun p : Fin 1 × Fin d => (![φ] : Fin 1 → Pt C 1 d) p.1 p.2)
          (fun p => hφ1 p.1 p.2),
          Fintype.sum_prod_type, Fin.sum_univ_one]
        rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hchain, map_sum]
      simp only [map_mul, constantCoeff_ev hφ1, cc_pderiv, linN_coeff hlin, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      unfold linM
      ring)
    (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, show comp1 lg φ i = ev ![φ] (lg i) from rfl, constantCoeff_ev hφ1, linN_const hlin]
      simp [linN_const hlin])
  exact sub_eq_zero.mp hQ

end OActLog

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLie
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLie

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePSplit

section Lin

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def linM (φ : Pt C 1 dd) : Matrix (Fin dd) (Fin dd) C :=
  Matrix.of fun i j => coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)

theorem linAct_eq (φ : Pt C 1 dd) (v : Fin dd → C) : linAct φ v = Matrix.mulVec (linM φ) v := by
  funext i
  rfl

theorem coeff_single_cc {σ : Type} (s : σ) (f : MvPowerSeries σ C) :
    coeff (Finsupp.single s 1) f = constantCoeff (MvPowerSeries.pderiv (R := C) s f) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem cc_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (g : MvPowerSeries σ C) : constantCoeff (MvPowerSeries.subst a g) = constantCoeff g := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha), finsum_eq_single _ 0]
  · simp
  · intro d hd
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      rw [map_finsuppProd]
      obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      show MvPowerSeries.constantCoeff (a s ^ d s) = 0
      rw [map_pow, ha s, zero_pow hs]
    rw [h0, smul_zero]

theorem lin_comp1 {φ ψ : Pt C 1 dd} (hψ : ∀ k, constantCoeff (ψ k) = 0) :
    linM (comp1 φ ψ) = linM φ * linM ψ := by
  ext i j
  simp only [linM, Matrix.of_apply, Matrix.mul_apply, coeff_single_cc]
  show constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), j)
    (MvPowerSeries.subst (fun p : Fin 1 × Fin dd => (![ψ] : Fin 1 → Pt C 1 dd) p.1 p.2) (φ i))) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => (![ψ] : Fin 1 → Pt C 1 dd) p.1 p.2)
    (fun p => (z0_1 ψ hψ) p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cc_subst (a := fun p : Fin 1 × Fin dd => (![ψ] : Fin 1 → Pt C 1 dd) p.1 p.2)
    (fun p => (z0_1 ψ hψ) p.1 p.2)]
  rfl

theorem lin_pt : linM (pt C (n := 1) dd 0) = 1 := by
  ext i j
  simp only [linM, pt, Matrix.of_apply, Matrix.one_apply, MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg, if_neg h]
    intro h2
    apply h
    have h3 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h2
    exact (Prod.mk.inj h3).2.symm

theorem cc_pderiv_X {σ : Type} [DecidableEq σ] (s t : σ) : constantCoeff (MvPowerSeries.pderiv (R := C) s (X t : MvPowerSeries σ C)) = if t = s then 1 else 0 := by
  rw [MvPowerSeries.pderiv_X]
  by_cases h : t = s
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem formal_group_coeff_first_linear {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (i j : Fin dd) :
    constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 2), j) (Y.B.G.F i)) = if i = j then 1 else 0 := by
  have hA : Z0 (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) := z0_p0 _ (z0_pt 0)
  have h := congrArg (fun f => constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), j) f)) (formalGroupLaw_ev_x_zero Y (pt C (n := 1) dd 0) (z0_pt 0) i)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [map_mul, cc_subst (a := fun p : Fin 2 × Fin dd => (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pt, Pi.zero_apply, map_zero,
    mul_zero, Finset.sum_const_zero, add_zero, cc_pderiv_X, Prod.mk.injEq, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]

theorem formal_group_coeff_second_linear {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (i j : Fin dd) :
    constantCoeff (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), j) (Y.B.G.F i)) = if i = j then 1 else 0 := by
  have hA : Z0 (![0, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k j'; fin_cases k
    · simp
    · exact z0_pt 0 j'
  have h := congrArg (fun f => constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), j) f)) (Y.B.G.unit i)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => (![0, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [map_mul, cc_subst (a := fun p : Fin 2 × Fin dd => (![0, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pt, Pi.zero_apply, map_zero,
    mul_zero, Finset.sum_const_zero, zero_add, cc_pderiv_X, Prod.mk.injEq, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]

theorem lin_addOf {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) {A B : Pt C 1 dd}
    (hA : ∀ k, constantCoeff (A k) = 0) (hB : ∀ k, constantCoeff (B k) = 0) :
    linM (addOf Y.B.G.F A B) = linM A + linM B := by
  have hZ : Z0 (![A, B] : Fin 2 → Pt C 1 dd) := constant_zero_two_points A B hA hB
  ext i j
  simp only [linM, Matrix.of_apply, Matrix.add_apply, coeff_single_cc]
  show constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), j)
    (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![A, B] : Fin 2 → Pt C 1 dd) p.1 p.2) (Y.B.G.F i))) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => (![A, B] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hZ p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [map_mul, cc_subst (a := fun p : Fin 2 × Fin dd => (![A, B] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hZ p.1 p.2), formal_group_coeff_first_linear Y, formal_group_coeff_second_linear Y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Lin

section Glue

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def linHom (Y : FBChart C V O dd) : O →+* Matrix (Fin dd) (Fin dd) C where
  toFun x := linM (Y.B.A.act x)
  map_one' := by rw [Y.B.A.one_act]; exact lin_pt
  map_mul' x y := by rw [Y.B.A.mul_act]; exact lin_comp1 (Y.B.A.const y)
  map_zero' := by
    have e := Y.B.A.add_act 0 0
    rw [add_zero] at e
    have h : linM (Y.B.A.act 0) = linM (Y.B.A.act 0) + linM (Y.B.A.act 0) := by
      conv_lhs => rw [e]
      exact lin_addOf Y (Y.B.A.const 0) (Y.B.A.const 0)
    have h2 := congrArg (fun M => M - linM (Y.B.A.act 0)) h
    simp only [sub_self, add_sub_cancel_right] at h2
    exact h2.symm
  map_add' x y := by rw [Y.B.A.add_act]; exact lin_addOf Y (Y.B.A.const x) (Y.B.A.const y)

theorem proj_core (Y : FBChart C V O dd) (ε : O) (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (e : Pt C 1 dd)
    (he : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))) :
    (∀ i, MvPowerSeries.constantCoeff (e i) = 0) ∧ comp1 e e = e ∧
      (∀ a, comp1 e (Y.B.A.act a) = comp1 (Y.B.A.act a) e) := by
  have hT := tends_of_endomorphism_limit Y he
  have e0 : ∀ i, constantCoeff (e i) = 0 := const_of_lim Y hT
  have act0 : ∀ x i, constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨e0, ?_, ?_⟩
  · funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (ε ^ V.l ^ n)) (b := fun n => Y.B.A.act (ε ^ V.l ^ n))
      (fun n => act0 _) e0 hT hT i
    have R := tendsS_of_small lSmall_holds Y (x := fun n => ε ^ V.l ^ n * ε ^ V.l ^ n) (sq_cong hε) hT i
    have eq : (fun n => comp1 (Y.B.A.act (ε ^ V.l ^ n)) (Y.B.A.act (ε ^ V.l ^ n)) i) =
        fun n => Y.B.A.act (ε ^ V.l ^ n * ε ^ V.l ^ n) i := funext fun n => by rw [Y.B.A.mul_act]
    rw [eq] at L
    exact L.unique R
  · intro a
    funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (ε ^ V.l ^ n)) (b := fun _ => Y.B.A.act a)
      (fun _ => act0 a) (act0 a) hT (fun _ => TendsS.const _) i
    have R := TendsS.comp1 (φ := fun _ => Y.B.A.act a) (b := fun n => Y.B.A.act (ε ^ V.l ^ n))
      (fun n => act0 _) e0 (fun _ => TendsS.const _) hT i
    have eq : (fun n => comp1 (Y.B.A.act (ε ^ V.l ^ n)) (Y.B.A.act a) i) =
        fun n => comp1 (Y.B.A.act a) (Y.B.A.act (ε ^ V.l ^ n)) i := funext fun n => by
      rw [← Y.B.A.mul_act, ← Y.B.A.mul_act, mul_comm]
    rw [eq] at L
    exact L.unique R

end Glue

end RowTiePLie

end Formalism.L2.FormalSeriesBounds
end
end

