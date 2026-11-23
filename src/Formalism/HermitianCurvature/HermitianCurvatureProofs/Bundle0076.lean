module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0027
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0071
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0068
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtInvpow
section
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

private lemma exists_zhat_eq_eval_poly_deg_le_one (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ P : Fin (r + 1) → Fin (r + 1) → MvPolynomial (Vr (2 * r + k + 1)) ℂ,
      (∀ a b, (P a b).totalDegree ≤ 1) ∧
        ∀ (g : Mat k r) a b, eval (vars g) (P a b) = Zhat k r z z' g a b := by
  refine ⟨fun a b => ∑ i, ∑ j, C (((Fm k r z)ᴴ * Hpk k r) a i * Fm k r z' j b) *
    MvPolynomial.X (Sum.inl (i, j)), ?_, ?_⟩
  · intro a b
    exact MvPolynomial.totalDegree_finsetSum_le fun i _ =>
      MvPolynomial.totalDegree_finsetSum_le fun j _ => deg_CX _ _
  · intro g a b
    rw [Zhat_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_C, eval_X, PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun x _ => by ring

private lemma exists_star_zhat_eq_eval_poly_deg_le_one (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ P : Fin (r + 1) → Fin (r + 1) → MvPolynomial (Vr (2 * r + k + 1)) ℂ,
      (∀ a b, (P a b).totalDegree ≤ 1) ∧
        ∀ (g : Mat k r) a b, eval (vars g) (P a b) = star (Zhat k r z z' g a b) := by
  refine ⟨fun a b => ∑ i, ∑ j, C (star (((Fm k r z)ᴴ * Hpk k r) a i * Fm k r z' j b)) *
    MvPolynomial.X (Sum.inr (i, j)), ?_, ?_⟩
  · intro a b
    exact MvPolynomial.totalDegree_finsetSum_le fun i _ =>
      MvPolynomial.totalDegree_finsetSum_le fun j _ => deg_CX _ _
  · intro g a b
    rw [Zhat_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_C, eval_X, PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul,
      star_sum, star_mul']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun x _ => by ring

private lemma exists_det_submatrix_poly_deg_le_of_entries_deg_le_one {m : ℕ} (f : Mat k r → Matrix (Fin m) (Fin m) ℂ)
    (P : Fin m → Fin m → MvPolynomial (Vr (2 * r + k + 1)) ℂ) (hP : ∀ a b, (P a b).totalDegree ≤ 1)
    (hf : ∀ g a b, eval (vars g) (P a b) = f g a b) (n : ℕ) (e : Fin n → Fin m) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ n ∧
      ∀ g, ((f g).submatrix e e).det = eval (vars g) q := by
  refine ⟨(Matrix.of fun a b => P (e a) (e b)).det, deg_det _ (fun a b => hP _ _), fun g => ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply, hf]

private lemma exists_dmin_eq_eval_poly_deg_le (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ l.val ∧
      ∀ g : Mat k r, Dmin k r z z' g l = eval (vars g) q := by
  obtain ⟨P, hP, hPe⟩ := exists_zhat_eq_eval_poly_deg_le_one (k := k) (r := r) z z'
  obtain ⟨q, hq, hqe⟩ := exists_det_submatrix_poly_deg_le_of_entries_deg_le_one (fun g => Zhat k r z z' g) P hP hPe l.val
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))
  exact ⟨q, hq, fun g => by rw [Dmin]; exact hqe g⟩

private lemma exists_star_dmin_eq_eval_poly_deg_le (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ l.val ∧
      ∀ g : Mat k r, star (Dmin k r z z' g l) = eval (vars g) q := by
  obtain ⟨P, hP, hPe⟩ := exists_star_zhat_eq_eval_poly_deg_le_one (k := k) (r := r) z z'
  obtain ⟨q, hq, hqe⟩ := exists_det_submatrix_poly_deg_le_of_entries_deg_le_one (fun g => (Zhat k r z z' g).map (starRingEnd ℂ)) P hP
    (fun g a b => by simp [hPe]) l.val (Fin.castLE (Nat.le_of_lt_succ l.isLt))
  refine ⟨q, hq, fun g => ?_⟩
  rw [← hqe g, Dmin, ← starRingEnd_apply, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

lemma dminPoly (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, Dmin k r z z' g l = eval (vars g) q := by
  obtain ⟨q, hq, hqe⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), hqe⟩

lemma dminStarPoly (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, star (Dmin k r z z' g l) = eval (vars g) q := by
  obtain ⟨q, hq, hqe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), hqe⟩

lemma gfPoly (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, ((Gf k r z z' g : ℝ) : ℂ) = eval (vars g) q := by
  obtain ⟨qa, ha, hae⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' (Fin.last (r + 1))
  obtain ⟨qab, hab, habe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' (Fin.last (r + 1))
  obtain ⟨qb, hb, hbe⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' ⟨r, by omega⟩
  obtain ⟨qbb, hbb, hbbe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' ⟨r, by omega⟩
  simp only [Fin.val_last] at ha hab hb hbb
  refine ⟨qa * qab - C ((Tz k r z * Tz k r z' : ℝ) : ℂ) * qb * qbb, ?_, fun g => ?_⟩
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (deg_cmul _ _ _).trans (by omega)
  · simp only [map_sub, map_mul, eval_C]
    rw [← hae g, ← habe g, ← hbe g, ← hbbe g, Gf]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring

def qDl (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (dminPoly (k := k) z z' l)

def qDbl (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (dminStarPoly (k := k) z z' l)

def qGf (z z' : Fin (2 * r + k + 1) → ℂ) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (gfPoly (k := k) z z')

lemma qDl_deg (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : (qDl (k := k) z z' l).totalDegree ≤ 2 * r + 2 :=
  (Classical.choose_spec (dminPoly (k := k) z z' l)).1
lemma qDl_eval (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) (g : Mat k r) :
    eval (vars g) (qDl z z' l) = Dmin k r z z' g l :=
  ((Classical.choose_spec (dminPoly (k := k) z z' l)).2 g).symm
lemma qDbl_deg (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : (qDbl (k := k) z z' l).totalDegree ≤ 2 * r + 2 :=
  (Classical.choose_spec (dminStarPoly (k := k) z z' l)).1
lemma qDbl_eval (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) (g : Mat k r) :
    eval (vars g) (qDbl z z' l) = star (Dmin k r z z' g l) :=
  ((Classical.choose_spec (dminStarPoly (k := k) z z' l)).2 g).symm
lemma qGf_deg (z z' : Fin (2 * r + k + 1) → ℂ) : (qGf (k := k) z z').totalDegree ≤ 2 * r + 2 :=
  (Classical.choose_spec (gfPoly (k := k) z z')).1
lemma qGf_eval (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    eval (vars g) (qGf z z') = ((Gf k r z z' g : ℝ) : ℂ) :=
  ((Classical.choose_spec (gfPoly (k := k) z z')).2 g).symm

structure CT (k r nf : ℕ) where
  q : MvPolynomial (Vr (2 * r + k + 1)) ℂ
  a : Fin (r + 2) → ℕ
  b : Fin (r + 2) → ℕ
  c : ℕ
  es : List (Fin nf × List (Mat k r))

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} (t : CT k r nf) (g : Mat k r) : ℂ :=
  eval (vars g) t.q * C6.monoM D t.a t.b t.c g

def cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (t : CT k r nf) (g : Mat k r) :
    C6.EndH Wp Wq :=
  cvs D t g • C6.Epart fib t.es g

def dscal (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  [{ t with q := dP X t.q }] ++
  List.ofFn (fun l : Fin (r + 2) => if t.a l = 0 then { t with q := 0 } else
    { t with q := C (-(t.a l : ℂ)) * t.q * dP X (qDl D.z D.z' l), a := t.a + Pi.single l 1 }) ++
  List.ofFn (fun l : Fin (r + 2) => if t.b l = 0 then { t with q := 0 } else
    { t with q := C (-(t.b l : ℂ)) * t.q * dP X (qDbl D.z D.z' l), b := t.b + Pi.single l 1 }) ++
  [if t.c = 0 then { t with q := 0 } else { t with q := C (-(t.c : ℂ)) * t.q * dP X (qGf D.z D.z'), c := t.c + 1 }]

def dfib {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  List.ofFn (fun i : Fin t.es.length => { t with es := t.es.set i ((t.es.get i).1, X :: (t.es.get i).2) })

def dco (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  dscal D X t ++ dfib X t

end vals

lemma hasDerivAt_invpow' {c : ℝ → ℂ} {c' : ℂ} (hc : HasDerivAt c c' 0) {a : ℕ} (h0 : a = 0 ∨ c 0 ≠ 0) :
    HasDerivAt (fun t => (c t)⁻¹ ^ a) (-(a : ℂ) * c' * (c 0)⁻¹ ^ (a + 1)) 0 := by
  cases a with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | succ n =>
    have hc0 : c 0 ≠ 0 := h0.resolve_left (Nat.succ_ne_zero n)
    have h2 := ((hasDerivAt_inv hc0).pow (n + 1)).comp (0 : ℝ) hc
    have h3 : HasDerivAt (fun t => (c t)⁻¹ ^ (n + 1))
        (((n + 1 : ℕ) : ℂ) * (c 0)⁻¹ ^ (n + 1 - 1) * -(c 0 ^ 2)⁻¹ * c') 0 := h2
    refine h3.congr_deriv ?_
    rw [Nat.add_sub_cancel, ← inv_pow]
    push_cast
    ring

lemma hasDerivAt_polyD (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    HasDerivAt (fun t => Dmin k r z z' (crv (false, X) g t) l) (eval (vars g) (dP X (qDl z z' l))) 0 := by
  have h := hasDerivAt_poly X g (qDl (k := k) z z' l)
  simp only [qDl_eval] at h
  exact h

lemma hasDerivAt_polyDb (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    HasDerivAt (fun t => star (Dmin k r z z' (crv (false, X) g t) l)) (eval (vars g) (dP X (qDbl z z' l))) 0 := by
  have h := hasDerivAt_poly X g (qDbl (k := k) z z' l)
  simp only [qDbl_eval] at h
  exact h

lemma hasDerivAt_polyG (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) :
    HasDerivAt (fun t => ((Gf k r z z' (crv (false, X) g t) : ℝ) : ℂ)) (eval (vars g) (dP X (qGf z z'))) 0 := by
  have h := hasDerivAt_poly X g (qGf (k := k) z z')
  simp only [qGf_eval] at h
  exact h

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadDZCompLeft
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

abbrev Coef (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] : Type :=
  (j : ℕ) → ℂ → (ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp))

abbrev AnnZ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Set ℂ :=
  {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ}

abbrev Dj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (j : ℕ)
    (q : (Fin P.r → ℂ) × ℂ) : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) :=
  iteratedFDeriv ℝ j (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec Φ (q.1, ζ)) q.2

def Rep (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (n : ℕ) (A : Coef Wp Wq) : Prop :=
  (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A j) (AnnZ P Bs)) ∧
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        ∑ j ∈ Finset.range (n + 1), A j q.2 (Dj P Bs (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) j q)

theorem rep_ext {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {n m : ℕ} (hnm : n ≤ m) {A : Coef Wp Wq}
    (h : Rep P Bs T n A) : Rep P Bs T m (fun j ζ => if j ≤ n then A j ζ else 0) := by
  refine ⟨fun j => ?_, fun Φ q hq => ?_⟩
  · by_cases hj : j ≤ n
    · simp only [hj, if_true]; exact h.1 j
    · simp only [hj, if_false]; exact contDiffOn_const
  · rw [h.2 Φ q hq]
    symm
    rw [← Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ m + 1))]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≤ n := by simp at hj; omega
      simp only [this, if_true]
    · intro j _ hj
      have : ¬ j ≤ n := by simp at hj; omega
      simp only [this, if_false, ContinuousLinearMap.zero_apply]

theorem radR_smul' (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : ℂ) (F : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    (x : (Fin P.r → ℂ) × ℂ) :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (c • F) x = c • NF.radR P.k P.r Bs.z Bs.z' Bs.μsec F x := by
  unfold NF.radR
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z' <;> simp [hx]

theorem radR_zero'' (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (x : (Fin P.r → ℂ) × ℂ) :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (0 : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x = 0 := by
  unfold NF.radR
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z' <;> simp [hx]

theorem radDZ_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    RadDZ P Bs (0 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) := by
  refine ⟨0, fun _ _ => 0, fun _ => contDiffOn_const, fun Φ q _ => ?_⟩
  have : (((0 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = 0 := rfl
  rw [this, radR_zero'']
  simp

theorem radDZ_one (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    RadDZ P Bs (1 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) := by
  refine ⟨0, fun j _ => ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun _ => 0),
    fun _ => contDiffOn_const, fun Φ q _ => ?_⟩
  rw [Finset.sum_range_one]
  show _ = (iteratedFDeriv ℝ 0 (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2)
    (fun _ => 0)
  rw [iteratedFDeriv_zero_apply]
  rfl

theorem radDZ_add {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T1 T2 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (h1 : RadDZ P Bs T1) (h2 : RadDZ P Bs T2) :
    RadDZ P Bs (T1 + T2) := by
  obtain ⟨n1, A1, hr1⟩ := h1
  obtain ⟨n2, A2, hr2⟩ := h2
  have e1 := rep_ext (by omega : n1 ≤ n1 + n2) hr1
  have e2 := rep_ext (by omega : n2 ≤ n1 + n2) hr2
  refine ⟨n1 + n2, fun j ζ => (if j ≤ n1 then A1 j ζ else 0) + (if j ≤ n2 then A2 j ζ else 0),
    fun j => (e1.1 j).add (e2.1 j), fun Φ q hq => ?_⟩
  have hc : ((T1 + T2) Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = (T1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) + (T2 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := rfl
  rw [hc, Formalism.FourierDecayAlt.P.NFRO.radR_add, e1.2 Φ q hq, e2.2 Φ q hq, ← Finset.sum_add_distrib]
  rfl

theorem radDZ_sum {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (h : ∀ i ∈ s, RadDZ P Bs (T i)) :
    RadDZ P Bs (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using radDZ_zero P Bs
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact radDZ_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem radDZ_comp_left {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T T' : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T)
    (Mf : ℂ → ((Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp)))
    (hM : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Mf (AnnZ P Bs))
    (h : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T' Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        Mf q.2 (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) :
    RadDZ P Bs T' := by
  obtain ⟨n, A, hA, hTA⟩ := hT
  refine ⟨n, fun j ζ => (Mf ζ).comp (A j ζ), fun j => hM.clm_comp (hA j), fun Φ q hq => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h Φ q hq, hTA Φ q hq, map_sum]
  rfl

theorem radDZ_fun_left {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T T' : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) (s : ℂ → ℂ)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s (AnnZ P Bs))
    (h : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T' Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        s q.2 • NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q) :
    RadDZ P Bs T' :=
  radDZ_comp_left hT (fun ζ => s ζ • ContinuousLinearMap.id ℝ (Wq →L[ℂ] Wp)) (hs.smul contDiffOn_const)
    fun Φ q hq => by rw [h Φ q hq]; rfl

theorem radDZ_smul {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) (c : ℂ) :
    RadDZ P Bs (c • T) :=
  radDZ_fun_left hT (fun _ => c) contDiffOn_const fun Φ q _ => by
    have : ((c • T) Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = c • (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := rfl
    rw [this, radR_smul']

theorem radDZ_neg {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) : RadDZ P Bs (-T) := by
  have := radDZ_smul hT (-1)
  rwa [neg_one_smul] at this

end closure

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

open Formalism.FourierDecayAlt.ThreeDimData

section Basic

variable {k r : ℕ}

theorem psi_norm (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1 := by
  simp [Formalism.QuantumDeterminants.psi, Complex.norm_exp]

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous (fun g : Mx k r => Formalism.QuantumDeterminants.psi k r z c g) := by
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul ?_))))
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [dif_pos h]
    fun_prop
  · simp only [dif_neg h, Matrix.mulVec, dotProduct]
    fun_prop

theorem isClosed_UH : IsClosed (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) : Set (Mx k r)) := by
  show IsClosed {g : Mx k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem isClosed_UW (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (Formalism.QuantumDeterminants.UWset k r z : Set (Mx k r)) := by
  have h1 : IsClosed {g : Mx k r | g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := isClosed_UH
  have h2 : IsClosed {g : Mx k r | ∀ a : Fin r, g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) ∧ g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)} := by
    simp only [Set.setOf_forall, Set.setOf_and]
    exact isClosed_iInter fun a =>
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  have h3 : IsClosed {g : Mx k r | g *ᵥ z = z} :=
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  exact h1.inter (h2.inter h3)

theorem aesm_of_contOn {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] [NormedAddCommGroup E] [SecondCountableTopology E]
    {μ : Measure α} {f : α → E} {s : Set α} (hf : ContinuousOn f s) (hs : MeasurableSet s)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) : AEStronglyMeasurable f μ := by
  have h := hf.aestronglyMeasurable hs (μ := μ)
  rwa [Measure.restrict_eq_self_of_ae_mem hμ] at h

theorem key_bound {A S X Y a : ℝ} (hA : 1 ≤ A) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hS0 : 0 < S) (ha : 0 < a)
    (hS : S ≤ A * X * Y) : Y ^ (-a) * A ^ (-a) ≤ X ^ (a / 2) * (Y ^ (-(a / 2)) * S ^ (-(a / 2))) := by
  have hA0 : 0 < A := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have y1 : 0 < Y ^ (-a) := Real.rpow_pos_of_pos hY0 _
  have a1 : 0 < A ^ (-a) := Real.rpow_pos_of_pos hA0 _
  have x2 : 0 < X ^ (a / 2) := Real.rpow_pos_of_pos hX0 _
  have y2 : 0 < Y ^ (-(a / 2)) := Real.rpow_pos_of_pos hY0 _
  have s2 : 0 < S ^ (-(a / 2)) := Real.rpow_pos_of_pos hS0 _
  have h1 : Real.log S ≤ Real.log A + Real.log X + Real.log Y := by
    have e1 : Real.log (A * X * Y) = Real.log A + Real.log X + Real.log Y := by
      rw [Real.log_mul (mul_pos hA0 hX0).ne' hY0.ne', Real.log_mul hA0.ne' hX0.ne']
    rw [← e1]
    exact Real.log_le_log hS0 hS
  have h2 : 0 ≤ Real.log A := Real.log_nonneg hA
  rw [← Real.log_le_log_iff (mul_pos y1 a1) (mul_pos x2 (mul_pos y2 s2)),
    Real.log_mul y1.ne' a1.ne', Real.log_mul x2.ne' (mul_pos y2 s2).ne', Real.log_mul y2.ne' s2.ne',
    Real.log_rpow hY0, Real.log_rpow hA0, Real.log_rpow hX0, Real.log_rpow hY0, Real.log_rpow hS0]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le, mul_nonneg ha.le h2]

end Basic

section Repro

end Repro

end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
end
end

