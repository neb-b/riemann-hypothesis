module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSectionAcrisBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.SecUHolds
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem secU_holds : CoreU → SecU := by
  intro hU l _ K bk N
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.AcrisPow.main l K bk (2 * N + 1) 1
  refine ⟨n₀ + 2 * N * n₀, fun d A A' hA => ?_⟩
  set ψ : bk.S →+* Per.Acris l := (algebraMap (Ainf l) (Per.Acris l)).comp bk.ev with hψ
  obtain ⟨htor, hcomp, ⟨v, hv⟩, hφ, -⟩ := GlobalTheory.AcrisFrobE.main l K bk
  have hφψ : ∀ s, phiA l (ψ s) = ψ (frobS l bk.a s) := fun s => by
    simp only [hψ, RingHom.comp_apply, hφ, bk.ev_frob]
  have hu : phiA l (ψ X) = ψ X ^ l := by rw [hφψ, frobS_X, map_pow]
  have hdiff : ∀ s : bk.S, ∃ t : Per.Acris l,
      ψ (frobS l bk.a s) - ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff s))) = ψ X ^ l * t := by
    intro s
    obtain ⟨t, ht⟩ := (PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)
    refine ⟨ψ (frobS l bk.a t), ?_⟩
    rw [← map_sub, ← map_sub, ht, map_mul, frobS_X, map_mul, map_pow]
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE0 : PowerSeries.constantCoeff bk.E = bk.Ep.coeff 0 := by simp
  set w0 : Per.Acris l := ψ (frobS l bk.a (PowerSeries.C (w : Wq l bk.a))) with hw0def
  have hw0u : IsUnit w0 := ((w.isUnit.map PowerSeries.C).map (frobS l bk.a)).map ψ
  have hP0 : ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) = (l : Per.Acris l) * w0 := by
    rw [hE0, hw, map_mul, map_natCast, map_mul, map_natCast, map_mul, map_natCast]
  set u : Per.Acris l := ψ X with hudef
  set P : Per.Acris l := ψ (frobS l bk.a bk.E) with hPdef
  set a : Per.Acris l := ((v⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hadef
  set b : Per.Acris l := ((hw0u.unit⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hbdef
  have hav : a * v = 1 := Units.inv_mul v
  have hbw : b * w0 = 1 := by rw [hbdef]; exact hw0u.val_inv_mul
  set fB : bk.S →+* Per.Acris l := ψ.comp (frobS l bk.a) with hfB
  set fB0 : bk.S →+* Per.Acris l := fB.comp (PowerSeries.C.comp PowerSeries.constantCoeff) with hfB0
  have hmap : ∀ f : bk.S →+* Per.Acris l, (A.map f) * (A'.map f) = (f bk.E) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    intro f
    rw [← Matrix.map_mul, hA]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hfE : fB bk.E = (l : Per.Acris l) * v := hv
  have hfE0 : fB0 bk.E = (l : Per.Acris l) * w0 := hP0
  have hcoef : ∀ (c y : Per.Acris l), c * y = 1 → c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) := by
    intro c y h
    calc c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) * (c * y) ^ (2 * N) := by ring
      _ = _ := by rw [h, one_pow, mul_one]
  have hα : (a ^ N • A.map fB) * (a ^ N • A'.map fB) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE, smul_smul, smul_smul, hcoef a v hav]
  have hβ : (b ^ N • A.map fB0) * (b ^ N • A'.map fB0) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE0, smul_smul, smul_smul, hcoef b w0 hbw]
  choose G hG using fun i j => hdiff (A i j)
  obtain ⟨z, hz⟩ := hdiff bk.E
  obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow w0 v N
  have hΓ : (l : Per.Acris l) • (a ^ N • A.map fB - b ^ N • A.map fB0) =
      u ^ l • ((((l : Per.Acris l) * a ^ N) • Matrix.of G) + (-(a ^ N * b ^ N * z * t)) • A.map fB0) := by
    ext i j
    have h1 : fB (A i j) - fB0 (A i j) = u ^ l * G i j := hG i j
    have h2 : (l : Per.Acris l) * v - (l : Per.Acris l) * w0 = u ^ l * z := by rw [← hfE, ← hfE0]; exact hz
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
      smul_eq_mul]
    have h4 : (a * v) ^ N = 1 := by rw [hav, one_pow]
    have h5 : (b * w0) ^ N = 1 := by rw [hbw, one_pow]
    linear_combination ((l : Per.Acris l) * a ^ N) * h1 + (-(a ^ N * b ^ N * t * fB0 (A i j))) * h2 +
      ((l : Per.Acris l) * a ^ N * b ^ N * fB0 (A i j)) * ht + ((l : Per.Acris l) * fB0 (A i j) * b ^ N) * h4 +
      (-((l : Per.Acris l) * fB0 (A i j) * a ^ N)) * h5
  obtain ⟨Q, Q', hQQ, ⟨Y, hY⟩, ⟨Y', hY'⟩, hQ⟩ := hU (Per.Acris l) d l l N htor hcomp (phiA l) u hu
    (Fact.out : l.Prime).pos _ _ _ _ _ hα hβ hΓ n₀ (fun n hn => hn₀ (n + 1) (by omega))
  refine ⟨Q, Q', ⟨hQQ, fun i j => ⟨Y i j, ?_⟩, fun i j => ⟨Y' i j, ?_⟩, ?_⟩⟩
  · rw [hY]; rfl
  · rw [hY']; rfl
  · have key : b ^ N • (Q * A.map fB0) = a ^ N • (A.map fB * Q.map (phiA l)) := by
      rw [← mul_smul_comm, hQ, smul_mul_assoc]
    have e1 : P ^ N = (P ^ N * w0 ^ N) * b ^ N := by
      rw [mul_assoc, ← mul_pow, mul_comm w0 b, hbw, one_pow, mul_one]
    have e2 : (P ^ N * w0 ^ N) * a ^ N = ((l : Per.Acris l) * w0) ^ N := by
      rw [hv]
      calc ((l : Per.Acris l) * v) ^ N * w0 ^ N * a ^ N = ((l : Per.Acris l) * w0) ^ N * (a * v) ^ N := by ring
        _ = _ := by rw [hav, one_pow, mul_one]
    show P ^ N • (Q * A.map fB0) =
      ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) ^ N • (A.map fB * Q.map (phiA l))
    rw [hP0, e1, ← smul_smul, key, smul_smul, e2]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrIdHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trId_holds :
    TrId := by
  intro l _ B _ u zb hz s d d' m t t' c pv p θ Pi e e' V V' h1 h2 lam
  have hscal : ∀ (z : ℤ_[l]) (x : Om l), u (lam (zOm l z * x)) = zb z * u (lam x) := by
    intro z x
    have hx : zOm l z * x = (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) • x := by
      rw [Algebra.smul_def]
      rfl
    rw [hx, map_smul, smul_eq_mul, map_mul, hz]
  have hk : ∀ k, ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (c k * t' j k)) = s * u (lam (c k * pv k)) := by
    intro k
    simpa using h2 k (lam ∘ₗ LinearMap.mulLeft ↥(MaximalUnramifiedExtension l) (c k))
  have hE : (fun i => zb ((Pi *ᵥ e' - e) i)) = Pi.map zb *ᵥ (fun j => zb (e' j)) - fun i => zb (e i) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have hX : (V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ (fun i => zb ((Pi *ᵥ e' - e) i)) =
      V *ᵥ (fun i => zb (e i)) - Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j)) := by
    rw [hE, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    abel
  have hA := h1 lam
  have hS1 : ∑ i, ((V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ fun i => zb ((Pi *ᵥ e' - e) i)) i * u (lam (t i)) =
      s * u (lam p) - ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
    rw [hX, ← hA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [_root_.Pi.sub_apply]
    ring
  have hS2 : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k)) =
      ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) - ∑ k, s * u (lam (c k * pv k)) := by
    have ha : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ i, zb (Pi i j) * u (lam (t i)) =
        ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
      generalize (V' *ᵥ fun i => zb (e' i)) = w
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hb : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ k, u (lam (c k * t' j k)) = ∑ k, s * u (lam (c k * pv k)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => hk k
    rw [← ha, ← hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, hscal, mul_sub]
  have hS3 : s * u (lam (θ - ∑ k, c k * pv k)) = s * u (lam θ) - ∑ k, s * u (lam (c k * pv k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, mul_sub, Finset.mul_sum]
  rw [hS1, hS2, hS3, map_sub, map_sub, mul_sub]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrLimHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLim_holds :
    TrStep → TrLim := by
  intro hstep l _ P AI T K bk Γ _ _ L₀ a r Cl Cv s V V' p θ pv hs hV hV' hlink hθ
  by_contra hne
  have hpθ : p - θ ≠ 0 := sub_ne_zero.mpr hne
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hlnorm : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h := PadicAlgCl.norm_extends l ((l : ℚ_[l]))
    rw [Padic.norm_p] at h
    simpa using h
  have hnp : ∀ (c : ℕ) (x : Om l), ‖(l : Om l) ^ c * x‖ = ((l : ℝ) ^ c)⁻¹ * ‖x‖ := by
    intro c x
    rw [norm_mul, norm_pow, hlnorm, inv_pow]
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt (‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖) hl1
  have hsmall : ∀ x : Om l, ‖x‖ ≤ ‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖ → ‖(l : Om l) ^ c₁ * x‖ ≤ 1 := by
    intro x hx
    rw [hnp, inv_mul_le_iff₀ (pow_pos hl0 c₁), mul_one]
    exact hx.trans hc₁.le
  have hsum0 : 0 ≤ ∑ i, ‖(Cv.b i).trace‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have ht : ∀ i, ‖(l : Om l) ^ c₁ * (Cv.b i).trace‖ ≤ 1 := fun i =>
    hsmall _ (((Finset.single_le_sum (f := fun i => ‖(Cv.b i).trace‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))).trans
      (le_add_of_nonneg_left (norm_nonneg _)))
  have hd : ‖(l : Om l) ^ c₁ * (p - θ)‖ ≤ 1 := hsmall _ (le_add_of_nonneg_right hsum0)
  have hpos : 0 < ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [hnp]
    exact mul_pos (inv_pos.mpr (pow_pos hl0 c₁)) (norm_pos_iff.mpr hpθ)
  obtain ⟨c₂, hc₂⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  have hc₂' : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [← inv_pow]
    exact hc₂.le
  have hdvd : ∀ M : ℕ, (l : Per.Acris l) ^ M ∣ (l : Per.Acris l) ^ c₂ * s := by
    intro M
    obtain ⟨m, hMm, hm⟩ := hlink M
    have hle : ((l : ℝ) ^ m)⁻¹ ≤ ((l : ℝ) ^ M)⁻¹ :=
      inv_anti₀ (pow_pos hl0 M) (pow_le_pow_right₀ hl1.le hMm)
    refine hstep l P AI T s Cv.d (Cv.tw.d' m) (Cv.lay m).m M c₁ c₂ (fun i => (Cv.b i).trace)
      (fun j k => ((Cv.lay m).b j k).trace) (Cv.lay m).c (pv m) p θ (Cv.tw.Pi m) Cv.e (Cv.lay m).e V (V' m)
      hV (hV' m) hm (fun i => (pow_dvd_pow _ hMm).trans (Cv.unit m i)) (fun j => ?_) ((hθ m).trans hle) ht hd hc₂'
    have h := Cv.trace m j
    rw [Matrix.trace_sum] at h
    simp only [Matrix.trace_smul, smul_eq_mul] at h
    exact h.trans hle
  obtain ⟨htor, hcomp, -⟩ := _root_.GlobalTheory.AcrisFrobE.main l K bk
  have hz := GlobalTheory.CrZero.eq_zero_of_forall_dvd _ hcomp.toIsHausdorff _ hdvd
  have hs0 : s = 0 := GlobalTheory.CrZero.pow_cancel (l : Per.Acris l) htor c₂ s 0 (by simpa using hz)
  haveI : Nontrivial P.R.B := GlobalTheory.Pst.nontrivial_B P
  haveI : Nontrivial (Per.Bcris l) := T.eB.injective.nontrivial
  rw [hs0, map_zero] at hs
  exact not_isUnit_zero hs
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrLinHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLin_holds :
    TrLin := by
  intro k B W J _ _ _ _ _ _ a ha κ ψ hψ T x w h
  classical
  let bW : Module.Basis (Fin a) k W := Module.finBasisOfFinrankEq k W ha
  have hexp : ∀ (y : W) (i : Fin a), ψ y i = ∑ m, κ (bW.repr y m) * ψ (bW m) i := by
    intro y i
    conv_lhs => rw [← bW.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hψ, Pi.smul_apply, smul_eq_mul]
  let X : Matrix (Fin a) (Fin a) B := Matrix.of fun i m => ψ (bW m) i
  let X' : Matrix (Fin a) (Fin a) B := Matrix.of fun m i' => ∑ j, w j * κ (bW.repr (x j i') m)
  have hXX : X * X' = 1 := by
    ext i i'
    rw [Matrix.mul_apply, Matrix.one_apply, ← h i i']
    simp only [X, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hexp (x j i') i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hXX' : X' * X = 1 := mul_eq_one_comm.mp hXX
  let Tm : Matrix (Fin a) (Fin a) B := (LinearMap.toMatrix bW bW T).map κ
  have hrepr : ∀ (y : W) (m : Fin a),
      bW.repr (T y) m = ∑ m', LinearMap.toMatrix bW bW T m m' * bW.repr y m' := by
    intro y m
    rw [← LinearMap.toMatrix_mulVec_repr bW bW T y]
    rfl
  have hentry : ∀ i i', ∑ j, w j * ψ (T (x j i')) i = (X * Tm * X') i i' := by
    intro i i'
    have hTX : ∀ y : W, ψ (T y) i = ∑ m, (X * Tm) i m * κ (bW.repr y m) := by
      intro y
      rw [hexp (T y) i]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hrepr, map_sum, map_mul, Matrix.mul_apply, X, Tm, Matrix.of_apply,
        Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
    rw [Matrix.mul_apply]
    simp only [hTX, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring
  have htr : Matrix.trace Tm = κ (LinearMap.trace k W T) := by
    rw [LinearMap.trace_eq_matrix_trace k bW T]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, Tm, map_sum]
  calc ∑ i, ∑ j, w j * ψ (T (x j i)) i = Matrix.trace (X * Tm * X') := by
        simp only [Matrix.trace, Matrix.diag_apply, hentry]
    _ = Matrix.trace (X' * X * Tm) := by
        rw [Matrix.trace_mul_cycle]
    _ = κ (LinearMap.trace k W T) := by
        rw [hXX', one_mul, htr]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrStep
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem core {Z R B : Type} [CommRing Z] [CommRing R] [CommRing B] (f : R →+* B) (zc : Z →+* R) (zb : Z →+* B)
    (hz : ∀ x, f (zc x) = zb x) (n a s g : R) (nZ : Z) (hn : zc nZ = n) {d d' : ℕ}
    (V : Matrix (Fin d) (Fin d) R) (V' : Matrix (Fin d') (Fin d') R) (Pm : Matrix (Fin d) (Fin d') Z)
    (e : Fin d → Z) (e' : Fin d' → Z) (h3 : ∀ i j, n ∣ (V * Pm.map zc - Pm.map zc * V') i j)
    (h4 : ∀ i, nZ ∣ (Pm *ᵥ e' - e) i) (ui : Fin d → B) (vj : Fin d' → B) (w : B) (ai : Fin d → R) (bj : Fin d' → R)
    (ha : ∀ i, f (ai i) = f a * ui i) (hv : ∀ j, vj j = f n * f (bj j)) (hw : w = f n * f g) :
    ∃ Y : R, f a * (∑ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i * ui i +
      ∑ j, (V'.map f *ᵥ fun i => zb (e' i)) j * vj j - f s * w) = f (n * Y) := by
  choose W hW using h3
  choose r hr using h4
  have hPb : Pm.map zb = (Pm.map zc).map f := by
    ext i j; simp [hz]
  have hE : (fun j => zb (e' j)) = f ∘ (fun j => zc (e' j)) := by
    ext j; simp [hz]
  have hD : V * Pm.map zc - Pm.map zc * V' = n • Matrix.of W := by
    ext i j; simp [hW]
  have hM : V.map f * Pm.map zb - Pm.map zb * V'.map f = (n • Matrix.of W).map f := by
    rw [← hD, hPb, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul]
  have hq : (fun i => zb ((Pm *ᵥ e' - e) i)) = f ∘ (fun i => n * zc (r i)) := by
    ext i; simp only [Function.comp, hr i, map_mul, hz, ← hn]
  have h1 : ∀ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i =
      f n * f ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) := by
    intro i
    rw [hM, hE, hq, Pi.sub_apply, ← RingHom.map_mulVec, ← RingHom.map_mulVec, ← map_mul, ← map_sub]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum, mul_sub]
    congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∀ j, (V'.map f *ᵥ fun i => zb (e' i)) j = f ((V' *ᵥ fun i => zc (e' i)) j) := by
    intro j; rw [hE, ← RingHom.map_mulVec]
  refine ⟨∑ i, ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) * ai i +
    ∑ j, a * (V' *ᵥ fun i => zc (e' i)) j * bj j - a * s * g, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h1, h2, hv, hw, map_mul, map_add (f := _), map_sub, map_sum, ha, Finset.mul_sum, mul_add, mul_sub]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

variable {l : ℕ} [Fact l.Prime]

private theorem u_alg {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l]) :
    uB T (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z := by
  show T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l]))) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact T.zB z

private theorem iB_zC (z : ℤ_[l]) : iB l (zC l z) = Per.zB l z := rfl

private theorem exists_iB {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (c : ↥(MaximalUnramifiedExtension l))
    (hc : ‖(c : Om l)‖ ≤ 1) : ∃ y : Per.Acris l, iB l y = uB T c := by
  obtain ⟨w, hw⟩ := GlobalTheory.ExpImage.exists_lifts_of_norm_le_one l P AI T (adjExt (c : Om l)) ⟨c, mem_adjExt _, c.2⟩ hc
  refine ⟨iA l w, ?_⟩
  have h : AI.ιA w = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c := hw
  show _ = T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c)
  rw [← h, T.ιA]
  rfl

private theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  rw [← h]
  congr 1

private theorem scale {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (lam : Om l →ₗ[↥(MaximalUnramifiedExtension l)] ↥(MaximalUnramifiedExtension l)) (n : ℕ) (y : Om l) :
    uB T (lam ((n : Om l) * y)) = (n : Per.Bcris l) * uB T (lam y) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trStep_holds :
    Func → TrId → TrStep := by
  intro hF hI l _ P AI T s d d' m M c₁ c₂ t t' c pv p θ Pi e e' V V' h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := norm_l
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl0 : (l : Om l) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact (inv_pos.2 hlpos).ne hn
  have hlK : (l : ↥(MaximalUnramifiedExtension l)) ≠ 0 := by
    intro h0
    apply hl0
    have := congrArg (fun x : ↥(MaximalUnramifiedExtension l) => (x : Om l)) h0
    simpa using this
  have hsmall : ∀ y : Om l, ‖y‖ ≤ ((l : ℝ) ^ M)⁻¹ → ‖y / (l : Om l) ^ M‖ ≤ 1 := by
    intro y hy
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ (by simpa using hy) (by positivity) |>.trans le_rfl
  let δ : Fin d' → Om l := fun j => ∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k
  let η : Om l := θ - ∑ k, c k * pv k
  let x : Fin d ⊕ Fin d' ⊕ Unit → Om l := Sum.elim (fun i => (l : Om l) ^ c₁ * t i)
    (Sum.elim (fun j => δ j / (l : Om l) ^ M) (fun _ => η / (l : Om l) ^ M))
  have hx : ∀ i, ‖x i‖ ≤ 1 := by
    rintro (i | j | _)
    · exact h7 i
    · exact hsmall _ (h5 j)
    · exact hsmall _ h6
  obtain ⟨lam, hl1, hl2, hl3⟩ := hF l (MaximalUnramifiedExtension l) (Fin d ⊕ Fin d' ⊕ Unit) x ((l : Om l) ^ c₁ * (p - θ)) hx h8
  have hid := hI l (Per.Bcris l) (uB T) (Per.zB l) (u_alg T) (iB l s) d d' m t t' c pv p θ Pi e e'
    (V.map (iB l)) (V'.map (iB l)) h1 h2 lam
  choose ai hai using fun i => exists_iB T (lam (x (Sum.inl i))) (hl1 _)
  choose bj hbj using fun j => exists_iB T (lam (x (Sum.inr (Sum.inl j)))) (hl1 _)
  obtain ⟨g, hg⟩ := exists_iB T (lam (x (Sum.inr (Sum.inr ())))) (hl1 _)
  have hpow : ∀ (k : ℕ) (y : Om l), uB T (lam ((l : Om l) ^ k * y)) = (l : Per.Bcris l) ^ k * uB T (lam y) := by
    intro k y
    have := scale T lam (l ^ k) y
    push_cast at this
    exact this
  have hdiv : ∀ y : Om l, uB T (lam y) = (l : Per.Bcris l) ^ M * uB T (lam (y / (l : Om l) ^ M)) := by
    intro y
    rw [← hpow, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨Y, hY⟩ := core (iB l) (zC l) (Per.zB l) iB_zC ((l : Per.Acris l) ^ M) ((l : Per.Acris l) ^ c₁) s g
    ((l : ℤ_[l]) ^ M) (by simp) V V' Pi e e' h3 h4
    (fun i => uB T (lam (t i))) (fun j => uB T (lam (δ j))) (uB T (lam η)) ai bj
    (fun i => by
      rw [hai i]
      simp only [map_pow, map_natCast]
      exact hpow c₁ (t i))
    (fun j => by
      rw [hbj j]
      simp only [map_pow, map_natCast]
      exact hdiv (δ j))
    (by
      rw [hg]
      simp only [map_pow, map_natCast]
      exact hdiv η)
  rw [← hid] at hY
  set q : ↥(MaximalUnramifiedExtension l) := lam ((l : Om l) ^ c₁ * (p - θ)) with hq
  have huq : uB T q = (l : Per.Bcris l) ^ c₁ * uB T (lam (p - θ)) := hpow c₁ (p - θ)
  have hqn : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(q : Om l)‖ := h9.trans hl2
  have hq0 : q ≠ 0 := by
    intro h0
    have h00 : (0 : ℝ) < ((l : ℝ) ^ c₂)⁻¹ := by positivity
    rw [h0, ZeroMemClass.coe_zero, norm_zero] at hqn
    exact absurd hqn (not_le.2 h00)
  have hq' : ‖(((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q : ↥(MaximalUnramifiedExtension l)) : Om l)‖ ≤ 1 := by
    push_cast
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ hqn (norm_nonneg _)
  obtain ⟨y', hy'⟩ := exists_iB T _ hq'
  refine ⟨Y * y', GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l ?_⟩
  have hqq : q * ((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q) = (l : ↥(MaximalUnramifiedExtension l)) ^ c₂ := mul_div_cancel₀ _ hq0
  have hu : uB T q * iB l y' = (l : Per.Bcris l) ^ c₂ := by
    rw [hy', ← map_mul, hqq, map_pow, map_natCast]
  show iB l _ = iB l _
  rw [← mul_assoc, map_mul (iB l) _ y', ← hY]
  simp only [map_mul, map_pow, map_natCast]
  rw [← hu, huq]
  ring
end

