module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLaw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

open GlobalTheory.KerWt

theorem applyAt0_const_mul (D : D7) {N N' : ℕ} (P : MvPolynomial (GL3Theta.Idx D N N') ℂ) (k : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (hG : Differentiable ℂ G) : GL3Theta.applyAt0 D P (fun z => k * G z) = k * GL3Theta.applyAt0 D P G := by
  exact (GlobalTheory.NormSum.applyAt0_minorPol_linear D N N' (fun _ => 0) G hG).2.2.1 k P

theorem applyAt0_polD_eigen (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' γ : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (k : ℂ) (hγ : ∀ τ, (γ τ).det ≠ 0)
    (hG : Differentiable ℂ G) (hk : ∀ z : TaylorLogMetric.VC D N N', G (fun τ => (γ τ * Matrix.of (z τ) : Matrix _ _ ℂ)) = k * G z) :
    GL3Theta.applyAt0 D (GL3Theta.polD D s Q (fun τ => γ τ * y' τ)) G = k * GL3Theta.applyAt0 D (GL3Theta.polD D s Q y') G := by
  have h := GlobalTheory.ClassSumEquiv.applyAt0_polD_equivariant D N N' s Q y' γ (fun _ => 1) (fun z => k * G z) hγ (hG.const_mul k)
  have e1 : (fun z : TaylorLogMetric.VC D N N' => k * G (fun τ => ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N') (Fin N) ℂ))) = G := by
    funext z
    refine (hk _).symm.trans (congrArg G (funext fun τ => ?_))
    have : (γ τ * ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ)) : Matrix (Fin N') (Fin N) ℂ) = Matrix.of (z τ) := by
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ (hγ τ).isUnit]
    exact this
  have e2 : (MvPolynomial.aeval (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) Q) = Q := by
    have : (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) = MvPolynomial.X := by
      funext k
      rw [Finset.sum_eq_single k.2.1]
      · simp
      · intro b _ hb
        simp [Matrix.one_apply_ne hb.symm]
      · simp
    rw [this, MvPolynomial.aeval_X_left_apply]
  beta_reduce at h
  rw [e1, e2, applyAt0_const_mul D _ k G hG] at h
  exact h

theorem lawAt_Kmap : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)), Differentiable ℂ (O.Th i c c') → ∀ g, TermLaw O i c c' g → ∀ f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → LawAt O (i + 1) g (C.Kmap i c c' f) := by
  intro D u C A Pm M O i hi h c c' hd g ⟨hdet, k, hk, hg⟩ f ⟨P, hP, hf⟩ y y' hy
  obtain ⟨n, hw, hn, -, -⟩ := _root_.GlobalTheory.KerWtStep.trueWt_step D u C A Pm M i hi
  have hs : C.sharp i f = frPoly O i (MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ) := by
    have h1 := mulFun_evG (fr := O.frm i) (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) (RingHom.id ℂ) _ (C.sSharp i) n hn P
    have e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
      funext y; simp only [O.frm_de i hi.le]
    rw [e1] at h1
    rw [hf]
    exact h1
  have hQ : MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ ∈ WtPol ℂ (nuT D u i) := by
    have h2 := vv_in_weight ℂ D.what₂.Tau _ (lamTG M i) n (MvPolynomial.map (RingHom.id ℂ) P) (map_mem_VV _ _ P hP)
    have e : (fun τ r => (lamTG M i τ).natW r + n τ) = nuT D u i := by funext τ r; exact hw τ r
    rwa [e] at h2
  generalize MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ = Q at hs hQ
  have hu : ∀ x : C.Y (i + 1), C.unf i c c' (C.sharp i f) x =
      GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c') := fun x => by
    rw [hs]
    exact (unfolding_iff_alt D u C O i hi.le _).1 h c c' Q hQ x
  have hK : ∀ x : C.Y (i + 1), C.Kmap i c c' f x = (C.rhoDet i c * C.rhoDet' i c') *
      ((∏ τ, (O.frm (i + 1) x τ).det ^ C.sDiv i τ)⁻¹ *
        GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c')) := fun x => by
    rw [← hu x]
    simp only [← O.frm_de (i + 1) hi]
    rfl
  have hdm : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det = TaylorLogMetric.embT D τ g.1.det := fun τ => ((TaylorLogMetric.embT D τ).map_det g.1).symm
  have hne : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det ≠ 0 := fun τ => by
    rw [hdm]; exact (map_ne_zero _).2 hdet
  have hy' : O.frm (i + 1) y = fun τ => g.1.map (TaylorLogMetric.embT D τ) * O.frm (i + 1) y' τ := funext hy
  rw [hK, hK, hy', applyAt0_polD_eigen D _ _ _ Q _ _ _ k hne hd hk, hg]
  simp only [Matrix.det_mul, hdm, mul_zpow, Finset.prod_mul_distrib, zpow_neg, Finset.prod_inv_distrib, mul_inv]
  ring

end GlobalTheory.KerJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomain
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.InvRatFun

variable {F : Type} [Field F]

noncomputable def shift (s : F ≃+* F) (t : F) : F[X] →+* F[X] :=
  (Polynomial.compRingHom (X + C t)).comp (Polynomial.mapRingHom (s : F →+* F))

theorem shift_apply (s : F ≃+* F) (t : F) (r : F[X]) :
    shift s t r = (r.map (s : F →+* F)).comp (X + C t) := rfl

theorem natDegree_shift (s : F ≃+* F) (t : F) (r : F[X]) :
    (shift s t r).natDegree = r.natDegree := by
  rw [shift_apply, natDegree_comp, natDegree_X_add_C, mul_one, natDegree_map]

theorem leadingCoeff_shift (s : F ≃+* F) (t : F) (r : F[X]) :
    (shift s t r).leadingCoeff = s r.leadingCoeff := by
  rw [shift_apply, leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero),
    leadingCoeff_X_add_C, one_pow, mul_one, leadingCoeff_map]
  rfl

theorem shift_eq_zero_iff (s : F ≃+* F) (t : F) (r : F[X]) : shift s t r = 0 ↔ r = 0 := by
  rw [← leadingCoeff_eq_zero, leadingCoeff_shift, map_eq_zero_iff _ s.injective,
    leadingCoeff_eq_zero]

theorem coeff_comp_X_add_C_sub' (P : F[X]) (r : F) (e : ℕ) (hP : P.degree ≤ (e + 1 : ℕ)) :
    (P.comp (X + C r) - P).coeff e = r * (e + 1) * P.coeff (e + 1) := by
  have h1 : P.natDegree ≤ e + 1 := natDegree_le_of_degree_le hP
  have h2 : (hasseDeriv e P).natDegree ≤ 1 := (natDegree_hasseDeriv_le P e).trans (by omega)
  rw [coeff_sub, ← taylor_apply, taylor_coeff, eq_X_add_C_of_natDegree_le_one h2,
    hasseDeriv_coeff, hasseDeriv_coeff]
  simp [add_comm 1 e]
  ring

variable [CharZero F]

theorem natDegree_eq_zero_of_fixed {ι : Type} (s : ι → F ≃+* F) (t : ι → F)
    (h : ¬ ∃ f : F, ∀ g, s g f - f = t g) (r : F[X]) (hr : r ≠ 0)
    (hfix : ∀ g, shift (s g) (t g) r = r) : r.natDegree = 0 := by
  by_contra hn
  obtain ⟨e, he⟩ : ∃ e, r.natDegree = e + 1 := ⟨r.natDegree - 1, by omega⟩
  set c := r.leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hr
  have hsc : ∀ g, s g c = c := fun g => by
    rw [hc, ← leadingCoeff_shift (s g) (t g), hfix g]
  apply h
  refine ⟨-r.coeff e / ((e + 1 : F) * c), fun g => ?_⟩
  have key : (shift (s g) (t g) r).coeff e = r.coeff e := by rw [hfix g]
  have hdeg : (r.map (s g : F →+* F)).degree ≤ (e + 1 : ℕ) := by
    rw [degree_map]; exact (degree_le_natDegree).trans (by rw [he])
  have hsub := coeff_comp_X_add_C_sub' (r.map (s g : F →+* F)) (t g) e hdeg
  rw [coeff_sub, ← shift_apply, key, coeff_map, coeff_map] at hsub
  have hlc : r.coeff (e + 1) = c := by rw [hc, leadingCoeff, he]
  rw [hlc] at hsub
  change _ - s g (r.coeff e) = t g * (e + 1) * s g c at hsub
  rw [hsc g] at hsub
  have he1 : (e + 1 : F) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
  rw [map_div₀, map_neg, map_mul, hsc g, map_add (f := _), map_natCast, map_one]
  field_simp
  linear_combination hsub

end GlobalTheory.InvRatFun

namespace GlobalTheory.InvRatFun

variable {F : Type} [Field F] [CharZero F]

theorem dvd_shift_mul {s : F ≃+* F} {t : F} {P Q r : F[X]} (hQ : Q ≠ 0)
    (hPQ : Q * shift s t P = shift s t Q * P) (hr : Q ∣ r * P) : Q ∣ shift s t r * P := by
  obtain ⟨w, hw⟩ := map_dvd (shift s t) hr
  rw [map_mul] at hw
  have hAQ : shift s t Q ≠ 0 := (shift_eq_zero_iff s t Q).not.mpr hQ
  refine ⟨w, ?_⟩
  apply mul_left_cancel₀ hAQ
  linear_combination (-(shift s t r)) * hPQ + Q * hw

theorem eq_C_mul_of_fixed {ι : Type} (s : ι → F ≃+* F) (t : ι → F)
    (h : ¬ ∃ f : F, ∀ g, s g f - f = t g) (P Q : F[X]) (hQ : Q ≠ 0)
    (hPQ : ∀ g, Q * shift (s g) (t g) P = shift (s g) (t g) Q * P) :
    ∃ c : F, P = C c * Q ∧ ∀ g, s g c = c := by
  classical
  have hex : ∃ n, ∃ r : F[X], r.Monic ∧ r.natDegree = n ∧ Q ∣ r * P :=
    ⟨_, Q * C Q.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hQ, rfl,
      ⟨C Q.leadingCoeff⁻¹ * P, by ring⟩⟩
  obtain ⟨q₀, hm, hdeg, hdvd⟩ := Nat.find_spec hex
  have hfix : ∀ g, shift (s g) (t g) q₀ = q₀ := by
    intro g
    set A := shift (s g) (t g)
    have hAm : (A q₀).Monic := by rw [shift_apply]; exact (hm.map _).comp_X_add_C _
    by_contra hne
    have hr : A q₀ - q₀ ≠ 0 := sub_ne_zero.mpr hne
    have hlt : (A q₀ - q₀).degree < (A q₀).degree :=
      degree_sub_lt (by rw [degree_eq_natDegree hAm.ne_zero, degree_eq_natDegree hm.ne_zero,
        natDegree_shift]) hAm.ne_zero (by rw [hAm.leadingCoeff, hm.leadingCoeff])
    have hlt' : (A q₀ - q₀).natDegree < Nat.find hex := by
      rw [← hdeg, ← natDegree_shift (s g) (t g) q₀]; exact natDegree_lt_natDegree hr hlt
    have hd : Q ∣ (A q₀ - q₀) * P := by
      rw [sub_mul]; exact dvd_sub (dvd_shift_mul hQ (hPQ g) hdvd) hdvd
    refine Nat.find_min hex hlt' ⟨(A q₀ - q₀) * C (A q₀ - q₀).leadingCoeff⁻¹,
      monic_mul_leadingCoeff_inv hr,
      natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hr)), ?_⟩
    rw [mul_right_comm]; exact dvd_mul_of_dvd_left hd _
  have h0 := natDegree_eq_zero_of_fixed s t h q₀ hm.ne_zero hfix
  have hq1 : q₀ = 1 := by
    have h1 : q₀.coeff 0 = 1 := by rw [← h0]; exact hm
    rw [eq_C_of_natDegree_eq_zero h0, h1, C_1]
  rw [hq1, one_mul] at hdvd
  obtain ⟨S, rfl⟩ := hdvd
  have hSfix : ∀ g, shift (s g) (t g) S = S := by
    intro g
    have hAQ : shift (s g) (t g) Q ≠ 0 := (shift_eq_zero_iff _ _ Q).not.mpr hQ
    have := hPQ g
    rw [map_mul] at this
    apply mul_left_cancel₀ (mul_ne_zero hQ hAQ)
    linear_combination this
  by_cases hS : S = 0
  · exact ⟨0, by simp [hS], fun g => map_zero _⟩
  have hS0 := natDegree_eq_zero_of_fixed s t h S hS hSfix
  refine ⟨S.leadingCoeff, ?_, fun g => ?_⟩
  · conv_lhs => rw [eq_C_of_natDegree_eq_zero hS0]
    rw [leadingCoeff, hS0, mul_comm]
  · rw [← leadingCoeff_shift (s g) (t g), hSfix g]

end GlobalTheory.InvRatFun

namespace GlobalTheory.InvRatFun

theorem fixed_ratio_const_of {B G : Type} (F : Type) [Field F] [CommRing B] [IsDomain B] [CharZero B] [Algebra B F] [IsFractionRing B F]
    (σ : G → B ≃+* B) (τ : G → B)
    (hτ : ∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g)
    (p q : Polynomial B) (hq : q ≠ 0)
    (hpq : ∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) =
      (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) :
    ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' := by
  classical
  have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
  haveI : CharZero F := charZero_of_injective_algebraMap hinj
  have hι0 : ∀ x : B, x ≠ 0 → (algebraMap B F) x ≠ 0 := fun x hx => by
    rwa [Ne, ← map_zero (algebraMap B F), hinj.eq_iff]
  let s : G → F ≃+* F := fun g => IsFractionRing.ringEquivOfRingEquiv (σ g)
  have hs : ∀ g x, s g ((algebraMap B F) x) = (algebraMap B F) (σ g x) := fun g x =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (σ g) x
  have hcomp : ∀ g, (algebraMap B F).comp (σ g : B →+* B) = (s g : F →+* F).comp (algebraMap B F) := fun g =>
    RingHom.ext fun x => (hs g x).symm
  have hmap : ∀ g (r : B[X]), ((r.map (σ g : B →+* B)).comp (X + C (τ g))).map (algebraMap B F) =
      shift (s g) ((algebraMap B F) (τ g)) (r.map (algebraMap B F)) := by
    intro g r
    rw [shift_apply, Polynomial.map_comp, Polynomial.map_map, Polynomial.map_map, hcomp g]
    simp

  have h : ¬ ∃ f : F, ∀ g, s g f - f = (algebraMap B F) (τ g) := by
    rintro ⟨f, hf⟩
    obtain ⟨d', d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) f
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    apply hτ d d' hd0
    intro g
    have e := hf g
    have h1 := hι0 d hd0
    have h2 := hι0 (σ g d) ((map_ne_zero_iff _ (σ g).injective).mpr hd0)
    rw [map_div₀, hs, hs] at e
    apply hinj
    simp only [map_sub, map_mul]
    field_simp at e
    linear_combination e
  have hQ : q.map (algebraMap B F) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hq
  obtain ⟨c, hc, hcs⟩ := eq_C_mul_of_fixed s (fun g => (algebraMap B F) (τ g)) h (p.map (algebraMap B F)) (q.map (algebraMap B F)) hQ
    (fun g => by
      have e := congrArg (Polynomial.map (algebraMap B F)) (hpq g)
      rwa [Polynomial.map_mul, Polynomial.map_mul, hmap, hmap] at e)
  obtain ⟨d', d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) c
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have h1 := hι0 d hd0
  refine ⟨d, d', hd0, ?_, fun g => ?_⟩
  · apply Polynomial.map_injective (algebraMap B F) hinj
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, hc, ← mul_assoc,
      ← C_mul, mul_div_cancel₀ _ h1]
  · have e := hcs g
    have h2 := hι0 (σ g d) ((map_ne_zero_iff _ (σ g).injective).mpr hd0)
    rw [map_div₀, hs, hs] at e
    apply hinj
    simp only [map_mul]
    field_simp at e
    linear_combination e

theorem fixed_ratio_const {B G : Type} [CommRing B] [IsDomain B] [CharZero B]
    (σ : G → B ≃+* B) (τ : G → B)
    (hτ : ∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g)
    (p q : Polynomial B) (hq : q ≠ 0)
    (hpq : ∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) =
      (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) :
    ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' :=
  fixed_ratio_const_of (FractionRing B) σ τ hτ p q hq hpq

end GlobalTheory.InvRatFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValEqExpNegOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLocUnif

theorem val_eq_exp_neg_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (w : Valuation E (WithZero (Multiplicative ℤ)))
    (h1 : ∀ x : 𝓞 E, x ∉ P.asIdeal → w (algebraMap (𝓞 E) E x) = 1)
    (ϖ : 𝓞 E) (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2)
    (hlt : w (algebraMap (𝓞 E) E ϖ) < 1)
    (y : 𝓞 E) (hy : w (algebraMap (𝓞 E) E y) = WithZero.exp (-1 : ℤ)) :
    w (algebraMap (𝓞 E) E ϖ) = WithZero.exp (-1 : ℤ) := by
  have hu : ∀ u : E, P.valuation E u = 1 → w u = 1 := by
    intro u hu
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer u hu.le
    have hd : (d : 𝓞 E) ∉ P.asIdeal := d.2
    have hn : n ∉ P.asIdeal := by
      rw [← P.valuation_eq_one_iff_notMem (K := E), ← hnd, map_mul, hu,
        (P.valuation_eq_one_iff_notMem (K := E)).2 hd, one_mul]
    have := h1 n hn
    rwa [← hnd, map_mul, h1 _ hd, mul_one] at this
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hP2 (zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
    exact WithZero.exp_ne_zero hy.symm
  have hϖE : algebraMap (𝓞 E) E ϖ ≠ 0 := by
    simpa using hϖ0
  have hvϖ : P.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
    have a1 := (P.intValuation_lt_one_iff_mem ϖ).2 hP
    have a2 := (P.intValuation_le_pow_iff_mem ϖ 2).not.2 hP2
    rw [P.intValuation_eq_exp_neg_multiplicity hϖ0] at a1 a2 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at a1
    rw [WithZero.exp_le_exp] at a2
    congr 1
    push_cast at a2
    omega
  set m : ℕ := multiplicity P.asIdeal (Ideal.span {y}) with hm
  have hvy : P.intValuation y = WithZero.exp (-(m : ℤ)) :=
    P.intValuation_eq_exp_neg_multiplicity hy0
  have e1 : P.valuation E (algebraMap (𝓞 E) E y) = WithZero.exp (-(m : ℤ)) :=
    (P.valuation_of_algebraMap (K := E) y).trans hvy
  have e2 : P.valuation E (algebraMap (𝓞 E) E ϖ) = WithZero.exp (-1 : ℤ) :=
    (P.valuation_of_algebraMap (K := E) ϖ).trans hvϖ
  have hq := hu (algebraMap (𝓞 E) E y / algebraMap (𝓞 E) E ϖ ^ m) (by
    rw [map_div₀, map_pow, e1, e2, ← WithZero.exp_nsmul, ← WithZero.exp_sub, ← WithZero.exp_zero]
    congr 1
    simp)
  have hw0 : w (algebraMap (𝓞 E) E ϖ) ≠ 0 := (Valuation.ne_zero_iff w).2 hϖE
  rw [map_div₀, map_pow, hy] at hq
  rw [← WithZero.exp_log hw0] at hq hlt ⊢
  set j := WithZero.log (w (algebraMap (𝓞 E) E ϖ))
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [← WithZero.exp_nsmul, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_inj] at hq
  congr 1
  simp only [nsmul_eq_mul] at hq
  have : (-j) * (m : ℤ) = 1 := by linarith
  have := Int.eq_one_of_mul_eq_one_right (by omega) this
  omega

theorem isUnifV_of_centre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* v.adicCompletion F), (∀ x : F, φ (algebraMap F E x) = algebraMap F (v.adicCompletion F) x) → (∀ x : 𝓞 E, φ (x : E) ∈ Formalism.UG.Ov F v) → (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ φ ((x : E)⁻¹) ∉ Formalism.UG.Ov F v)) → ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → Formalism.UG.IsUnifV F v (φ (ϖ : E)) := by
  intro F E _ _ _ _ _ v P φ hF hO hc ϖ hP hP2
  let w : Valuation E (WithZero (Multiplicative ℤ)) := (Valued.v).comap φ
  have hw : ∀ x : E, w x = Valued.v (φ x) := fun _ => rfl
  have hmem : ∀ x : E, φ x ∈ Formalism.UG.Ov F v ↔ w x ≤ 1 := fun _ => Iff.rfl
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hP2 (zero_mem _)
  obtain ⟨y, hy⟩ := v.intValuation_exists_uniformizer
  refine val_eq_exp_neg_one P w ?_ ϖ hP hP2 ?_ (algebraMap (𝓞 F) (𝓞 E) y) ?_
  · intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (zero_mem _)
    have hxE : algebraMap (𝓞 E) E x ≠ 0 := by simpa using hx0
    have a1 : w (algebraMap (𝓞 E) E x) ≤ 1 := (hmem _).1 (hO x)
    have a2 : w ((algebraMap (𝓞 E) E x)⁻¹) ≤ 1 := (hmem _).1 (not_not.1 ((hc x hx0).not.1 hx))
    rw [map_inv₀] at a2
    have hw0 : w (algebraMap (𝓞 E) E x) ≠ 0 := (Valuation.ne_zero_iff w).2 hxE
    exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 hw0)).1 a2)
  · have hxE : algebraMap (𝓞 E) E ϖ ≠ 0 := by simpa using hϖ0
    have a2 : ¬ w ((algebraMap (𝓞 E) E ϖ)⁻¹) ≤ 1 := (hmem _).not.1 ((hc ϖ hϖ0).1 hP)
    rw [map_inv₀, not_le] at a2
    have hw0 : w (algebraMap (𝓞 E) E ϖ) ≠ 0 := (Valuation.ne_zero_iff w).2 hxE
    exact (one_lt_inv₀ (zero_lt_iff.2 hw0)).1 a2
  · have e : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) y)
        = algebraMap F E (algebraMap (𝓞 F) F y) := by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [e, hw, hF, ← hy, ← v.valuation_of_algebraMap (K := F)]
    exact v.valuedAdicCompletion_eq_valuation' (algebraMap (𝓞 F) F y)

end GlobalTheory.SplitLocUnif
end

