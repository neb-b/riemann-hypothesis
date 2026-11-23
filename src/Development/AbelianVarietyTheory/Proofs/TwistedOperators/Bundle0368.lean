module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjections
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
open GlobalTheory.UnifPoint

noncomputable section

namespace GlobalTheory.HeckeLift

theorem int_eq_of_exp_eq_coprime {m n : ℤ} {p : ℕ} (hp : 0 < p)
    (h : ∀ k : ℕ, 0 < k → k.Coprime p → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  set K : ℕ := 1 + (n - m).natAbs * p with hK
  have hk : 0 < K := by omega
  have hcop : K.Coprime p := by
    rw [hK]
    first
      | exact (Nat.coprime_add_mul_right_left 1 p _).2 (Nat.coprime_one_left p)
      | exact (Nat.coprime_add_mul_left_left 1 p _).2 (Nat.coprime_one_left p)
      | simp
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h K hk hcop)
  have h0 : ((K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ((n - m : ℤ) : ℂ) = (((K : ℕ) : ℤ) * j : ℤ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize ((K : ℕ) : ℂ) = k at h0 hj
    field_simp at hj
    linear_combination (2 * Real.pi * Complex.I) * hj
  have hlt : (n - m).natAbs < K := by
    have : (n - m).natAbs ≤ (n - m).natAbs * p := Nat.le_mul_of_pos_right _ hp
    omega
  have h2 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j, Int.cast_injective h1⟩ (by
    rw [Int.natAbs_natCast]; exact hlt)
  omega

theorem exists_linearMap_of_isHkIsog : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → IsHkIsog p (F.u i P) (F.u j P') C ψ ψp → ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ ∀ z, F.ex j P' (h z) = ψp (F.ex i P z) := by
  intro E _ _ _ H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hk
  obtain ⟨-, -, hfib, hact, hsurj, hker, hweil, -⟩ := hk
  obtain ⟨e, he⟩ : ∃ e : (Fin g → ℂ) → (Over.mk (F.u j P') ⟶ Xo.univ.t.G), ∀ z, e z = ψp (F.ex i P z) :=
    ⟨_, fun _ => rfl⟩
  have hpow : ∀ (n : ℕ) z, F.ex i P (n • z) = F.ex i P z ^ n := fun n z => by
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact (F.ex_ker i P hP 0).2 ⟨0, map_zero P⟩
    | succ n ih => rw [succ_nsmul, F.ex_add i P hP, ih, pow_succ]
  have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hkerC : ∀ z, e z = 1 → ∃ a, P a = (p ^ 2) • z := fun z hz => by
    have hmem : F.ex i P z ∈ C := by rw [← hker, MonoidHom.mem_ker, ← he, hz]
    obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 ((hpow _ z).trans (hC _ hmem))
    exact ⟨a, ha⟩
  have hhol : IsHolTo Set.univ (fun z => (e z).left) := by
    have h1 := (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G _ g (F.ex i P)
      (GlobalTheory.ClassUniq.isHolTo_ex F i P hP)).2 _ (ψ ≫ pullback.fst _ _)
    convert h1 using 2 with z
    rw [← Category.assoc, hfib, he]
    unfold fibPt
    exact (pullback.lift_fst _ _ _).symm
  have hc : {z | e z = 1}.Countable := by
    refine ((countable_periods hP).image fun w => ((p ^ 2 : ℕ) : ℂ)⁻¹ • w).mono fun z hz => ?_
    obtain ⟨a, ha⟩ := hkerC z hz
    refine ⟨P a, ⟨a, rfl⟩, ?_⟩
    have h0 : ((p ^ 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
    simp only [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h0]
  have hexp : IsExp (F.ex j P') := ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP',
    (F.ex_diff j P' hP').1, (F.ex_diff j P' hP').2⟩
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' hexp (F.ex_ker j P' hP') (e₀ := e)
    (fun z w => by rw [he, he, he, F.ex_add i P hP, map_mul]) (fun y => by
      obtain ⟨z, hz⟩ := hsurj.comp (F.ex_onto i P hP) y
      exact ⟨z, (he z).trans hz⟩) hhol hc
  have hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a := fun a z => by
    rw [he, he, F.ex_lin i P hP, hact]
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (F.ex_ker j P' hP' _).1 ((eq_iff_sub_of_add (F.ex_add j P' hP') _ _).1
          (((hh _).trans (hlin a x)).trans (by rw [← hh]; exact (F.ex_lin j P' hP' a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a =>
    (F.ex_ker j P' hP' _).1 ((hh _).trans (by rw [he, (F.ex_ker i P hP _).2 ⟨a, rfl⟩, map_one]))
  choose r₀ hr₀ using hmem
  let r₁ : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add (f := _), hr₀, hr₀, hr₀, map_add (f := _), map_add (f := _)])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  refine ⟨r₁, h, fun a b => ?_, hr₀, fun b => ?_, fun z => (hh z).trans (he z)⟩
  · refine int_eq_of_exp_eq_coprime hp.pos fun k hk hcop => ?_
    have w := F.ex_weil i P hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have w1 := hweil k _ _ _ hcop w
    have w' := F.ex_weil j P' hP' k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh, he, he] at w'
    have := congrArg Units.val (weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ (F.u j P') k _ _ _ _ w' w1)
    simp only [Units.val_mk0, Units.val_pow_eq_pow_val] at this
    rw [show r₁ a = r₀ a from rfl, show r₁ b = r₀ b from rfl, this, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · obtain ⟨a, ha⟩ := hkerC (h.symm (P' b)) (by
      rw [← hh, h.apply_symm_apply]; exact (F.ex_ker j P' hP' _).2 ⟨b, rfl⟩)
    refine ⟨a, hP'.2.1 ?_⟩
    change P' (r₀ a) = _
    rw [hr₀, ha, map_nsmul, h.apply_symm_apply, map_nsmul]

end GlobalTheory.HeckeLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFockVacuumCauchyRiemann
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.HeisTranslCR

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem deriv_twisted_line_at {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] (F : R → ℂ) (hF : Differentiable ℝ F)
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a w u : R) :
    deriv (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a (t • u) : ℂ)) * F (w + t • u)) 0 =
      fderiv ℝ F w u - Real.pi * Complex.I * (om a u : ℂ) * F w := by
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 : HasDerivAt (fun t : ℝ => F (w + t • u)) (fderiv ℝ F w u) 0 := by
    have h := (hF (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * (om a (t • u) : ℂ))
      (-(Real.pi * Complex.I) * (om a u : ℂ)) 0 := by
    have e : (fun t : ℝ => -(Real.pi * Complex.I) * (om a (t • u) : ℂ)) =
        fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * (om a u : ℂ)) := by
      funext t
      rw [LinearMap.map_smul, smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [e]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (-(Real.pi * Complex.I) * (om a u : ℂ))
  have h4 := (h3.cexp.mul h2).deriv
  refine Eq.trans h4 ?_
  simp only [zero_smul, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul]
  ring

theorem differentiable_phase {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a : R) :
    Differentiable ℝ fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) := by
  have h : Differentiable ℝ fun w : R => ((om a w : ℝ) : ℂ) :=
    Complex.ofRealCLM.differentiable.comp (LinearMap.toContinuousLinearMap (om a)).differentiable
  exact ((differentiable_const _).mul h).cexp

theorem fderiv_phase_mul {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (F : R → ℂ)
    (hF : Differentiable ℝ F) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a w u : R) :
    fderiv ℝ (fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) * F w) w u =
      Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) *
        (fderiv ℝ F w u - Real.pi * Complex.I * (om a u : ℂ) * F w) := by
  have hG : Differentiable ℝ fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) * F w :=
    (differentiable_phase om a).mul hF
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 := (hG (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [zero_smul, add_zero, Function.comp_def] at h2
  rw [← h2.deriv]
  have e : (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a (w + t • u) : ℂ)) * F (w + t • u)) =
      fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) *
        (Complex.exp (-(Real.pi * Complex.I) * (om a (t • u) : ℂ)) * F (w + t • u)) := by
    funext t
    rw [LinearMap.map_add (f := _), Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  rw [e, deriv_const_mul_field, deriv_twisted_line_at F hF om a w u]

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem heisO_real_at (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (y : WO S T) (w : RW T S) :
    heisO ψ S T (iotaW σ T S w) f y =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S y) w : ℂ)) * f (y + iotaW σ T S w) := by
  unfold heisO
  rw [GlobalTheory.OrientedChar.char_symplOH D θ ψ h.inf hψ S T _ _ (Or.inr (h.real_iota T S w)), h.pi_iota]


open Classical in
theorem dRho_eq_at (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (y : WO S T) (hF : Differentiable ℝ fun v : RW T S => f (y + iotaW σ T S v)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : RW T S) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f (y + iotaW σ T S w) =
      fderiv ℝ (fun v : RW T S => f (y + iotaW σ T S v)) w (Pi.single τ z) -
        Real.pi * Complex.I * (omO S T (piW θ T S y + w) (Pi.single τ z) : ℂ) * f (y + iotaW σ T S w) := by
  refine Eq.trans ?_ (deriv_twisted_line_at _ hF (omO S T) (piW θ T S y + w) w (Pi.single τ z))
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ z t, heisO_real_at h hψ, (piW θ T S).map_add, h.pi_iota, add_assoc,
    ← (iotaW σ T S).map_add]


open Classical in
theorem heis_translate_cauchy_riemann : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ y : WO S T, Differentiable ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) ∧ ∀ w z : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w z + Complex.I * fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) = (Real.pi : ℂ) * Complex.I * ((GlobalTheory.VacUnique.omO S T w z : ℂ) + Complex.I * (GlobalTheory.VacUnique.omO S T w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) : ℂ)) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y := by
  intro D θ σ h ψ hψ S T A B f hf y
  have hF : Differentiable ℝ fun v : RW T S => f (y + iotaW σ T S v) :=
    (GlobalTheory.OrientedHeis.theta_sm h hf.1 y).differentiable (by simp)
  have hG : (fun w : RW T S => heisO ψ S T (iotaW σ T S w) f y) = fun w : RW T S =>
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S y) w : ℂ)) * f (y + iotaW σ T S w) := by
    funext w
    exact heisO_real_at h hψ S T f y w
  rw [hG]
  refine ⟨(differentiable_phase (omO S T) (piW θ T S y)).mul hF, fun w z => ?_⟩
  rw [fderiv_phase_mul _ hF, fderiv_phase_mul _ hF]
  rw [heisO_real_at h hψ S T f y w]
  set a := piW θ T S y with ha
  set Fd := fderiv ℝ (fun v : RW T S => f (y + iotaW σ T S v)) w with hFd
  set Fw := f (y + iotaW σ T S w) with hFw
  let L : RW T S →+ ℂ :=
    { toFun := fun s => Fd s - Real.pi * Complex.I * (omO S T (a + w) s : ℂ) * Fw
      map_zero' := by simp
      map_add' := fun x x' => by
        rw [ContinuousLinearMap.map_add (f := _), LinearMap.map_add (f := _), Complex.ofReal_add]
        ring }
  have hL : L z + Complex.I * L (jO S T A.cart B.cart z) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single z, map_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun τ _ => ?_
    have h1 := congrFun (hf.2 τ (z τ)) (y + iotaW σ T S w)
    have h2 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z τ) f (y + iotaW σ T S w) +
        Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (A.cart τ) (B.cart τ) (z τ)) f
          (y + iotaW σ T S w) = 0 := h1
    have h3 := dRho_eq_at h hψ S T f y hF τ (z τ) w
    have h4 := dRho_eq_at h hψ S T f y hF τ (cplxO (A.cart τ) (B.cart τ) (z τ)) w
    have h5 := GlobalTheory.VacUnique.Ann.jO_single S T A.cart B.cart τ (z τ)
    have h6 : L (Pi.single τ (z τ)) + Complex.I * L (Pi.single τ (cplxO (A.cart τ) (B.cart τ) (z τ))) = 0 :=
      (congrArg₂ (fun a b : ℂ => a + Complex.I * b) h3 h4).symm.trans h2
    exact (congrArg (fun b => L (Pi.single τ (z τ)) + Complex.I * L b) h5).trans h6
  have e1 : L z = Fd z - Real.pi * Complex.I * ((omO S T a z : ℂ) + (omO S T w z : ℂ)) * Fw := by
    show Fd z - Real.pi * Complex.I * (omO S T (a + w) z : ℂ) * Fw = _
    rw [LinearMap.map_add (f := _), LinearMap.add_apply, Complex.ofReal_add]
  have e2 : L (jO S T A.cart B.cart z) = Fd (jO S T A.cart B.cart z) - Real.pi * Complex.I *
      ((omO S T a (jO S T A.cart B.cart z) : ℂ) + (omO S T w (jO S T A.cart B.cart z) : ℂ)) * Fw := by
    show Fd _ - Real.pi * Complex.I * (omO S T (a + w) _ : ℂ) * Fw = _
    rw [LinearMap.map_add (f := _), LinearMap.add_apply, Complex.ofReal_add]
  rw [e1, e2] at hL
  linear_combination (Complex.exp (-(Real.pi * Complex.I) * (omO S T a w : ℂ))) * hL

end GlobalTheory.HeisTranslCR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingFourierJacobiStepBasePointColumn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB

variable {D : D7}

theorem hA_smul_left (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T (c • y) z = c * hA T y z := by
  simp only [hA, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem hA_smul_right (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T y (c • z) = cA D c * hA T y z := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ratV_smul' {n : ℕ} (c : D.host.E) (v : Fin n → D.host.E) : ratV (c • v) = incA D c • ratV v := by
  funext i; simp [ratV, map_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem xFB_col (F : Frames G) (hF : Std F) (σ : ℕ) (h' : 2 * σ + 2 ≤ D.R.m) (p : Fin (σ + 1)) :
    (fun k => xFB F σ h' k p) = incA D ((-D.host.xi0) ^ (p.1 + 1)) •
      ratV (fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) := by
  obtain ⟨h2, he, -⟩ := hF.hB σ h'
  induction p using Fin.lastCases with
  | last =>
    have hc : (Fin.castLE (by omega) (Fin.last σ) : Fin (2 * σ + 2 - 1)) = ⟨σ, by omega⟩ := Fin.ext (by simp)
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_last, vecB, HypDec.j0, ← ratV_mulVec, Matrix.mulVec_mulVec,
      hF.ζ (σ + 1), Matrix.mulVec_smul, hF.zB' σ h', ratV_smul', Fin.val_last, hc]
  | cast i =>
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, rat, Matrix.map_apply, he, colsOf,
      Pi.smul_apply, smul_eq_mul, ratV, map_mul, Fin.val_castSucc]
    rfl

theorem extY_col (F : Frames G) (hF : Std F) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)) :
    (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
        ratV (fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
          (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) =
      incA D (star ((-D.host.xi0) ^ (p.1 + 1))) • fun k => a' k p := by
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hq := ProjTgt.qY_mul_a (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)) (F.dJ (σ + 1) h) (by omega) h2 he

  rw [HypDec.extY_apply, ← Matrix.mulVec_mulVec, HypDec.pY, ← ratV_mulVec]
  have hv : ∀ (M : Matrix (Fin (σ + 1)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) D.host.E)
      (N : Matrix (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (Fin (2 * (σ + 1) + 1 - 1)) D.host.E) (q : Fin (2 * (σ + 1) + 1 - 1)),
      M *ᵥ (fun k => N k q) = fun r => (M * N) r q := fun M N q => by
    funext r; simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hv, hq]
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ratV, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp only [ite_true, mul_one]; ring
  · intro r _ hr
    have : ¬ ((Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev = (Fin.castLE (by omega) r).rev) := by
      intro e; apply hr; rw [Fin.rev_inj] at e; exact Fin.ext (by simpa [Fin.ext_iff] using e.symm)
    simp only [this, ite_false, mul_zero, map_zero]
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem hA_xFB_col : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)),
    hA _ (fun k => xFB F σ h' k p) (fun k => a' k p) =
      hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p))
        ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
          ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
            (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) := by
  intro D _ T L _ _ sc G _ _ _ F hF σ h h' a' p
  rw [xFB_col F hF σ h' p, extY_col F hF σ h a' p, hA_smul_left, hA_smul_right, GlobalTheory.DualPairCheck.cA_incA, star_star]

end GlobalTheory.CharXFB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableConjMonomialBargmannGaussian
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

theorem integrable_vcx_prod {ι : Type} [Fintype ι] {a b : ℕ} (g : ι → Fin b → Fin a → ℂ → ℂ)
    (hg : ∀ τ i j, Integrable (g τ i j)) :
    Integrable fun z : VCx ι a b => ∏ τ, ∏ i, ∏ j, g τ i j (z τ i j) := by
  have h1 : ∀ τ i, Integrable (fun w : Fin a → ℂ => ∏ j, g τ i j (w j)) := fun τ i =>
    Integrable.fintype_prod (f := fun j (w : ℂ) => g τ i j w) (hg τ i)
  have h2 : ∀ τ, Integrable (fun w : Fin b → Fin a → ℂ => ∏ i, ∏ j, g τ i j (w i j)) := fun τ =>
    Integrable.fintype_prod (f := fun i (w : Fin a → ℂ) => ∏ j, g τ i j (w j)) (h1 τ)
  exact Integrable.fintype_prod (f := fun τ (w : Fin b → Fin a → ℂ) => ∏ i, ∏ j, g τ i j (w i j)) h2

theorem exp_gq_eq_prod {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z : VCx ι a b) :
    (Real.exp (-gq c z / 2) : ℂ) = ∏ τ, ∏ i, ∏ j, (Real.exp (-(c τ * ‖z τ i j‖ ^ 2) / 2) : ℂ) := by
  have h : -gq c z / 2 = ∑ τ, ∑ i, ∑ j, (-(c τ * ‖z τ i j‖ ^ 2) / 2) := by
    simp [gq, Finset.sum_div, Finset.sum_neg_distrib, neg_div]
  rw [h]
  simp only [Real.exp_sum]
  push_cast
  rfl

theorem integrable_conj_pow_mul_gauss (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable fun w : ℂ => conj w ^ n * (Real.exp (-(c * ‖w‖ ^ 2) / 2) : ℂ) := by
  have h := GlobalTheory.integrable_norm_pow_mul_exp_neg_mul_norm_sq (E := ℂ) n (b := c / 2) (by positivity)
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
  rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply le_of_eq
  congr 2
  ring

theorem integrable_exp_bargmann_mul_gauss (u : ℂ) {c : ℝ} (hc : 0 < c) :
    Integrable fun w : ℂ => Complex.exp ((c : ℂ) * u * conj w) * (Real.exp (-(c * ‖w‖ ^ 2) / 2) : ℂ) := by
  have h := (GlobalTheory.integrable_exp_neg_mul_norm_sq (E := ℂ) (b := c / 4) (by positivity)).const_mul
    (Real.exp (c * ‖u‖ ^ 2))
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : ((c : ℂ) * u * conj w).re ≤ c * (‖u‖ * ‖w‖) := by
    calc _ ≤ ‖(c : ℂ) * u * conj w‖ := Complex.re_le_norm _
      _ = c * (‖u‖ * ‖w‖) := by
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hc.le]
        ring
  have h2 : ‖u‖ * ‖w‖ ≤ ‖u‖ ^ 2 + ‖w‖ ^ 2 / 4 := by nlinarith [sq_nonneg (‖u‖ - ‖w‖ / 2)]
  have h3 := mul_le_mul_of_nonneg_left h2 hc.le
  nlinarith

theorem integrable_conjMono_bargmann_gauss : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) →
    (∀ m : DVar ι a b →₀ ℕ, Integrable fun z => conjMono m z * (Real.exp (-gq c z / 2) : ℂ)) ∧
      ∀ z₀ : VCx ι a b, Integrable fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) := by
  intro ι _ a b c hc
  constructor
  · intro m
    have h := integrable_vcx_prod (fun τ i j w => conj w ^ m (τ, i, j) * (Real.exp (-(c τ * ‖w‖ ^ 2) / 2) : ℂ))
      (fun τ i j => integrable_conj_pow_mul_gauss _ (hc τ))
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [conjMono, exp_gq_eq_prod, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Fintype.prod_prod_type, Finset.prod_mul_distrib]
  · intro z₀
    have h := integrable_vcx_prod (fun τ i j w => Complex.exp ((c τ : ℂ) * z₀ τ i j * conj w) *
      (Real.exp (-(c τ * ‖w‖ ^ 2) / 2) : ℂ)) (fun τ i j => integrable_exp_bargmann_mul_gauss _ (hc τ))
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [bk, exp_gq_eq_prod]
    simp only [Complex.exp_sum, Finset.prod_mul_distrib]

end GlobalTheory.FockTransl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableGaussianExpLinearNormTermComplexMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

theorem integrable_exp_lin_sub_sq_norm_complex {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    Integrable fun w : ℂ => Real.exp (r * ‖w‖ - c * ‖w‖ ^ 2 / 2) := by
  have hg : Integrable fun w : ℂ => Real.exp (-(c / 4) * ‖w‖ ^ 2) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := ((c / 4 : ℝ) : ℂ))
      (by simp; linarith) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  refine (hg.const_mul (Real.exp (r ^ 2 / c))).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key : r ^ 2 / c + -(c / 4) * ‖w‖ ^ 2 - (r * ‖w‖ - c * ‖w‖ ^ 2 / 2)
      = (r - c * ‖w‖ / 2) ^ 2 / c := by
    field_simp
    ring
  have : 0 ≤ (r - c * ‖w‖ / 2) ^ 2 / c := by positivity
  linarith

theorem integrable_exp_lin_sub_gq (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ) (hc : ∀ τ, 0 < c τ)
    (z₀ : VCx ι a b) :
    Integrable fun z : VCx ι a b => Real.exp ((∑ k : DVar ι a b,
      ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
  have key : ∀ z : VCx ι a b, Real.exp ((∑ k : DVar ι a b,
      ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2)
      = ∏ τ, ∏ i, ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖z τ i j‖ - c τ * ‖z τ i j‖ ^ 2 / 2) := by
    intro z
    simp only [← Real.exp_sum, gq, DVar, Fintype.sum_prod_type, Finset.sum_div,
      ← Finset.sum_sub_distrib]
  simp_rw [key]
  refine Integrable.fintype_prod (f := fun τ (x : Fin b → Fin a → ℂ) =>
    ∏ i, ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖x i j‖ - c τ * ‖x i j‖ ^ 2 / 2)) fun τ => ?_
  refine Integrable.fintype_prod (f := fun i (y : Fin a → ℂ) =>
    ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖y j‖ - c τ * ‖y j‖ ^ 2 / 2)) fun i => ?_
  refine Integrable.fintype_prod (f := fun j (w : ℂ) =>
    Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖w‖ - c τ * ‖w‖ ^ 2 / 2)) fun j => ?_
  exact integrable_exp_lin_sub_sq_norm_complex (hc τ) (norm_nonneg _)

end GlobalTheory.FockTransl

end
end

