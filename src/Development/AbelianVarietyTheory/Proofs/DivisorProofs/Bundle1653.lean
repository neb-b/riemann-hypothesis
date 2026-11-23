module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacuumOfReadsGaussianEntire
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis
open scoped ComplexConjugate

variable {D : D7}

theorem hasDerivAt_line_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (E Φ : V → ℂ)
    (hE : Differentiable ℝ E) (hΦ : Differentiable ℝ Φ) (K : ℂ) (z v : V) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * K) * (E (z + t • v) * Φ (z + t • v)))
      (K * (E z * Φ z) + (fderiv ℝ E z v * Φ z + E z * fderiv ℝ Φ z v)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * K)) K 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const K).cexp
    simpa using this
  have hl : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hE' : HasDerivAt (fun t : ℝ => E (z + t • v)) (fderiv ℝ E z v) 0 := by
    have := (hE (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rwa [zero_smul, add_zero] at this
  have hΦ' : HasDerivAt (fun t : ℝ => Φ (z + t • v)) (fderiv ℝ Φ z v) 0 := by
    have := (hΦ (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rwa [zero_smul, add_zero] at this
  refine (h1.mul (hE'.mul hΦ')).congr_deriv ?_
  simp only [Pi.mul_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, zero_smul, add_zero, one_mul]

theorem formAt_gram_one {S T : HSp D} (hS1 : S.gram = 1) (hT1 : T.gram = 1) (τ : D.what₂.Tau)
    (x y : Fin T.rank → Fin S.rank → ℂ) :
    ((GlobalTheory.OrientedHeis.formAt S T τ x y : ℝ) : ℂ) = Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * (∑ i, ∑ j, x i j * conj (y i j)) -
      Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * conj (∑ i, ∑ j, x i j * conj (y i j)) := by
  have hS : ∀ a b, tauE D τ ((S.gram⁻¹) a b) = if a = b then 1 else 0 := fun a b => by
    rw [hS1, inv_one, Matrix.one_apply]; split_ifs <;> simp
  have hT : ∀ a b, tauE D τ (T.gram a b) = if a = b then 1 else 0 := fun a b => by
    rw [hT1, Matrix.one_apply]; split_ifs <;> simp
  have hs : ∑ a, ∑ b, ∑ e, ∑ d, tauE D τ (S.gram⁻¹ a b) * conj (y e b) * tauE D τ (T.gram e d) * x d a =
      ∑ i, ∑ j, x i j * conj (y i j) := by
    simp only [hS, hT, ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have h1 : ∀ a : Fin S.rank, (∑ b : Fin S.rank, ∑ e : Fin T.rank,
        if a = b then conj (y e b) * x e a else 0) = ∑ e : Fin T.rank, conj (y e a) * x e a := fun a => by
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    simp only [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm (conj (y i j)) (x i j)
  unfold GlobalTheory.OrientedHeis.formAt
  rw [hs, GlobalTheory.FockPos.xi_zero_eq_host τ]
  push_cast
  rw [Complex.re_eq_add_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem omO_gram_one {S T : HSp D} (hS1 : S.gram = 1) (hT1 : T.gram = 1) (z v : RW T S) :
    ((GlobalTheory.OrientedHeis.omO S T z v : ℝ) : ℂ) =
      Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * (∑ τ, ∑ i, ∑ j, z τ i j * conj (v τ i j)) -
        Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * conj (∑ τ, ∑ i, ∑ j, z τ i j * conj (v τ i j)) := by
  show ((∑ τ, GlobalTheory.OrientedHeis.formAt S T τ (z τ) (v τ) : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [formAt_gram_one hS1 hT1, map_sum, Finset.mul_sum, Finset.sum_sub_distrib]

theorem reads_isFockVacAt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f := by
  intro D ψ θ S T a d hS hT cc δ r hset G f hG hR τ
  subst hS hT
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hset.inf
  have hψ := hset.std
  have hth : IsThetaFunO ψ S T f := hR.1
  have hR' := ((reads_iff hset.crv hset.scale G f).1 hR).2
  obtain ⟨hEd, hEc⟩ := GlobalTheory.FockPos.gauss_cr (ι := D.what₂.Tau) (m := T.rank) (n := S.rank) (-Formalism.L2.Pj.xiR D)
  set E : VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp ((Real.pi * (-Formalism.L2.Pj.xiR D) * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) with hEdef
  let L : VC D S.rank T.rank →L[ℂ] VC D S.rank T.rank := LinearMap.toContinuousLinearMap
    { toFun := fun Z τ i j => δ * embT D τ r * Z τ i j
      map_add' := fun Y Z => by funext τ i j; simp only [Pi.add_apply]; ring
      map_smul' := fun c Z => by funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  set Φ : VC D S.rank T.rank → ℂ := fun Z => G (fun τ i j => δ * embT D τ r * Z τ i j) with hΦdef
  have hΦd : Differentiable ℂ Φ := hG.comp L.differentiable
  have hΦc : ∀ z v : VC D S.rank T.rank, fderiv ℝ Φ z (Complex.I • v) = Complex.I * fderiv ℝ Φ z v := fun z v => by
    rw [((hΦd z).hasFDerivAt.restrictScalars ℝ).fderiv]
    exact (fderiv ℂ Φ z).map_smul Complex.I v
  have hreal : ∀ w : WO S T, w.map (finPart D) = 0 → ∀ x : RW T S, (w + iotaW σ T S x).map (finPart D) = 0 := by
    intro w hw x
    have h2 := h.real_iota T S x
    ext i j
    have a1 := congrFun (congrFun hw i) j
    have a2 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at a1 a2 ⊢
    rw [Matrix.add_apply, map_add (finPart D), a1, a2, add_zero]
  have hval : ∀ w : WO S T, w.map (finPart D) = 0 → f w = E (piW θ T S w) * Φ (piW θ T S w) := by
    intro w hw
    rw [hR' w hw]
    have hz : GlobalTheory.FockPos.zCo θ 1 1 w = piW θ T S w := by
      funext τ
      have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
        Matrix.map_one _ (map_zero _) (map_one _)
      simp only [GlobalTheory.FockPos.zCo, e, inv_one, Matrix.one_mul, Matrix.mul_one]
      rfl
    rw [GlobalTheory.FockPos.gaussO, hz]
    show Complex.exp _ * G _ = Complex.exp _ * G _
    congr 2
    push_cast
    ring
  have hline : ∀ (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) (x : RW T S),
      (∀ t : ℝ, lineAt θ τ u t = iotaW σ T S (t • x)) → ∀ w : WO S T, w.map (finPart D) = 0 →
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f w =
        (-(Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T (piW θ T S w) x : ℝ) : ℂ)) *
            (E (piW θ T S w) * Φ (piW θ T S w)) +
          (fderiv ℝ E (piW θ T S w) x * Φ (piW θ T S w) + E (piW θ T S w) * fderiv ℝ Φ (piW θ T S w) x) := by
    intro u x hx w hw
    have hfun : (fun t : ℝ => heisO ψ S T (lineAt θ τ u t) f w) = fun t : ℝ =>
        Complex.exp ((t : ℂ) * (-(Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T (piW θ T S w) x : ℝ) : ℂ))) *
          (E (piW θ T S w + t • x) * Φ (piW θ T S w + t • x)) := by
      funext t
      rw [hx t, heisO_iota h hψ, hval _ (hreal w hw _), AddMonoidHom.map_add (f := _), h.pi_iota T S, LinearMap.map_smul]
      congr 2
      rw [smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [Formalism.IndefR.Datum.dRho, hfun]
    exact (hasDerivAt_line_mul E Φ hEd (hΦd.restrictScalars ℝ) _ _ _).deriv
  let X : Matrix (Fin T.rank) (Fin S.rank) ℂ → RW T S := fun u τ' i j => if τ' = τ then u i j else 0
  have hX : ∀ u (t : ℝ), lineAt θ τ u t = iotaW σ T S (t • X u) := fun u t => by
    rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ u t]
    congr 2
    funext τ' i j
    by_cases e : τ' = τ
    · subst e
      simp [X, Pi.single, Function.update]
    · simp [X, e, Pi.single, Function.update]
  have hXI : ∀ u, X (Complex.I • u) = Complex.I • X u := fun u => by
    funext τ' i j
    by_cases e : τ' = τ <;> simp [X, e]
  have hJ : ∀ u : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      cplxO (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) u = Complex.I • u :=
    fun u => by simp only [cplxO, Matrix.one_mul, Matrix.mul_one]
  intro u
  have hθa : IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ (cplxO 1 1) u f) := by
    have hc := (GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hset.inf S T f hth).2
    exact (GlobalTheory.FinWeilO.thetaSub ψ S T).add_mem (hc τ u)
      ((GlobalTheory.FinWeilO.thetaSub ψ S T).smul_mem Complex.I (hc τ _))
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hθa fun w hw => ?_
  have hw' : w.map (finPart D) = 0 := hw
  show Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f w +
    Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO 1 1 u) f w = 0
  rw [hJ, hline u (X u) (hX u) w hw', hline _ (X (Complex.I • u)) (hX _) w hw', hXI]
  have hp' : ∑ τ', ∑ i, ∑ j, piW θ T S w τ' i j * conj ((Complex.I • X u) τ' i j) =
      -Complex.I * ∑ τ', ∑ i, ∑ j, piW θ T S w τ' i j * conj (X u τ' i j) := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [omO_gram_one hset.gS hset.gT, omO_gram_one hset.gS hset.gT, hp', hΦc]
  simp only [map_mul, map_neg, Complex.conj_I, neg_neg]
  have key := hEc (piW θ T S w) (X u)
  rw [Complex.ofReal_neg] at key
  set P := ∑ τ', ∑ i, ∑ j, piW θ T S w τ' i j * conj (X u τ' i j) with hP
  linear_combination (Φ (piW θ T S w)) * key +
    (E (piW θ T S w) * Φ (piW θ T S w) * (Real.pi : ℂ) * (Formalism.L2.Pj.xiR D : ℂ) *
        (Complex.I ^ 2 * (P + conj P) - 2 * P) + E (piW θ T S w) * fderiv ℝ Φ (piW θ T S w) (X u)) * Complex.I_sq

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianColumnsLinearParametrisationFinitePlac
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLagParam

open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev lift (v : Pl (F := F)) : Fv F v ⊗[F] E →ₗ[F] AE F E := (liftV v).rTensor E

theorem compFin_lift (v : Pl (F := F)) (t : Fv F v ⊗[F] E) : compFin F E v (lift v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem liftV_one_smul_eq (v : Pl (F := F)) (a : AE F E) : liftV v (1 : Fv F v) • a = lift v (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin]
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]

theorem compFin_smul (v : Pl (F := F)) (r : AF F) (a : AE F E) : compFin F E v (r • a) = evFin F v r • compFin F E v a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [compFin, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

theorem at_map_lift {α β : Type} (v : Pl (F := F)) (A : Matrix α β (Fv F v ⊗[F] E)) : At (evFin F v) (A.map (lift v)) := by
  intro u hu
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  induction A i k using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    rw [← smul_eq_mul, at_liftV v x u hu, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]

theorem eq_map_lift {α β : Type} (v : Pl (F := F)) (z : Matrix α β (AE F E)) (hz : At (evFin F v) z) :
    z = (z.map (compFin F E v)).map (lift v) := by
  conv_lhs => rw [← liftV_one_smul v z hz]
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, liftV_one_smul_eq]

theorem map_lift_compFin {α β : Type} (v : Pl (F := F)) (A : Matrix α β (Fv F v ⊗[F] E)) :
    (A.map (lift v)).map (compFin F E v) = A := by
  ext i k; simp [compFin_lift]

end GlobalTheory.InertLagParam
end

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem card_eq_of_inv {R : Type} [CommRing R] [Nontrivial R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (A : Matrix α β R) (B : Matrix β α R) (h1 : A * B = 1) (h2 : B * A = 1) :
    Fintype.card α = Fintype.card β := by
  let f : (β → R) ≃ₗ[R] (α → R) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := f.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at this
  exact this.symm

theorem eq_zero_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (v : Pl (F := F)) (u : W) (hu : At (evFin F v) u) (h0 : locCo co v u = 0) : u = 0 := by
  have h1 : co.e u = liftV v (1 : Fv F v) • co.e u := by rw [← LinearEquiv.map_smul, liftV_one_smul v u hu]
  have h2 : co.e u = 0 := by
    rw [h1]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have := congrArg (fun p => p.1 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
    · have := congrArg (fun p => p.2 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
  exact co.e.map_eq_zero_iff.1 h2

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam

def mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin m) R →ₗ[R] Matrix (Fin n) (Fin m) R where
  toFun x := A * x
  map_add' x y := Matrix.mul_add A x y
  map_smul' c x := Matrix.mul_smul A c x

theorem det_mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.det (mulLeft n m A) = A.det ^ m := by
  let τ : Matrix (Fin n) (Fin m) R ≃ₗ[R] (Fin m → Fin n → R) :=
    { toFun := fun x k i => x i k
      invFun := fun y => Matrix.of fun i k => y k i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : (τ : _ →ₗ[R] _) ∘ₗ mulLeft n m A ∘ₗ (τ.symm : (Fin m → Fin n → R) →ₗ[R] _) =
      LinearMap.pi fun k : Fin m => Matrix.toLin' A ∘ₗ LinearMap.proj k := by
    refine LinearMap.ext fun y => ?_
    funext k i
    rfl
  rw [← LinearMap.det_conj (mulLeft n m A) τ, h, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

theorem param : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl (F := F))
    (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    d = 2 * m ∧ ∃ (N : ℕ) (j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
      (ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E)), Function.Injective j ∧
      (∀ y, At (evFin F v) (ζ y) ∧ locCo M.co v (ζ y * Cᵀ) = j y) ∧
      (∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z → ∃ y, ζ y = z) ∧
      ∀ s : GL (Fin n) (AE F E), ∃ T : GL (Fin N) (Fv F v), (∀ y, ζ (T.val *ᵥ y) = s.val * ζ y) ∧
        T.val.det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
  intro F E _ _ _ _ _ σ n d X W M v m C hC
  obtain ⟨h0, Cx, P, hx, h1, h2⟩ := hC
  have hP1 : P.toRows₁ * C.map (compFin F E v) = 1 := by
    have h2' := h2
    rw [← Matrix.fromRows_toRows P, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_inj] at h2'
    exact h2'.1
  refine ⟨?_, ?_⟩
  · have := card_eq_of_inv _ _ h1 h2
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  let Z := Matrix (Fin n) (Fin m) (Fv F v ⊗[F] E)
  let N := Module.finrank (Fv F v) Z
  let e : (Fin N → Fv F v) ≃ₗ[Fv F v] Z := (Module.finBasis (Fv F v) Z).equivFun.symm
  let ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E) := fun y => (e y).map (lift v)
  have hζat : ∀ y, At (evFin F v) (ζ y) := fun y => at_map_lift v _
  have hζc : ∀ y, (ζ y).map (compFin F E v) = e y := fun y => map_lift_compFin v _
  have hζadd : ∀ y y', ζ (y + y') = ζ y + ζ y' := fun y y' => by
    simp only [ζ, map_add (f := _)]
    exact Matrix.map_add _ (map_add _) _ _
  have hζsmul : ∀ (a : Fv F v) y, ζ (a • y) = liftV v a • ζ y := fun a y => by
    have hat : At (evFin F v) (liftV v a • ζ y) := fun u hu => by rw [smul_comm, hζat y u hu, smul_zero]
    rw [eq_map_lift v _ hat]
    congr 1
    ext i k
    simp [ζ, compFin_smul, evFin_liftV, compFin_lift] <;> rfl
  let j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun y => locCo M.co v (ζ y * Cᵀ)
      map_add' := fun y y' => by rw [hζadd, Matrix.add_mul, map_add (f := _)]
      map_smul' := fun a y => by
        rw [hζsmul, Matrix.smul_mul]
        ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul] }
  refine ⟨N, j, ζ, ?_, fun y => ⟨hζat y, rfl⟩, fun z hz => ?_, fun s => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hu := eq_zero_of_locCo M.co v _ (at_mul v _ (hζat y) _) hy
    have h3 : e y * (C.map (compFin F E v))ᵀ = 0 := by
      have := congrArg (fun x => Matrix.map x (compFin F E v)) hu
      simp only [Matrix.map_mul, Matrix.transpose_map, hζc, Matrix.map_zero _ (map_zero _)] at this
      exact this
    have h4 : e y = 0 := by
      have h5 : e y = e y * (P.toRows₁ * C.map (compFin F E v))ᵀ := by
        rw [hP1, Matrix.transpose_one, Matrix.mul_one]
      rw [h5, Matrix.transpose_mul, ← Matrix.mul_assoc, h3, Matrix.zero_mul]
    exact e.map_eq_zero_iff.1 h4
  · exact ⟨e.symm (z.map (compFin F E v)), by simp only [ζ, LinearEquiv.apply_symm_apply]; exact (eq_map_lift v z hz).symm⟩
  · let sv := s.val.map (compFin F E v)
    let L : Z →ₗ[Fv F v] Z := (mulLeft n m sv).restrictScalars (Fv F v)
    let f := e.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap
    have hdet : (LinearMap.toMatrix' f).det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
      rw [LinearMap.det_toMatrix']
      have hf : f = e.symm.toLinearMap ∘ₗ L ∘ₗ e.symm.symm.toLinearMap := rfl
      rw [hf, LinearMap.det_conj, LinearMap.det_restrictScalars, det_mulLeft, map_pow, RingHom.map_det]
      rfl
    have hs : IsUnit s.val.det := by simpa using (Matrix.GeneralLinearGroup.det s).isUnit
    have hne : (LinearMap.toMatrix' f).det ≠ 0 := by
      rw [hdet]
      exact (((hs.map (compFin F E v)).map (Algebra.norm (Fv F v))).pow m).ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne, fun y => ?_, hdet⟩
    show ζ (LinearMap.toMatrix' f *ᵥ y) = s.val * ζ y
    rw [LinearMap.toMatrix'_mulVec]
    have hat : At (evFin F v) (s.val * ζ y) := fun u hu => by rw [← Matrix.mul_smul, hζat y u hu, Matrix.mul_zero]
    rw [eq_map_lift v _ hat, Matrix.map_mul, hζc]
    simp [ζ, f, L, mulLeft, sv]

end GlobalTheory.InertLagParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantDistributionCharacters
section
namespace GlobalTheory.LatticeComb
open scoped SchwartzMap

theorem comb_unique : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (a : V) (T : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ l ∈ Λ, ∀ f f' : SchwartzMap V ℂ, (∀ x, f' x = f (x + l)) → T f' = T f) →
    (∀ μ : V, (∀ l ∈ Λ, ∃ k : ℤ, P l μ = k) → ∀ f f' : SchwartzMap V ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * f x) →
      T f' = Complex.exp (2 * Real.pi * Complex.I * (P a μ : ℂ)) * T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap V ℂ, T f = c * ∑' l : Λ, f (a + l) := by
  intro V _ _ _ P hP Λ _ _ a T htr hmod
  obtain ⟨h, hhc, hh1⟩ := _root_.GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one Λ
  refine ⟨T h, fun f => ?_⟩
  have hth : ∀ l : Λ, (fun x => h (x + (l : V))).HasTemperateGrowth := fun l =>
    HasCompactSupport.hasTemperateGrowth (hhc.comp_homeomorph (Homeomorph.addRight (l : V)))
      ((h.smooth ⊤).comp (contDiff_id.add contDiff_const))
  have hh : (⇑h).HasTemperateGrowth := HasCompactSupport.hasTemperateGrowth hhc (h.smooth ⊤)
  let u : Λ → 𝓢(V, ℂ) := fun l => SchwartzMap.smulLeftCLM ℂ (fun x => h (x + (l : V))) f
  have hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x := fun l x => by
    simp [u, SchwartzMap.smulLeftCLM_apply_apply (hth l)]
  obtain ⟨F1, hF1p, hF1T⟩ := _root_.GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms u (GlobalTheory.T.lattice_translates_cutoff_summable Λ h f hhc u hu)
  have hF1 : F1 = f := by
    ext x
    refine (hF1p x).unique ?_
    simpa [hu] using (hh1 x).mul_right (f x)
  let w : Λ → 𝓢(V, ℂ) := fun l => SchwartzMap.smulLeftCLM ℂ (⇑h) (SchwartzMap.compSubConstCLM ℂ (l : V) f)
  have hw : ∀ (l : Λ) (x : V), w l x = h x * f (x - l) := fun l x => by
    simp [w, SchwartzMap.smulLeftCLM_apply_apply hh]
  have huw : ∀ l, T (u l) = T (w l) := fun l =>
    htr l l.2 (w l) (u l) (fun x => by rw [hu, hw]; simp)
  obtain ⟨G, hGp, hGT⟩ := _root_.GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms w (_root_.GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub Λ h f hhc w hw)
  have h1 : T f = T G := by
    have := hF1T T
    rw [hF1] at this
    simp_rw [huw] at this
    exact this.unique (hGT T)
  obtain ⟨c, hcs, hcP⟩ := GlobalTheory.T.lattice_dual_fourier_expansion_schwartz P hP Λ f
  have hch : ∀ μ : V, (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))).HasTemperateGrowth := by
    intro μ
    have e : (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) =
        fun x : V => Complex.exp ((Complex.I * ((2 * Real.pi : ℝ) : ℂ)) *
          ((LinearMap.toContinuousLinearMap (P.flip μ) x : ℝ) : ℂ)) := by
      funext x
      simp only [LinearMap.coe_toContinuousLinearMap']
      show _ = Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ) * ((P x μ : ℝ) : ℂ))
      push_cast; ring_nf
    rw [e]
    exact GlobalTheory.CharFormDeriv.hasTemperateGrowth_char (LinearMap.toContinuousLinearMap (P.flip μ)) (2 * Real.pi)
  let v0 : V → 𝓢(V, ℂ) := fun μ => SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) h
  have hv0 : ∀ μ x, v0 μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x := fun μ x => by
    simp [v0, SchwartzMap.smulLeftCLM_apply_apply (hch μ)]
  let v : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} → 𝓢(V, ℂ) := fun μ => c μ • v0 μ
  have hvs : ∀ k n : ℕ, Summable (fun μ => SchwartzMap.seminorm ℂ k n (v μ)) := by
    intro k n
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth P h v0 hv0 k n
    refine Summable.of_nonneg_of_le (fun μ => apply_nonneg _ _) (fun μ => ?_) ((hcs n).mul_left C)
    simp only [v, map_smul_eq_mul]
    calc ‖c μ‖ * SchwartzMap.seminorm ℂ k n (v0 μ) ≤ ‖c μ‖ * (C * (1 + ‖(μ : V)‖) ^ n) :=
          mul_le_mul_of_nonneg_left (hC μ) (norm_nonneg _)
      _ = C * (‖c μ‖ * (1 + ‖(μ : V)‖) ^ n) := by ring
  obtain ⟨G', hG'p, hG'T⟩ := _root_.GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms v hvs
  have hGG : G = G' := by
    ext x
    refine (hGp x).unique ?_
    have e1 : HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => v μ x)
        (h x * ∑' l : Λ, f (x + l)) := by
      have := (hcP x).mul_left (h x)
      have hfun : (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => v μ x) =
          fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => h x * (c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) := by
        funext μ
        simp only [v, SchwartzMap.smul_apply, hv0, smul_eq_mul]
        ring
      rw [hfun]; exact this
    have e2 : h x * ∑' l : Λ, f (x + l) = G' x := e1.unique (hG'p x)
    rw [← e2]
    have hsum : Summable (fun l : Λ => h x * f (x - l)) := by simpa [hw] using (hGp x).summable
    have e3 : ∑' l : Λ, f (x + l) = ∑' l : Λ, f (x - l) := by
      rw [← (Equiv.neg Λ).tsum_eq]
      simp [sub_eq_add_neg]
    rw [e3, ← tsum_mul_left]
    simpa [hw] using hsum.hasSum
  have hTv : ∀ μ, T (v μ) = c μ * Complex.exp (2 * Real.pi * Complex.I * (P a μ : ℂ)) * T h := by
    intro μ
    simp only [v, map_smul, smul_eq_mul]
    rw [hmod μ μ.2 h (v0 μ) (hv0 μ)]
    ring
  have h2 := hG'T T
  simp_rw [hTv] at h2
  rw [h1, hGG, ← h2.tsum_eq, tsum_mul_right, (hcP a).tsum_eq, mul_comm]

end GlobalTheory.LatticeComb
end

