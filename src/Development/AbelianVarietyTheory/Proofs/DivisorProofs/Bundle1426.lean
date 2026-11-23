module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelChernFormOfGramMatrixEqZero
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.ChernDel

variable {n : ℕ}

theorem del_del_comm {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (ξ η : V n) :
    del (fun x => del u x ξ) z η = del (fun x => del u x η) z ξ := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have key : ∀ a b : V n, del (fun x => del u x a) z b = (1 / 2 : ℂ) • (del (fun x => fderiv ℝ u x a) z b -
      Complex.I • del (fun x => fderiv ℝ u x (Complex.I • a)) z b) := by
    intro a b
    simp only [del_apply u]
    rw [del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul Complex.I)),
      del_sub (h1 _) ((h1 _).fun_const_smul Complex.I), del_const_smul _ (h1 _)]
    rfl
  rw [key, key]
  simp only [del_apply, fderiv_fderiv_apply hu, hs.eq ξ, hs.eq (Complex.I • ξ), smul_eq_mul]
  ring

section Mat

variable {r : Type} [Fintype r] [DecidableEq r]

theorem mdel_conn {H : V n → Matrix r r ℂ} {z : V n} (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : V n) :
    mdel (fun x => conn H x ξ) z η = mdel (fun x => conn H x η) z ξ +
      (conn H z ξ * conn H z η - conn H z η * conn H z ξ) := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  have hc : mdel (fun x => mdel H x ξ) z η = mdel (fun x => mdel H x η) z ξ := by
    ext a b; exact del_del_comm (h a b) ξ η
  simp only [conn]
  rw [mdel_mul (h1.transpose.inv hu') (h.mdel (by norm_num) ξ).transpose,
    mdel_mul (h1.transpose.inv hu') (h.mdel (by norm_num) η).transpose,
    mdel_inv h1.transpose hu', mdel_inv h1.transpose hu', mdel_transpose (fun x => mdel H x ξ),
    mdel_transpose (fun x => mdel H x η), hc, mdel_transpose, mdel_transpose]
  simp only [Matrix.neg_mul, Matrix.mul_assoc]
  abel

theorem mdel_curv_comm {H : V n → Matrix r r ℂ} {z : V n} (h : MContDiffAt 3 H z) (hu : IsUnit (H z).det)
    {ξ η : V n} (hξ : conn H z ξ = 0) (hη : conn H z η = 0) (ζ : V n) :
    mdel (fun x => curv H x ξ ζ) z η = mdel (fun x => curv H x η ζ) z ξ := by
  have h2 : MContDiffAt 2 H z := h.of_le (by norm_num)
  have c2 : ∀ a, MContDiffAt 2 (fun x => conn H x a) z := fun a => h.conn hu (by norm_num) a
  have c1 : ∀ a, MContDiffAt 1 (fun x => conn H x a) z := fun a => (c2 a).of_le one_le_two
  have he : (fun x => mdel (fun y => conn H y ξ) x η) =ᶠ[𝓝 z] fun x => mdel (fun y => conn H y η) x ξ +
      (conn H x ξ * conn H x η + -(conn H x η * conn H x ξ)) := by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit hu] with x h3 h4
    rw [mdel_conn h3 h4, sub_eq_add_neg]
  simp only [curv]
  rw [mdel_neg, mdel_neg, mdel_mdbar (c2 ξ), mdel_mdbar (c2 η), ← mdbar_mdel (c2 ξ), ← mdbar_mdel (c2 η),
    mdbar_congr he, mdbar_add ((c2 η).mdel (by norm_num) ξ) (((c1 ξ).mul (c1 η)).add ((c1 η).mul (c1 ξ)).neg),
    mdbar_add ((c1 ξ).mul (c1 η)) ((c1 η).mul (c1 ξ)).neg, mdbar_neg, mdbar_mul (c1 ξ) (c1 η),
    mdbar_mul (c1 η) (c1 ξ), hξ, hη]
  simp

end Mat

theorem delAt_congr {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.del_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem delAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {u : ι → V n → ℂ} (hu : ∀ i, DifferentiableAt ℝ (u i) v)
    (α : ι → Alt n) :
    delAt (fun x => ∑ i, u i x • α i) v = ∑ c, ∑ i, del (u i) v (coordVec c) • (dz c * α i) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  have : coefwise (fun f => del f v (coordVec c)) (fun x => ∑ i, u i x • α i) =
      ∑ i, del (u i) v (coordVec c) • α i := by
    refine (bas n).ext_elem fun S => ?_
    rw [FormMul.repr_coefwise]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [del_sum fun i _ => (hu i).mul_const _, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_mul (hu i) (differentiableAt_const _), del_const]
    simp
  rw [this, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem delAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  rw [delAt, delAt, delAt, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_add]
  congr 1
  refine (bas n).ext_elem fun S => ?_
  simp only [map_add (f := _), Finsupp.add_apply, FormMul.repr_coefwise]
  rw [del_add (hF S) (hG S), ContinuousLinearMap.add_apply]

theorem delAt_const (α : Alt n) (v : V n) : delAt (fun _ => α) v = 0 := by
  simp [delAt, coefwise]

def closedAt (v : V n) : Subalgebra ℂ (V n → Ev n) where
  carrier := {F | (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧
    delAt (fun x => (F x : Alt n)) v = 0}
  mul_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.mul_apply, Subalgebra.coe_mul, FormMul.repr_mul (F _ : Alt n)]
      exact DifferentiableAt.fun_sum fun p _ => ((hF p.1).mul (hG p.2)).mul_const _
    · obtain ⟨y, hy⟩ := FormMul.delAt_mul hF hG
      simp only [Pi.mul_apply, Subalgebra.coe_mul]
      rw [hy, hF0, hG0, zero_mul, mul_zero, add_zero]
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.add_apply, Subalgebra.coe_add, map_add (f := _), Finsupp.add_apply]
      exact (hF S).add (hG S)
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [delAt_add hF hG, hF0, hG0, add_zero]
  algebraMap_mem' c := ⟨fun S => differentiableAt_const ((bas n).repr (algebraMap ℂ (Ev n) c : Alt n) S),
    delAt_const (algebraMap ℂ (Ev n) c : Alt n) v⟩

theorem mem_closedAt {v : V n} {F : V n → Ev n} : F ∈ closedAt v ↔
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧ delAt (fun x => (F x : Alt n)) v = 0 :=
  Iff.rfl

theorem coeff_charpolyRev_map {R S r : Type} [CommRing R] [CommRing S] [Fintype r] [DecidableEq r] (f : R →+* S)
    (M : Matrix r r R) (j : ℕ) : (M.map f).charpolyRev.coeff j = f (M.charpolyRev.coeff j) := by
  rw [← Polynomial.coeff_map]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  apply congrArg (fun A : Matrix r r (Polynomial S) => A.det.coeff j)
  ext a b
  simp [Matrix.one_apply, apply_ite (Polynomial.map f)]

theorem mem_closedAt_of_symm {v : V n} {u : Fin n × Fin n → V n → ℂ} (hu : ∀ p, DifferentiableAt ℝ (u p) v)
    (hs : ∀ a b c, del (u (a, b)) v (coordVec c) = del (u (c, b)) v (coordVec a)) :
    (fun x => ∑ p, u p x • sym p) ∈ closedAt v := by
  refine mem_closedAt.2 ⟨fun S => ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, map_sum, map_smul, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul]
    exact DifferentiableAt.fun_sum fun p _ => (hu p).mul_const _
  · simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul]
    rw [delAt_sum_smul hu]
    simp only [Fintype.sum_prod_type]
    set T : Alt n := ∑ c, ∑ a, ∑ b, del (u (a, b)) v (coordVec c) • (dz c * (sym (a, b) : Alt n)) with hT
    have h2 : T = -T := by
      conv_rhs => rw [hT, Finset.sum_comm]
      rw [hT]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs a b c, ← smul_neg]
      congr 1
      show dz c * (dz a * dzb b) = -(dz a * (dz c * dzb b))
      rw [← mul_assoc, ← mul_assoc, ← neg_mul]
      congr 1
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have h3 : (2 : ℂ) • T = 0 := by rw [two_smul]; nth_rewrite 2 [h2]; exact add_neg_cancel T
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

variable {r : Type} [Fintype r] [DecidableEq r]

theorem delAt_chernAt_of_conn_eq_zero {H : V n → Matrix r r ℂ} {v : V n} (h : MContDiffAt 3 H v)
    (hu : IsUnit (H v).det) (h0 : ∀ a, conn H v (coordVec a) = 0) (j : ℕ) :
    delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  have hm : ∀ i k, (fun x => ∑ p : Fin n × Fin n, curv H x (coordVec p.1) (coordVec p.2) i k • sym p) ∈ closedAt v :=
    fun i k => mem_closedAt_of_symm (u := fun p x => curv H x (coordVec p.1) (coordVec p.2) i k)
      (fun p => (h.curv hu (j := 1) (by norm_num) _ _).diff i k)
      fun a b c => congrFun (congrFun (mdel_curv_comm h hu (h0 a) (h0 c) (coordVec b)) i) k
  let M : Matrix r r (closedAt v) := Matrix.of fun i k => ⟨_, hm i k⟩
  set_option synthInstance.maxHeartbeats 200000 in
  have e : (fun w => chernAt H w j) = (kappa ^ j • (-M).charpolyRev.coeff j : closedAt v) := by
    funext w
    let ev : closedAt v →+* Ev n := (Pi.evalRingHom (fun _ => Ev n) w).comp (closedAt v).val.toRingHom
    have e1 := coeff_charpolyRev_map ev (-M) j
    have e2 := coeff_charpolyRev_map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom (-curvPoly H w) j
    have e3 : (-M).map ev = (-curvPoly H w).map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom := by
      ext i k : 2
      simp only [Matrix.map_apply, Matrix.neg_apply, map_neg]
      congr 1
      simp [M, ev, curvPoly, Fintype.sum_prod_type, Algebra.smul_def]
    rw [e3, e2] at e1
    show kappa ^ j • _ = kappa ^ j • ev _
    rw [← e1]
    rfl
  set_option synthInstance.maxHeartbeats 200000 in
  have := (kappa ^ j • (-M).charpolyRev.coeff j : closedAt v).2
  rw [← e] at this
  exact (mem_closedAt.1 this).2

theorem delAt_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  intro n r _ _ H s hs hH hu j v hv
  have h3 : MContDiffAt 3 H v := fun a b => ((hH a b).contDiffAt (hs.mem_nhds hv)).of_le (by norm_cast)
  have h2 : MContDiffAt 2 H v := h3.of_le (by norm_num)
  let L : r → r → V n →L[ℂ] ℂ := fun i k => ∑ a, conn H v (coordVec a) i k • EuclideanSpace.proj a
  let A : V n → Matrix r r ℂ := fun w => Matrix.of fun i k => (1 : Matrix r r ℂ) i k + L i k v - L i k w
  have hAv : A v = 1 := by ext i k; simp [A]
  have hAa : ∀ w i k, AnalyticAt ℂ (fun w => A w i k) w := fun w i k => analyticAt_const.sub ((L i k).analyticAt w)
  have hA3 : MContDiffAt 3 A v := fun i k => (hAa v i k).contDiffAt.restrict_scalars ℝ
  have hAu : IsUnit (A v).det := by rw [hAv, det_one]; exact isUnit_one
  have hA0 : ∀ η, mdbar A v η = 0 := fun η => by
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hAa v a b).differentiableAt]
    rfl
  have hAd : ∀ c, mdel A v (coordVec c) = -conn H v (coordVec c) := fun c => by
    ext i k
    rw [mdel_apply, del_eq_fderiv (hAa v i k).differentiableAt]
    have : HasFDerivAt (fun w => A w i k) (-L i k) v := (L i k).hasFDerivAt.const_sub _
    rw [this.fderiv]
    simp [L, Pi.single_apply]
  have hK : MContDiffAt 3 (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) v :=
    (hA3.transpose.mul h3).mul hA3.conjTranspose.transpose
  have hKu : IsUnit ((A v)ᵀ * H v * (A v)ᴴᵀ).det := by simpa [hAv] using hu v hv
  have he : (fun w => (chernAt H w j : Alt n)) =ᶠ[𝓝 v]
      fun w => (chernAt (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) w j : Alt n) := by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit (hu v hv), hA3.eventually_isUnit hAu] with w a1 a2 a3
    rw [chernAt_changeFrame (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) H A w a1 a2 (hAa w) a3
      (Eventually.of_forall fun _ => rfl) j]
  rw [delAt_congr he]
  refine delAt_chernAt_of_conn_eq_zero hK hKu (fun a => ?_) j
  rw [conn_changeFrame (h3.of_le (by norm_num)) (hu v hv) (hA3.of_le (by norm_num)) hAu hA0, hAd, hAv]
  simp

end GlobalTheory.CxForm.ChernDel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertOrbitalIntegralUnitEqLatticeCount
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma
theorem unitLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := _root_.GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual
theorem unitLat_stable_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := _root_.GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff
theorem unitLat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := _root_.GlobalTheory.InertUnitLat.unitLat_eq_iff
theorem exists_unitLat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ q : UL n w, unitLat e B ψ q = L := _root_.GlobalTheory.InertUnitOrb.LatOnto.exists_unitLat_eq
theorem exists_torus_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := _root_.GlobalTheory.CentTorusModel.cent_equiv_torus
theorem cptPart_iff_intUnits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := _root_.GlobalTheory.InertUnitOrb.cptPart_iff_intUnits_of_model
theorem twOrb_unit : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G), twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := _root_.GlobalTheory.OrbIndUnit.twOrb_id_indicator
theorem relIndex_transport : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := _root_.GlobalTheory.relIndex_eq_of_mulEquiv_subgroup
end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem mem_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) (a : Aˣ) (y : A) :
    y ∈ mulLat O (a : A) L ↔ ((a⁻¹ : Aˣ) : A) * y ∈ L := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [← mul_assoc] using hz
  · intro h
    exact ⟨((a⁻¹ : Aˣ) : A) * y, h, by simp [← mul_assoc]⟩

theorem mem_stabLat_iff : ∀ (O : Type) [CommRing O] (A : Type) [CommRing A] [Algebra O A] (L : Submodule O A) (u : Aˣ), u ∈ stabLat O L ↔ mulLat O (u : A) L = L := by
  intro O _ A _ _ L u
  constructor
  · intro h
    have h' : ∀ y, y ∈ L ↔ (u : A) * y ∈ L := h
    ext y
    rw [mem_mulLat_unit, h', ← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    have hy := mem_mulLat_unit L u ((u : A) * y)
    rw [h, ← mul_assoc, Units.inv_mul, one_mul] at hy
    exact hy.symm

theorem unitLat_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (t q : UL n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = ((((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → unitLat e B ψ (t * q) = mulLat K.O (a : B.A) (unitLat e B ψ q) := by
  intro E _ _ _ hE w hw K e he hint n B ψ t q a ha
  have hmap : ∀ (g h : UL n w), ((((g * h : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) =
      (((g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm *
        (((h : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
    intro g h
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul (f := (e.symm : w.adicCompletion E →+* K.E))
  have hinv : ∀ y, ((((t⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y =
      ψ (((a⁻¹ : B.Aˣ) : B.A) * y) := by
    intro y
    have h1 : ψ y = ((((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ
        ψ (((a⁻¹ : B.Aˣ) : B.A) * y) := by
      rw [← ha, ← mul_assoc, Units.mul_inv, one_mul]
    rw [h1, Matrix.mulVec_mulVec, ← hmap, inv_mul_cancel]
    simp
  have key : ∀ (r : UL n w) (z : B.A), z ∈ unitLat e B ψ r ↔
      ∀ i, (((((r⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ z) i ∈
        (algebraMap K.O K.E).range := fun r z => Iff.rfl
  ext y
  rw [key, _root_.mul_inv_rev, hmap, ← Matrix.mulVec_mulVec, hinv, ← key, mem_mulLat_unit]

end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem mulLat_one' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) :
    mulLat O (1 : A) L = L := by
  simp [mulLat]

theorem mulLat_mul' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a b : A) (L : Submodule O A) :
    mulLat O (a * b) L = mulLat O a (mulLat O b L) := by
  rw [mulLat, mulLat, mulLat, LinearMap.mulLeft_mul, Submodule.map_comp]

theorem orbRel_equivalence {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (G : Subgroup Aˣ)
    (X : Set (Submodule O A)) :
    Equivalence (fun L M : X => ∃ t ∈ G, (M : Submodule O A) = mulLat O (t : A) (L : Submodule O A)) := by
  constructor
  · intro L
    exact ⟨1, G.one_mem, by simp [mulLat_one']⟩
  · rintro L M ⟨t, ht, h⟩
    refine ⟨t⁻¹, G.inv_mem ht, ?_⟩
    rw [h, ← mulLat_mul', Units.inv_mul, mulLat_one']
  · rintro L M N ⟨t, ht, h⟩ ⟨s, hs, h'⟩
    refine ⟨s * t, G.mul_mem hs ht, ?_⟩
    rw [h', h, Units.val_mul, mulLat_mul']

theorem ratCast_finsum' {α : Type} (f : α → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, ((f i : ℚ) : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact AddMonoidHom.map_finsum (Rat.castHom ℂ).toAddMonoidHom h
  · rw [finsum_of_infinite_support h, finsum_of_infinite_support]
    · simp
    · have : Function.support (fun i => ((f i : ℚ) : ℂ)) = Function.support f := by
        ext i; simp
      rwa [this]

theorem finsum_ite_subtype' {α M : Type} [AddCommMonoid M] (p : α → Prop) [DecidablePred p] (f : α → M) :
    ∑ᶠ i, (if p i then f i else 0) = ∑ᶠ i : Subtype p, f i := by
  rw [finsum_subtype_eq_finsum_cond]
  exact finsum_congr fun i => finsum_eq_if.symm

theorem orb_eq_N : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (γ : UL n w) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B (γ.1.val.map e.symm) x ψ → twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  intro E _ _ _ hE w hw K e he hint n B hsep γ x ψ hM
  obtain ⟨hx, hg, hh⟩ := hM
  obtain ⟨τ, hτ⟩ := exists_torus_equiv E hE w hw K e he hint n B ψ x γ ⟨hx, hg, hh⟩ hsep
  have hcpt := cptPart_iff_intUnits E hE w hw K e he hint n B ψ x γ ⟨hx, hg, hh⟩ hsep τ hτ
  have hS1 := unitLat_selfDual E hE w hw K e he hint n B ψ x hx hh
  have hS1b := unitLat_stable_iff E hE w hw K e he hint n B ψ γ hg
  have hS2 := unitLat_eq_iff E hE w hw K e he hint n B ψ
  have hS3 := exists_unitLat_eq E hE w hw K e he hint n B ψ x hx hh
  have hS6 : ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (q : UL n w),
      unitLat e B ψ ((t : UL n w) * q) = mulLat K.O ((τ t : B.Aˣ) : B.A) (unitLat e B ψ q) :=
    fun t q => unitLat_mul E hE w hw K e he hint n B ψ t q (τ t) (hτ t)
  have hcomm : ∀ s t : twCent (MonoidHom.id (UL n w)) γ, (s : UL n w) * t = t * s := by
    intro s t
    have h1 : τ (s * t) = τ (t * s) := by rw [map_mul, map_mul, mul_comm]
    have := congrArg Subtype.val (τ.injective h1)
    simpa using this
  have hX : ∀ q : UL n w, q⁻¹ * γ * q ∈ KL n w → unitLat e B ψ q ∈ B.X x := fun q hq =>
    ⟨(hS1 q).1, (hS1b q).2 hq, (hS1 q).2⟩
  have hrel : ∀ L M : B.X x, (Quot.mk _ L : Orb K.O B.T (B.X x)) = Quot.mk _ M →
      ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) L := fun L M h =>
    (orbRel_equivalence B.T (B.X x)).eqvGen_iff.mp (Quot.eqvGen_exact h)
  have hcle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ twCent (MonoidHom.id (UL n w)) γ :=
    (Subgroup.closure_le _).mpr fun s hs => hs.1
  have hconj : ∀ (Q s : UL n w), s ∈ (KL n w).map (MulAut.conj Q).toMonoidHom ↔ Q⁻¹ * s * Q ∈ KL n w := by
    intro Q s
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [twOrb_unit]
  unfold InvAlg.N orbSum
  rw [ratCast_finsum']
  rw [finsum_ite_subtype']
  let φ : {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) γ : Set (UL n w)) (KL n w : Set (UL n w)) //
      (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ KL n w} → Orb K.O B.T (B.X x) :=
    fun q => Quot.mk _ ⟨unitLat e B ψ (Quotient.out q.1), hX _ q.2⟩
  refine finsum_eq_of_bijective φ ⟨?_, ?_⟩ ?_
  · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
    obtain ⟨a, ha, hQ⟩ := hrel _ _ h
    set t := τ.symm ⟨a, ha⟩
    have hta : ((τ t : B.Aˣ) : B.A) = a := by simp [t]
    rw [← hta, ← hS6, hS2] at hQ
    apply Subtype.ext
    show q = q'
    rw [← DoubleCoset.out_eq' q, ← DoubleCoset.out_eq' q', DoubleCoset.eq]
    exact ⟨t, t.2, _, (KL n w).inv_mem hQ, by group⟩
  · intro o
    set R := Quot.out o
    obtain ⟨q0, hq0⟩ := hS3 R.1 R.2.1 R.2.2.2
    have hq0K : q0⁻¹ * γ * q0 ∈ KL n w := (hS1b q0).1 (hq0 ▸ R.2.2.1)
    obtain ⟨h, hh, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0
    have hhγ : h * γ = γ * h := hh
    have hP : (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0))⁻¹ * γ *
        Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0) ∈ KL n w := by
      rw [hout]
      have : (h * q0 * k)⁻¹ * γ * (h * q0 * k) = k⁻¹ * (q0⁻¹ * γ * q0) * k := by
        calc (h * q0 * k)⁻¹ * γ * (h * q0 * k) = k⁻¹ * q0⁻¹ * (h⁻¹ * (γ * h)) * q0 * k := by group
          _ = k⁻¹ * (q0⁻¹ * γ * q0) * k := by rw [← hhγ]; group
      rw [this]
      exact (KL n w).mul_mem ((KL n w).mul_mem ((KL n w).inv_mem hk) hq0K) hk
    refine ⟨⟨_, hP⟩, ?_⟩
    show Quot.mk _ _ = o
    rw [← Quot.out_eq o]
    refine (Quot.sound ?_).symm
    refine ⟨τ ⟨h, hh⟩, (τ ⟨h, hh⟩).2, ?_⟩
    show unitLat e B ψ _ = mulLat K.O _ R.1
    rw [hout, ← hq0, ← hS6]
    exact ((hS2 _ _).2 (by simpa [mul_assoc] using hk)).symm
  · rintro ⟨q, hq⟩
    set R := Quot.out (φ ⟨q, hq⟩)
    have hR : (Quot.mk _ R : Orb K.O B.T (B.X x)) = φ ⟨q, hq⟩ := Quot.out_eq _
    obtain ⟨a, ha, hRa⟩ := hrel _ _ hR.symm
    set t := τ.symm ⟨a, ha⟩
    have hta : ((τ t : B.Aˣ) : B.A) = a := by simp [t]
    rw [← hta, ← hS6] at hRa
    simp only [one_mul, Rat.cast_natCast]
    congr 1
    refine relIndex_transport (UL n w) B.Aˣ _ B.T τ _ _ (stabLat K.O R.1) (intUnits K.O B.A) inf_le_left hcle ?_ hcpt
    intro s
    rw [mem_stabLat_iff, hRa, ← hS6, hS2, Subgroup.mem_inf, hconj]
    simp only [SetLike.coe_mem, true_and]
    have : ((s : UL n w) * ((t : UL n w) * Quotient.out q))⁻¹ * ((t : UL n w) * Quotient.out q) =
        ((Quotient.out q)⁻¹ * s * Quotient.out q)⁻¹ := by
      rw [← mul_assoc (s : UL n w), hcomm s t]
      group
    rw [this]
    exact inv_mem_iff.symm

end GlobalTheory.InertUnitOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SectionLattice

def IntegralAtSection {W K' : Type} [CommRing W] [Field K'] [Algebra W K'] {G : Scheme.{0}}
    (p : G ⟶ Sp W) {P M : LB G} {N : LB (pullback p (spMap (algebraMap W K')))}
    (w : LB.Iso (M.pull (pullback.fst p (spMap (algebraMap W K')))) N)
    (w₁ : LB.Iso (P.pull (pullback.fst p (spMap (algebraMap W K')))) N) : Prop :=
  ∃ (e₀ : Sp W ⟶ G) (_ : e₀ ≫ p = 𝟙 _) (x : Sp K' ⟶ pullback p (spMap (algebraMap W K')))
    (_ : x ≫ pullback.fst p (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀)
    (_ : x ≫ pullback.snd p (spMap (algebraMap W K')) = 𝟙 _)
    (i : P.ι) (m : M.ι) (n : N.ι) (_ : ⊤ ≤ e₀ ⁻¹ᵁ P.U i) (_ : ⊤ ≤ e₀ ⁻¹ᵁ M.U m)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => i)))
    (h₂ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => m)))
    (a : W),
    (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h₁).hom (w₁.s (n, fun _ => i)).val) =
      algebraMap W K' a * (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
        ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)

end GlobalTheory.SectionLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEndomorphismPowLevelComponentEqOneOfRelationStatement
section
open GlobalTheory.HTLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation : ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : Fin n → (M →* M)) (c : Fin n → ℤ_[l]), ∑ i, c i • Tate.map l (φ i) = 0 → ∀ (N : ℕ) (m : Fin n → ℤ), (∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N))) → ∀ t : Tate l M, ∏ i, φ i (t.lev N) ^ m i = 1 := by
  first | exact @GlobalTheory.TateRel.prod_pow_eq_one | exact GlobalTheory.TateRel.prod_pow_eq_one | (intros; apply GlobalTheory.TateRel.prod_pow_eq_one <;> assumption)
end

