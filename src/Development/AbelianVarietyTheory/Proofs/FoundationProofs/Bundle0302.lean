module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosed
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_mul_int_left (χ : kˣ →* ℂˣ) {x y : k} (hx : valuation k x ≤ 1) (hy : Triv χ y) :
    Triv χ (x * y) :=
  triv_mono χ y (x * y) (by rw [map_mul]; exact mul_le_of_le_one_left' hx) hy

theorem triv_mul_int_right (χ : kˣ →* ℂˣ) {x y : k} (hy : valuation k y ≤ 1) (hx : Triv χ x) :
    Triv χ (x * y) := by
  rw [mul_comm]; exact triv_mul_int_left χ hy hx

theorem grp_mul {n : ℕ} (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) {a b : GL (Fin n) k}
    (ha : a ∈ grp ψ) (hb : b ∈ grp ψ) : a * b ∈ grp ψ := by
  refine ⟨(KO k (Fin n)).mul_mem ha.1 hb.1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
    (triv_zero _) (fun l _ => ?_)
  rcases le_or_gt l i with hli | hil
  ·
    have h1 : Triv (ψ l / ψ j) (b.val l j) := hb.2 l j (lt_of_le_of_lt hli hij)
    have h2 : Triv (ψ i / ψ j) (b.val l j) := hψ l i j j hli hij.le le_rfl _ h1
    exact triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) h2
  · rcases lt_or_ge l j with hlj | hjl
    · have h1 : Triv (ψ i / ψ l) (a.val i l * b.val l j) :=
        triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) (ha.2 i l hil)
      have h2 : Triv (ψ l / ψ j) (a.val i l * b.val l j) :=
        triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) (hb.2 l j hlj)
      have h3 := triv_mul _ _ _ h1 h2
      rwa [div_mul_div_cancel] at h3
    · have h1 : Triv (ψ i / ψ l) (a.val i l) := ha.2 i l hil
      have h2 : Triv (ψ i / ψ j) (a.val i l) := hψ i i j l le_rfl hij.le hjl _ h1
      exact triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) h2

theorem grp_mul_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, a * b ∈ grp ψ :=
  fun _ _ _ _ _ _ ψ hψ _ ha _ hb => grp_mul ψ hψ ha hb

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarAdditionFormulaPadicModelParameter
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SigmaAdd

open PowerSeries

def gap {R τ : Type} [CommRing R] (s T : PowerSeries R) (x y : MvPowerSeries τ R) : MvPowerSeries τ R :=
  subst (x + y) s * subst (x - y) s - (subst x s * subst x s * subst y T - subst y s * subst y s * subst x T)

theorem mv_subst_subst {R σ τ : Type} [CommRing R] {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b)
    {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries R) :
    MvPowerSeries.subst b (subst a f : MvPowerSeries σ R) = subst (MvPowerSeries.subst b a) f := by
  have has : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply has hb]
  rfl

theorem subst_gap {R τ : Type} [CommRing R] (s T : PowerSeries R) {b : Fin 3 → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (gap s T (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) R) =
      gap s T (b 0) (b 1) := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have hp : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have hm : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  simp only [gap, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_mul hb, mv_subst_subst hb h0,
    mv_subst_subst hb h1, mv_subst_subst hb hp, mv_subst_subst hb hm, MvPowerSeries.subst_add hb,
    MvPowerSeries.subst_X hb]

theorem map_gap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (s T : PowerSeries R) :
    MvPowerSeries.map φ (gap s T (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) R) =
      gap (PowerSeries.map φ s) (PowerSeries.map φ T) (MvPowerSeries.X 0) (MvPowerSeries.X 1) := by
  have e : ∀ (a : MvPowerSeries (Fin 3) R), MvPowerSeries.constantCoeff a = 0 → ∀ f : PowerSeries R,
      MvPowerSeries.map φ (subst a f) = subst (MvPowerSeries.map φ a) (PowerSeries.map φ f) :=
    fun a ha f => PowerSeries.map_subst (HasSubst.of_constantCoeff_zero ha) f
  simp only [gap, map_sub, map_mul]
  rw [e _ (by simp), e _ (by simp), e _ (by simp), e _ (by simp), e _ (by simp), e _ (by simp)]
  simp only [map_add (f := _), map_sub, MvPowerSeries.map_X]

theorem add_entire {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z w : ℂ) :
    sgStar Λ (z + w) * sgStar Λ (z - w) =
      sgStar Λ z * sgStar Λ z * sqTh Λ v w - sgStar Λ w * sgStar Λ w * sqTh Λ v z := by
  have h1 := (h.differentiable_sqTh v).continuous
  have h3 := h.differentiable.continuous
  refine congrFun (Continuous.ext_on h.dense_compl
    (f := fun z => sgStar Λ (z + w) * sgStar Λ (z - w))
    (g := fun z => sgStar Λ z * sgStar Λ z * sqTh Λ v w - sgStar Λ w * sgStar Λ w * sqTh Λ v z)
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  beta_reduce
  have h0 := (h.sg_eq_zero z).not.2 hz
  have e : sgStar Λ (z + w) * sgStar Λ (z - w) = sgStar Λ z ^ 2 * sqTh Λ z w := by
    rw [sqTh]; field_simp
  rw [e, h.sqTh_sub hz hv w, h.sqTh_eq hv hz]
  ring

theorem tay_mul {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) :
    PowerSeries.mk (coef1 fun z => F z * G z) = PowerSeries.mk (coef1 F) * PowerSeries.mk (coef1 G) := by
  ext n
  simp only [coeff_mul, coeff_mk, GlobalTheory.SerTransport.taylorCoeff_mul_entire hF hG]

theorem tay_add {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) :
    PowerSeries.mk (coef1 fun z => F z + G z) = PowerSeries.mk (coef1 F) + PowerSeries.mk (coef1 G) := by
  ext n
  simp only [map_add (f := _), coeff_mk, GlobalTheory.SerTransport.taylorCoeff_add_entire hF hG]

theorem tay_scale {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) :
    (subst (C c * X : PowerSeries ℂ) (PowerSeries.mk (coef1 F)) : PowerSeries ℂ) =
      PowerSeries.mk (coef1 fun z => F (c * z)) := by
  rw [← smul_eq_C_mul, ← rescale_eq_subst]
  ext n
  simp only [coeff_rescale, coeff_mk, GlobalTheory.SerTransport.taylorCoeff_scale_entire hF]

theorem gap_taylor {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    (gap (PowerSeries.mk (coef1 (sgStar Λ))) (PowerSeries.mk (coef1 (sqTh Λ v)))
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ) = 0 := by
  refine GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines ℂ _ fun t => ?_
  have hb : MvPowerSeries.HasSubst (fun i => (C (t i) * X : PowerSeries ℂ)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      rw [map_mul]; exact mul_eq_zero_of_right _ (PowerSeries.constantCoeff_X (R := ℂ))
  have hs := h.differentiable
  have hT := h.differentiable_sqTh v
  refine (subst_gap _ _ hb).trans ?_
  have key : (subst (C (t 0 + t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) : PowerSeries ℂ) *
      subst (C (t 0 - t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) +
      subst (C (t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 0) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sqTh Λ v))) =
      subst (C (t 0) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 0) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sqTh Λ v))) := by
    simp only [tay_scale hs, tay_scale hT]
    rw [← tay_mul (by fun_prop) (by fun_prop), ← tay_mul (by fun_prop) (by fun_prop),
      ← tay_mul (by fun_prop) (by fun_prop), ← tay_mul (by fun_prop) (by fun_prop),
      ← tay_mul (by fun_prop) (by fun_prop), ← tay_add (by fun_prop) (by fun_prop)]
    congr 2
    funext z
    rw [add_mul, sub_mul, add_entire h hv]
    ring
  rw [map_add (f := _), map_sub, add_mul, sub_mul] at key
  unfold gap
  linear_combination key

variable {p : ℕ} [Fact p.Prime]

theorem sigmaAdditionFormula_padicTransfer_of_algebraicTaylor (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G)
    (h : (gap (PowerSeries.mk (coef1 F)) (PowerSeries.mk (coef1 G))
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ) = 0) :
    (gap (GL3Theta.ser1 lam F) (GL3Theta.ser1 lam G)
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
  have e : ∀ {H : ℂ → ℂ}, AlgEnt H → ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 H) = PowerSeries.map (algebraMap Qbar ℂ) S := fun {H} hH =>
    ⟨PowerSeries.mk fun n => ⟨coef1 H n, hH.2 n⟩, by
      ext n; rw [coeff_map, coeff_mk, coeff_mk]; rfl⟩
  obtain ⟨s, hs⟩ := e hF
  obtain ⟨T, hT⟩ := e hG
  rw [hs, hT, ← map_gap] at h
  have h' : (gap s T (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) Qbar) = 0 := by
    ext d
    have := congrArg (MvPowerSeries.coeff d) h
    rw [MvPowerSeries.coeff_map, map_zero] at this
    simpa using this
  rw [Param.theta_series_map_coefficients lam _ _ hs, Param.theta_series_map_coefficients lam _ _ hT, ← map_gap, h', map_zero]

theorem const_subst {τ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (subst a f : MvPowerSeries τ ℂ_[p]) = 0 := by
  obtain ⟨f', rfl⟩ := X_dvd_iff.2 hf
  have hs := HasSubst.of_constantCoeff_zero ha
  rw [subst_mul hs, subst_X hs, map_mul, ha, zero_mul]

theorem subst_inv {τ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : constantCoeff f ≠ 0) :
    (subst a f⁻¹ : MvPowerSeries τ ℂ_[p]) = (subst a f : MvPowerSeries τ ℂ_[p])⁻¹ := by
  have hs := HasSubst.of_constantCoeff_zero ha
  have e : (subst a f⁻¹ : MvPowerSeries τ ℂ_[p]) * subst a f = 1 := by
    rw [← subst_mul hs, PowerSeries.inv_mul_cancel _ hf, ← coe_substAlgHom hs, map_one]
  refine (MvPowerSeries.eq_inv_iff_mul_eq_one fun h0 => ?_).2 e
  have := congrArg MvPowerSeries.constantCoeff e
  rw [map_mul, h0, mul_zero, map_one] at this
  exact zero_ne_one this

theorem subst_atU (g : GL3Theta.G1 p) {τ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (F : ℂ → ℂ) : (subst a (g.atU F) : MvPowerSeries τ ℂ_[p]) =
      subst (MvPowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.lg a) (GL3Theta.ser1 g.lam F) := by
  have hs := HasSubst.of_constantCoeff_zero ha
  rw [GlobalTheory.SerTransport.atU_eq, subst_comp_subst_apply
    (HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g _)) hs, subst_mul hs, subst_C]
  rfl

theorem lg_pt (g : GL3Theta.G1 p) (hg : g.Ok) {τ : Type} {x : MvPowerSeries τ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hs := HasSubst.of_constantCoeff_zero hx
  rw [GL3Theta.G1.lg, GL3Theta.G1.pt, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hg.2.2.1) hs,
    hg.2.2.2, subst_X hs]

theorem sigma_add_param : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicSigmaAdditionFormula D := by
  intro D p _ cc δ g hA
  obtain ⟨hq, hL, h2, h3, hσ, v, hv, hw⟩ := GlobalTheory.FrobStick.AtData.atData D p cc δ g hA
  have hok : g.Ok := hA.2.2.2.2
  obtain ⟨aT, eT⟩ := Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  have eS := GlobalTheory.FrobStick.sgStar_atU g hL hσ
  have hgap := sigmaAdditionFormula_padicTransfer_of_algebraicTaylor g.lam hσ aT (gap_taylor hL hv)
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (GL3Theta.Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hl : ∀ i : Fin 2, MvPowerSeries.constantCoeff (g.lg (GL3Theta.Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => const_subst (hX i) (GlobalTheory.SerTransport.const_l g)
  have hb : MvPowerSeries.HasSubst (![MvPowerSeries.C ε * g.lg (GL3Theta.Xv 0), MvPowerSeries.C ε * g.lg (GL3Theta.Xv 1), 0] :
      Fin 3 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i <;> simp [hl]
  have k := subst_gap (GL3Theta.ser1 g.lam (sgStar g.abelian₂)) (GL3Theta.ser1 g.lam (sqTh g.abelian₂ v)) hb
  rw [hgap, ← MvPowerSeries.coe_substAlgHom hb, map_zero] at k
  have hp0 : MvPowerSeries.constantCoeff
      (g.lg (GL3Theta.Xv 0) + g.lg (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [hl]
  have hm0 : MvPowerSeries.constantCoeff
      (g.lg (GL3Theta.Xv 0) - g.lg (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [hl]
  have hp : MvPowerSeries.constantCoeff (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    const_subst hp0 hok.2.2.1
  have hm : MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    const_subst hm0 hok.2.2.1
  have kp := subst_atU g hp (sgStar g.abelian₂)
  have km := subst_atU g hm (sgStar g.abelian₂)
  rw [show g.lg (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = _ from lg_pt g hok hp0] at kp
  rw [show g.lg (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = _ from lg_pt g hok hm0] at km
  simp only [gap, Matrix.cons_val_zero, Matrix.cons_val_one, ← mul_add, ← mul_sub] at k
  rw [← kp, ← km, ← subst_atU g (hX 0), ← subst_atU g (hX 0), ← subst_atU g (hX 1), ← subst_atU g (hX 1),
    eS, eT] at k
  have sS : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      (subst a (C ε * X * ePhi1 g.lam g.abelian₂ g.C g.wq) : MvPowerSeries (Fin 2) ℂ_[p]) =
        MvPowerSeries.C ε * a * subst a (ePhi1 g.lam g.abelian₂ g.C g.wq) := fun a ha => by
    have hs := HasSubst.of_constantCoeff_zero ha
    rw [subst_mul hs, subst_mul hs, subst_X hs, subst_C]
  have hwq : constantCoeff g.wq ≠ 0 := by
    have e := congrArg constantCoeff (show g.wq = _ from hq)
    simp only [map_add (f := _), map_mul, map_pow, map_one, constantCoeff_X] at e
    rw [e]
    simp
  have sT : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      (subst a (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v)) : MvPowerSeries (Fin 2) ℂ_[p]) =
        subst a (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 *
          ((subst a g.wq : MvPowerSeries (Fin 2) ℂ_[p])⁻¹ - MvPowerSeries.C (xAt g v) * a ^ 2) := fun a ha => by
    have hs := HasSubst.of_constantCoeff_zero ha
    rw [lineSer, subst_mul hs, subst_pow hs, subst_sub hs, subst_mul hs, subst_pow hs, subst_X hs, subst_C,
      subst_inv ha hwq]
  rw [sS _ hp, sS _ hm, sS _ (hX 0), sS _ (hX 1), sT _ (hX 0), sT _ (hX 1)] at k
  have hne : (MvPowerSeries.C ε : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 ≠ 0 := by
    refine pow_ne_zero 2 fun h => Units.ne_zero g.C.u⁻¹ ?_
    have e := congrArg MvPowerSeries.constantCoeff h
    rwa [MvPowerSeries.constantCoeff_C, map_zero] at e
  apply mul_left_cancel₀ hne
  linear_combination -k

end GlobalTheory.SigmaAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestVectorAdelicPairTranslatesMovedLatticeVacuum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.Expand
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ArchFree.expand

theorem om_expand : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  intro D cc δ t0 Q hC _ P g g' L₁ L₁' hL hL'
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · exact ⟨0, 0, Fin.elim0, Fin.elim0, fun h => absurd h (by omega)⟩
  have hSD : ∀ (N : ℕ) (g : GA D N) L, Moves D (g : GL (Fin N) (AE D)) L → SD D L := by
    intro N g L hL
    obtain ⟨Lt, h1, -⟩ := _root_.GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    have : L = Lt g := by
      ext x; rw [hL x, (h1 g).1 x]
    rw [this]; exact (h1 g).2
  have hSD0 : ∀ N : ℕ, SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := _root_.GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hW, hint, -⟩ := _root_.GlobalTheory.ThetaLine.theta_line D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ hC P.a P.d (La0 D (tor0 D cc δ) P.a P.d)
    (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  obtain ⟨-, -, -, -, -, -, hq⟩ := _root_.GlobalTheory.ThetaLine.theta_line D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ hC P.a P.d (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨_, _, hSD _ g _ hL, hSD _ g' _ hL', rfl⟩)
  have he0 : P.e0 ∈ Th D (tor0 D cc δ) (stdL D P.a) (stdL D P.d) := P.vac.1
  have hfix : ∀ x ∈ La0 D (tor0 D cc δ) P.a P.d, Wd D (tor0 D cc δ) x P.e0 = P.e0 := by
    intro x hx
    rw [hW x hx]; funext z; exact he0.2 x hx z
  have heT : P.e0 ∈ TT D (tor0 D cc δ) P.a P.d :=
    ⟨he0.1, 1, one_pos, fun x hx => by rw [one_nsmul]; exact hfix x hx⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := _root_.GlobalTheory.ArchFree.weilc.vacuum_under_adelic_pair D cc δ hC P.a P.d (P.d_even.mul_left _) P.e0 he0 P.W g g'
    L₁ L₁' hL hL'
  obtain ⟨k, r, z, hz, hr1, hr2, hF⟩ := P.pres
  have hT : ∀ i, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 ∈ TT D (tor0 D cc δ) P.a P.d := by
    intro i
    refine ⟨Wd_diff _ he0.1, Q, hQ, fun x hx => ?_⟩
    obtain ⟨m, hm⟩ := hint x hx _ (hz i)
    rw [Hf_nsmul_right, ← Hf_nsmul_left] at hm
    rw [Wd_comm _ _ m hm, hfix _ (nsmul_mem hx _)]
  have hQc : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQ.ne'
  have key : ∀ i, ∃ y : VC D P.a P.d, Q • y ∈ La D (tor0 D cc δ) L₁ L₁' ∧
      P.W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0) =
        Wd D (tor0 D cc δ) y (P.W.Om g g' P.e0) := by
    intro i
    obtain ⟨B, hB, h⟩ := approx_La (_root_.GlobalTheory.InducedType.induced_type D).1.1 _ _ hL hL' (hz i)
    obtain ⟨m, hm, hl⟩ := P.W.lift g g' ((Q : D.host.E)⁻¹ • B) P.e0 heT
    obtain ⟨B', h1, h2⟩ := h (m * Q) (by positivity)
    refine ⟨pt D (tor0 D cc δ) δ ((Q : D.host.E)⁻¹ • B'), ?_, ?_⟩
    · rw [pt_div, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hQc, one_smul]; exact h1
    · rw [← hl _ (closeTo_div hQ h2), pt_div, ← hB, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hQc, one_smul]
  choose y hy1 hy2 using key
  have hu : ∀ i, ∃ u : Qbar, (u : ℂ) = wdPh D (tor0 D cc δ) (y i) ∧ IsIntegral ℤ u ∧
      ∀ ρ : Qbar →+* ℂ, ‖ρ u‖ = 1 := by
    intro i
    obtain ⟨m, hm⟩ := hq _ (hy1 i)
    exact root_unity (by positivity) (wdPh_pow _ m hm)
  choose u hu1 hu2 hu3 using hu
  refine ⟨c, k, fun i => r i * u i, y, fun _ => ⟨hc1, hy1, fun i => ?_, fun ρ => ?_, ?_, hc3⟩⟩
  · rw [← mul_assoc]; exact (hr1 i).mul (hu2 i)
  · simpa only [map_mul, norm_mul, hu3, mul_one] using hr2 ρ
  · have hF' : P.F = ∑ i, (r i : ℂ) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 := by
      rw [hF]; funext w; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hF', (Om_sum P.W g g' Finset.univ _ _ hT).2]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hy2, hc2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.coe_mul, hu1]
    simp only [Wd, U]
    ring

end GlobalTheory.ArchFree.expand
end
end

