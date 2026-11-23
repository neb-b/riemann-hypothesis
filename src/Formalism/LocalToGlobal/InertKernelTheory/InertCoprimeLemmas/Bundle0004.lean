module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0010
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0008
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0003

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMCoord
section
noncomputable section

namespace Formalism.L2.KerInert

namespace MMCoord

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def inclCL (D : D7) : (D.what₂.Tau → ℂ) →L[ℂ] VC D 1 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v τ _ _ => v τ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem inclCL_apply (v : D.what₂.Tau → ℂ) : inclCL D v = fun τ _ _ => v τ := rfl

theorem translate_theta_coordinates (B : Base D cc δ) (s₁ v : D.what₂.Tau → ℂ) :
    U D B.tor (fun τ _ _ => s₁ τ) (B.thZero 1 1) (fun τ _ _ => v τ) =
      Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) s₁ B.thMM v := by
  have hA : Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  have hT : B.tor.abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := rfl
  simp only [U, Formalism.MainNotions.TaylorLogMetric.Hf, Base.thZero, tensPow, Formalism.L2.Th1.H.opU, Formalism.L2.Th1.H.matH, LinearMap.mk₂'ₛₗ_apply, hOne,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.univ_unique, Finset.sum_singleton,
    Finset.prod_singleton, hT, hA]
  congr 1
  have e1 : ∀ w : D.what₂.Tau → ℂ, ∑ x, w x * ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (s₁ x) =
      (∑ x, w x * (starRingEnd ℂ) (s₁ x)) / ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) := fun w => by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e1]

theorem u_incl (B : Base D cc δ) (s : VC D 1 1) (v : D.what₂.Tau → ℂ) :
    U D B.tor s (B.thZero 1 1) (inclCL D v) =
      Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM v := by
  have hs : s = fun τ _ _ => s τ 0 0 := by
    funext τ i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  have h := translate_theta_coordinates B (fun τ => s τ 0 0) v
  rw [← hs] at h
  exact h

def projM (D : D7) : Matrix D.what₂.Tau (D.what₂.Tau × Fin 1 × Fin 1) ℂ :=
  Matrix.of fun τ k => if k = (τ, 0, 0) then 1 else 0

theorem projM_mulVec (w : D.what₂.Tau × Fin 1 × Fin 1 → ℂ) : (projM D).mulVec w = fun τ => w (τ, 0, 0) := by
  funext τ
  simp [projM, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_eq']

theorem flat_eq (w : D.what₂.Tau × Fin 1 × Fin 1 → ℂ) :
    Formalism.L2.AlgTh.flat D.what₂.Tau 1 1 w = inclCL D ((projM D).mulVec w) := by
  rw [projM_mulVec, inclCL_apply]
  funext τ i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  rfl

theorem linSubst_projM (T : MvPowerSeries D.what₂.Tau ℂ) :
    Formalism.L2.Th1.H.linSubst (projM D) T =
      MvPowerSeries.subst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) T := by
  unfold Formalism.L2.Th1.H.linSubst
  congr 1
  funext τ
  simp [projM, apply_ite MvPowerSeries.C, ite_mul, Finset.sum_ite_eq']

theorem map_subst_liftT {p : ℕ} [Fact p.Prime] (h : ℂ →+* ℂ_[p]) (T : MvPowerSeries D.what₂.Tau ℂ) :
    MvPowerSeries.map h (MvPowerSeries.subst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) T) =
      liftT D (MvPowerSeries.map h T) := by
  have ha : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
      (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) :=
    MvPowerSeries.HasSubst.X_comp (fun τ : D.what₂.Tau => ((τ, 0, 0) : D.what₂.Tau × Fin 1 × Fin 1))
  rw [MvPowerSeries.map_subst ha]
  unfold liftT
  congr 1
  funext τ
  simp [MvPowerSeries.map_X]

end MMCoord

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical MMCoord

theorem coordinates_one_theta_algebraic : CoordTieA := by
  intro D cc δ B _ _ p _ lam ι hι s
  refine ⟨fun hG => ?_, fun hs => ?_⟩
  · have hgG : Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM =
        fun v => U D B.tor s (B.thZero 1 1) (inclCL D v) := funext fun v => (u_incl B s v).symm
    have hg0 : AnalyticAt ℂ
        (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM) 0 := by
      rw [hgG]
      exact (hG.1 _ trivial).comp ((inclCL D).analyticAt 0)
    have hfun : (fun z => U D B.tor s (B.thZero 1 1) (Formalism.L2.AlgTh.flat D.what₂.Tau 1 1 z)) =
        fun w => Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM
          ((projM D).mulVec w) := by
      funext w
      rw [flat_eq, hgG]
    rw [power_series_embedding D 1 1 p lam ι hι _ hG.2, IntTens.taylorSer_eq_taylorMv _ hG.1, hfun,
      Formalism.L2.Th1.H.taylorMvComp _ _ (projM D) _ hg0, linSubst_projM]
    exact map_subst_liftT ι.toRingHom _
  · obtain ⟨n, hn, hcop, hmem⟩ := hs
    have h0 := B.lat0OK 1 1
    unfold Base.Lat0OK at h0
    rw [h0] at hmem
    refine ⟨n, hn, fun hd => ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hcop.symm) hd, ?_⟩
    have h00 : (fun τ => (n • s) τ 0 0) ∈ B.lamM := hmem 0 0
    convert h00 using 1
    funext τ
    simp [nsmul_eq_mul]

theorem coordTie_of (h : CoordTieA) (hz : AlgZero) : CoordTie := by
  intro D cc δ B hcc hδ p _ hp hin lam ι hι s hs
  obtain ⟨h1, h2⟩ := h D cc δ B hcc hδ p lam ι hι s
  exact ⟨h1 (hz D cc δ B hcc hδ p hp hin 1 1 s hs), h2 hs⟩

theorem coordTie_of_algZero (hz : AlgZero) : CoordTie := coordTie_of coordinates_one_theta_algebraic hz

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMReadS
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

open ParameterChangeLemmas IntegralOrthonormalChange

theorem change_of_parameters_const_scale : ReadChangeS := by
  intro D p _ hp lam Λ C wq ph h Uu κ hph0 h0 hhi h1 hlog hUu hexp r v e F hInt
  obtain ⟨g, g0, gI, hg⟩ := exists_inv h h0 hhi h1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨S, hSi⟩ : ∃ S : Fin r → MvPowerSeries D.what₂.Tau ℂ_[p],
      ∀ i, S i = PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p]) h :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S', hS'i⟩ : ∃ S' : D.what₂.Tau → MvPowerSeries (Fin r) ℂ_[p],
      ∀ j, S' j = PowerSeries.subst (MvPowerSeries.X (e j) : MvPowerSeries (Fin r) ℂ_[p]) g :=
    ⟨_, fun _ => rfl⟩
  have hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 := fun i => by rw [hSi]; exact constantCoeff_inVar_eq_zero _ h h0
  have hS'0 : ∀ j, MvPowerSeries.constantCoeff (S' j) = 0 := fun j => by rw [hS'i]; exact constantCoeff_inVar_eq_zero _ g g0
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  have hS's : MvPowerSeries.HasSubst S' := MvPowerSeries.hasSubst_of_constantCoeff_zero hS'0
  have hh : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' g0
  have hl0 := flog_constantCoeff (C • wModel lam Λ) wq

  have hA : MvPowerSeries.subst S (atLogV D lam Λ C wq v (liftT D F)) =
      ReadTh1 p (fun τ j => κ * v (e j) (τ, 0, 0)) F := by
    have hXfl : ∀ i : Fin r, MvPowerSeries.constantCoeff (PowerSeries.subst
        (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) = 0 :=
      fun i => constantCoeff_inVar_eq_zero i _ hl0
    have hΦ : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin 1 × Fin 1 =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i k) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hXfl]
    have hΦ' : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i (τ, 0, 0)) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hXfl]
    have hL : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun τ => MvPowerSeries.constantCoeff_X _)
    unfold atLogV liftT ReadTh1
    try dsimp only
    rw [MvPowerSeries.subst_comp_subst_apply hL hΦ]
    simp only [MvPowerSeries.subst_X hΦ]
    rw [MvPowerSeries.subst_comp_subst_apply hΦ' hSs]
    congr 1
    funext τ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hSs, map_sum]
    simp only [map_mul, AlgHom.commutes, MvPowerSeries.coe_substAlgHom, subst_single_var S hSs]
    refine (Fintype.sum_equiv e _ _ fun j => ?_).symm
    rw [hSi, e.symm_apply_apply, ← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X j)]
    unfold Formalism.InvariantFactorPaths.G7.at1
    have key := congrArg (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p])) hlog
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X j), PowerSeries.subst_mul (PowerSeries.HasSubst.X j),
      PowerSeries.subst_C, PowerSeries.subst_C] at key
    have hid : ∀ x : ℂ_[p], algebraMap ℂ_[p] ℂ_[p] x = x := fun _ => rfl
    simp only [MvPowerSeries.algebraMap_apply, hid] at key ⊢
    first
      | linear_combination (MvPowerSeries.C (v (e j) (τ, 0, 0)) : MvPowerSeries D.what₂.Tau ℂ_[p]) * key
      | linear_combination (-(MvPowerSeries.C (v (e j) (τ, 0, 0)) : MvPowerSeries D.what₂.Tau ℂ_[p])) * key

  have hB : MvPowerSeries.subst S (ePh lam Λ C wq r) =
      (∏ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) Uu) *
        Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries D.what₂.Tau ℂ_[p]) := by
    have hfac : ∀ i : Fin r, MvPowerSeries.subst S
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (ePhi1 lam Λ C wq))⁻¹ =
        PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p])
          (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p])) := by
      intro i
      rw [← subst_inv _ (MvPowerSeries.constantCoeff_X i) (ePhi1 lam Λ C wq), subst_single_var S hSs, hSi,
        ← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X _), hexp]
    unfold ePh
    rw [if_neg hp2, ← MvPowerSeries.coe_substAlgHom hSs, map_prod]
    simp only [MvPowerSeries.coe_substAlgHom, hfac]
    rw [Fintype.prod_equiv e.symm
      (fun i => PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p])
        (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p])))
      (fun j => PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p])
        (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p]))) (fun _ => rfl)]
    simp only [PowerSeries.subst_mul (PowerSeries.HasSubst.X _)]
    rw [Finset.prod_mul_distrib]
    congr 1
    have hph : ∀ j : D.what₂.Tau, MvPowerSeries.constantCoeff
        (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) ph) = 0 :=
      fun j => constantCoeff_inVar_eq_zero j ph hph0
    change _ = Formalism.L2.Th1.C.mvExp (∑ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) ph)
    rw [Formalism.L2.Th1.C.mvExp_sum _ _ (fun j _ => hph j)]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact Formalism.L2.Th1.C.subst_mvExp hph0 (MvPowerSeries.constantCoeff_X j)

  have hSG : IntegralMv (MvPowerSeries.subst S (atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r)) := by
    rw [← MvPowerSeries.coe_substAlgHom hSs, map_mul, MvPowerSeries.coe_substAlgHom, hA, hB]
    have hInt' : IntegralMv (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries D.what₂.Tau ℂ_[p]) *
        ReadTh1 p (fun τ j => κ * v (e j) (τ, 0, 0)) F) := hInt
    have hU : IntegralMv (∏ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) Uu) :=
      integral_prod _ _ fun j _ => integral_subst_single_variable j Uu hUu
    have := integral_mul hU hInt'
    convert this using 1
    ring

  have hback : MvPowerSeries.subst S' (MvPowerSeries.subst S
      (atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r)) =
      atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r := by
    rw [MvPowerSeries.subst_comp_subst_apply hSs hS's]
    have hid : (fun i => MvPowerSeries.subst S' (S i)) = MvPowerSeries.X := by
      funext i
      rw [hSi, subst_single_var S' hS's, hS'i, e.apply_symm_apply,
        ← PowerSeries.subst_comp_subst_apply hgs (PowerSeries.HasSubst.X i), hg,
        PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
    rw [hid, MvPowerSeries.subst_self]
    rfl
  rw [← hback]
  exact integral_subst S' hS'0 (fun j => by rw [hS'i]; exact integral_subst_single_variable _ g gI) hSG

end Formalism.L2.KerInert
end
end

