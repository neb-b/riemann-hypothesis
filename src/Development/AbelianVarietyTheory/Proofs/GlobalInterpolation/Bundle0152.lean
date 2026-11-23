module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStandardIsometryFourthPowerSplitPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0034
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0148
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatioOfUnfolding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassCountBoundParamsLambdaConstructedPoints
section
namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

theorem h_la_all (𝒜 : FamClass) : H_la 𝒜 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ => ⟨Fm.x1 + 1, fun x hx i => GlobalTheory.famP_La_nonneg _ Fm x (by linarith) i⟩⟩⟩

theorem classCountBound_all_classes (𝒜 : FamClass) : ClassCountBoundAllPoints 𝒜 :=
  GlobalTheory.ColClassNumber.classNumber_closed (W1 𝒜)

theorem classCountBound_paramsLambda_constructedPoints : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), R0.ClassCountBoundAtConstructedPoints Q Lk ∧ R0.LambdaConditionAtConstructedPoints Q Lk := by
  intro Bd Q Lk
  refine ⟨?_, ?_⟩
  · apply Row.of_sel
    intros
    exact classCountBound_all_classes _
  · apply Row.of_sel
    intros
    exact h_la_all _

end GlobalTheory.Fc.R0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaBaseVectorTranslatesIntegral
section
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_of_analytic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ}
    (h : AnalyticOnNhd ℂ f Set.univ) : ContDiff ℂ ⊤ f :=
  contDiffOn_univ.1 (h.contDiffOn uniqueDiffOn_univ)

theorem contDiff_opU_one (L : PeriodPair) (s : ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.F.opU L s f) := by
  have hd : Differentiable ℂ (Formalism.L2.Th1.F.opU L s f) := by
    have h1 : Differentiable ℂ (fun z : ℂ => f (z + s)) := hf.comp (differentiable_id.add_const s)
    have h2 : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z s
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L s s / 2)) := by
      unfold Formalism.L2.Th1.F.herm
      fun_prop
    exact h1.mul h2
  exact hd.contDiff

theorem norm_sqrt_inv {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (hm : Nat.Coprime m q) :
    ‖ι (((Real.sqrt m : ℝ) : ℂ)⁻¹)‖ = 1 := by
  have h1 : (((Real.sqrt m : ℝ) : ℂ)) ^ 2 = (m : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg m)]; simp
  have h2 : ‖ι ((Real.sqrt m : ℝ) : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_natCast]
    exact GlobalTheory.MomOne.Basic.norm_nat_eq_one hm.symm
  have h3 : ‖ι ((Real.sqrt m : ℝ) : ℂ)‖ = 1 := by
    have := norm_nonneg (ι ((Real.sqrt m : ℝ) : ℂ))
    nlinarith [sq_nonneg (‖ι ((Real.sqrt m : ℝ) : ℂ)‖ - 1), sq_nonneg (‖ι ((Real.sqrt m : ℝ) : ℂ)‖ + 1)]
  rw [map_inv₀, norm_inv, h3, inv_one]

theorem norm_root {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) :
    ‖ι z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm).1 (by rw [← norm_pow, ← map_pow, hz, map_one, norm_one])

theorem translates_latInt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (t : D.what₂.Tau → ℂ) (n : ℕ), Nat.Coprime n q → (n : ℂ) • t ∈ B.lamM → LatInt ι (Ω / ι δ₀) B.lamM (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
  intro D cc δ B hcc hδ q _ hq2 hjac hcop ι δ₀ θ Ω hPer t n hn hnt
  obtain ⟨g, e, hS, hidx, he, hten⟩ := _root_.GlobalTheory.CmThetaMoment.isomStd D cc δ B hcc hδ q hq2 hjac hcop ι

  have hmem : B.thMM ∈ Formalism.L2.Th1.H.Th (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))
      (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))) B.lamM :=
    (thM_spec B.L B.ω₀ B.cq B.lamM B.gC B.kappa (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) B.kappa_ne_zero).1
  have hUs : ContDiff ℂ ⊤ (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) :=
    contDiff_of_analytic (Formalism.L2.Th1.H.opUAnalytic (D.what₂.Tau → ℂ) _ t B.thMM hmem.1)
  have hthd : Differentiable ℂ B.th0 := (Formalism.L2.Th1.F.th0Basic B.L B.ω₀ hS.per hS.half).1

  obtain ⟨S, hSr⟩ := (Formalism.L2.Th1.H.repsExist _ _ _ hS.idx₁).1
  have hshape := Formalism.L2.Th1.H.quadraticSemicharacter_identity_reformulated₂ B.L B.ω₀ D.what₂.Tau (hOne B.L D.what₂.Tau) B.lamM _ _ g hS e B.thMM hten S hSr t
  have hidxC : Nat.Coprime (Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
      (Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) q :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hidx).symm
  set Im := Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM) with hIm
  set St := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hSt
  set idx := Formalism.L2.Th1.H.relIdx St Im with hidxdef
  set v : Fin 4 × D.what₂.Tau → ℂ := g (fun w => t w.2) with hv
  set ω : ℂ_[q] := Ω / ι δ₀ with hω
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : q = 1 := by simpa using hn
    exact (Fact.out : q.Prime).one_lt.ne' h1

  have hnv : (n : ℂ) • v ∈ Im := by
    refine AddSubgroup.mem_map.2 ⟨(n : ℂ) • (fun w : Fin 4 × D.what₂.Tau => t w.2), fun a => hnt, ?_⟩
    show g ((n : ℂ) • fun w : Fin 4 × D.what₂.Tau => t w.2) = (n : ℂ) • v
    rw [map_smul]

  have hord : ∀ x ∈ S, ∀ w, ((n * idx : ℕ) : ℂ) * (v w + x w) ∈ B.L.lattice := by
    intro x hx w
    have h1 : (n : ℂ) • (v + x) ∈ Im := by
      rw [smul_add]
      refine add_mem hnv ?_
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hSr.1 x hx) n
    have h2 := Formalism.L2.Th1.H.relIdx_smul_mem St Im h1
    have h3 := ((AddSubgroup.mem_pi Set.univ).1 h2) w (Set.mem_univ _)
    have e1 : ((n * idx : ℕ) : ℂ) * (v w + x w) = (((idx : ℕ) : ℂ) • (n : ℂ) • (v + x)) w := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      push_cast
      ring
    rw [e1]
    exact h3
  have hNq : Nat.Coprime (n * idx) q := Nat.Coprime.mul_left hn hidxC

  have hfac : ∀ x ∈ S, ∀ w,
      LatInt ι ω St (fun y : Fin 4 × D.what₂.Tau → ℂ => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) := by
    intro x hx w
    refine _root_.GlobalTheory.MomN.latInt_pull q ι ℂ (Fin 4 × D.what₂.Tau → ℂ) ω (lamOf D cc δ) St
      (ContinuousLinearMap.proj w) _ (contDiff_opU_one B.L _ hthd) ?_
      (_root_.GlobalTheory.MomN.latInt_opU_of_coprime D cc δ B hcc hδ q hq2 hjac hcop ι δ₀ θ Ω hPer _ (n * idx) hNq (hord x hx w))
    intro y hy
    refine ⟨1, Nat.coprime_one_left q, ?_⟩
    rw [one_smul, ← B.lat]
    exact ((AddSubgroup.mem_pi Set.univ).1 hy) w (Set.mem_univ _)
  have hcd : ∀ (x : Fin 4 × D.what₂.Tau → ℂ) (w : Fin 4 × D.what₂.Tau),
      ContDiff ℂ ⊤ (fun y : Fin 4 × D.what₂.Tau → ℂ => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) :=
    fun x w => (contDiff_opU_one B.L _ hthd).comp (contDiff_apply ℂ (fun _ => ℂ) w)
  have hprod : ∀ x : Fin 4 × D.what₂.Tau → ℂ, ContDiff ℂ ⊤ (fun y : Fin 4 × D.what₂.Tau → ℂ =>
      ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) :=
    fun x => contDiff_prod fun w _ => hcd x w

  have hP : ∀ x ∈ S, LatInt ι ω St (fun y : Fin 4 × D.what₂.Tau → ℂ =>
      ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) := fun x hx =>
    (_root_.GlobalTheory.MomN.latInt_prod_sum q ι (Fin 4 × D.what₂.Tau → ℂ) ω St).1 (Fin 4 × D.what₂.Tau)
      (fun w y => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) (hcd x) (hfac x hx)

  set r : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun x => e * ((Real.sqrt idx : ℝ) : ℂ)⁻¹
      * Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) x
      * Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.H.altE (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ)) with hr
  have hrn : ∀ x ∈ S, ‖ι (r x)‖ ≤ 1 := by
    intro x hx
    have hx2 := hSr.1 x hx
    have hb : ‖ι (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) x)‖ = 1 := by
      rcases hS.betaSemi.1 x hx2 with h | h <;> simp [h]
    have hph : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I
        * (Formalism.L2.Th1.H.altE (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ)))‖ = 1 :=
      norm_root ι (m := 2 * n) (by omega)
        (Formalism.L2.Th1.H.phase_root_selfDual _ Im hS.selfDual n hnv hx2)
    simp only [hr, map_mul, norm_mul, he, norm_sqrt_inv ι hidxC, hb, hph, one_mul, le_refl]
  set G : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun y =>
    ∑ x ∈ S, r x * ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w) with hG
  have hGd : ContDiff ℂ ⊤ G :=
    ContDiff.sum fun x _ => contDiff_const.mul (hprod x)
  have hGl : LatInt ι ω St G :=
    (_root_.GlobalTheory.MomN.latInt_prod_sum q ι (Fin 4 × D.what₂.Tau → ℂ) ω St).2 _ S r _ (fun x _ => hprod x) hrn hP

  have hpull : LatInt ι ω (Formalism.L2.Th1.H.pow4 B.lamM)
      (fun z => G (LinearMap.toContinuousLinearMap (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) z)) := by
    refine _root_.GlobalTheory.MomN.latInt_pull q ι _ _ ω St _ _ G hGd ?_ hGl
    intro x hx
    refine ⟨idx, hidxC, ?_⟩
    have h1 : g x ∈ Im := AddSubgroup.mem_map.2 ⟨x, hx, rfl⟩
    have h2 := Formalism.L2.Th1.H.relIdx_smul_mem St Im h1
    rw [Nat.cast_smul_eq_nsmul] at h2
    exact h2
  have hfun : (fun z => G (LinearMap.toContinuousLinearMap (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) z))
      = Formalism.L2.Th1.H.tens4 (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
    funext z
    have hz := hshape (g z)
    rw [LinearEquiv.symm_apply_apply] at hz
    rw [hz]
    rfl
  rw [hfun] at hpull
  exact _root_.GlobalTheory.MomRoot.jets_root q ι D.what₂.Tau ω B.lamM _ hUs hpull

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DivisionSecondComplementConstructedPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.ClassTwoEntries

theorem divisionSecondComplement_constructedPoints : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), ClassTwoEntries.DivisionSecondComplementAtConstructedPoints Q Lk := by
  intro Bd Q Lk
  exact Row0.row (Row0.of_all (Q := Q) fun 𝒜 =>
    GlobalTheory.admissibleConstants_closed_under_sizeBounds (W3 𝒜) fun _ h => ⟨h.2.2.1, h.2.2.2⟩) Lk

end GlobalTheory.Fc.ClassTwoEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjIsAutFormU
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem exists_conj_isAutFormU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ)
    (φ : UA E n → ℂ) (hφ : IsAutFormU φ) :
    ∃ φ' : UA E n → ℂ, IsAutFormU φ' ∧ ∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g) := by
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.T.autFormDefiniteUnitary_eq_sum_polynomial_mul_autForm E n φ hφ
  choose p' hp' hpp using fun i => _root_.GlobalTheory.UnitaryBC.exists_conj_polyFun E n σ (p i) (hpe i).1
  obtain ⟨hD, -, -, a, b, -, -, hab, -⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨φ', hc, hl, hk, hv⟩ := GlobalTheory.T.exists_definiteUnitary_function_polynomial_mul_smooth E n m p' (fun i g => σ (e i g.1)) hp' (fun i => by
    refine ⟨
      { carrier := {k : finU (E := E) (n := n) | RU E n k (e i) = e i}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }, ?_, ?_⟩
    · exact (hpe i).2.level
    · intro u hu g
      exact congrArg σ (congrFun (show RU E n u (e i) = e i from hu) g.1))
  have key : ∀ γ ∈ ratU E n, ∀ x : UA E n, cInf x = cInf γ → φ' x = σ (φ x) := by
    intro γ hγ x hx
    have h1 : cInf (b x).1 = cInf γ := by
      rw [← hx]
      conv_rhs => rw [hab x, map_mul, show cInf (a x).1 = 1 from (a x).2, one_mul]
    conv_lhs => rw [hab x, hv]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [hab x, hdec, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hpp i γ hγ _ h1]
  refine ⟨φ', ⟨hc, fun γ hγ g => ?_, hl, hk⟩, fun g hg => key 1 (one_mem _) g (by rw [map_one]; exact hg)⟩
  have hc2 : Continuous fun x => φ' (γ * x) := hc.comp (continuous_const.mul continuous_id)
  refine congrFun (Continuous.ext_on hD hc2 hc ?_) g
  rintro _ ⟨δ, hδ, u, hu, rfl⟩
  have hu' : cInf u = 1 := hu
  change φ' (γ * (δ * u)) = φ' (δ * u)
  rw [key (γ * δ) (mul_mem hγ hδ) _ (by simp only [map_mul, hu', mul_one]),
    key δ hδ _ (by simp only [map_mul, hu', mul_one]), hφ.left γ hγ]

end GlobalTheory.UnitaryBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatio
section
namespace GlobalTheory.VolRatioFromSecondClause

theorem volumeRatio : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1b2 F E σ M J) → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D :=
  fun hSW D =>
    GlobalTheory.VolRatioUnfold.volumeRatio_of_unfolding GlobalTheory.LatticeDensityClosed.selfDualLatticeDensity
      GlobalTheory.RealPlaceMeasuresProof.realPlaceMeasures GlobalTheory.DensityProductClosed.eulerProductOfDensities
      GlobalTheory.VolIndepClosed.volIndep GlobalTheory.UnitPerpObj.unitVectorPerp GlobalTheory.UnfoldingObj.unfolding hSW D

end GlobalTheory.VolRatioFromSecondClause
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatioUpPositiveLine
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VolRatioUp

theorem volRatio_up : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK →
    (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) →
    D.vol U / D.vol W = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E (P + Q + 1) := by
  intro D hT h2 W P Q hW hWs hPQ U hU hUs
  have hUr : U.rank = P + Q + 1 := by
    have := Formalism.BasicNotions.sig_sum U hU D.host.φ₀
    rw [hUs] at this
    simp only at this
    omega
  have hWr : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hWs] at this
    exact this.symm
  obtain ⟨x, -, W', ι, -, -, hW'ok, hW's, hratio⟩ :=
    h2 U (P + 1) Q hU hUs (by omega) true (by simp)
  have hW's' : ∀ τ, W'.sig τ = (P, Q) := fun τ => by
    have := hW's τ
    simpa using this
  have hW'r : W'.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W' hW'ok D.host.φ₀
    rw [hW's'] at this
    exact this.symm
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D W W' hW hW'ok (by rw [hWr, hW'r])
    (fun τ => by rw [hWs, hW's'])
  have hvol : D.vol W = D.vol W' :=
    (GlobalTheory.VolIndepClosed.volIndep D).2.2 hT W W' P Q ⟨hW, hWs⟩ ⟨hW'ok, hW's'⟩ φ hφ
  rw [hvol, hratio, hUr]

end GlobalTheory.VolRatioUp
end

