module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostAdeleIso

theorem intAE_mul_mem (D : D7) {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem mem_intAE_iff_comm (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y ∈
      Formalism.L2.DIV.RInt D.host.F D.host.E := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem r hr =>
      obtain ⟨a, ha, x, rfl⟩ := hr
      have e : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
          (a ⊗ₜ[D.host.F] (x : D.host.E)) =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha
  · intro hw
    let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm
    have key : ∀ z ∈ Formalism.L2.DIV.RInt D.host.F D.host.E, c z ∈ intAE D := by
      intro z hz
      induction hz using Subring.closure_induction with
      | mem r hr =>
        rcases hr with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
        · exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), b, rfl⟩
        · exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | one =>
        rw [map_one]
        exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), 1, rfl⟩
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
      | mul a b _ _ ha hb => rw [map_mul]; exact intAE_mul_mem D ha hb
    have := key _ hw
    rwa [show c (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = y from
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply _] at this

theorem exists_finiteAdele_equiv : ∀ D : D7, ∃ ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E, (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) ∧ (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) ∧ (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) := by
  intro D
  obtain ⟨ι, h1, h2, -, h4⟩ :=
    GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv D.host.F D.host.E
  refine ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans ι,
    fun x => h1 x, fun y => (mem_intAE_iff_comm D y).trans (h2 _), fun a k P n h => h4 a k P n h⟩

end GlobalTheory.HostAdeleIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem adicCompletion_exists_approx_lt (L : Type) [Field L] [NumberField L]
    (P : HeightOneSpectrum (𝓞 L)) (y c : P.adicCompletion L) (hc : c ≠ 0) :
    ∃ k : L, Valued.v (y - algebraMap L (P.adicCompletion L) k) < Valued.v c := by
  have ho : IsOpen {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c} := by
    have h0 := (Valued.isOpen_ball (P.adicCompletion L)
      ((Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).restrict c)).preimage
        (continuous_sub_left y)
    simpa only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] using h0
  have hy : y ∈ {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c} := by
    show Valued.v (y - y) < Valued.v c
    rw [sub_self, map_zero]
    exact (Valuation.pos_iff _).2 hc
  obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) (K := L)
    (v := P)).exists_mem_open ho ⟨y, hy⟩
  exact ⟨k, hk⟩

private lemma valued_v_algebraMap_adicCompletion_foundation (L : Type) [Field L] [NumberField L]
    (P : HeightOneSpectrum (𝓞 L)) (k : L) :
    Valued.v (algebraMap L (P.adicCompletion L) k) = P.valuation L k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (v := P) k

theorem adicCompletion_exists_unit_approx (L : Type) [Field L] [NumberField L] (N : ℕ) (hN : 0 < N)
    (P : HeightOneSpectrum (𝓞 L)) (y : P.adicCompletion L) (hy : y ≠ 0) :
    ∃ k : Lˣ, Valued.v y = P.valuation L (k : L) ∧
      Valued.v (y - algebraMap L _ (k : L)) ≤ P.valuation L (N : L) * P.valuation L (k : L) ∧
      Valued.v (y - algebraMap L _ (k : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer L
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hN0 : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hN1 : P.valuation L (N : L) ≤ 1 := by
    simpa using P.valuation_le_one (K := L) (N : 𝓞 L)
  have he1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  set c := y * algebraMap L (P.adicCompletion L) ((N : L) * π) with hcdef
  have hc : c ≠ 0 := mul_ne_zero hy ((map_ne_zero _).2 (mul_ne_zero hN0 hπ0))
  obtain ⟨k₀, hk₀⟩ := adicCompletion_exists_approx_lt L P y c hc
  have hvc : Valued.v c = Valued.v y * (P.valuation L (N : L) * WithZero.exp (-1 : ℤ)) := by
    rw [hcdef, map_mul, valued_v_algebraMap_adicCompletion_foundation, map_mul, hπ]
  have hlt : Valued.v (y - algebraMap L _ k₀) < Valued.v y := by
    refine hk₀.trans_le ?_
    rw [hvc]
    exact mul_le_of_le_one_right' (mul_le_one' hN1 he1)
  have hyk : P.valuation L k₀ = Valued.v y := by
    rw [← valued_v_algebraMap_adicCompletion_foundation]
    apply Valuation.map_eq_of_sub_lt
    rwa [Valuation.map_sub_swap]
  have hk0 : k₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hyk
    exact hy ((Valuation.zero_iff _).1 hyk.symm)
  refine ⟨Units.mk0 k₀ hk0, ?_, ?_, ?_⟩
  · rw [Units.val_mk0, hyk]
  · rw [Units.val_mk0, hyk]
    refine (hk₀.trans_eq hvc).le.trans ?_
    rw [mul_comm (Valued.v y)]
    gcongr ?_ * _
    exact mul_le_of_le_one_right' he1
  · rw [Units.val_mk0, hyk]
    refine (hk₀.trans_eq hvc).le.trans ?_
    rw [mul_comm (Valued.v y)]
    gcongr ?_ * _
    exact mul_le_of_le_one_left' hN1

theorem finiteIdele_exists_local_approx :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N → ∀ x : (FiniteAdeleRing (𝓞 L) L)ˣ, ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (k : HeightOneSpectrum (𝓞 L) → Lˣ), (∀ P ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ P.valuation L (N : L) * P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k P : L)) ∧ ∀ P, P ∉ S → Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = 1 ∧ (N : 𝓞 L) ∉ P.asIdeal := by
  intro L _ _ N hN x
  obtain ⟨hx0, hx1⟩ := FiniteAdeleRing.isUnit_iff.1 x.isUnit
  choose k hk using fun P => adicCompletion_exists_unit_approx L N hN P _ (hx0 P)
  have hN0 : (N : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h2 : {P : HeightOneSpectrum (𝓞 L) | P.asIdeal ∣ Ideal.span {(N : 𝓞 L)}}.Finite :=
    Ideal.finite_factors (by simpa using hN0)
  have hfin := (Filter.eventually_cofinite.1 hx1).union h2
  refine ⟨hfin.toFinset, k, fun P _ => hk P, fun P hP => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hP
  obtain ⟨hP1, hP2⟩ := hP
  simp only [Set.mem_ofPred_eq, not_not] at hP1 hP2
  exact ⟨hP1, fun hmem => hP2 (Ideal.dvd_span_singleton.2 hmem)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeTranslateHalfPeriodSigmaStarPowEightMulEq
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.HalfPeriodValue

open Filter Topology

theorem U1_sgStar_pow_eight : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t : ℂ, t ∉ Λ → 2 * t ∈ Λ →
    U1 Λ t (sgStar Λ) 0 ^ 8 * ((wpF Λ t ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ t) = 1 := by
  intro Λ hΛ t ht h2t
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have laws := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  have hd : Differentiable ℂ (sgStar Λ) := laws.1.1
  have hd0 : deriv (sgStar Λ) 0 = 1 := laws.1.2.1
  have hz0 : sgStar Λ 0 = 0 := (laws.2.1 0).2 Λ.zero_mem
  have hzw : sgStar Λ (2 * t) = 0 := (laws.2.1 _).2 h2t
  have htL : t ∉ L.lattice := fun h => ht ((hL t).2 h)
  have hD0 : L.derivWeierstrassP t = 0 :=
    (GlobalTheory.derivWeierstrassP_eq_zero_iff L htL).2 (by rw [← two_mul]; exact (hL _).1 h2t)

  have hA : HasDerivAt (fun z => sgStar Λ (2 * z)) (deriv (sgStar Λ) (2 * t) * 2) t := by
    have := (hd (2 * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul (2 : ℂ))
    rw [mul_one] at this
    exact this
  have hB : HasDerivAt (fun z => -(L.derivWeierstrassP z) * sgStar Λ z ^ 4)
      (-(6 * L.weierstrassP t ^ 2 - L.g₂ / 2) * sgStar Λ t ^ 4 +
        -(L.derivWeierstrassP t) * ((4 : ℕ) * sgStar Λ t ^ (4 - 1) * deriv (sgStar Λ) t)) t :=
    (GlobalTheory.hasDerivAt_derivWeierstrassP L htL).neg.mul ((hd t).hasDerivAt.pow 4)
  have hev : (fun z => sgStar Λ (2 * z)) =ᶠ[𝓝 t] (fun z => -(L.derivWeierstrassP z) * sgStar Λ z ^ 4) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds htL] with z hz
    have hz' : z ∉ Λ := fun h => hz ((hL z).1 h)
    rw [GlobalTheory.SigmaDuplication.sgStar_two_mul hΛ hz', GlobalTheory.LatticeInvariants.wpD_eq hL z]
  have hu := hA.unique (hB.congr_of_eventuallyEq hev)
  rw [hD0] at hu

  set s : ℂ := if 2 * t / 2 ∈ Λ then 1 else -1 with hs
  have hfun : U1 Λ (2 * t) (sgStar Λ) = fun z => s * sgStar Λ z := funext (hΛ.sg_law h2t)
  have hE : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)))) := by fun_prop
  have hC : HasDerivAt (U1 Λ (2 * t) (sgStar Λ))
      (deriv (sgStar Λ) (0 + 2 * t) * Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ))) +
        sgStar Λ (0 + 2 * t) * deriv (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)))) 0) 0 :=
    ((hd _).hasDerivAt.comp_add_const 0 (2 * t)).mul (hE 0).hasDerivAt
  have hC' : HasDerivAt (U1 Λ (2 * t) (sgStar Λ)) (s * 1) 0 := by
    rw [hfun, ← hd0]; exact (hd 0).hasDerivAt.const_mul s
  have hv := hC.unique hC'
  rw [zero_add, hzw] at hv
  have hs2 : s ^ 2 = 1 := by rw [hs]; split_ifs <;> norm_num
  have hU : U1 Λ t (sgStar Λ) 0 = sgStar Λ t * Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) := by
    simp only [U1, zero_add]
    congr 1
    congr 1
    ring
  have hexp : Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ))) =
      Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) ^ 4 := by
    rw [← Complex.exp_nat_mul, map_mul, map_ofNat]
    congr 1
    push_cast
    ring
  rw [hexp] at hv
  have key : U1 Λ t (sgStar Λ) 0 ^ 4 * (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) = -2 * s := by
    rw [hU, mul_pow]
    linear_combination (Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) ^ 4) * hu - 2 * hv

  have hcub : 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
    have := L.derivWeierstrassP_sq t htL
    rw [hD0] at this
    linear_combination -this
  obtain ⟨hg2, hg3, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  rw [hg2, hg3, (hw t ht).1]
  linear_combination (1 / 4 : ℂ) * (U1 Λ t (sgStar Λ) 0 ^ 4 * (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) - 2 * s) * key
    + hs2 - 2 * L.weierstrassP t * U1 Λ t (sgStar Λ) 0 ^ 8 * hcub

end GlobalTheory.HalfPeriodValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormTangentDenominatorEqOneOfUnitDiscrDoubleStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_tangentDenominator_eq_one_of_unitDiscr_double : ∀ {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x y m : ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 → W.toAffine.Equation x y → ‖x‖ ≤ 1 → 2 * y + W.a₁ * x + W.a₃ ≠ 0 → m * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y → ‖m ^ 2 + W.a₁ * m - W.a₂ - 2 * x‖ ≤ 1 → ‖2 * y + W.a₁ * x + W.a₃‖ = 1 := by
  first | exact @GlobalTheory.ThetaPar.unit_of_double_integral | exact GlobalTheory.ThetaPar.unit_of_double_integral | (intros; apply GlobalTheory.ThetaPar.unit_of_double_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOrderParameterSeriesBounded
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter
open scoped Topology

noncomputable section

namespace GlobalTheory.ThetaOrderBdd
open GlobalTheory.ThetaTransl GlobalTheory.ThetaTranslDecomp

variable {Λ : AddSubgroup ℂ}

theorem ratio_add (hΛ : IsLat Λ) {G : ℂ → ℂ} {k : ℕ}
    (hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k)
    (z : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    G (z + l) / sgStar Λ (z + l) ^ k = G z / sgStar Λ z ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hlaw l hl z
  by_cases hz : z ∈ Λ
  · rw [(hΛ.sg_eq_zero z).2 hz, (hΛ.sg_eq_zero _).2 (add_mem hz hl), zero_pow hk.ne']
    simp
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have h1 : sgStar Λ (z + l) ≠ 0 := (hΛ.sg_eq_zero _).not.2 (fun h => hz (by simpa using sub_mem h hl))
  rw [div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h0)]
  exact hlaw l hl z

theorem exists_decomp_gen : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (k : ℕ) (G : ℂ → ℂ), Differentiable ℂ G →
    (∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k) →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), k ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - k) * G z =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  intro Λ hΛ k G hG hlaw v hv
  obtain ⟨L, h⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hσ := hΛ.differentiable
  have hS := hΛ.differentiable_sqTh v
  have hT : Continuous (sqThD Λ v) := by
    have h1 := hσ.deriv.continuous
    have h2 := hS.deriv.continuous
    have h3 := hσ.continuous
    have h4 := hS.continuous
    unfold sqThD
    fun_prop
  have hc : ∀ z, z ∉ L.lattice →
      ContinuousAt (fun z => G z / sgStar Λ z ^ k) z := fun z hz =>
    (hG z).continuousAt.div ((hσ z).continuousAt.pow k)
      (pow_ne_zero _ ((hΛ.sg_eq_zero z).not.2 ((h z).not.2 hz)))
  obtain ⟨A, B, hAB⟩ := GlobalTheory.EllipticPoles.no_pole_case L
    (g := fun z => G z / sgStar Λ z ^ k)
    (fun a => (hG.analyticAt a).meromorphicAt.div ((hσ.analyticAt a).meromorphicAt.pow k))
    (fun a ha => ⟨_, (hc a ha).tendsto.mono_left nhdsWithin_le_nhds⟩)
    (fun z l hl => ratio_add hΛ hlaw z ((h l).2 hl))
  have hAB' : ∀ z, z ∉ L.lattice → G z / sgStar Λ z ^ k =
      A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    intro z hz
    have h1 := (L.analyticOnNhd_weierstrassP z hz).continuousAt
    have h2 := (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt
    have h3 : ContinuousAt (fun z => A.eval (L.weierstrassP z) +
        B.eval (L.weierstrassP z) * L.derivWeierstrassP z) z :=
      (A.continuous.continuousAt.comp h1).add ((B.continuous.continuousAt.comp h1).mul h2)
    exact tendsto_nhds_unique_of_eventuallyEq ((hc z hz).tendsto.mono_left nhdsWithin_le_nhds)
      (h3.tendsto.mono_left nhdsWithin_le_nhds) (hAB z)
  set A' := Polynomial.taylor (wpF Λ v) A with hA'
  set B' := Polynomial.taylor (wpF Λ v) B with hB'
  obtain ⟨I, hI⟩ : ∃ I, I = A'.natDegree + B'.natDegree + k := ⟨_, rfl⟩
  refine ⟨I, A'.coeff, B'.coeff, by omega, fun z => ?_⟩
  have h3 := hσ.continuous
  have h4 := hS.continuous
  have h5 := hG.continuous
  refine congrFun (Continuous.ext_on hΛ.dense_compl
    (f := fun z => sgStar Λ z ^ (2 * I + 3 - k) * G z)
    (g := fun z => ∑ i ∈ Finset.range (I + 1),
      A'.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
      ∑ j ∈ Finset.range (I + 1),
        B'.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z))
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  have hz' : z ∉ L.lattice := (h z).not.1 hz
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have e := hAB' z hz'
  rw [← Polynomial.taylor_eval_sub (wpF Λ v) A, ← Polynomial.taylor_eval_sub (wpF Λ v) B,
    ← hA', ← hB', Polynomial.eval_eq_sum_range' (n := I + 1) (p := A') (by omega),
    Polynomial.eval_eq_sum_range' (n := I + 1) (p := B') (by omega),
    div_eq_iff (pow_ne_zero _ h0)] at e
  beta_reduce
  rw [e, mul_left_comm, ← pow_add, Nat.sub_add_cancel (by omega), sqThD_eq hΛ L h hv hz,
    hΛ.sqTh_eq hv hz, GlobalTheory.OddTheta.wpF_eq L Λ h z, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun i hi => ?_
  all_goals
    obtain ⟨m, rfl⟩ : ∃ m, I = i + m := Nat.exists_eq_add_of_le (by simpa [Nat.lt_succ_iff] using hi)
    rw [Nat.add_sub_cancel_left, mul_pow]
    ring


set_option maxHeartbeats 800000 in
theorem order_bdd : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
    ∀ (k : ℕ) (G : ℂ → ℂ), AlgEnt G →
      (∀ ω ∈ g.abelian₂, ∀ z, G (z + ω) * sgStar g.abelian₂ z ^ k = G z * sgStar g.abelian₂ (z + ω) ^ k) →
      ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU G = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B := by
  intro p _ g hok hlat' h2 h3 hdisc hsg v hv hwv k G hG hlaw
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg v hv hwv
  have gS : GoodAt g 2 (sqTh g.abelian₂ v) := ⟨hSa, lineSer g.wq⁻¹ (xAt g v),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := GlobalTheory.ThetaTransl.CubeSer.sqThD_atU p g hok hlat' h2 h3 hdisc hsg v hv hwv
  have gT : GoodAt g 3 (sqThD g.abelian₂ v) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := exists_decomp_gen g.abelian₂ hlat' k G hG.1 hlaw v hv
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ v z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ v z ^ (j : ℕ) * sqThD g.abelian₂ v z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hG (2 * I + 3 - k) 1
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - k) * G z ^ 1 = ∑ j, c j * φ j z := by
    intro z
    rw [pow_one, hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := GlobalTheory.TranslLin.transl_lin p g _ φ c _ hEa (fun j => (gφ j).1) hEq
  choose B hB hBe using fun j => (gφ j).2
  have hS : BddSer (∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j) :=
    bdd_sum _ _ fun j _ => bdd_mul (bdd_C _) (hB j)
  rw [hEe, hsgU, pow_one] at hlin
  simp only [hBe] at hlin
  set Bk : PowerSeries ℂ_[p] := (e ^ k)⁻¹ * g.atU G with hBk
  have hGe : g.atU G = e ^ k * Bk := by
    rw [hBk, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [map_pow, he0, one_pow]; exact one_ne_zero),
      one_mul]
  rw [hGe] at hlin
  set K := 2 * I + 3 - k with hKd
  have hK : K + k = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ j, PowerSeries.C (lamC g.lam (a' j)) * (e ^ (2 * I + 3) * B j) =
      e ^ (2 * I + 3) * ∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e ^ k * Bk) =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * Bk)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨Bk, ⟨C0, fun n => ?_⟩, hGe⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaOrderBdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslatePowerSeriesPowBoundedCoeffsOfTorsiStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslatePowerSeries_pow_boundedCoeffs_of_torsion : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∀ N : ℕ, 0 < N → (N : ℂ) * t ∈ g.abelian₂ →
      GlobalTheory.EvenTheta.BddSer (GlobalTheory.ThetaTransl.tau g t ^ N) := by
  first | exact @GlobalTheory.ThetaTransl.tau_pow_bdd | exact GlobalTheory.ThetaTransl.tau_pow_bdd | (intros; apply GlobalTheory.ThetaTransl.tau_pow_bdd <;> assumption)
end

