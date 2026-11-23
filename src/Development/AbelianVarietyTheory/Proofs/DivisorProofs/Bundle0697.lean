module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0682
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCoordsNonunit
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TangentIndep

theorem subst_nmul_eq (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) (n : ℕ) :
    subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g +
      ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := _root_.GlobalTheory.QLog.subst_nmul_eq R d μ hμ g n

theorem up_nmul_eq (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up S (nmul μ n) = nmul (up S μ) n := _root_.GlobalTheory.QLog.up_nmul R S d μ hμ n

theorem map_at2_eq (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (τ : Type)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    map (algebraMap R S) (at2 t u v) = at2 (map (algebraMap R S) t) (up S u) (up S v) := _root_.GlobalTheory.QLog.map_algebraMap_powerSeriesEvalTwoGroups R S d τ t u v hu hv

theorem constantCoeff_subst_eq (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (g : MvPowerSeries σ R) :
    constantCoeff (subst a g) = constantCoeff g := _root_.GlobalTheory.constantCoeff_subst_of_constantCoeff_zero R σ τ a ha g

theorem coeff_powerSeriesEvalTwoGroups_mem_ideal (R : Type) [CommRing R] (d : ℕ) (τ : Type) (I : Ideal R)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (ht : ∀ α, coeff α t ∈ I) (α : τ →₀ ℕ) : coeff α (at2 t u v) ∈ I := _root_.GlobalTheory.IdealAt2.coeff_powerSeriesEvalTwoGroups_mem_ideal R d τ I t u v hu hv ht α

theorem ev_mem_smul_add (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (n : ℕ) (I : Ideal O) (h : MvPowerSeries (Fin d) O) (hh : ∀ α, coeff α h ∈ I) :
    ∃ a ∈ I • (⊤ : Submodule O (G.A n)), ∃ b : G.A n, c.ev n h = a + (p : G.A n) * b := _root_.GlobalTheory.Chart.ev_mem_ideal_smul_add_p p O G d c n I h hh

theorem ev_subst_nmul (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n k : ℕ) (h : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := _root_.GlobalTheory.EvMul.ev_subst_nmul p O G d c n k h

theorem repr_mem_maximalIdeal (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M))
    (l : Module.Dual O M) (hl : ∀ w, l w ∈ IsLocalRing.maximalIdeal O) (j : Fin k) :
    lb.repr l j ∈ IsLocalRing.maximalIdeal O := _root_.GlobalTheory.dualBasis_coord_mem_maximalIdeal O M k lb l hl j

theorem nmul_const (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have h : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
      simp only [nmul]; rw [Function.iterate_succ_apply']
    rw [h, op, at2, constantCoeff_subst_eq R _ _ _ (fun x => by cases x with | inl a => exact ih a | inr a => simp), hμ]

theorem powerSeriesEvalTwoGroups_add (R : Type) [CommRing R] (d : ℕ) (τ : Type) (a b : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (a + b) u v = at2 a u v + at2 b u v := by
  unfold at2
  exact subst_add (hasSubst_of_constantCoeff_zero fun x => by cases x with | inl i => exact hu i | inr i => exact hv i) a b

theorem constantCoeff_formalGroupLawCoboundaryOne (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) :
    constantCoeff (cob1 μ g) = - constantCoeff g := by
  simp only [cob1, inL, inR, map_sub]
  rw [constantCoeff_subst_eq R _ _ _ hμ, constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _), constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _)]
  ring

theorem QL_comb (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) E) (a : O) (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) :
    QL μ ⊤ (f + algebraMap O E a • g) := by
  have hμE : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by simp [up, hμ]
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · simp [hf.1, hg.1]
  · obtain ⟨x, -, hx⟩ := hf.2.1 i
    obtain ⟨y, -, hy⟩ := hg.2.1 i
    refine ⟨x + a * y, trivial, ?_⟩
    simp only [lin] at hx hy ⊢
    rw [map_add (f := _), coeff_smul, hx, hy, map_add (f := _), map_mul]
  · obtain ⟨x, -, hx⟩ := hf.2.2 α
    obtain ⟨y, -, hy⟩ := hg.2.2 α
    refine ⟨x + a * y, trivial, ?_⟩
    rw [formalCoboundary_add hμE, formalCoboundary_smul hμE, map_add (f := _), coeff_smul, hx, hy, map_add (f := _), map_mul]

theorem tangent_coords_nonunit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∀ (b : Fin k → O) (s : MvPowerSeries (Fin d) O), (∀ α, ∃ o : O, ¬IsUnit o ∧ coeff α (cob1 (up E c.μ) (comb (Sum.elim 0 b) e) - map (algebraMap O E) (cob1 c.μ s)) = algebraMap O E o) → ∀ j, ¬IsUnit (b j) := by
  intro p _ K _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQL hLie hlog b s hH j
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hmem : ∀ o : O, o ∈ IsLocalRing.maximalIdeal O ↔ ¬IsUnit o := fun o => IsLocalRing.mem_maximalIdeal o
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := (hmem _).2 Fact.out
  have hμ : ∀ i, constantCoeff (c.μ i) = 0 := c.isLaw.const
  let f := comb (Sum.elim 0 b) e
  let l : G.dual.Lie := ∑ j, b j • lb j
  have lin : ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' →
      QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
    fun f g l l' a hf hg => (_root_.GlobalTheory.LieLin.main p K v O hv G d c E hF f g l l' a hf hg).1
  have h00 : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
    have := lin _ _ _ _ (-1) (hLie j) (hLie j) (hQL _) (hQL _)
    simpa using this
  have hsum : ∀ S : Finset (Fin k), QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) ∧
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) (∑ i ∈ S, b i • lb i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨?_, by simpa using h00⟩
      simpa using QL_comb O E d c.μ hμ _ _ (-1) (hQL (Sum.inr j)) (hQL (Sum.inr j))
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • lb a)]
      exact ⟨QL_comb O E d c.μ hμ _ _ (b a) ih.1 (hQL _), lin _ _ _ _ (b a) ih.2 (hLie a) ih.1 (hQL _)⟩
  have hf_eq : f = ∑ i, algebraMap O E (b i) • e (Sum.inr i) := by
    simp [f, comb, Fintype.sum_sum_type]
  have hfl : c.IsLie f l := by rw [hf_eq]; exact (hsum Finset.univ).2

  have hμE : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by simp [up, hμ]
  choose t ht using hH
  let T : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => t α
  have hT : ∀ α, coeff α T = t α := fun α => rfl
  have hcob : cob1 (up E c.μ) f = map (algebraMap O E) (cob1 c.μ s + T) := by
    ext α
    have h := (ht α).2
    rw [map_sub, sub_eq_iff_eq_add] at h
    rw [map_add (f := _), map_add (f := _), h]
    simp only [coeff_map, hT]
    ring
  have hf0 : constantCoeff f = algebraMap O E (constantCoeff s - t 0) := by
    have h := (ht 0).2
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, constantCoeff_formalGroupLawCoboundaryOne E d _ hμE, constantCoeff_map,
      constantCoeff_formalGroupLawCoboundaryOne O d _ hμ] at h
    rw [map_sub, ← h, map_neg]; ring
  have hnc := nmul_const O d c.μ hμ
  let s' : MvPowerSeries (Fin d) O := -C (constantCoeff s - t 0) -
    ∑ k ∈ Finset.range p, at2 (cob1 c.μ s + T) (nmul c.μ k) (fun i => X i)
  have hX : up E (fun i : Fin d => (X i : MvPowerSeries (Fin d) O)) = fun i => X i := by
    funext i; simp [up, map_X]
  have hs' : map (algebraMap O E) s' = defect c.μ (p ^ 1) f := by
    rw [defect, pow_one, up_nmul_eq O E d c.μ hμ, subst_nmul_eq E d _ hμE f p, hcob, hf0]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [s', map_sub, map_neg, map_sum, map_C]
    rw [Finset.sum_congr rfl (fun k _ => map_at2_eq O E d (Fin d) _ _ _ (hnc k) (fun i => constantCoeff_X i))]
    simp only [hX, up_nmul_eq O E d c.μ hμ]
    abel
  have hs'2 : s' = C (t 0) + (p : O) • s - subst (nmul c.μ p) s -
      ∑ k ∈ Finset.range p, at2 T (nmul c.μ k) (fun i => X i) := by
    rw [subst_nmul_eq O d c.μ hμ s p]
    simp only [s']
    rw [Finset.sum_congr rfl (fun k _ => powerSeriesEvalTwoGroups_add O d (Fin d) _ _ _ _ (hnc k) (fun i => constantCoeff_X i)),
      Finset.sum_add_distrib, map_sub]
    abel
  have key : ∀ w : G.dual.omega, l w ∈ IsLocalRing.maximalIdeal O := by
    intro w
    obtain ⟨φ₀, hφ₀⟩ := AugCot.d_surjective _ (w.1 1)
    set φ : CartierDual O (G.A 1) := φ₀ - algebraMap O _ (Coalgebra.counit (R := O) φ₀) with hφdef
    have hφd : PDiv.dUnit (R := O) φ = w.1 1 := by
      rw [hφdef, PDiv.dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact hφ₀
    have hφ1 : φ 1 = 0 := by
      rw [hφdef]
      simp [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]

    have hL := hfl.2 1 w φ s' hφd hs'
    have hA : ∀ r : O, φ (algebraMap O (G.A 1) r) = 0 := fun r => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hφ1, smul_zero]
    have hev : φ (c.ev 1 s') ∈ IsLocalRing.maximalIdeal O := by
      have h1 := G.mulBy_pow_self 1 (c.ev 1 s)
      rw [pow_one] at h1
      have hC : c.ev 1 (C (t 0)) = algebraMap O _ (t 0) := (c.ev 1).commutes (t 0)
      rw [hs'2]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_add (f := _), map_smul, map_sum, ev_subst_nmul p O G d c 1 p s, h1, hC]
      have hA' : ∀ r : O, φ.ofConv (algebraMap O (G.A 1) r) = 0 := hA
      rw [hA', hA', zero_add, sub_zero, smul_eq_mul]
      refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hpm) (Ideal.sum_mem _ fun k _ => ?_)
      obtain ⟨a, ha, b', hb'⟩ := ev_mem_smul_add p O G d c 1 (IsLocalRing.maximalIdeal O) _
        (coeff_powerSeriesEvalTwoGroups_mem_ideal O d (Fin d) _ T _ _ (hnc k) (fun i => constantCoeff_X i) (fun α => (hmem _).2 (ht α).1))
      rw [hb', map_add (f := _)]
      refine Ideal.add_mem _ ?_ ?_
      · have hle : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (G.A 1)) ≤
            Submodule.comap φ.ofConv (IsLocalRing.maximalIdeal O) :=
          Submodule.smul_le.2 fun r hr x _ => by
            rw [Submodule.mem_comap, map_smul, smul_eq_mul]
            exact Ideal.mul_mem_right _ _ hr
        exact hle ha
      · rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
        exact Ideal.mul_mem_right _ _ hpm
    obtain ⟨q, hq⟩ := hL
    have : l w = (p : O) ^ 1 * q + φ (c.ev 1 s') := by rw [← hq]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (by simpa using hpm)) hev
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p K v O hv G.dual
  have h6 := repr_mem_maximalIdeal O G.dual.omega k lb l key j
  have hrep : lb.repr l j = b j := by
    have : l = lb.equivFun.symm b := by rw [Module.Basis.equivFun_symm_apply]
    rw [← Module.Basis.equivFun_apply, this, LinearEquiv.apply_symm_apply]
  rw [hrep] at h6
  exact (hmem _).1 h6

end GlobalTheory.TangentIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCompChain
section
set_option autoImplicit false

open Filter Topology

namespace GlobalTheory.PeriodFamily

section
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)

theorem taylor_finset_sum_chain {ι : Type} (S : Finset ι) (f : ι → (I → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    taylor N t (fun z ↦ ∑ i ∈ S, f i z) = ∑ i ∈ S, taylor N t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (_root_.GlobalTheory.PeriodFamily.taylor_formal_properties N t).2.2.1 0
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [(_root_.GlobalTheory.PeriodFamily.taylor_formal_properties N t).1 (f i) (fun z ↦ ∑ i ∈ S, f i z) (hf i)
      (Finset.analyticAt_fun_sum S fun j _ ↦ hf j), ih]

theorem taylor_finset_prod_chain (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) {ι : Type} (S : Finset ι)
    (f : ι → (I → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    taylor N t (fun z ↦ ∏ i ∈ S, f i z) = ∏ i ∈ S, taylor N t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (_root_.GlobalTheory.PeriodFamily.taylor_formal_properties N t).2.2.1 1
  | insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    rw [_root_.GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero N t ht (f i) (fun z ↦ ∏ i ∈ S, f i z) (hf i)
      (Finset.analyticAt_fun_prod S fun j _ ↦ hf j), ih]

end

theorem taylor_comp_chain : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {K : Type} [Fintype K] [DecidableEq K] (Φ : (I → ℂ) → K → ℂ) (h : (K → ℂ) → ℂ), AnalyticAt ℂ Φ 0 → Φ 0 = 0 → AnalyticAt ℂ h 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (Φ z)) = GlobalTheory.PeriodFamily.taylor N (fun k ↦ GlobalTheory.PeriodFamily.taylor N t fun z ↦ Φ z k) h := by
  intro I _ _ D _ _ N t ht K _ _ Φ h hΦ h0 hh
  have hk : ∀ k, AnalyticAt ℂ (fun z ↦ Φ z k) 0 := fun k ↦ analyticAt_pi_iff.1 hΦ k
  have hhΦ : AnalyticAt ℂ (fun z ↦ h (Φ z)) 0 := AnalyticAt.comp (g := h) (f := Φ) (by rw [h0]; exact hh) hΦ
  have hprod : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ ∏ a, Φ z (s a)) 0 := fun k s ↦
    Finset.analyticAt_fun_prod _ fun a _ ↦ hk (s a)
  set c : (k : ℕ) → (Fin k → K) → ℂ := fun k s ↦
    (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k h 0 fun a ↦ Pi.single (s a) 1 with hc
  have hP : (fun z ↦ taylor N (Φ z) h) =
      fun z ↦ ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a) := by
    funext z
    simp only [taylor, smul_eq_mul, hc]
  have hterm : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ c k s * ∏ a, Φ z (s a)) 0 := fun k s ↦
    analyticAt_const.mul (hprod k s)
  have hin : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) 0 := fun k ↦
    Finset.analyticAt_fun_sum _ fun s _ ↦ hterm k s
  have hPa : AnalyticAt ℂ (fun z ↦ taylor N (Φ z) h) 0 := by
    rw [hP]
    exact Finset.analyticAt_fun_sum _ fun k _ ↦ hin k
  have hra : AnalyticAt ℂ (fun z ↦ h (Φ z) - taylor N (Φ z) h) 0 := hhΦ.sub hPa
  have htend : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have := hΦ.continuousAt.tendsto
    rwa [h0] at this
  have hO : Φ =O[𝓝 0] fun z : I → ℂ ↦ z := by
    have := hΦ.differentiableAt.isBigO_sub
    simpa [h0] using this
  have hr : (fun z ↦ h (Φ z) - taylor N (Φ z) h) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1) :=
    ((_root_.GlobalTheory.PeriodFamily.taylor_remainder_and_flat N h hh).1.comp_tendsto htend).trans (hO.norm_norm.pow (N + 1))
  have hz : taylor N t (fun z ↦ h (Φ z) - taylor N (Φ z) h) = 0 := (_root_.GlobalTheory.PeriodFamily.taylor_remainder_and_flat N _ hra).2 hr t
  have hsplit : (fun z ↦ h (Φ z)) = fun z ↦ (h (Φ z) - taylor N (Φ z) h) + taylor N (Φ z) h := by
    funext z; ring
  rw [hsplit, (_root_.GlobalTheory.PeriodFamily.taylor_formal_properties N t).1 _ _ hra hPa, hz, zero_add, hP,
    taylor_finset_sum_chain N t _ (fun k z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) hin]
  conv_rhs => rw [taylor]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [taylor_finset_sum_chain N t _ (fun s z ↦ c k s * ∏ a, Φ z (s a)) (hterm k)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(_root_.GlobalTheory.PeriodFamily.taylor_formal_properties N t).2.1 _ _ (hprod k s),
    taylor_finset_prod_chain N t ht _ (fun a z ↦ Φ z (s a)) fun a ↦ hk (s a)]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCoordAndEval
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_coord_of_nilpotent {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D]
    [Algebra ℂ D] (N : ℕ) (t : I → D) (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (i : I) :
    taylor N t (fun z ↦ z i) = t i := by
  have hd : (fun y : I → ℂ ↦ fderiv ℂ (fun z : I → ℂ ↦ z i) y) =
      fun _ ↦ ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i := by
    funext y
    exact (hasFDerivAt_apply i y).fderiv
  have h2 : ∀ (k : ℕ) (v : Fin (k + 1 + 1) → I → ℂ),
      iteratedFDeriv ℂ (k + 1 + 1) (fun z : I → ℂ ↦ z i) 0 v = 0 := by
    intro k v
    rw [iteratedFDeriv_succ_apply_right, hd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp
  have h1 : ∀ v : Fin 1 → I → ℂ, iteratedFDeriv ℂ 1 (fun z : I → ℂ ↦ z i) 0 v = v 0 i := by
    intro v
    rw [iteratedFDeriv_one_apply, congrFun hd 0]
    simp
  unfold taylor
  cases N with
  | zero =>
    have := ht fun _ ↦ i
    simp at this
    simp [this]
  | succ N =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [h2, mul_zero, zero_smul, Finset.sum_const_zero, zero_add, h1]
    rw [Finset.sum_eq_single (fun _ ↦ i)]
    · simp
    · intro s _ hs
      have : s 0 ≠ i := fun h ↦ hs (funext fun a ↦ by rw [Fin.fin_one_eq_zero a, h])
      simp [Pi.single_eq_of_ne' this]
    · simp

theorem taylor_coord_and_eval : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → (∀ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ z i) = t i) ∧ ∀ P : MvPolynomial I ℂ, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ MvPolynomial.eval z P) = MvPolynomial.aeval t P := by
  intro I _ _ D _ _ N t ht
  refine ⟨taylor_coord_of_nilpotent N t ht, fun P ↦ ?_⟩
  obtain ⟨hadd, -, hconst, -⟩ := _root_.GlobalTheory.PeriodFamily.taylor_formal_properties N t
  have hc : ∀ i, AnalyticAt ℂ (fun z : I → ℂ ↦ z i) 0 := fun i ↦
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i).analyticAt 0
  have han : ∀ Q : MvPolynomial I ℂ, AnalyticAt ℂ (fun z : I → ℂ ↦ MvPolynomial.eval z Q) 0 := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simpa using analyticAt_const
    | add p q hp hq => simpa using hp.fun_add hq
    | mul_X p i hp => simpa using hp.fun_mul (hc i)
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hconst a
  | add p q hp hq =>
    simp only [map_add (f := _)]
    rw [hadd _ _ (han p) (han q), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X]
    rw [_root_.GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero N t ht _ _ (han p) (hc i), hp, taylor_coord_of_nilpotent N t ht]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSubValueEqSumSqZeroVector
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem taylor_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → ∀ τ : (I → ℂ) → Fin g → ℂ, AnalyticAt ℂ τ 0 → ∃ n : Fin r → Fin g → R, (∀ j a, n j a ∈ J) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, taylor N (fun i ↦ ∑ j, m j i) (fun z ↦ τ z a) - algebraMap ℂ R (τ 0 a) = ∑ j, n j a := by
  intro I _ _ g R _ _ J N hJ r
  induction r with
  | zero =>
    intro m _ _ τ _
    refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun a => ?_⟩
    have h := (taylor_formal_properties N (fun i ↦ ∑ j : Fin 0, m j i)).2.2.2.2.2 (fun z ↦ τ z a)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    have : Set.range (fun _ : I => (0 : R)) ⊆ {0} := by
      rintro _ ⟨_, rfl⟩; rfl
    have hb : Ideal.span (Set.range (fun _ : I => (0 : R))) = ⊥ := by
      rw [Ideal.span_eq_bot]; rintro _ ⟨_, rfl⟩; rfl
    rw [hb, Ideal.mem_bot] at h
    exact h
  | succ r ih =>
    intro m hmJ hm τ hτ
    obtain ⟨n', hn'J, hn', hn'eq⟩ := ih (fun j => m (Fin.castSucc j)) (fun j i => hmJ _ i)
      (fun j i i' => hm _ i i') τ hτ
    set t : I → R := fun i => ∑ j : Fin r, m (Fin.castSucc j) i with ht
    set l : I → R := fun i => m (Fin.last r) i with hl
    let v : Fin g → R := fun a => ∑ i, taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i 1)) * l i
    have htJ : ∀ i, t i ∈ J := fun i => J.sum_mem fun j _ => hmJ _ i
    have hlJ : ∀ i, l i ∈ J := fun i => hmJ _ i
    have hspan : Ideal.span (Set.range t ∪ Set.range l) ≤ J := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact htJ i
      · exact hlJ i
    have hvJ : ∀ a, v a ∈ J := fun a => J.sum_mem fun i _ => J.mul_mem_left _ (hlJ i)
    have hv : ∀ a b, v a * v b = 0 := by
      intro a b
      simp only [v, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
      have := hm (Fin.last r) i' i
      calc _ = (taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z b) z (Pi.single i 1)) *
              taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i' 1))) * (l i' * l i) := by ring
        _ = 0 := by simp only [hl, this, mul_zero]
    refine ⟨Fin.snoc (α := fun _ => Fin g → R) n' v, ?_, ?_, ?_⟩
    · intro j a
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hvJ a
      · simpa using hn'J j a
    · intro j a b
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hv a b
      · simpa using hn' j a b
    · intro a
      have hfa : AnalyticAt ℂ (fun z ↦ τ z a) 0 :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) a).analyticAt (τ 0)).comp hτ
      have hsum : (fun i ↦ ∑ j : Fin (r + 1), m j i) = fun i => t i + l i := by
        funext i; simp only [ht, hl, Fin.sum_univ_castSucc]
      have hstep := taylor_add_of_mul_eq_zero N t l
        (fun s hs => hJ s fun a => hspan (hs a)) (fun i j => hm (Fin.last r) i j) _ hfa
      rw [hsum, hstep, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← hn'eq a]
      simp only [v, t]
      ring

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvalChar
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogPeriod

theorem theta_eval_char : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ (t : G.Tate) (n : ℕ) (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → (∀ i, ∃ N : ℕ, (p : F.B) ∣ z i ^ N) → ∀ E : MvPowerSeries (Fin d) F.B →ₐ[F.B] F.B, IsEval p z E → F.θ (E g) = zeta ε n ^ GlobalTheory.PDiv.digit n (epsPairing hε G t χ) := by
  intro p _ O _ _ _ _ ε hε F G d c χ g hg t n z hz hnil E hE
  haveI := F.frame.complete
  let Ev : MvPowerSeries (Fin d) O →ₐ[O] O := (t.pt n).comp (c.ev n)
  have hEv : IsEval p (fun i => F.θ (z i)) Ev := by
    refine ⟨fun i => ?_, fun m => ?_⟩
    · change t.pt n (c.ev n (X i)) = F.θ (z i)
      rw [(c.isEval n).1 i, hz]
    · obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun g hg => ?_⟩
      obtain ⟨w, hw⟩ := hN g hg
      refine ⟨t.pt n w, ?_⟩
      change t.pt n (c.ev n g) = _
      rw [hw, map_mul, map_pow, map_natCast]
  have h1 : F.θ (E g) = Ev (map F.θ g) :=
    ((_root_.GlobalTheory.CEval.continuous_eval p F.B F.B (Fin d) z hnil).2 E hE).2.2 O O F.θ F.θ Ev (fun _ => rfl) hEv g
  have h2 : Ev (map F.θ g) = t.pt n (charElem χ n) := by
    change t.pt n (c.ev n (map F.θ g)) = _
    rw [hg n]
  rw [h1, h2, ← GlobalTheory.PDivGroup.muRoot_pairing, ← GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing_smul hε,
    GlobalTheory.PDivGroup.muRoot_smul]
  unfold epsTate
  rw [GlobalTheory.PDivGroup.muRoot_muTate]

end GlobalTheory.QLogPeriod
end
end

