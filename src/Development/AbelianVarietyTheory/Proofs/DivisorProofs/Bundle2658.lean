module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSiegelChartOfPolarisedMonomialPeriodChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg

theorem hasChart_of_hasPolChart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o)
    (j : F.X ⟶ S) [IsOpenImmersion j] {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ)
    (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) (hn : n ≠ 0) (h : HasPolChart F s j e φ BD d x) :
    HasChart F s j e φ BD d x := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, ⟨hc, hz, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨hM, hX, hδ, hdef, hmon⟩, ha, hBD⟩ := h
  have hCN : IsCN R := ⟨inferInstance, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2, hc, hz⟩
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i h0
    have := ht.2 (Pi.single i 1) (by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
      simp [h0]) i
    simp at this
  have hsym : ∀ i y z, ((n : ℤ) • δ i) y z = ((n : ℤ) • δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, (mem_balForms_int.1 (hδ.mem i)) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hδ.nonneg i y)
  have hpos : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    exact ⟨i, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hi⟩
  obtain ⟨R', _, _, _, ρ, r, D, ε, hCN', hinj, hfin, hloc, hr, href, hmon'⟩ :=
    _root_.GlobalTheory.PolDeg.refine_monomial_of_polarised R Q m t (fun i => (n : ℤ) • δ i) hCN hmon ht.1 ht0 hsym hnn hpos
  obtain ⟨G', _, _, π, A, U, hU⟩ := hM.unif R' ρ hCN' hinj hfin D ε href
  let ϑ : Fin m → LinearMap.BilinForm ℤ D.toPre.X := fun i => pull ε.toIntLinearEquiv.toLinearMap (δ i)
  have hϑ : ∀ (k : ℤ) i, pull ε.toIntLinearEquiv.toLinearMap (k • δ i) = k • ϑ i := fun k i =>
    LinearMap.ext₂ fun y z => by simp [ϑ]
  refine ⟨R, inferInstance, inferInstance, b, ξ, m, t, R', inferInstance, inferInstance, inferInstance, ρ, r, G', inferInstance,
    inferInstance, π, D, A, U, ϑ, a, ⟨hc, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨⟨hCN'.1, inferInstance, hCN'.2.1, hCN'.2.2.1⟩, hCN'.2.2.2, hinj, hfin, hloc, hr⟩,
    ⟨hU, ?_, hδ.pull_equiv ε.toIntLinearEquiv, ?_⟩, fun i => ?_, hBD⟩
  · rw [LinearEquiv.finrank_eq ε.toIntLinearEquiv]; exact hX
  · convert hmon' using 2 with i
    rw [hϑ, ← mul_smul]
  · rw [ha i, ← hϑ, evalZ_pull φ ε.toIntLinearEquiv.surjective]

end GlobalTheory.PolDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GdegMetric

theorem coeff_eq_zero_of_const (N : ℕ) (γ : ℕ → ℝ) (K : ℝ)
    (h : ∀ c : ℕ, ∑ m ∈ Finset.range (N + 1), (c : ℝ) ^ m * γ m = K) {m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    γ m = 0 := by
  let P : Polynomial ℝ := ∑ j ∈ Finset.range (N + 1), Polynomial.C (γ j) * Polynomial.X ^ j
  have hP : P = Polynomial.C K := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.infinite_of_injective_forall_mem (f := fun c : ℕ => (c : ℝ)) Nat.cast_injective fun c => ?_
    simp only [Set.mem_ofPred_eq, P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h c]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e := congrArg (fun Q : Polynomial ℝ => Q.coeff m) hP
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] at e
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) m, if_pos (Finset.mem_range.2 (by omega)),
    if_neg (by omega)] at e
  exact e

theorem map_mul_add_pow {ι : Type} (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (A x y : MvPolynomial ι ℝ) (c : ℝ) (n : ℕ) :
    Φ (A * (MvPolynomial.C c * x + y) ^ n) =
      ∑ m ∈ Finset.range (n + 1), c ^ m * ((n.choose m : ℝ) * Φ (A * x ^ m * y ^ (n - m))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : A * ((MvPolynomial.C c * x) ^ m * y ^ (n - m) * (n.choose m : MvPolynomial ι ℝ)) =
      (c ^ m * (n.choose m : ℝ)) • (A * x ^ m * y ^ (n - m)) := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, map_natCast, mul_pow, ← map_pow]
    ring
  rw [e, map_smul, smul_eq_mul]
  ring

end GlobalTheory.GdegMetric

namespace GlobalTheory.GdegMetric

open MvPolynomial HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem lin_single' {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    (lin fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℝ)) = MvPolynomial.X i := by
  simp [lin, Pi.single_apply, apply_ite, ite_mul]

theorem isConj_const_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (c : ℝ) (σ σ' : k →+* ℂ) :
    (Weight.ofFun fun y => c * u σ y).IsConj (Weight.ofFun fun y => c * u σ' y) :=
  fun i y y' h hy => congrArg (c * ·) (hc σ σ' i y y' h hy)

theorem icls_fnB_sum {u v w : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu hc hv hd hw he) (e : ∀ σ y, w σ y = u σ y + v σ y) :
    (fnB w hw he).icls = (fnB u hu hc).icls + (fnB v hv hd).icls := by
  rw [← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]
  exact icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)

theorem icls_fnB_zsmul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (n : ℤ) :
    (fnB (fun σ y => (n : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _)).icls =
      n • (fnB u hu hc).icls := by
  have key (m : ℤ) := icls_fnB_sum (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y)
    (u := fun σ y => (m : ℝ) * u σ y)
    (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _)
    (isConj_const_mul hc _) fun σ y => by push_cast; ring
  induction n using Int.induction_on with
  | zero =>
    have := icls_fnB_sum (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y)
      (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc hu hc fun σ y => by push_cast; ring
    rw [zero_smul]
    exact right_eq_add.1 this
  | succ n ih => rw [key, ih, add_smul, one_smul]
  | pred n ih =>
    have := key (-(n : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [sub_smul, one_smul, ← ih, this, add_sub_cancel_right]

theorem chInt_raise_const (N : HermLB p) (t : ℝ) (hu : ∀ σ (y : CxPts p σ), CInfAt (fun _ => t) y) (hc) (D : ℕ)
    (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) :
    chInt (N.raise (fun _ _ => t) hu hc) D f = chInt N D f := by
  simp only [chInt, HermLB.raise, Weight.chernInt, Weight.chernPart_addFn_const]

end GlobalTheory.GdegMetric

namespace GlobalTheory.GdegMetric

open MvPolynomial HermLB

theorem gdeg_up : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p), gdeg (up L u) D = gdeg L D := by
  intro HC k _ S _ p D hX L u
  classical
  let one : ∀ σ : k →+* ℂ, CxPts p σ → ℝ := fun _ _ => 1
  have h1 : ∀ σ (y : CxPts p σ), CInfAt (one σ) y := fun σ y => cInfAt_const 1 y
  have hc1 : ∀ σ σ', (Weight.ofFun (one σ)).IsConj (Weight.ofFun (one σ')) := fun _ _ _ _ _ _ _ => rfl
  let T : HermLB p := fnB one h1 hc1
  let U : HermLB p := fnB u.u u.cInf u.conj
  let G : Fin 3 → HermLB p := ![T, L, U]
  obtain ⟨Φ, hΦ⟩ := ((HC.arExists k S p D hX).2 _ G).1
  let eA : Option (Fin 3) → Fin 3 := fun o => o.elim 2 id
  have hA : IsArFun (fun o : Option (Fin 3) => o.elim U G) D
      (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eA o) : MvPolynomial (Fin 3) ℝ)).toLinearMap) := by
    have := ((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 3)) (fun o => o.elim U G)
      (fun o => Pi.single (eA o) 1) fun o => by
        rcases o with _ | j
        · exact isometric_comb_single G 2
        · exact isometric_comb_single G j
    simpa only [lin_single'] using this
  let eB : Option (Fin 2) → Fin 3 := fun o => o.elim 0 Fin.succ
  have hB : IsArFun (fun o : Option (Fin 2) => o.elim T ![L, U]) D
      (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eB o) : MvPolynomial (Fin 3) ℝ)).toLinearMap) := by
    have := ((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 2)) (fun o => o.elim T ![L, U])
      (fun o => Pi.single (eB o) 1) fun o => by
        rcases o with _ | j
        · exact isometric_comb_single G 0
        · fin_cases j
          · exact isometric_comb_single G 1
          · exact isometric_comb_single G 2
    simpa only [lin_single'] using this
  have chA : ∀ c b : ℤ, Φ (X 2 * (C (c : ℝ) * X 0 + (X 1 + C (b : ℝ) * X 2)) ^ D) =
      1 / 2 * chInt (comb G ![c, 1, b]) D u.u := by
    intro c b
    have := HC.arChange k S p D hX (Fin 3) G u.u u.cInf u.conj _ hA ![c, 1, b]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [← this]
    congr 1
    simp [lin, Fin.sum_univ_three, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eA]
    ring
  have chB : ∀ b : ℤ, Φ (X 0 * (X 1 + C (b : ℝ) * X 2) ^ D) = 1 / 2 * gdeg (comb ![L, U] ![1, b]) D := by
    intro b
    have := HC.arChange k S p D hX (Fin 2) ![L, U] one h1 hc1 _ hB ![1, b]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [gdeg, ← this]
    congr 1
    simp [lin, Fin.sum_univ_two, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eB]

  have iso : ∀ c b : ℤ, (comb G ![c, 1, b]).Isometric ((comb ![L, U] ![1, b]).raise (fun _ _ => (c : ℝ) * 1)
      (fun σ y => cInfAt_const _ y) (fun _ _ _ _ _ _ _ => rfl)) := by
    intro c b
    refine Isometric.trans (icls_eq_iff.1 ?_) (isometric_tens_fnB _ _ _ _)
    rw [icls_tens]
    have e : (fnB (p := p) (fun _ _ => (c : ℝ) * 1) (fun σ y => cInfAt_const _ y)
        (fun _ _ _ _ _ _ _ => rfl)).icls = c • T.icls := icls_fnB_zsmul h1 hc1 c
    rw [e, icls_comb, icls_comb, Fin.sum_univ_three, Fin.sum_univ_two]
    simp [G]
    abel
  have hind : ∀ c b : ℤ, chInt (comb G ![c, 1, b]) D u.u = chInt (comb G ![0, 1, b]) D u.u := by
    intro c b
    rw [(iso c b).chInt_eq, (iso 0 b).chInt_eq]
    exact (chInt_raise_const _ _ _ _ _ _).trans (chInt_raise_const _ _ _ _ _ _).symm
  have i1 : (comb ![L, U] ![1, 1]).Isometric (up L u) := icls_eq_iff.1 (by
    rw [← icls_eq_iff.2 (isometric_tens_fnB L u.u u.cInf u.conj), icls_tens, icls_comb, Fin.sum_univ_two]
    simp [U])
  have i0 : (comb ![L, U] ![1, 0]).Isometric L := icls_eq_iff.1 (by
    rw [icls_comb, Fin.sum_univ_two]
    simp)
  rw [← i1.gdeg_eq, ← i0.gdeg_eq]
  have e1 := chB 1
  have e0 := chB 0
  cases D with
  | zero =>
    simp only [pow_zero, mul_one] at e1 e0
    linarith
  | succ d =>
    have s1 : ∀ b : ℤ, Φ (X 2 * X 0 * (X 1 + C (b : ℝ) * X 2) ^ d) = 0 := by
      intro b
      have h := coeff_eq_zero_of_const (d + 1)
        (fun m => ((d + 1).choose m : ℝ) * Φ (X 2 * X 0 ^ m * (X 1 + C (b : ℝ) * X 2) ^ (d + 1 - m)))
        (1 / 2 * chInt (comb G ![0, 1, b]) (d + 1) u.u) (fun c => by
          beta_reduce
          rw [← map_mul_add_pow, ← hind c b, ← chA c b]
          push_cast
          rfl) (le_refl 1) (by omega)
      simp only [Nat.choose_one_right, pow_one, Nat.add_sub_cancel] at h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h (by positivity)
      · exact h
    have s2 : ∀ m ≤ d, Φ (X 2 * X 0 * X 2 ^ m * X 1 ^ (d - m)) = 0 := by
      intro m hm
      have hs : ∀ c : ℕ, ∑ j ∈ Finset.range (d + 1),
          (c : ℝ) ^ j * ((d.choose j : ℝ) * Φ (X 2 * X 0 * X 2 ^ j * X 1 ^ (d - j))) = 0 := by
        intro c
        rw [← map_mul_add_pow]
        have := s1 c
        rw [add_comm] at this
        push_cast at this
        exact this
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · have := hs 0
        rw [Finset.sum_range_succ'] at this
        simpa using this
      · have h := coeff_eq_zero_of_const d _ 0 hs hm0 hm
        rcases mul_eq_zero.1 h with h | h
        · exact absurd h (by exact_mod_cast (Nat.choose_pos hm).ne')
        · exact h
    have ex := map_mul_add_pow Φ (X 0) (X 2) (X 1) 1 (d + 1)
    rw [Finset.sum_range_succ'] at ex
    have hz : ∀ i ∈ Finset.range (d + 1), (1 : ℝ) ^ (i + 1) * (((d + 1).choose (i + 1) : ℝ) *
        Φ (X 0 * X 2 ^ (i + 1) * X 1 ^ (d + 1 - (i + 1)))) = 0 := by
      intro i hi
      have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Nat.add_sub_add_right, show (X 0 * X 2 ^ (i + 1) * X 1 ^ (d - i) : MvPolynomial (Fin 3) ℝ) =
        X 2 * X 0 * X 2 ^ i * X 1 ^ (d - i) by ring, s2 i hi', mul_zero, mul_zero]
    rw [Finset.sum_eq_zero hz, zero_add] at ex
    have e1' : Φ (X 0 * (C 1 * X 2 + X 1) ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 1]) (d + 1) := by
      rw [← e1, add_comm]
      push_cast
      rfl
    have e0' : Φ (X 0 * X 1 ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 0]) (d + 1) := by
      rw [← e0]
      simp
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero] at ex
    linarith

end GlobalTheory.GdegMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFamilyWeierstrassTwist
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam

theorem famGL_coe_redGL (N : ℕ) (γ : SL(2, ℤ)) :
    ((redGL N γ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) := rfl

theorem famGL_vmul_gact (N : ℕ) (y : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) (γ : SL(2, ℤ)) :
    vmul y (gact N 1 α γ) = vact N (vmul y α) γ := by
  rw [gact_one, vact, vmul, vmul, vmul, Matrix.vecMul_vecMul, Units.val_mul]

theorem isFam_hfun_GL : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (y : Fin 2 → ZMod N) (κ : Emb F → ℕ), IsFam (gact N 1) (wt (2 * s) κ : ℕ) (fun α ↦ hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hF s N _ L hs hL y κ
  refine _root_.GlobalTheory.HilbFam.isFam_hfun_twist hE F hF s N L hs (Nat.pos_of_ne_zero (NeZero.ne N)) hL (GL (Fin 2) (ZMod N)) (gact N 1)
    (fun α ↦ (α : Matrix (Fin 2) (Fin 2) (ZMod N))) (fun α ↦ wB N (vmul y α)) κ ?_ ?_
  · intro α γ
    simp only [gact_one, Units.val_mul, famGL_coe_redGL]
  · intro α γ τ
    simp only [famGL_vmul_gact]
    exact _root_.GlobalTheory.WpFam.wB_smul_transform N (vmul y α) γ τ

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_eventuallyEq_pull {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun y => pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y)) := by
  have hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hxU : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  refine Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => ?_
  show A.loc α x.1.1 y = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y))
  let p : A.Pt := ⟨(x.1.1, x.ch.symm y), x.ch.map_target hy.1⟩
  let p' : A.Pt := ⟨(x'.1.1, x.ch.symm y), hy.2⟩
  have e1 : A.loc α x.1.1 y = α p := by rw [HolAtlas.loc, dite_eq_left hy.1]
  have e2 : A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y) = α p' := A.loc_crd α p'
  have e3 : p.crd = y := x.ch.right_inv hy.1
  rw [e1, e2, hα.compat p p' rfl]
  show pull (fderiv ℂ (x'.ch ∘ x.ch.symm) p.crd) (α p') = _
  rw [e3]

theorem chg_facts (x x' : A.Pt) (h : x.pt = x'.pt) :
    IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧ x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source ∧
    DifferentiableOn ℂ (x'.ch ∘ x.ch.symm) (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧
    (x'.ch ∘ x.ch.symm) x.crd = x'.crd :=
  ⟨x.ch.isOpen_inter_preimage_symm x'.ch.open_source,
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩,
    A.holo x.1.1 x'.1.1, by simp only [Function.comp_apply, x.ch.left_inv x.2, h]⟩

theorem loc_diffAt {α : A.Fld} (hα : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x.1.1 y) S) x.crd :=
  ((hα.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)

theorem isForm_del_dbar {α : A.Fld} (hα : A.IsForm α) : A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  have hloc : ∀ (T : (V n → Alt n) → V n → Alt n) (i : A.ι) (v : V n), v ∈ (A.e i).target →
      A.loc (fun x => T (A.loc α x.1.1) x.crd) i v = T (A.loc α i) v := by
    intro T i v hv
    rw [HolAtlas.loc, dite_eq_left hv]
    show T (A.loc α i) ((A.e i) ((A.e i).symm v)) = _
    rw [(A.e i).right_inv hv]
  refine ⟨⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩
  · exact ((_root_.GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).1).congr fun v hv => by
      rw [show A.del α = fun x => delAt (A.loc α x.1.1) x.crd from rfl, hloc delAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show delAt (A.loc α x.1.1) x.crd = pull _ (delAt (A.loc α x'.1.1) x'.crd)
    rw [((_root_.GlobalTheory.CxForm.delAt_dbarAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).1,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).1, hτx]
  · exact ((_root_.GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).2).congr fun v hv => by
      rw [show A.dbar α = fun x => dbarAt (A.loc α x.1.1) x.crd from rfl, hloc dbarAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)
    rw [((_root_.GlobalTheory.CxForm.delAt_dbarAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).2,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).2, hτx]

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.isForm_del_dbar : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) :=
  fun _ _ _ A _ hα => A.isForm_del_dbar hα
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecMonomialOfConeCombinatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Arith

theorem idlAlong_monomial : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ)
    (J : Z.IdealSheafData) (d : ℕ), ValOn F i φ J d →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (ga δ : Fin m → LinearMap.BilinForm ℤ X)
      (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) →
    ∀ (T : Trait F) (W : Type) [CommRing W] [IsLocalRing W] (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ X)
      (x : Sp W ⟶ Z) (s : Fin m → W), Function.Bijective σ → jK T.V ≫ spMap σ ≫ x = T.y ≫ i →
      (∀ k, Associated (σ (s k)) (T.ϖ ^ c k)) → (∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b)) →
      idlAlong J x = Ideal.span {∏ k, s k ^ b k} := by
  intro o _ ζ g n F Z i φ J d hV X _ _ _ m ga δ M hcone hδ b hb T W _ _ σ c e' x s hσ hcomm hs hβ
  obtain ⟨a, ha, hid⟩ := hV T (spMap σ ≫ x) hcomm
  have heq (χ : Sp W ⟶ Z) (U : Z.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of W)).hom).hom := by
    have hx : χ (closedPoint W) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have hcomp : idlAlong J (spMap σ ≫ x) = (idlAlong J x).map σ := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens
      (show x (closedPoint W) ∈ (⊤ : Z.Opens) from trivial)
    have hle : ⊤ ≤ x ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem x hx).ge
    have hle' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun y _ => hle (show spMap σ y ∈ (⊤ : (Sp W).Opens) from trivial)
    have heq' : idlAlong J (spMap σ ≫ x) = (J.ideal ⟨U, hU⟩).map
        ((spMap σ ≫ x).appLE U ⊤ hle' ≫ (Scheme.ΓSpecIso (.of T.V)).hom).hom := by
      have hx' : (spMap σ ≫ x) (closedPoint T.V) ∈ U := hle' trivial
      unfold idlAlong
      rw [ds_stalkId_eq_map J ⟨U, hU⟩ _ hx', Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
      congr 2
    rw [heq x ⟨U, hU⟩ hle, heq', Ideal.map_map]
    congr 1
    have e : (spMap σ ≫ x).appLE U ⊤ hle' = x.appLE U ⊤ hle ≫ (spMap σ).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  rw [hcomp] at hid
  have hlin : φ.LinearOn δ := by
    have := hcone.linearOn_smul M
    rwa [show δ = fun k => (M : ℤ) • ga k from funext hδ]
  have hev : φ.evalZ T.β = ∑ k, (c k : ℝ) * φ.evalZ (δ k) := by
    refine InvFun.LinearOn.eval_eq_sum (X := X) hlin (r := e'.symm.toIntLinearEquiv.toLinearMap)
      e'.symm.surjective (fun k => Nat.cast_nonneg _) ?_
    intro u v
    simp [hβ]
  have haN : a = ∑ k, c k * b k := by
    have : (a : ℝ) = ∑ k, (c k : ℝ) * b k := by
      rw [ha, hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb k]; ring
    exact_mod_cast this
  have hassoc : Associated (∏ k, σ (s k) ^ b k) (T.ϖ ^ a) := by
    rw [haN, ← Finset.prod_pow_eq_pow_sum]
    refine Associated.prod _ _ _ fun k _ => ?_
    rw [pow_mul]
    exact (hs k).pow_pow
  have hmap : (idlAlong J x).map σ = (Ideal.span {∏ k, s k ^ b k}).map σ := by
    rw [hid, Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]
    exact (Ideal.span_singleton_eq_span_singleton.2 hassoc).symm
  rw [← Ideal.comap_map_of_bijective σ hσ (I := idlAlong J x), hmap, Ideal.comap_map_of_bijective σ hσ]

end GlobalTheory.Poinc.Arith
end

