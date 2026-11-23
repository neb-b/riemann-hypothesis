module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisationStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  first | (exact @GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (exact GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (intros; apply GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionsOrderFiniteUnramifiedScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem GlobalTheory.EndLoc.actRep_finite_unramified : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π ∧ FormallyUnramified R.π := by
  intro S _ A _ _ Q hA hQ h1 h2 hs ha O _ bar r e W d hbar hspan hW hd hcas
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_finite_scheme_adjoint_actions_abelian S A Q hA hQ h1 h2 hs ha O bar r e W d hbar hspan hW hd hcas
  exact ⟨R, hR, _root_.GlobalTheory.EndLoc.formallyUnramified_actRep S A Q O bar R hA⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelOfPrincipalisation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem ampleHS_of_principalisation : GlobalTheory.Published.Principalisation → AmpleHS := by
  intro hPr k _ X _ p D hX P a hA hS ha
  have hC := GlobalTheory.MixHt.arCalc_of_principalisation hPr
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hA
  obtain ⟨B, hB0, hB⟩ := _root_.GlobalTheory.HSAmp.exists_isCan_bdd k X p D hX P e x hx
  have hG := _root_.GlobalTheory.HSAmp.GoodH.goodFam_H hC k X p D hX P hA
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation hPr k X p D hX P a hS ha hG
  obtain ⟨C, hCb⟩ := _root_.GlobalTheory.HSAmp.selfInter_canWeight_le hC k X p D hX P hA e x hx
  refine ⟨max (t₀ + B) 1, fun t ht => ?_⟩
  have ht1 : t₀ + B ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hball : ∀ (u : SmFn p) (m : ℕ) (R : ℝ), ballIn (upperParabolic P u) (P.H m 1) m 1 R = (upperParabolic P u).Bl m 1 R :=
    fun _ _ _ => rfl
  have hball' : ∀ (m : ℕ) (R : ℝ), ballIn P (P.H m 1) m 1 R = P.Bl m 1 R := fun _ _ => rfl
  have hF : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hF1 : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hLg : 0 ≤ Real.log ((D : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  set g := gdeg P.L D with hg
  have hc : (a + ((D : ℝ) + 1) * t * g) / ((D + 1).factorial : ℝ) = g / D.factorial * t + a / (D + 1).factorial := by
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
  have key : ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      |P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) - (g / D.factorial * t + a / (D + 1).factorial)|
        ≤ |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * n) / e) + |C| / n / (D + 1).factorial + 2 * ε := by
    intro n hn ε hε
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨u, hu, huB⟩ := hB n hn
    have hsemi := _root_.GlobalTheory.HSAmp.semiPos_up_of_isCan k X p D hX P e x hx n u hn hu
    obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (up P.L u)
    have hsi : (up P.L u).IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    have han := hCb n u _ hn hu hsi
    have hdiff := ht₀ u B _ hB0 huB hsemi hsi t ht1
    obtain ⟨hnu1, hnu2, hgu, -, -⟩ := _root_.GlobalTheory.HSAmp.canNorms k X p D hX P e x hx n u hn hu
    have hκ1 : Real.exp (-(Real.log ((D : ℝ) + 1) / (2 * n))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hLg (by positivity)))
    have hcnt := _root_.GlobalTheory.HSAmp.lc_exp_bounds hC k X p D hX (upperParabolic P u) hA e x hgu _ t (Real.exp_pos _) hκ1 ht2 hnu1 hnu2 ε hε
    rw [show (upperParabolic P u).L = up P.L u from rfl, _root_.GlobalTheory.GdegMetric.gdeg_up hC k X p D hX P.L u, Real.log_exp, ← hg] at hcnt
    simp only [hball, hball'] at hdiff
    have hd := hdiff.eventually (Metric.ball_mem_nhds _ hε)
    set an := h (genericPoint X)
    set T := Real.log ((D : ℝ) + 1) / (2 * n) / e with hT
    have hT0 : 0 ≤ T := by positivity
    have hup : g / D.factorial * (t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e) ≤ g / D.factorial * t + |g| / D.factorial * T := by
      rw [show t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e = t + T by rw [hT]; ring, mul_add]
      gcongr
      exact le_abs_self g
    have han1 : an / (D + 1).factorial ≤ |C| / n / (D + 1).factorial :=
      div_le_div_of_nonneg_right ((le_abs_self an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    have hgT : 0 ≤ |g| / D.factorial * T := by positivity
    have han2 : -(an / (D + 1).factorial) ≤ |C| / n / (D + 1).factorial := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right ((neg_le_abs an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    filter_upwards [hd, hcnt] with m hm1 hm2
    rw [Real.dist_eq, abs_sub_lt_iff] at hm1
    have hsplit : P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) =
        (upperParabolic P u).lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) -
          (Real.log ((upperParabolic P u).Bl m 1 (Real.exp (t * m))).ncard - Real.log (P.Bl m 1 (Real.exp (t * m))).ncard) /
            (m : ℝ) ^ (D + 1) := by
      simp only [Pair.lc]; ring
    have hq : (an - a) / ((D + 1).factorial : ℝ) = an / (D + 1).factorial - a / (D + 1).factorial := sub_div _ _ _
    rw [hsplit, abs_le]
    constructor <;> linarith [hm2.1, hm2.2]
  rw [hc]
  refine Metric.tendsto_nhds.2 fun δ hδ => ?_
  set K := |g| / D.factorial * (Real.log ((D : ℝ) + 1) / 2 / e) + |C| / (D + 1).factorial with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K / δ)
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hKn : |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) / e) +
      |C| / ((n + 1 : ℕ) : ℝ) / (D + 1).factorial = K / ((n + 1 : ℕ) : ℝ) := by
    rw [hK]; field_simp
  have hKlt : K / ((n + 1 : ℕ) : ℝ) < δ / 2 := by
    have h1 : 2 * K / δ < ((n + 1 : ℕ) : ℝ) := hn.trans (by exact_mod_cast Nat.lt_succ_self n)
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ hn1]
    linarith
  filter_upwards [key (n + 1) (Nat.le_add_left 1 n) (δ / 8) (by positivity)] with m hm
  rw [hKn] at hm
  rw [Real.dist_eq]
  linarith

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqMinpolyPow
section
open CategoryTheory Polynomial
open GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.CharpolyMinpolyPower

theorem eq_pow_of_roots (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (P m : ℚ[X]) (hP : P.Monic)
    (hm : m.Monic) (hirr : Irreducible m) (h : ∀ a : Ω, aeval a P = 0 → minpoly ℚ a = m) :
    ∃ k : ℕ, P = m ^ k := by
  suffices H : ∀ n : ℕ, ∀ Q : ℚ[X], Q.natDegree = n → Q.Monic →
      (∀ a : Ω, aeval a Q = 0 → minpoly ℚ a = m) → ∃ k : ℕ, Q = m ^ k from H _ P rfl hP h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hQn hQ hroots
    by_cases hn : Q.natDegree = 0
    · exact ⟨0, by rw [pow_zero]; exact Polynomial.eq_one_of_monic_natDegree_zero hQ hn⟩
    · have hdeg : Q.degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hQ.ne_zero]
        exact_mod_cast hn
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_aeval_eq_zero Ω Q hdeg
      have hdvd : m ∣ Q := hroots a ha ▸ minpoly.dvd ℚ a ha
      obtain ⟨Q', rfl⟩ := hdvd
      have hQ' : Q'.Monic := hm.of_mul_monic_left hQ
      have hsum : (m * Q').natDegree = m.natDegree + Q'.natDegree := hm.natDegree_mul hQ'
      have hm0 : 0 < m.natDegree := hirr.natDegree_pos
      obtain ⟨k, hk⟩ := ih Q'.natDegree (by omega) Q' rfl hQ'
        (fun b hb => hroots b (by rw [map_mul, hb, mul_zero]))
      exact ⟨k + 1, by rw [hk, pow_succ, mul_comm]⟩

theorem deg_ne_zero {K : Type} [Field K] (A : AbVar K) {F : Type} [Field F] [NumberField F]
    (ι : NumberField.RingOfIntegers F →+* End A) (r : NumberField.RingOfIntegers F) (hr : r ≠ 0) :
    deg (ι r).asHom ≠ 0 := by
  have hI : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hN0 : Ideal.absNorm (Ideal.span {r}) ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
  have hc : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hN0
  have hι : (ι r).asHom ≫ (ι s).asHom = ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • 𝟙 A := by
    rw [← End.mul_asHom, ← map_mul, hs, map_natCast, natCast_zsmul, ← nsmul_one]
    exact map_nsmul End.addEquiv _ (1 : End A)
  obtain ⟨-, hdN⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A _ hc
  have hcomp := (isIsogeny_comp_iff_and_deg_comp K A A A (ι r).asHom (ι s).asHom rfl rfl).2
  rw [hι, hdN] at hcomp
  intro h0
  rw [h0, zero_mul] at hcomp
  exact pow_ne_zero _ (Int.natAbs_ne_zero.2 hc) hcomp

theorem charpoly_eq_minpoly_pow {K : Type} [Field K] (A : AbVar K) (hA : A.dim ≠ 0) {F : Type} [Field F]
    [NumberField F] (ι : NumberField.RingOfIntegers F →+* End A) (x : NumberField.RingOfIntegers F) :
    ∃ k : ℕ, 0 < k ∧ (charpoly (ι x)).map (Int.castRingHom ℚ) = minpoly ℚ (x : F) ^ k := by
  obtain ⟨hcp, -⟩ := charpoly_spec K A (ι x)
  obtain ⟨hmon, hdeg, -⟩ := hcp
  have hPm : ((charpoly (ι x)).map (Int.castRingHom ℚ)).Monic := hmon.map _
  have hPdeg : ((charpoly (ι x)).map (Int.castRingHom ℚ)).natDegree = 2 * A.dim := by
    rw [hmon.natDegree_map, hdeg]
  let ιa : NumberField.RingOfIntegers F →ₐ[ℤ] End A :=
    AlgHom.mk ι (fun n => by
      show ι (algebraMap ℤ _ n) = algebraMap ℤ (End A) n
      rw [eq_intCast (algebraMap ℤ (NumberField.RingOfIntegers F)), eq_intCast (algebraMap ℤ (End A))]
      exact map_intCast ι n)
  have hxint : IsIntegral ℚ (x : F) := Algebra.IsIntegral.isIntegral _
  have key : ∀ a : AlgebraicClosure ℚ, aeval a ((charpoly (ι x)).map (Int.castRingHom ℚ)) = 0 →
      minpoly ℚ a = minpoly ℚ (x : F) := by
    intro a ha
    have haint : IsIntegral ℚ a := IsAlgebraic.isIntegral ⟨_, hPm.ne_zero, ha⟩
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ a)
    have hRa : aeval a (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 :=
      IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) _ (minpoly.aeval ℚ a)
    have hprod := deg_aeval_eq_prod_aroots K A (ι x) (AlgebraicClosure ℚ)
      (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))
    have hmem : a ∈ ((charpoly (ι x)).map (Int.castRingHom ℚ)).aroots (AlgebraicClosure ℚ) :=
      (Polynomial.mem_aroots).2 ⟨hPm.ne_zero, ha⟩
    rw [Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, hmem, hRa⟩)] at hprod
    have hdeg0 : deg (aeval (ι x)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))).asHom = 0 := by
      have h := (map_eq_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective).1 hprod
      exact_mod_cast h
    rw [show aeval (ι x) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) =
        ι (aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))) from
      Polynomial.aeval_algHom_apply ιa x _] at hdeg0
    have hRx : aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 := by
      by_contra hne
      exact deg_ne_zero A ι _ hne hdeg0
    have hRxF : aeval (x : F) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 := by
      have h := congrArg (algebraMap (NumberField.RingOfIntegers F) F) hRx
      rwa [map_zero, ← Polynomial.aeval_algebraMap_apply] at h
    have hqx : aeval (x : F) (minpoly ℚ a) = 0 := by
      have h1 : aeval (x : F) ((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
          (minpoly ℚ a)).map (algebraMap ℤ ℚ)) = 0 := by
        rwa [Polynomial.aeval_map_algebraMap]
      rw [hb, map_zsmul] at h1
      exact (smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero hbM)
    exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible haint) hqx (minpoly.monic haint)
  obtain ⟨k, hk⟩ := eq_pow_of_roots (AlgebraicClosure ℚ) _ _ hPm (minpoly.monic hxint)
    (minpoly.irreducible hxint) key
  refine ⟨k, Nat.pos_of_ne_zero ?_, hk⟩
  rintro rfl
  rw [hk, pow_zero, Polynomial.natDegree_one] at hPdeg
  omega

end GlobalTheory.CharpolyMinpolyPower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesWithOfIsSquareConstOfTriple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem commutesWith_of_isSquareConst_of_triple (hWC : GlobalTheory.SquareSt.WeilConvergence)
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound)
    {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    (hT : SquareTriple W t i j) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c := by
  intro M hM Θ Θ' hΘ F hF hFc hFl hA hB
  funext g₁
  obtain ⟨hBa, hBe⟩ := _root_.GlobalTheory.BigRoute.lift_eq_integral_kerBig hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  obtain ⟨z, hz, hSa, hSe⟩ := _root_.GlobalTheory.SmallRoute.exists_translates_lift hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  refine mul_left_cancel₀ hz ?_
  rw [Pi.smul_apply, smul_eq_mul, hBe, mul_left_comm, hSe, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hBa, hSa] with g hb hs
  have h := hc M hM Θ Θ' hΘ z g g₁ ⟨hb, hs⟩
  linear_combination F g * h

theorem commutesWith_of_isSquareConst (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T}
    {i j : Fin D.R.m} (hS : SquareStanding G t) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c :=
  commutesWith_of_isSquareConst_of_triple hWC hK hP hL (squareTriple_of_standing hL W t i j hS) hc

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperUnitaryLevelGaloisActsOnLabels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.UGalLab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem three_le_level (X₁ : USetup C) : 3 ≤ X₁.S.r * X₁.S.N := by
  have hN := X₁.ρ.N_eq
  have hn := X₁.ρ.n_prime.two_le
  have hk := X₁.ρ.two_le
  have hr := X₁.S.r_pos
  have h4 : 4 ≤ X₁.S.N := by
    rw [hN]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (X₁.ρ.n ^ X₁.ρ.k) ^ 2 :=
        Nat.pow_le_pow_left (le_trans hn (Nat.le_self_pow (by omega) _)) 2
  nlinarith

theorem uIsLab_onto (X : USetup C) {p : ℕ} [Fact p.Prime] {z : X.M.Z} (ct : UCTrait X p z)
    (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (h : UIsLab X ct yy) (μ : ct.T.P.D.toPre.X) :
    ∃ a, yy a = QuotientAddGroup.mk μ := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, -, G, _, α, β, -, -, -, y₀, -, u, lb, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := lb.yy_onto (QuotientAddGroup.mk (j.symm μ))
  exact ⟨a, by rw [hyy a _ ha, AddEquiv.apply_symm_apply]⟩

theorem be_pos (T : UTrait Xo cf) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem congMod_of_mk_eq {X : Type} [AddCommGroup X] [Module.Free ℤ X] (κ : X ≃+ X) (m d L₁ : ℕ) (hm : m = d * L₁)
    (hd : d ≠ 0) (x : X)
    (h : (QuotientAddGroup.mk (d • x) : ModN m X) = QuotientAddGroup.mk (κ (d • x))) : CongMod L₁ (κ x) x := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.1 h
  simp only [nsmulAddMonoidHom_apply, map_nsmul] at hw
  refine ⟨w, ?_⟩
  have key : (d : ℤ) • ((L₁ : ℤ) • w) = (d : ℤ) • (κ x - x) := by
    rw [← mul_smul, ← Nat.cast_mul, ← hm, natCast_zsmul, hw, smul_sub, natCast_zsmul, natCast_zsmul]; abel
  have := smul_right_injective X (show (d : ℤ) ≠ 0 by exact_mod_cast hd) key
  rw [← natCast_zsmul, this]; abel

end GlobalTheory.UPoinc.UGalLab

namespace GlobalTheory.UPoinc.UGalLab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem eq_of_diag_congMod (T : UTrait Xo cf) (κ : T.P.D.toPre.X ≃+ T.P.D.toPre.X)
    (hd : ∀ x, T.be (κ x) (κ x) = T.be x x) (L : ℕ) (hL : 3 ≤ L) (hc : ∀ x, CongMod L (κ x) x) (x : T.P.D.toPre.X) :
    κ x = x := by
  let β : LinearMap.BilinForm ℤ T.P.D.toPre.X := T.be + T.be.flip
  have hβ : ∀ u v, β u v = T.be u v + T.be v u := fun u v => rfl
  let e : T.P.D.toPre.X ≃ₗ[ℤ] T.P.D.toPre.X := κ.toIntLinearEquiv
  have hiso : ∀ u v, β (e u) (e v) = β u v := by
    intro u v
    have huv := hd (u + v)
    simp only [map_add (f := _), LinearMap.add_apply] at huv
    rw [hd u, hd v] at huv
    rw [hβ, hβ]
    show T.be (κ u) (κ v) + T.be (κ v) (κ u) = _
    linarith
  have hpos : ∀ u, u ≠ 0 → 0 < β u u := fun u hu => by
    rw [hβ]; have := be_pos T u hu; linarith
  have he := eq_refl_of_isometry_congMod _ β hpos e hiso L hL hc
  have := congrArg (fun f : T.P.D.toPre.X ≃ₗ[ℤ] T.P.D.toPre.X => f x) he
  simpa [e] using this

end GlobalTheory.UPoinc.UGalLab

namespace GlobalTheory.UPoinc.UGalLab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem rigid (hpq : 1 ≤ Dw.p + Dw.q) {X₁ : USetup C} (D : UDeep X₁) {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}
    (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X) (h₁ : UIsLab X₁ ct yy₁)
    (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y)
    (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X)
    (hl : UIsLab D.X (D.lift ct y h) yy) (hc : D.Compat yy₁ yy)
    (hl' : UIsLab D.X (D.lift ct y h) yy') (hc' : D.Compat yy₁ yy') : yy' = yy := by
  obtain ⟨κ, hκβ, hκ⟩ := _root_.GlobalTheory.UPoinc.ULabUniq.main E H Dw hpq l Xo cf C D.X p (y (cPt p)) (D.lift ct y h) yy yy' hl hl'
  have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
    rw [D.sq]
    exact D.dvd.trans ((dvd_pow_self D.m two_ne_zero).mul_left _)
  have hdL : D.X.S.r * D.X.S.N = D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) :=
    (Nat.div_mul_cancel hdvd).symm
  have hd0 : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) ≠ 0 := by
    intro h0
    have h3 := three_le_level D.X
    rw [hdL, h0, zero_mul] at h3
    omega
  have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (κ x) x := by
    intro x
    obtain ⟨a, ha⟩ := uIsLab_onto X₁ ct yy₁ h₁ x
    have e1 := hc a _ ha
    have e2 := hc' a _ ha
    have e3 := hκ (D.lab a) _ e1
    rw [e2] at e3
    exact congMod_of_mk_eq κ _ _ _ hdL hd0 x e3
  have hκ1 : ∀ x, κ x = x := eq_of_diag_congMod ct.T κ hκβ _ (three_le_level X₁) hcong
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy x)
  rw [hκ x μ hμ.symm, ← hμ, hκ1]

end GlobalTheory.UPoinc.UGalLab

theorem GlobalTheory.UPoinc.UGalLab.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → UIsLab D.X (D.lift ct (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (a x) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D σ s hs
  obtain ⟨a, hfix, htr⟩ := _root_.GlobalTheory.UPoinc.uGalTransport E H Dw hpq l Xo cf C X₁ D σ s hs
  refine ⟨a, hfix, ?_⟩
  intro p _ z₁ ct yy₁ h₁ y h h' yy yy' hl hc hl' hc' x
  have hl2 := htr p z₁ ct y h h' yy hl
  have hc2 : D.Compat yy₁ (yy.comp a.toAddMonoidHom) := fun b μ hb => by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hfix]
    exact hc b μ hb
  have := GlobalTheory.UPoinc.UGalLab.rigid hpq D ct yy₁ h₁ (y ≫ s) h' (yy.comp a.toAddMonoidHom) yy' hl2 hc2 hl' hc'
  exact DFunLike.congr_fun this x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdArootsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_aeval_end_eq_prod_aroots : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ), algebraMap ℚ Ω (deg (A := A) (B := A) (Polynomial.aeval f R).asHom : ℚ) = ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map (fun a => Polynomial.aeval a R)).prod := by
  intro K _ A f Ω _ _ _ R
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  refine GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim
    (fun F => (deg (Polynomial.aeval f F).asHom : ℚ))
    ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R
  · intro F G
    have h := (isIsogeny_comp_iff_and_deg_comp K A A A
      (Polynomial.aeval f G).asHom (Polynomial.aeval f F).asHom rfl rfl).2
    change (deg (Polynomial.aeval f (F * G)).asHom : ℚ) =
      (deg (Polynomial.aeval f F).asHom : ℚ) * (deg (Polynomial.aeval f G).asHom : ℚ)
    rw [map_mul, End.mul_asHom, h, Nat.cast_mul, mul_comm]
  · intro n u
    obtain ⟨Φ, hΦ, hΦev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n
      (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦev m]
    change _ = (deg (End.addEquiv (Polynomial.aeval f (∑ i, m i • u i))) : ℚ)
    simp only [map_sum, map_zsmul, End.addEquiv_apply]
  · exact hm.map _
  · rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hd
  · intro n
    have e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = (n : End A) - f := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]
    change ((charpoly f).map (Int.castRingHom ℚ)).eval (n : ℚ) =
      (deg (Polynomial.aeval f (Polynomial.C n - Polynomial.X)).asHom : ℚ)
    rw [Polynomial.eval_intCast_map, Int.cast_id, hev n, e, map_natCast]
end

