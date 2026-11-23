module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorThreeStepsConjugatePlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNine
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.TwistDeg

open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem logSum_bad_le {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) :
    logSum (GlobalTheory.FlatTw.badPrimes H l) ≤ Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hd := H.d_prime.ne_zero
  have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hd) hD) hM
  have h0 : ∀ p ∈ (2 * H.d * (discr E).natAbs * l.M').primeFactors, (p : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have e : Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' =
      Real.log ((2 * H.d * (discr E).natAbs * l.M' : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Nat.cast_natAbs, Int.cast_abs, Nat.cast_ofNat]
  rw [e, logSum, GlobalTheory.FlatTw.badPrimes, ← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Nat.prod_primeFactors_dvd _))
  exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem lrd_eq (E : Type) [Field E] [NumberField E] :
    lrd E = Real.log |(discr E : ℝ)| / (Module.finrank ℚ E : ℝ) := by
  have h : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  rw [lrd, rootDiscr_def, Int.cast_abs, Real.log_rpow h, div_eq_inv_mul]

theorem numeric {f r L q a b s c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hq : q ≤ r)
    (hb0 : 0 ≤ b) (hb : b ≤ 3 * L) (hs0 : 0 ≤ s) (hs : s ≤ 6 * f * r) (hc : |a| ≤ 9 * r * L * s)
    (hB : c ≤ 1 + 2 * b + 2 * f * b + 30 * L) : -(120 * (f * r * L) ^ 2) ≤ a - q * b * s - c := by
  have h1 : q * b * s ≤ r * (3 * L) * (6 * f * r) := by gcongr
  have h2 : 9 * r * L * s ≤ 9 * r * L * (6 * f * r) := by gcongr
  have h3 : f * b ≤ f * (3 * L) := by gcongr
  have h4 : f * r ^ 2 * L ≤ (f * r * L) ^ 2 := by
    rw [show (f * r * L) ^ 2 = f * r ^ 2 * L * (f * L) by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hf hL)
  have h5 : f * L ≤ f * r ^ 2 * L := by
    rw [show f * r ^ 2 * L = f * L * r ^ 2 by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr)
  have h6 : L ≤ f * L := le_mul_of_one_le_left (by positivity) hf
  have h7 := (abs_le.1 hc).1
  nlinarith

end GlobalTheory.TwistDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorThreeStepsConjugatePlacesStatement
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatVector_three_steps_conjugate_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∃ (eg ea et : AE D) (fg hA : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum ea (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ IsIdemSum et (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ GlobalTheory.BaseCmp.IsTypeVec R i eg fg ∧ ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (R.xiR t) ea) hA ∧ ThAt R i (cA D et) hA (GlobalTheory.BaseCmp.flatDat R i ((flipPart (R := R) t (B.de.Q ∪ ψ.Q)).image conjPl) (fun PP => B.de.locC PP * ψ.locC PP) (cA D et)) ((princ B).vecFlat ψ) := by
  first | exact @GlobalTheory.FlatThreeSteps.vecFlat_three_steps | exact GlobalTheory.FlatThreeSteps.vecFlat_three_steps | (intros; apply GlobalTheory.FlatThreeSteps.vecFlat_three_steps <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierJacobiExpansionFderivTermwise
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FJD

open GlobalTheory.MBLow.Cl.FJ

theorem deriv_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f) (Z W : E) :
    deriv (fun s : ℂ => f (Z + s • W)) 0 = fderiv ℂ f Z W := by
  have h1 : HasDerivAt (fun s : ℂ => Z + s • W) W 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const W).const_add Z
  have h2 : HasFDerivAt f (fderiv ℂ f Z) (Z + (0 : ℂ) • W) := by
    simpa using (hf Z).hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv

theorem termwise {J E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : J → E → ℂ} {F : E → ℂ}
    (hf : ∀ i, Differentiable ℂ (f i)) (hF : Differentiable ℂ F) (hs : ∀ Z, ∑' i, f i Z = F Z) (Z W : E)
    {u : J → ℝ} (hu : Summable u) (hb : ∀ i (s : ℂ), ‖s‖ ≤ 2 → ‖f i (Z + s • W)‖ ≤ u i) :
    (Summable fun i => ‖fderiv ℂ (f i) Z W‖) ∧ ∑' i, fderiv ℂ (f i) Z W = fderiv ℂ F Z W := by
  have hl : Differentiable ℂ (fun s : ℂ => Z + s • W) := by fun_prop
  have hd : ∀ i, Differentiable ℂ (fun s : ℂ => f i (Z + s • W)) := fun i => (hf i).comp hl
  refine ⟨hu.of_nonneg_of_le (fun _ => norm_nonneg _) fun i => ?_, ?_⟩
  · rw [← deriv_line (hf i)]
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := 1) (C := u i) one_pos
      (hd i).diffContOnCl (fun s hs => hb i s (by
        have : ‖s‖ = 1 := by simpa using hs
        linarith))
    simpa using this
  · have h := Complex.hasSum_deriv_of_summable_norm (U := Metric.ball (0 : ℂ) 2) (z := 0)
      (F := fun i s => f i (Z + s • W)) hu (fun i => (hd i).differentiableOn) Metric.isOpen_ball
      (fun i s hs => hb i s (le_of_lt (by simpa using hs))) (by simp)
    simp only [hs] at h
    rw [deriv_line hF] at h
    simp only [deriv_line (hf _)] at h
    exact h.tsum_eq

theorem norm_exp_le_corners (α c s : ℂ) (hs : ‖s‖ ≤ 2) :
    ‖Complex.exp (α + s * c)‖ ≤ ‖Complex.exp (α + (2 + 2 * Complex.I) * c)‖ + ‖Complex.exp (α + (2 - 2 * Complex.I) * c)‖ +
      ‖Complex.exp (α + (-2 + 2 * Complex.I) * c)‖ + ‖Complex.exp (α + (-2 - 2 * Complex.I) * c)‖ := by
  have h1 := abs_le.mp ((Complex.abs_re_le_norm s).trans hs)
  have h2 := abs_le.mp ((Complex.abs_im_le_norm s).trans hs)
  simp only [Complex.norm_exp]
  have p1 := Real.exp_pos (α + (2 + 2 * Complex.I) * c).re
  have p2 := Real.exp_pos (α + (2 - 2 * Complex.I) * c).re
  have p3 := Real.exp_pos (α + (-2 + 2 * Complex.I) * c).re
  have p4 := Real.exp_pos (α + (-2 - 2 * Complex.I) * c).re
  rcases le_total 0 c.re with hr | hr <;> rcases le_total 0 c.im with hi | hi
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (2 - 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (2 + 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (-2 - 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (-2 + 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith

theorem norm_thT_le_corners {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b Z W : Fin k → ℂ) (n : Fin k → ℤ) (s : ℂ)
    (hs : ‖s‖ ≤ 2) :
    ‖thT τ a b (Z + s • W) n‖ ≤ ‖thT τ a b (Z + (2 + 2 * Complex.I) • W) n‖ + ‖thT τ a b (Z + (2 - 2 * Complex.I) • W) n‖ +
      ‖thT τ a b (Z + (-2 + 2 * Complex.I) • W) n‖ + ‖thT τ a b (Z + (-2 - 2 * Complex.I) • W) n‖ := by
  have key : ∀ t : ℂ, thT τ a b (Z + t • W) n =
      Complex.exp ((Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
        2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (Z + b))) +
        t * (2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ W))) := by
    intro t
    unfold thT
    congr 1
    generalize ((fun i => (n i : ℂ)) + a) = v
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  simp only [key]
  exact norm_exp_le_corners _ _ s hs

def splitE {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) : (Fin g → ℤ) ≃ (Fin r → ℤ) × (Fin g' → ℤ) where
  toFun := fun n => (tP σ n, zP σ n)
  invFun := fun p j => Sum.elim p.2 p.1 (σ j)
  left_inv := fun n => by
    funext j
    rcases h : σ j with i | l
    · simp only [h, Sum.elim_inl, zP]; rw [σ.symm_apply_eq.mpr h.symm]
    · simp only [h, Sum.elim_inr, tP]; rw [σ.symm_apply_eq.mpr h.symm]
  right_inv := fun p => by ext <;> simp [zP, tP]

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

theorem fj_eq_tsum (S : Matrix (Fin r) (Fin r) ℂ) (χ : N.X) (Z : Fin g → ℂ) :
    d.fj σ S χ Z = ∑' m, thT (d.full σ S) (d.aF σ) (d.bF σ) Z ((splitE σ).symm (bX.equivFun χ, m)) := by
  have hcv : cv (bX.equivFun χ) = co bX χ := by
    funext l; simp [cv, co, Module.Basis.equivFun_apply]
  have hsymm : ∀ p, splitE σ ((splitE σ).symm p) = p := (splitE σ).apply_symm_apply
  simp only [CD.fj, thetaChar_eq_tsum, ← tsum_mul_left]
  congr 1
  funext m
  have h1 : tP σ ((splitE σ).symm (bX.equivFun χ, m)) = bX.equivFun χ := congrArg Prod.fst (hsymm (bX.equivFun χ, m))
  have h2 : zP σ ((splitE σ).symm (bX.equivFun χ, m)) = m := congrArg Prod.snd (hsymm (bX.equivFun χ, m))
  rw [thT_full, h1, h2, hcv]

theorem half_aF : Half (d.aF σ) := by
  intro j
  simp only [CD.aF]
  rcases σ j with i | l
  · exact d.ha i
  · simp

theorem half_bF : Half (d.bF σ) := by
  intro j
  simp only [CD.bF]
  rcases σ j with i | l
  · exact d.hb i
  · exact d.hb2 l

theorem full_isSymm {S : Matrix (Fin r) (Fin r) ℂ} (hS : S.IsSymm) : (d.full σ S).IsSymm :=
  (Matrix.IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hS)).submatrix σ

theorem differentiable_fj (S : Matrix (Fin r) (Fin r) ℂ) (χ : N.X) : Differentiable ℂ (d.fj σ S χ) := by
  have h := (thetaChar_entire_ne_zero_automorphy g' d.τ d.a d.b d.symm d.pos d.ha d.hb).1
  have hz : Differentiable ℂ (fun Z : Fin g → ℂ => zP σ Z + d.t12 *ᵥ co bX χ) := by
    refine Differentiable.add_const _ ?_
    unfold zP
    fun_prop
  have ht : Differentiable ℂ (fun Z : Fin g → ℂ => co bX χ ⬝ᵥ (tP σ Z + d.b2)) := by
    simp only [dotProduct, tP, Pi.add_apply]
    fun_prop
  unfold CD.fj
  exact (((ht.const_mul _).const_add _).cexp).mul (h.comp hz)

theorem exists_bound {S : Matrix (Fin r) (Fin r) ℂ} (hpos : ((d.full σ S).map Complex.im).PosDef) (Z W : Fin g → ℂ) :
    ∃ u : N.X → ℝ, Summable u ∧ ∀ χ (s : ℂ), ‖s‖ ≤ 2 → ‖d.fj σ S χ (Z + s • W)‖ ≤ u χ := by
  have haF : ∀ j, ((d.aF σ j).re : ℂ) = d.aF σ j := by
    intro j
    rcases half_aF d σ j with h | h <;> simp [h]
  have hF : ∀ t : ℂ, Summable fun p => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) (Z + t • W) ((splitE σ).symm p)‖ := fun t =>
    ((splitE σ).symm.summable_iff (f := fun n => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) (Z + t • W) n‖)).mpr
      (summable_thT hpos haF (d.bF σ) _)
  have hG := (((hF (2 + 2 * Complex.I)).add (hF (2 - 2 * Complex.I))).add (hF (-2 + 2 * Complex.I))).add
    (hF (-2 - 2 * Complex.I))
  refine ⟨_, hG.prod.comp_injective bX.equivFun.injective, fun χ s hs => ?_⟩
  rw [fj_eq_tsum]
  refine (norm_tsum_le_tsum_norm ((hF s).prod_factor _)).trans ?_
  exact Summable.tsum_le_tsum (fun m => norm_thT_le_corners _ _ _ Z W _ s hs) ((hF s).prod_factor _) (hG.prod_factor _)

end GlobalTheory.MBLow.Cl.FJD


open GlobalTheory.MBLow.Cl.FJD in
theorem GlobalTheory.MBLow.Cl.fj_expansion_fderiv : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → (∀ χ, Differentiable ℂ (d.fj σ S χ)) ∧ ∀ Z W, (Summable fun χ => ‖fderiv ℂ (d.fj σ S χ) Z W‖) ∧ ∑' χ, fderiv ℂ (d.fj σ S χ) Z W = fderiv ℂ (thetaChar (d.full σ S) (d.aF σ) (d.bF σ)) Z W := by
  intro N g' r g bX d σ S hS hpos
  refine ⟨differentiable_fj d σ S, fun Z W => ?_⟩
  obtain ⟨u, hu, hb⟩ := exists_bound d σ hpos Z W
  exact termwise (differentiable_fj d σ S)
    (thetaChar_entire_ne_zero_automorphy g _ _ _ (full_isSymm d σ hS) hpos (half_aF d σ) (half_bF d σ)).1
    (fun Z => (fj_expansion N g' r g bX d σ S hS hpos Z).2) Z W hu hb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionsUnitDenominatorsReplaceGenerators
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem fractions_unit_denominators_replace_generators : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (P : L → Prop) (s₀ : Finset L), (∀ x ∈ s₀, ∃ b d : L, P b ∧ P d ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ x = b / d) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ t : Finset L, (∀ x ∈ t, P x) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑t), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro L _ ψ V P s₀ h1 h2
  classical
  choose b d hb hd hd0 hdV hx using h1
  let t : Finset L := (s₀.attach.image (fun x => b x.1 x.2)) ∪ (s₀.attach.image (fun x => d x.1 x.2))
  refine ⟨t, ?_, ?_⟩
  · intro x hx'
    simp only [t, Finset.mem_union, Finset.mem_image] at hx'
    rcases hx' with ⟨⟨y, hy⟩, _, rfl⟩ | ⟨⟨y, hy⟩, _, rfl⟩
    · exact hb y hy
    · exact hd y hy
  · let S : Subring L := Subring.closure (Set.range ψ ∪ (t : Set L))
    have hVone : (1 : L)⁻¹ ∈ V := by simpa using V.one_mem
    let F : Subring L :=
      { carrier := {y | ∃ b ∈ S, ∃ d ∈ S, d ≠ 0 ∧ d⁻¹ ∈ V ∧ y = b / d}
        mul_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * b₂, S.mul_mem hb₁ hb₂, d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_mul_div_comm]
        one_mem' := ⟨1, S.one_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        add_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * d₂ + d₁ * b₂, S.add_mem (S.mul_mem hb₁ hd₂) (S.mul_mem hd₁ hb₂),
            d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_add_div _ _ h₁ h₂]
        zero_mem' := ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        neg_mem' := by
          rintro _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩
          exact ⟨-b₁, S.neg_mem hb₁, d₁, hd₁, h₁, i₁, by rw [neg_div]⟩ }
    have htS : ∀ x ∈ t, x ∈ S := fun x hx' => Subring.subset_closure (Or.inr hx')
    have hle : Subring.closure (Set.range ψ ∪ (s₀ : Set L)) ≤ F := by
      rw [Subring.closure_le]
      rintro x (⟨c, rfl⟩ | hx')
      · exact ⟨ψ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), 1, S.one_mem, one_ne_zero, hVone, by simp⟩
      · refine ⟨b x hx', htS _ ?_, d x hx', htS _ ?_, hd0 x hx', hdV x hx', hx x hx'⟩
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem (fun y : s₀ => b y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun y : s₀ => d y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
    intro s hs
    obtain ⟨B, hB, D, hD, hD0, hDV, rfl⟩ := h2 s hs
    obtain ⟨b₁, hb₁, b₂, hb₂, hb₂0, hb₂V, rfl⟩ := hle hB
    obtain ⟨d₁, hd₁, d₂, hd₂, hd₂0, hd₂V, rfl⟩ := hle hD
    have hd₁0 : d₁ ≠ 0 := by
      rintro rfl; exact hD0 (by simp)
    have hd₁V : d₁⁻¹ ∈ V := by
      have : d₁⁻¹ = (d₁ / d₂)⁻¹ * d₂⁻¹ := by
        field_simp
      rw [this]; exact mul_mem hDV hd₂V
    refine ⟨b₁ * d₂, S.mul_mem hb₁ hd₂, b₂ * d₁, S.mul_mem hb₂ hd₁, mul_ne_zero hb₂0 hd₁0, ?_, ?_⟩
    · rw [mul_inv]; exact mul_mem hb₂V hd₁V
    · rw [div_div_div_eq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameBallSubsetExpChartImageFrameBox
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.BallCover

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_exp_lower (n : Type) [Fintype n] [DecidableEq n] :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < ρ → ‖Y‖ ≤ 2 * ‖NormedSpace.exp Y - 1‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero] at this
  have h1 : ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 2 * ‖Y‖ := this
  have h2 : ‖Y‖ ≤ ‖NormedSpace.exp Y - 1‖ + ‖NormedSpace.exp Y - 1 - Y‖ := by
    calc ‖Y‖ = ‖(NormedSpace.exp Y - 1) - (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

end Exp

section Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frBall_subset_chartExp_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (hG : G.det ≠ 0), (∀ τ, (mat x τ).det ≠ 0) → ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → frBall Ψ G x ε ⊆ GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} := by
  intro E _ _ _ r Ψ G x hG hx δ hδ
  obtain ⟨ρ, hρ, hexp⟩ := exists_exp_lower (Fin r)
  let cj : (Ψ → Fin r → Fin r → ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    fun X τ => (mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ
  have hcj : Continuous cj :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const
  let U : Set (realLie Ψ G) := {X | ‖X‖ < δ ∧ ∀ τ, ‖cj X.1 τ‖ < ρ}
  have hU : U ∈ nhds 0 := by
    refine IsOpen.mem_nhds ?_ ?_
    · change IsOpen ({X : realLie Ψ G | ‖X‖ < δ} ∩
        {X : realLie Ψ G | ∀ τ, ‖cj X.1 τ‖ < ρ})
      refine (isOpen_lt continuous_norm continuous_const).inter ?_
      change IsOpen {X : realLie Ψ G | ∀ τ, ‖cj X.1 τ‖ < ρ}
      rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun τ =>
        isOpen_lt ((continuous_apply τ).comp (hcj.comp continuous_subtype_val)).norm continuous_const
    · refine ⟨by simpa using hδ, fun τ => ?_⟩
      have e : cj (0 : realLie Ψ G).1 τ = 0 := by
        change (mat x τ)⁻¹ * (0 : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 0
        simp
      rw [e, norm_zero]; exact hρ
  have hev := GlobalTheory.SUVol.DensOne.eventually_mem_image Ψ G hG hU
  rw [Filter.eventually_comap] at hev
  obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.1 hev
  let bk : (Ψ → Matrix (Fin r) (Fin r) ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    fun A τ => mat x τ * A τ * (mat x τ)⁻¹
  have hbk : Continuous bk :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const
  have hbk0 : bk 0 = 0 := by funext τ; simp [bk]
  obtain ⟨ε₁, hε₁, hbkε⟩ := Metric.continuous_iff.1 hbk 0 η hη
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ g hg => ?_⟩
  let A : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1
  have hA : ‖A‖ < ε := (pi_norm_lt_iff hε).2 fun τ => (Matrix.norm_lt_iff hε).2 fun a b => hg τ a b
  have hbkA : bk A = GlobalTheory.SUVol.DensOne.matR Ψ G g - 1 := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1) * (mat x τ)⁻¹ =
      GlobalTheory.SUVol.DensOne.matR Ψ G g τ - 1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hx τ).isUnit,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hdist : dist (GlobalTheory.SUVol.DensOne.matR Ψ G g) 1 < η := by
    have := hbkε A (by rw [dist_zero_right]; linarith)
    rw [hbk0, dist_zero_right, hbkA] at this
    rwa [dist_eq_norm]
  obtain ⟨X, ⟨hXδ, hXρ⟩, rfl⟩ := hh hdist g rfl
  refine ⟨X, ⟨hXδ, fun τ a b => ?_⟩, rfl⟩
  have hY := hexp (cj X.1 τ) (hXρ τ)
  have he : NormedSpace.exp (cj X.1 τ) - 1 = A τ := by
    change NormedSpace.exp ((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) - 1 =
      (mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1
    rw [Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
  have hAτ : ‖A τ‖ < ε := lt_of_le_of_lt (norm_le_pi_norm A τ) hA
  rw [he] at hY
  calc ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ = ‖cj X.1 τ a b‖ := rfl
    _ ≤ ‖cj X.1 τ‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖A τ‖ := hY
    _ < 2 * ε := by linarith

end Main

end GlobalTheory.CovTop.VolUp.BallCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecResidueFieldCompAutEqOfFixesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromSpecResidueField_comp_aut_eq_of_fixes : ∀ (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ] (ρ : Γ →* Aut X) (γ : Γ) (x : X),
    (ρ γ).asIso.hom x = x → (∀ u : X.functionFieldˣ, RegAt x u → ZeroAt x ((fnAct ρ γ u : X.functionField) - u)) →
    X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x := by
  first | exact @GlobalTheory.OrbitSep.fromSpecResidueField_comp_eq_of_fixes | exact GlobalTheory.OrbitSep.fromSpecResidueField_comp_eq_of_fixes | (intros; apply GlobalTheory.OrbitSep.fromSpecResidueField_comp_eq_of_fixes <;> assumption)
end

