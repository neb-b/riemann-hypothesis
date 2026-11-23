module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0104
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0110

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsOfIsoDirectSumStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracts_of_iso_directSum' : ∀ (H G I F V : Type) [Monoid H] [Monoid G] [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V] (A B : I → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (a : ∀ i, Representation ℂ H (A i)) (b : ∀ i, Representation ℂ G (B i)) (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V) (i₀ : I), Iso (Representation.directSum fun i => Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) φ → (∀ i, i ≠ i₀ → invFun ((a i).tprod σ) = ⊥) → Module.finrank ℂ (invFun ((a i₀).tprod σ)) = 1 → Contracts φ σ (b i₀) := by
  first | exact @GlobalTheory.OneFunctional.contracts_of_iso_directSum | exact GlobalTheory.OneFunctional.contracts_of_iso_directSum | (intros; apply GlobalTheory.OneFunctional.contracts_of_iso_directSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.CoverKGen

open GlobalTheory.RealPar GlobalTheory.RealPar.KStabLie GlobalTheory.RealPar.TorusWt Matrix

variable {p q : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (p := p) (q := q) finSumFinEquiv (fun i => (finSumFinEquiv.symm i).isLeft) := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · have hlt : a < b := hab
    simp only [finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd]
    exact Fin.lt_def.mp hlt
  · simp [posC] at hab
  · simp [posC] at hab
  · have hlt : a < b := hab
    have := Fin.lt_def.mp hlt
    simp only [finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd]
    omega

theorem exists_log (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    ∃ X, X ∈ upq p q ∧ IsKC X ∧ T.cov (T.expt X) = T.cov k := by
  have hB := blockOrd_std p q
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exponential_surjective _ _ _ (mem_Kset hB T hk)
  letI : NormedRing (Mat p q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Mat p q) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Mat p q) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Mat p q) := FiniteDimensional.complete ℂ (Mat p q)
  letI : NormedRing (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :=
    FiniteDimensional.complete ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := p) (n := q))
  have hφc : Continuous φ := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact continuous_id.matrix_reindex _ _
  have hφX : φ (φ.symm Y) = Y := φ.apply_symm_apply Y
  have hJ : φ (Jm p q) = Formalism.REAL.Jm (fun i => (finSumFinEquiv.symm i).isLeft) := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact hB.reindex_Jm
  have hstar : ∀ M : Mat p q, φ Mᴴ = (φ M)ᴴ := fun M =>
    (Matrix.conjTranspose_reindex _ _ M).symm
  have hX : φ.symm Y ∈ upq p q := by
    show (φ.symm Y)ᴴ * Jm p q + Jm p q * φ.symm Y = 0
    apply φ.injective
    rw [map_add (f := _), map_mul, map_mul, hstar, hJ, hφX, map_zero]
    exact hY.1
  refine ⟨φ.symm Y, hX, ?_, ?_⟩
  · rw [isKC_iff]
    apply φ.injective
    rw [map_mul, map_mul, hJ, hφX]
    exact hY.2
  · apply Units.ext
    rw [T.expt_cov _ hX]
    apply φ.injective
    have hm : φ (NormedSpace.exp (φ.symm Y)) = NormedSpace.exp (φ (φ.symm Y)) :=
      NormedSpace.map_exp φ hφc _
    rw [hm, hφX, hexp]
    rfl

theorem torX_isKC (θ : Ix p q → ℝ) : IsKC (torX θ) := by
  intro a b hab
  have hne : a ≠ b := by
    rintro rfl
    exact hab (by cases a <;> trivial)
  simp [torX, Matrix.diagonal_apply_ne _ hne]

theorem cov_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.cov (T.expt (torX θ)) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
  rw [T.expt_cov _ (torX_mem θ)]
  unfold torX
  rw [Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]

private theorem sq_expt_torX_sq_eq_exp (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) ^ 2 =
      Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) ^ 2 := by
  rw [T.sq_sq, cov_expt_torX, Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_nat_mul]
  congr 1
  rw [← Finset.sum_mul]
  push_cast
  ring

theorem sq_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) = Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) := by
  let f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • torX θ)) : ℂˣ) : ℂ)
  let g : ℝ → ℂ := fun t => Complex.exp ((∑ a, ((t * θ a : ℝ) : ℂ)) * Complex.I / 2)
  have hsq : ∀ t, f t ^ 2 = g t ^ 2 := fun t => by
    simp only [f, g]
    rw [smul_torX]
    exact sq_expt_torX_sq_eq_exp T _
  have hg : ∀ t, g t ≠ 0 := fun t => Complex.exp_ne_zero _
  have hfc : Continuous f := by
    have h1 : Continuous fun t : ℝ => T.expt (t • torX θ) :=
      T.expt_cont.comp_continuous (continuous_id.smul continuous_const)
        (fun t => smul_mem_upq (torX_mem θ) t)
    have h2 : Continuous fun x : T.G => T.sq x := continuous_snd.comp T.emb.continuous
    exact Units.continuous_val.comp (h2.comp h1)
  have hgc : Continuous g := by fun_prop
  have hh : ∀ t, f t / g t = 1 ∨ f t / g t = -1 := fun t => by
    have h2 : (f t / g t) ^ 2 = 1 := by
      rw [div_pow, hsq t, div_self (pow_ne_zero 2 (hg t))]
    exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
  have h0 : f 0 / g 0 = 1 := by
    simp [f, g, T.expt_zero]
  have hcont : Continuous fun t => f t / g t := hfc.div hgc hg
  have h1 : f 1 / g 1 = 1 := by
    rcases hh 1 with h1 | h1
    · exact h1
    exfalso
    have hre : Continuous fun t => (f t / g t).re := Complex.continuous_re.comp hcont
    have hmem : (0 : ℝ) ∈ Set.Icc ((f 1 / g 1).re) ((f 0 / g 0).re) := by
      rw [h0, h1]
      norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' zero_le_one hre.continuousOn hmem
    rcases hh t with h2 | h2 <;> simp only [h2] at ht <;> norm_num at ht
  have hfg : f 1 = g 1 := (div_eq_one_iff_eq (hg 1)).mp h1
  simpa [f, g] using hfg

theorem kset_gen : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q), ∀ k ∈ T.Kset,
    k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) := by
  intro p q hpq T k hk
  have mem : ∀ X, X ∈ upq p q → IsKC X →
      T.expt X ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) :=
    fun X h1 h2 => Subgroup.subset_closure ⟨X, ⟨h1, h2⟩, rfl⟩
  obtain ⟨a0⟩ : Nonempty (Ix p q) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
  have hc := mem _ (torX_mem (Pi.single a0 (2 * Real.pi))) (torX_isKC (Pi.single a0 (2 * Real.pi)))
  have hcov : T.cov (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = 1 := by
    apply Units.ext
    rw [cov_expt_torX, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases ha : a = a0
    · subst ha
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [Pi.single_eq_of_ne ha]
  have hsqc : T.sq (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = -1 := by
    apply Units.ext
    rw [sq_expt_torX]
    have hs : (∑ a, (((Pi.single a0 (2 * Real.pi) : Ix p q → ℝ) a : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) := by
      rw [Finset.sum_eq_single a0 (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp
    have hpi : 2 * (Real.pi : ℂ) * Complex.I / 2 = Real.pi * Complex.I := by ring
    rw [hs, hpi, Complex.exp_pi_mul_I]
    simp
  obtain ⟨X, hX, hXK, hcovX⟩ := exists_log T hk
  have hy := mem X hX hXK
  have huniq : ∀ x : T.G, T.cov x = T.cov k → T.sq x = T.sq k → x = k := fun x h1 h2 =>
    (T.bij (T.cov k) (T.cov_mem k) (T.sq k) (T.sq_sq k)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  have hsq2 : ((T.sq (T.expt X) : ℂˣ) : ℂ) ^ 2 = ((T.sq k : ℂˣ) : ℂ) ^ 2 := by
    rw [T.sq_sq, T.sq_sq, hcovX]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
  · rw [← huniq _ hcovX (Units.ext h)]
    exact hy
  · have hk' : T.expt X * T.expt (torX (Pi.single a0 (2 * Real.pi))) = k := by
      apply huniq
      · rw [map_mul, hcov, mul_one, hcovX]
      · apply Units.ext
        rw [map_mul, hsqc]
        simp [h]
    rw [← hk']
    exact Subgroup.mul_mem _ hy hc

end GlobalTheory.CoverKGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadColumnWeightsStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ganGrossPrasad_column_weights : ∀ (S : Sizes) (Q : Entries S), Q.Good → ∃ kap : ∀ i : Fin (S.m + 1), DomWeight (S.nC i), (∀ r, (kap 0).dual.w r = hw Q.basePar r) ∧ (∀ r, (kap (Fin.last _)).dual.w r = hw Q.smallPar r) ∧ ∀ i : Fin S.m, StepW (Q.c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (-Q.c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)) (kap i.castSucc) (kap i.succ) := by
  first | exact @GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | exact GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | (intros; apply GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadRowWeightsStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ganGrossPrasad_row_weights : ∀ (S : Sizes) (Q : Entries S), Q.Good → ∃ lam : ∀ j : Fin (S.m + 1), DomWeight (S.nR j), (∀ i, (lam 0).w i = hw Q.psiPar i) ∧ (∀ i, (lam (Fin.last _)).w i = hw Q.bigPar i) ∧ ∀ j : Fin S.m, StepW (Q.e j - (S.nR j.succ / 2 : ℕ)) (-Q.e j + (S.nR j.castSucc / 2 : ℕ)) (lam j.castSucc) (lam j.succ) := by
  first | exact @GlobalTheory.OneFunctional.RowWeights.exists_row_weights | exact GlobalTheory.OneFunctional.RowWeights.exists_row_weights | (intros; apply GlobalTheory.OneFunctional.RowWeights.exists_row_weights <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOnePlaceIsoDirectSumPartitions
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem iso_directSum_fockOne : ∀ (a b : ℕ) (α β : ℤ), Iso (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b))) ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) (fockOne a b α β) := by
  intro a b α β
  obtain ⟨e⟩ := GlobalTheory.GLDuality.nonempty_equiv_polyRep a b
  obtain ⟨e, he⟩ := Iso.of_equiv e
  refine ⟨e, fun p x => ?_⟩
  have key : (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod
      ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b)))
      ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) p x =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
      (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) =>
        GlobalTheory.GLDuality.pieceRep (MonoidHom.id (GL (Fin a) ℂ)) (MonoidHom.id (GL (Fin b) ℂ)) i)
        (unitaryIncl a (conjU a p.1), unitaryIncl b p.2) x := by
    apply DFinsupp.ext
    intro i
    change TensorProduct.map ((((detU a ^ α) p.1 : ℂˣ) : ℂ) • (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)))
        ((((detU b ^ β) p.2 : ℂˣ) : ℂ) • (irr b (GlobalTheory.GLDuality.pad b i) p.2)) (x i) =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
        TensorProduct.map (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)) (irr b (GlobalTheory.GLDuality.pad b i) p.2) (x i)
    rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul, Units.val_mul, LinearMap.smul_apply]
  rw [key, map_smul, he]
  rfl

end GlobalTheory.OneFunctional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoTwistDetIrrShiftStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_twist_detU_pow_irr_of_weight_shift : ∀ (n : ℕ) (c : ℤ) (lam lam' : DomWeight n), (∀ i, lam'.w i = lam.w i + c) → Iso (twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  first | exact @GlobalTheory.OneFunctional.iso_twist_det_irr_shift | exact GlobalTheory.OneFunctional.iso_twist_det_irr_shift | (intros; apply GlobalTheory.OneFunctional.iso_twist_det_irr_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.SmallerSource

theorem discrete_series_gk_admissible_irreducible (X : ProvA) (h5 : admQ5 X) {r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) :
    AdmGK (X.ds r s lam).HK ∧ IrrGK (X.ds r s lam).HK := by
  obtain ⟨hU, -, -⟩ := h5 r s hrs
  set D := X.ds r s lam
  exact (hU D.U ⟨D.nontriv, D.irred⟩).2.2 D.HK D.ι ⟨D.ι_inj, D.ι_range, D.der⟩

theorem cPair_sub {p q i : ℕ} (hp : i ≤ p) (hq : i ≤ q) : cPair (p - i) (q - i) = cPair p q := by
  unfold cPair
  rw [Nat.cast_sub hp, Nat.cast_sub hq]
  ring

theorem intw_eq_zero (X : ProvA) (h2 : admH2 X) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam))
    (MM : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam).HK.V)
    (hf : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK f) : f = 0 := by
  by_contra hf0

  have hAI := discrete_series_gk_admissible_irreducible X h5 hrs lam
  have hI : Intw MM (X.ds r s lam).HK f := (isIntw_iff (X.fock p q r s) MM _ f).1 hf
  obtain ⟨hfin, -, hcone⟩ := hD r s lam hlam

  have hex : ∃ v, IsHW (X.ds r s lam).HK.act (blattner lam) v := by
    have hne : hwSub (X.ds r s lam).HK.act (blattner lam) ≠ ⊥ := by
      intro h
      rw [h] at hfin
      simp at hfin
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨v, hv0, hv⟩

  have hmin : ∀ ν w, IsHW (X.ds r s lam).HK.act ν w →
      degW (cPair p q) (blattner lam) ≤ degW (cPair p q) ν :=
    GlobalTheory.T.degW_blattner_le_of_blattnerCone r s (X.ds r s lam).HK lam (cPair p q) θ hcone hsign

  obtain ⟨⟨μ, P, hPJ, hP1, hP2, hfP⟩, -⟩ :=
    _root_.GlobalTheory.FockAlg.min_second p q r s MM (X.ds r s lam).HK f hAI.2 hAI.1 hI hf0 (blattner lam) hex hmin

  have hbot := ((h2 p q r s).2.2.2.2.1 μ (blattner lam)).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 μ ⊓ hwSub (X.fock p q r s).act2 (blattner lam) ⊓
      Submodule.span ℂ (X.fock p q r s).J := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hP1.2, hP2.2⟩, ?_⟩
    rw [J_eq (X.fock p q r s)]
    exact Submodule.subset_span hPJ
  rw [hbot] at hmem
  exact hP1.1 ((Submodule.mem_bot ℂ).1 hmem)

theorem no_map_smaller_source :
    ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  intro X _ h2 hD h5
  unfold ArchimedeanRallisFifth ARv DataAR DataARm
  constructor
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, -, hlam', -, hs'⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de hA
    have hno := ((_root_.GlobalTheory.LowestTypeDrop.lowestType_not_jointShape t al be ga de hA i hi1).2.2 hne hip hiq).1
    refine intw_eq_zero X h2 hD h5 (by omega) (lamA' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, hlam', -, hs'⟩ := _root_.GlobalTheory.TypesMirror.types_mirror t al be ga de hA
    have hno := ((_root_.GlobalTheory.LowestTypeDrop.lowestType_not_jointShape t al be ga de hA i hi1).2.2 hne hip hiq).2
    refine intw_eq_zero X h2 hD h5 (by omega) (lamM' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'

end GlobalTheory.SmallerSource
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorFockOnePlaceIsoUnitaryFock
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum Kronecker Matrix

namespace GlobalTheory.OneFunctional.FockTensor

theorem linSub_prod {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] (M : ι → Matrix σ σ ℂ)
    (f : ι → MvPolynomial (ι × σ) ℂ) : linSub M (∏ τ, f τ) = ∏ τ, linSub M (f τ) := by
  simp only [linSub, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, map_prod]

theorem linSub_rename {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] (M : ι → Matrix σ σ ℂ)
    (τ : ι) (f : MvPolynomial σ ℂ) :
    linSub M (rename (Prod.mk τ) f) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.sub (M τ)ᵀ f) := by
  unfold Formalism.GradedWeylDivisibility.sub
  simp only [linSub, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  congr 1
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Function.comp_apply, map_sum, Matrix.transpose_apply]

theorem fockOne_apply (a b : ℕ) (α β : ℤ) (h : U a) (g : U b) (f : MvPolynomial (Fin b × Fin a) ℂ) :
    fockOne a b α β (h, g) f =
      ((detU a h ^ α * detU b g ^ β : ℂˣ) : ℂ) • Formalism.GradedWeylDivisibility.sub (g.1 ⊗ₖ (star h.1)ᵀ)ᵀ f := rfl

theorem fock_apply {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ) (h : UG ι a) (g : UG ι b)
    (f : Pol ι a b) :
    fock a b α β (h, g) f =
      (((∏ τ, detU a (h τ) ^ α τ) * ∏ τ, detU b (g τ) ^ β τ : ℂˣ) : ℂ) •
        linSub (fun τ => (g τ).1 ⊗ₖ (star (h τ).1)ᵀ) f := rfl

theorem outer₂_fockOne_iso : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ),
    Iso (outer₂ fun τ => fockOne a b (α τ) (β τ)) (fock a b α β) := by
  intro ι _ _ a b α β
  obtain ⟨e, he⟩ := GlobalTheory.PolyTensor.exists_piTensor_equiv ι (Fin b × Fin a)
  refine ⟨e, ?_⟩
  rintro ⟨h, g⟩ x
  have key : e.toLinearMap ∘ₗ outer₂ (fun τ => fockOne a b (α τ) (β τ)) (h, g) =
      fock a b α β (h, g) ∘ₗ e.toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      outer₂_apply, PiTensorProduct.map_tprod, he, fockOne_apply, fock_apply, linSub_prod, linSub_rename]
    simp only [map_smul]
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, ← map_prod, Units.coe_prod, Units.val_mul]
  exact LinearMap.congr_fun key x

end GlobalTheory.OneFunctional.FockTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StrictInterlaceGanGrossPrasadBigSmallStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictInterlace_ganGrossPrasad_big_small : ∀ (S : Sizes) (Q : Entries S), Q.Good → GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.Interlace Q.bigPar Q.smallPar := by
  first | exact @GlobalTheory.StrictInterlace.interlace_big_small | exact GlobalTheory.StrictInterlace.interlace_big_small | (intros; apply GlobalTheory.StrictInterlace.interlace_big_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorRepresentationIntertwinerCompatStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_representation_intertwiner_compat : ∀ (Γ A B C D X Y : Type) [Monoid Γ] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (a : Representation ℂ Γ A) (b : Representation ℂ Γ B) (c : Representation ℂ Γ C) (d : Representation ℂ Γ D) (x : Representation ℂ Γ X) (y : Representation ℂ Γ Y) (p : A ⊗[ℂ] C →ₗ[ℂ] X) (q : B ⊗[ℂ] D →ₗ[ℂ] Y), Function.Surjective p → Function.Surjective q → (∀ g u w, p (a g u ⊗ₜ[ℂ] c g w) = x g (p (u ⊗ₜ[ℂ] w))) → (∀ g u w, q (b g u ⊗ₜ[ℂ] d g w) = y g (q (u ⊗ₜ[ℂ] w))) → (∀ l : Module.Dual ℂ (A ⊗[ℂ] C), (∀ g, b g = 1 → d g = 1 → ∀ u w, l (a g u ⊗ₜ[ℂ] c g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, p z = 0 → l z = 0) → (∀ l : Module.Dual ℂ (B ⊗[ℂ] D), (∀ g, a g = 1 → c g = 1 → ∀ u w, l (b g u ⊗ₜ[ℂ] d g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, q z = 0 → l z = 0) → Module.finrank ℂ (invFun (a.tprod (b.tprod (c.tprod d)))) = Module.finrank ℂ (invFun (x.tprod y)) := by
  first | exact @GlobalTheory.OneFunctional.finrank_invFun_two_contractions | exact GlobalTheory.OneFunctional.finrank_invFun_two_contractions | (intros; apply GlobalTheory.OneFunctional.finrank_invFun_two_contractions <;> assumption)
end

