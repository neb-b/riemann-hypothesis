module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnimodularLatticeLocalConjSymm
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CcMulSelf
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem cc_mul_self (φ : Formalism.HC.Frame) : φ.cc * φ.cc = 1 := by
  ext <;> simp [Formalism.HC.Frame.cc, c0]

theorem hcAt_eq_hc : ∀ (D : D7) (ρ : D.what₂.Tau) (g : D.R.GG), (((D.eTau ρ : D.R.Psi) : D.R.GG) = g ∨ ((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc = g) → hcAt D g = D.hc ρ := by
  intro D ρ g h
  have hm : ((D.eTau ρ : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2
  have hp : plc g = ((D.eTau ρ : D.R.Psi) : D.R.GG) := by
    rcases h with rfl | rfl
    · simp [plc, hm]
    · unfold plc
      have h2 : (((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc).1.2 ≠ 1 := by
        simp [Formalism.HC.Frame.cc, c0, hm]
      rw [if_neg h2, mul_comm, mul_assoc, cc_mul_self, mul_one]
  unfold hcAt
  have : (⟨plc g, plc_mem g⟩ : D.R.Psi) = D.eTau ρ := Subtype.ext hp
  rw [this, Equiv.symm_apply_apply]

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClusterDepthAtPrimeEqLeastPowerDepth
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem jA_eq_depth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  intro D L l hl hlA
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hx : (1 : ℝ) < (l : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) < LevelStarExponents.lA L := by linarith
  have key : ∀ j : ℕ, LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j ↔ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ ≤ j := by
    intro j
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow hx hA, Real.rpow_natCast]
  have hlog : 1 < Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L) := by
    rw [Real.lt_logb_iff_rpow_lt hx hA, Real.rpow_one]; linarith
  have hc : 1 ≤ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    rw [Nat.one_le_ceil_iff]; linarith
  have hset : {j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} = Set.Ici ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    ext j; simp only [Set.mem_setOf_eq, Set.mem_Ici]; exact key j
  unfold jA depth
  rw [hset, csInf_Ici, max_eq_right hc]

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmpFamMemFunMod
section
namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

namespace CmpMem

theorem isLattice_map {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A : GL (Fin k) K)
    {L : Submodule R (Fin k → K)} (hL : IsLattice R L) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) := by
  obtain ⟨g, hg, rfl⟩ := hL
  refine ⟨(A : Matrix (Fin k) (Fin k) K) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul hg
  · unfold colSpan
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf}

theorem isLatTup_smul (C : Level P) (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) :=
  fun v => isLattice_map (C.act v γ) (hL v)

variable {X : Fields} (T : PlTie X P) {n : ℕ} (hn : n = P.m + 1) {lam : X.Tau → DomWeight n} {c : ℤ}

variable {S : GSD X.K} (Y : PSys X n p lam S)

end CmpMem

end GlobalTheory.GO
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationDualWeightInvolutive
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp.Invol

theorem aeval_scale {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {r n : ℕ} (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (colW r n) f ν) (c : S)
    (x : Fin r × Fin n → S) :
    aeval (fun v => c * x v) f = c ^ (∑ i, ν i) * aeval x f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (colW r n) d = ν := hf (mem_support_iff.mp hd)
  have hs : ∑ i, ν i = ∑ v, d v := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finset.sum_apply, colW, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.mul_sum]
    simp [Pi.single_apply]
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

def cofM (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MP R n) :=
  (genM R n).adjugate.transpose.submatrix id Fin.revPerm

theorem map_genM (R : Type) [CommRing R] (n : ℕ) :
    (cofAct R n).mapMatrix (genM R n) = cofM R n := by
  ext1 a s
  simp [cofAct, genM, cofM]

theorem det_cofM (R : Type) [CommRing R] (m : ℕ) :
    (cofM R (m + 1)).det = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : MP R (m + 1)) *
      (genM R (m + 1)).det ^ m := by
  rw [cofM, Matrix.det_permute', Matrix.det_transpose, Matrix.det_adjugate]
  simp

theorem cofAct_det (R : Type) [CommRing R] (n : ℕ) :
    cofAct R n (genM R n).det = (cofM R n).det := by
  rw [AlgHom.map_det, map_genM]

theorem det_mul_cofAct_cofAct_X (R : Type) [CommRing R] (n : ℕ) (v : Fin n × Fin n) :
    (genM R n).det * cofAct R n (cofAct R n (X v)) = (cofM R n).det * X v := by
  have h1 : cofM R n * (genM R n).transpose.submatrix Fin.revPerm id = (genM R n).det • (1 : Matrix _ _ _) := by
    rw [cofM, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Matrix.mul_adjugate]
    simp
  have h2 : (cofM R n).det • (genM R n).transpose.submatrix Fin.revPerm id =
      (genM R n).det • (cofM R n).adjugate := by
    have := congrArg (fun M => (cofM R n).adjugate * M) h1
    simpa [← Matrix.mul_assoc, Matrix.adjugate_mul] using this
  have h3 : cofAct R n (cofAct R n (X v)) = (cofM R n).adjugate v.2.rev v.1 := by
    rw [← map_genM, ← AlgHom.map_adjugate]
    simp [cofAct]
  have h4 := congrFun (congrFun h2 v.2.rev) v.1
  rw [h3]
  simpa [genM] using h4.symm

theorem cofAct_cofAct (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) (f : MP R n)
    (hf : IsWeightedHomogeneous (colW n n) f ν) :
    (genM R n).det ^ (∑ i, ν i) * cofAct R n (cofAct R n f) = (cofM R n).det ^ (∑ i, ν i) * f := by
  have h1 : cofAct R n (cofAct R n f) = aeval (fun v => cofAct R n (cofAct R n (X v))) f := by
    have : (cofAct R n).comp (cofAct R n) = aeval (fun v => cofAct R n (cofAct R n (X v))) := by
      ext1 v; simp
    exact DFunLike.congr_fun this f
  rw [h1, ← aeval_scale ν f hf]
  simp only [det_mul_cofAct_cofAct_X]
  rw [aeval_scale ν f hf, aeval_X_left_apply]

theorem cofRel_invol (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) :
    ∃ ε : ℤˣ, ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∀ g : MP R (m + 1),
      CofRel R m ν f g → CofRel R m (nuDual ν) g ((ε : ℤ) • f) := by
  refine ⟨Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) ^ ν 0, fun f hf g hg => ?_⟩
  have hD : (genM R (m + 1)).det ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin (m + 1)) R
  have hδ : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : MP R (m + 1)) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with h | h <;> simp [h]
  have hC : (cofM R (m + 1)).det ≠ 0 := by
    rw [det_cofM]; exact mul_ne_zero hδ (pow_ne_zero _ hD)
  have hle : ν 0 ≤ ∑ i, ν i := Finset.single_le_sum (fun i _ => Nat.zero_le (ν i)) (Finset.mem_univ _)
  have hd0 : nuDual ν 0 = ν 0 := by simp [nuDual, h0]
  have hle' : nuDual ν 0 ≤ ∑ i, nuDual ν i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (nuDual ν i)) (Finset.mem_univ _)
  have hsum : ∑ i, nuDual ν i + ∑ i, ν i = (m + 1) * ν 0 := by
    rw [← Equiv.sum_comp Fin.revPerm ν, ← Finset.sum_add_distrib]
    have : ∀ i : Fin (m + 1), nuDual ν i + ν (Fin.revPerm i) = ν 0 :=
      fun i => Nat.sub_add_cancel (hν (Fin.zero_le i.rev))
    simp only [this]
    simp
  have hexp : ∑ i, ν i + (∑ i, nuDual ν i - nuDual ν 0) = m * ν 0 := by
    rw [add_mul] at hsum; omega
  have h1 := cofAct_cofAct R (m + 1) ν f hf.1
  unfold CofRel at hg ⊢
  rw [← hg, map_mul, map_pow, cofAct_det] at h1
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  have he' : ∑ i, ν i - ν 0 = e := by omega
  rw [he'] at h1
  have h2 : (genM R (m + 1)).det ^ (∑ i, ν i) * cofAct R (m + 1) g = (cofM R (m + 1)).det ^ ν 0 * f := by
    apply mul_left_cancel₀ (pow_ne_zero e hC)
    rw [mul_left_comm, h1, he]
    ring
  apply mul_left_cancel₀ (pow_ne_zero (∑ i, ν i) hD)
  rw [h2, ← mul_assoc, ← pow_add, hexp, det_cofM, mul_pow, pow_mul]
  simp only [Units.val_pow_eq_pow_val, zsmul_eq_mul, Int.cast_pow]
  ring

end GlobalTheory.ValCmp.Invol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowActEquivariant
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp.Eqv

theorem degree_of_colWeight {n : ℕ} {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [colW, Pi.single_apply]

theorem rowAct_smul_matrix {n : ℕ} {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (colW n n) f ν) :
    rowAct R (c • g) f = c ^ (∑ j, ν j) • rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_colWeight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

theorem rowAct_genM {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) :
    (rowAct R (n := n) g).mapMatrix (genM R n) = (C : R →+* MP R n).mapMatrix g * genM R n := by
  ext a s : 2
  simp [rowAct, genM, Matrix.mul_apply]

theorem rowAct_det_genM {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (genM R n).det = C g.det * (genM R n).det := by
  rw [AlgHom.map_det, rowAct_genM, Matrix.det_mul, RingHom.map_det]

theorem rowAct_transpose_cofAct {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) (f : MP R n) :
    rowAct R g.transpose (cofAct R n f) = cofAct R n (rowAct R g.adjugate f) := by
  have h : (rowAct R (n := n) g.transpose).comp (cofAct R n) = (cofAct R n).comp (rowAct R g.adjugate) := by
    apply MvPolynomial.algHom_ext
    intro v
    have h1 : (rowAct R (n := n) g.transpose).mapMatrix (genM R n).adjugate =
        (genM R n).adjugate * (C : R →+* MP R n).mapMatrix g.transpose.adjugate := by
      rw [AlgHom.map_adjugate, rowAct_genM, Matrix.adjugate_mul_distrib, RingHom.map_adjugate]
    have h2 := congrFun (congrFun h1 v.2.rev) v.1
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AlgHom.comp_apply, AlgHom.comp_apply, cofAct, aeval_X, h2, rowAct, aeval_X, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, aeval_X, aeval_C, ← Matrix.adjugate_transpose, mul_comm]
    rfl
  exact DFunLike.congr_fun h f

theorem cofRel_rowAct : ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit h.det → ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ g : MP K (m + 1), CofRel K m ν f g → CofRel K m ν (rowAct K h⁻¹ f) (h.det ^ (-(ν 0 : ℤ)) • rowAct K h.transpose g) := by
  intro K _ m ν h hh f hf g hfg
  have hd : h.det ≠ 0 := hh.ne_zero
  have hadj : h.adjugate = h.det • h⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hd, one_smul]
  have hle : ν 0 ≤ ∑ i, ν i := Finset.single_le_sum (f := ν) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  unfold CofRel at hfg ⊢
  have h1 := congrArg (rowAct K h.transpose) hfg
  rw [rowAct_transpose_cofAct, hadj, rowAct_smul_matrix _ _ _ hf.1, map_smul, map_mul, map_pow, rowAct_det_genM,
    Matrix.det_transpose, mul_pow, ← C_pow, mul_assoc, ← smul_eq_C_mul] at h1
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  rw [he, Nat.add_sub_cancel_left] at h1 ⊢
  rw [pow_add, mul_comm (h.det ^ ν 0), mul_smul] at h1
  have h2 : _ = _ := smul_right_injective _ (pow_ne_zero e hd) h1
  rw [mul_smul_comm, h2, smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hd), one_smul]

end GlobalTheory.ValCmp.Eqv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwap
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp

theorem adjugate_transvection_of_ne {A : Type} [CommRing A] {n : ℕ} (a b : Fin n) (hab : a ≠ b) (c : A) :
    (Matrix.transvection a b c).adjugate = Matrix.transvection a b (-c) := by
  have h1 : Matrix.transvection a b c * Matrix.transvection a b (-c) = 1 := by
    rw [Matrix.transvection_mul_transvection_same a b hab, add_neg_cancel, Matrix.transvection_zero]
  calc (Matrix.transvection a b c).adjugate
      = (Matrix.transvection a b c).adjugate * (Matrix.transvection a b c * Matrix.transvection a b (-c)) := by
        rw [h1, Matrix.mul_one]
    _ = Matrix.transvection a b (-c) := by
        rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transvection_of_ne a b hab, one_smul,
          Matrix.one_mul]

theorem rowGen_map_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) :
    (rowGen R (n := n) b a).toRingHom.mapMatrix (genM R n) =
      Matrix.transvection a b Polynomial.X * (Polynomial.C (R := MP R n)).mapMatrix (genM R n) := by
  ext1 i s
  by_cases hi : i = a
  · subst hi
    rw [Matrix.transvection_mul_apply_same]
    simp [genM, rowGen]
  · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hi]
    simp [genM, rowGen, hi]

theorem rowGen_det_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    rowGen R (n := n) b a (genM R n).det = Polynomial.C (genM R n).det := by
  have h := RingHom.map_det (rowGen R (n := n) b a).toRingHom (genM R n)
  rw [rowGen_map_genM, Matrix.det_mul, Matrix.det_transvection_of_ne a b hab, one_mul,
    ← RingHom.map_det] at h
  exact h

theorem rowGen_adjugate_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (t i : Fin n) :
    rowGen R (n := n) b a ((genM R n).adjugate t i) =
      Polynomial.C ((genM R n).adjugate t i) +
        (if i = b then -Polynomial.X * Polynomial.C ((genM R n).adjugate t a) else 0) := by
  have h := RingHom.map_adjugate (rowGen R (n := n) b a).toRingHom (genM R n)
  rw [rowGen_map_genM, Matrix.adjugate_mul_distrib, adjugate_transvection_of_ne a b hab,
    ← RingHom.map_adjugate] at h
  have h2 := congrFun (congrFun h t) i
  refine Eq.trans h2 ?_
  by_cases hi : i = b
  · subst hi
    rw [Matrix.mul_transvection_apply_same]
    simp
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hi]
    simp [hi]

theorem rowGen_cofAct (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (f : MP R n) :
    rowGen R (n := n) b a (cofAct R n f) =
      ((rowGen R (n := n) a b f).map (cofAct R n).toRingHom).comp (Polynomial.C (-1) * Polynomial.X) := by
  induction f using MvPolynomial.induction_on with
  | C x =>
    have e1 : (C x : MP R n) = algebraMap R _ x := rfl
    rw [e1, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, Polynomial.algebraMap_apply,
      Polynomial.map_C, Polynomial.C_comp]
    exact congrArg Polynomial.C ((cofAct R n).commutes x).symm
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.map_add (f := _), Polynomial.add_comp]
  | mul_X p v hp =>
    simp only [map_mul, hp, Polynomial.map_mul, Polynomial.mul_comp]
    refine congrArg₂ (· * ·) rfl ?_
    have e1 : ∀ w : Fin n × Fin n, cofAct R n (X w) = (genM R n).adjugate w.2.rev w.1 := fun w => by
      simp [cofAct]
    rw [e1, rowGen_adjugate_genM R n a b hab]
    by_cases hv : v.1 = b
    · simp [rowGen, hv, e1]
    · simp [rowGen, hv, e1]

theorem cofRel_rowDiv (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ)
    (f g : MP R (m + 1)) (hab : a ≠ b) (h : CofRel R m ν f g) :
    CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  unfold CofRel at h ⊢
  have h1 := congrArg (fun p => (rowGen R (n := m + 1) b a p).coeff k) h
  simp only [map_mul, map_pow, rowGen_det_genM R _ a b hab, rowGen_cofAct R _ a b hab,
    Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at h1
  rw [← map_pow, Polynomial.coeff_C_mul] at h1
  have h2 : ((-1 : MP R (m + 1)) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  unfold rowDiv
  rw [zsmul_eq_mul, mul_left_comm, h1]
  push_cast
  rw [mul_left_comm, h2, mul_one]
  rfl

end GlobalTheory.ValCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCyclotomicCharacterPeriodDatum
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem continuous_cycLL_period : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l),
    Continuous (fun s => ((cycLL (P.PD K) ↥LL.1 s : (↥LL.1)ˣ) : ↥LL.1)) := by
  intro l _ P K LL
  have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1
  have e : (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1)) =
      fun g : ↥(GK K) => algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) := by
    funext g
    change algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
    rw [P.PD_χ]
  rw [e]
  refine Continuous.subtype_mk (f := fun g : ↥(GK K) =>
    algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])) ?_ _
  exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h.comp continuous_subtype_val)

end GlobalTheory.HTW.Rec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersLetterwise
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem clusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  intro n th j hC t ht
  obtain ⟨F, sp, hF, huniq⟩ := hC
  obtain ⟨x, ⟨hxF, hxt⟩, -⟩ := huniq t ht
  obtain ⟨hthx, hspj, -, -, hbetween, hbefore⟩ := hF x hxF
  rcases hxt with rfl | rfl
  · exact Or.inl hbefore
  · by_cases hsp0 : sp x = 0
    · left
      rw [hsp0, Nat.cast_zero, add_zero]
      exact hbefore
    · right
      refine ⟨sp x, Nat.one_le_iff_ne_zero.2 hsp0, hspj, by simpa using hthx, fun k hk1 hk2 hkd => ?_⟩
      rcases lt_or_gt_of_ne hkd with hlt | hgt
      · have e : x + (sp x : ZMod n) - k = x + ((sp x - k : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hlt.le]
          ring
        rw [e]
        exact hbetween (sp x - k) (by omega) (by omega)
      · have e : x + (sp x : ZMod n) - k = x - ((k - sp x : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hgt.le]
          ring
        rw [e]
        exact hbefore (k - sp x) (by omega) (by omega)

end GlobalTheory.HTW.Rec
end

