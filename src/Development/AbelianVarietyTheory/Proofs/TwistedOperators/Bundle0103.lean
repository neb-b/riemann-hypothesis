module

public import Mathlib
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0040
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableDisjoint
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality.Compl

private theorem totalDegree_sum_C_mul_X_le_one {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (i : σ) :
    (∑ j, C (A i j) * X j : MvPolynomial σ ℂ).totalDegree ≤ 1 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X j).le

theorem totalDegree_linSub_le {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (P : MvPolynomial σ ℂ) :
    (sub A P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [sub, aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  calc _ ≤ ∑ i ∈ m.support, ((∑ j, C (A i j) * X j : MvPolynomial σ ℂ) ^ m i).totalDegree :=
        totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans
          ((Nat.mul_le_mul_left (m i) (totalDegree_sum_C_mul_X_le_one A i)).trans (le_of_eq (mul_one _)))
    _ ≤ P.totalDegree := le_totalDegree hm

def fockLin {σ : Type} (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun f := fockF f g
  map_add' _ _ := Formalism.REAL.fischerInner_add_left _ _ _
  map_smul' c f := by
    rw [smul_eq_C_mul, LFocks_C_mul_left]
    rfl

def orth {σ : Type} (K : Submodule ℂ (MvPolynomial σ ℂ)) : Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨅ m : K, LinearMap.ker (fockLin (m : MvPolynomial σ ℂ))

theorem mem_orth {σ : Type} {K : Submodule ℂ (MvPolynomial σ ℂ)} {v : MvPolynomial σ ℂ} :
    v ∈ orth K ↔ ∀ m ∈ K, fockF v m = 0 := by
  constructor
  · intro h m hm
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 h ⟨m, hm⟩)
  · intro h
    exact (Submodule.mem_iInf _).2 fun m => LinearMap.mem_ker.2 (h m m.2)

private theorem fockF_sum_smul_right {σ ι : Type} (s : Finset ι) (c : ι → ℂ) (b : ι → MvPolynomial σ ℂ)
    (v : MvPolynomial σ ℂ) :
    fockF v (∑ i ∈ s, c i • b i) = ∑ i ∈ s, star (c i) * fockF v (b i) := by
  rw [Formalism.REAL.fischerInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_right]

theorem inf_orth_ne_bot {σ : Type} (U K : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ U] (h : K < U) :
    U ⊓ orth K ≠ ⊥ := by
  classical
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le h.le
  have hlt : Module.finrank ℂ K < Module.finrank ℂ U := Submodule.finrank_lt_finrank_of_lt h
  let b := Module.finBasis ℂ K

  let Φ : U →ₗ[ℂ] (Fin (Module.finrank ℂ K) → ℂ) :=
    LinearMap.pi fun i => (fockLin ((b i : K) : MvPolynomial σ ℂ)).comp U.subtype
  have hker : LinearMap.ker Φ ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hbot, finrank_bot, add_zero] at h1
    have h2 : Module.finrank ℂ (LinearMap.range Φ) ≤ Module.finrank ℂ K := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  intro hbot
  apply hx0
  have hmem : (x : MvPolynomial σ ℂ) ∈ U ⊓ orth K := by
    refine ⟨x.2, mem_orth.2 fun m hm => ?_⟩
    have hm' : m = ∑ i, (b.repr ⟨m, hm⟩ i) • ((b i : K) : MvPolynomial σ ℂ) := by
      have e := congrArg Subtype.val (b.sum_repr ⟨m, hm⟩)
      rw [Submodule.coe_sum] at e
      simpa only [Submodule.coe_smul] using e.symm
    rw [hm', fockF_sum_smul_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : fockF (x : MvPolynomial σ ℂ) ((b i : K) : MvPolynomial σ ℂ) = 0 :=
      congrFun (LinearMap.mem_ker.1 hx) i
    rw [h0, mul_zero]
  rw [hbot] at hmem
  exact Submodule.coe_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)

theorem fockF_matRep {n n' : ℕ} (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (v m : MvPolynomial (Fin n' × Fin n) ℂ) :
    fockF (matRep n n' (g, h) v) m = fockF v (matRep n n' (star g, star h) m) := by
  have e : (((h : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ)ᴴ =
      (((star h : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
        ((star g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ := by
    rw [Units.coe_star, Units.coe_star, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      ← Matrix.conjTranspose_kronecker]
    ext a b
    rfl
  rw [matRep_apply, matRep_apply, Formalism.GradedWeylDivisibility.fockSubAdj, e]

theorem exists_stable_disjoint (n n' : ℕ) (M : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hM : M ≠ ⊤)
    (hst : ∀ p : GL (Fin n) ℂ × GL (Fin n') ℂ, ∀ v ∈ M, matRep n n' p v ∈ M) :
    ∃ N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ), N ≠ ⊥ ∧ N ⊓ M = ⊥ ∧
      ∀ p : GL (Fin n) ℂ × GL (Fin n') ℂ, ∀ v ∈ N, matRep n n' p v ∈ N := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, p ∉ M := by
    by_contra hc
    push_neg at hc
    exact hM (eq_top_iff.2 fun x _ => hc x)

  let U := restrictTotalDegree (Fin n' × Fin n) ℂ p.totalDegree
  have hpU : p ∈ U := (mem_restrictTotalDegree _ _ _).2 le_rfl
  have hdeg : ∀ (a : GL (Fin n) ℂ) (c : GL (Fin n') ℂ) (w : MvPolynomial (Fin n' × Fin n) ℂ),
      w ∈ U → matRep n n' (a, c) w ∈ U := by
    intro a c w hw
    rw [mem_restrictTotalDegree] at hw ⊢
    rw [matRep_apply]
    exact (totalDegree_linSub_le _ _).trans hw
  have hKU : M ⊓ U < U := lt_of_le_of_ne inf_le_right fun hEq => by
    have hK : p ∈ M ⊓ U := by rw [hEq]; exact hpU
    exact hp hK.1
  refine ⟨U ⊓ orth (M ⊓ U), inf_orth_ne_bot U (M ⊓ U) hKU, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro v ⟨⟨hvU, hvO⟩, hvM⟩
    rw [Submodule.mem_bot]
    by_contra hv0
    have h0 : fockF v v = 0 := mem_orth.1 hvO v ⟨hvM, hvU⟩
    have hpos := (Formalism.GradedWeylDivisibility.fockPos _ v hv0).1
    rw [h0, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨a, c⟩ v ⟨hvU, hvO⟩
    refine ⟨hdeg a c v hvU, mem_orth.2 fun m hm => ?_⟩
    rw [fockF_matRep]
    exact mem_orth.1 hvO _ ⟨hst (star a, star c) m hm.1, hdeg _ _ m hm.2⟩

end GlobalTheory.GLDuality.Compl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.FockAlg

theorem fock_structure : ∀ X : ProvA, admH2 X := by
  intro X p q r s
  refine ⟨fun d μ P hP hw => (_root_.GlobalTheory.FockAlg.degW_le_of_homog_wtSub p q r s).1 d μ P hP hw.1 hw.2.1,
    fun d μ P hP hw => (_root_.GlobalTheory.FockAlg.degW_le_of_homog_wtSub p q r s).2 d μ P hP hw.1 hw.2.1,
    fun μ P h0 ht hh => (_root_.GlobalTheory.FockAlg.harmonic_homog_of_type p q r s).1 μ P h0 ht hh,
    fun μ P h0 ht hh => (_root_.GlobalTheory.FockAlg.harmonic_homog_of_type p q r s).2 μ P h0 ht hh,
    fun μ μ' => ⟨_root_.GlobalTheory.JointHarm.finrank_joint_highest_of_shape p q r s μ μ', _root_.GlobalTheory.FockAlg.jointHarm_hw_eq_bot p q r s μ μ'⟩, ?_⟩
  intro u1 u2 hu d
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.FischerParts.fischer_parts p q r s d
  cases u1 <;> cases u2
  · simp at hu
  · have e1 : lowKer X (X.fock p q r s) false true = harm1 p q r s := by
      ext P; simp [lowKer, harm1, FockData.act2]
    have e2 : raised X (X.fock p q r s) false true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act2]
    rw [e1, e2]; exact h2
  · have e1 : lowKer X (X.fock p q r s) true false = harm2 p q r s := by
      ext P; simp [lowKer, harm2, FockData.act1]
    have e2 : raised X (X.fock p q r s) true false d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1]
    rw [e1, e2]; exact h1
  · have e1 : lowKer X (X.fock p q r s) true true = jointHarm p q r s := by
      ext P; simp [lowKer, jointHarm, harm1, harm2, FockData.act1, FockData.act2]
    have e2 : raised X (X.fock p q r s) true true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨
          ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1, FockData.act2]
    rw [e1, e2]; exact h3

end GlobalTheory.FockAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericSubmoduleMonomials
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.Proof.GenericSubmoduleMonomials

noncomputable def genSub (n n' k : ℕ) : MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ]
    MvPolynomial (Fin n × Fin k) (MvPolynomial (Fin n' × Fin n) ℂ) :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (X (v.1, t)) * X (t, v.2))

theorem map_eval_genSub (n n' k : ℕ) (x : Matrix (Fin n') (Fin n) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) :
    map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k f) =
      aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [genSub, aeval_C, aeval_C]
    simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    have hv : map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k (X v)) =
        ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [genSub, aeval_X, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, map_C, map_X, eval_X]
    rw [map_mul, map_mul, hp, map_mul, hv, aeval_X]

theorem repr_basisMonomials {σ : Type} (φ : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (basisMonomials σ ℂ).repr φ m = AddMonoidAlgebra.coeff φ m := rfl

theorem exists_pairing : ∀ (n n' k : ℕ), ∃ T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ, ∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f)) := by
  intro n n' k
  refine ⟨(basisMonomials (Fin n × Fin k) ℂ).constr ℂ (fun m => ((∏ j ∈ m.support, (m j).factorial : ℕ) : ℂ) •
    (((lcoeff (MvPolynomial (Fin n' × Fin n) ℂ) m).restrictScalars ℂ) ∘ₗ (genSub n n' k).toLinearMap)), ?_⟩
  intro φ f x
  have hs : ((basisMonomials (Fin n × Fin k) ℂ).repr φ).support = φ.support := by
    ext m
    rw [Finsupp.mem_support_iff, repr_basisMonomials, mem_support_iff]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Module.Basis.constr_apply, Finsupp.sum, hs, fockF, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [repr_basisMonomials, ← map_eval_genSub, coeff_map, coeff_map]
  simp only [LinearMap.smul_apply, smul_eval, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.restrictScalars_apply, lcoeff_apply, starRingEnd_apply, star_star]
  ring

end GlobalTheory.Proof.GenericSubmoduleMonomials
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetOperatorBideterminantBasisReprIsAlgebraic
section
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.JetAlg

open Formalism.L2.DIV Formalism.BasicNotions

abbrev algPol (σ : Type) : Subring (MvPolynomial σ ℂ) :=
  (MvPolynomial.map (algebraMap (algebraicClosure ℚ ℂ) ℂ)).range

theorem X_mem {σ : Type} (v : σ) : (X v : MvPolynomial σ ℂ) ∈ algPol σ := ⟨X v, map_X _ _⟩

theorem monomial_mem {σ : Type} (u : σ →₀ ℕ) {c : ℂ} (hc : IsAlgebraic ℚ c) :
    monomial u c ∈ algPol σ :=
  ⟨monomial u ⟨c, mem_algebraicClosure_iff.2 hc⟩, by rw [map_monomial]; rfl⟩

theorem coeff_isAlgebraic {σ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ algPol σ) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (p.coeff m) := by
  obtain ⟨q, rfl⟩ := hp
  rw [coeff_map]
  exact mem_algebraicClosure_iff.1 (q.coeff m).2

theorem det_mem {σ : Type} {s : ℕ} (M : Matrix (Fin s) (Fin s) (MvPolynomial σ ℂ))
    (h : ∀ p q, M p q ∈ algPol σ) : M.det ∈ algPol σ := by
  choose N hN using h
  refine ⟨(Matrix.of N).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [hN]

theorem aeval_mem {σ τ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ algPol σ) (g : σ → MvPolynomial τ ℂ)
    (hg : ∀ v, g v ∈ algPol τ) : aeval g p ∈ algPol τ := by
  obtain ⟨q, rfl⟩ := hp
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨C a, by simp [algebraMap_eq]⟩
  | add p q hp hq => rw [map_add (f := _), map_add (f := _)]; exact add_mem hp hq
  | mul_X p v hp => rw [map_mul, map_mul, map_X, aeval_X]; exact mul_mem hp (hg v)

theorem bVVfun_mem {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (j : VVIdx lam) :
    bVVfun ℂ lam j ∈ algPol (ι × Fin n × Fin n) := by
  unfold bVVfun ten
  refine prod_mem fun τ _ => ?_
  obtain ⟨-, -, K, sz, hsz, I, -, -, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℂ n n (lam τ).natW).choose_spec.2 (j τ)
  have hb' : ssB ℂ (lam τ).natW (j τ) = Formalism.GradedWeylDivisibility.bideterminant ℂ sz hsz I := hb
  show Formalism.GradedWeylDivisibility.blockEmb ℂ τ (ssB ℂ (lam τ).natW (j τ)) ∈ _
  rw [hb']
  have hB : Formalism.GradedWeylDivisibility.bideterminant ℂ sz hsz I ∈ algPol (Fin n × Fin n) := by
    unfold Formalism.GradedWeylDivisibility.bideterminant Formalism.GradedWeylDivisibility.initMinor
    exact prod_mem fun k _ => det_mem _ fun p q => X_mem _
  obtain ⟨q, hq⟩ := hB
  exact ⟨Formalism.GradedWeylDivisibility.blockEmb _ τ q, by rw [← hq]; exact map_rename _ _ _⟩

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem frDet_mem (τ : ι) : frDet ℂ a τ ∈ algPol (ι × Fin a × Fin a) :=
  det_mem _ fun _ _ => X_mem _

theorem subD_mem {P : Pol ℂ ι a} (hP : P ∈ algPol (ι × Fin a × Fin a)) :
    subD ℂ ι a b P ∈ algPol ((ι × Fin b × Fin b) ⊕ DVar ι a b) := by
  unfold subD
  refine aeval_mem hP _ fun v => ?_
  split_ifs
  · exact sum_mem fun β _ => mul_mem (X_mem _) (X_mem _)
  · exact zero_mem _

theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → ℂ) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) (c : ℂ) :
    jetLin J (monomial m c) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h1 : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) = c • basisMonomials _ ℂ m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

theorem jetLin_mem (J : (DVar ι a b →₀ ℕ) → ℂ) (hJ : ∀ m, IsAlgebraic ℚ (J m))
    {p : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ} (hp : p ∈ algPol _) :
    jetLin J p ∈ algPol (ι × Fin b × Fin b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [p.as_sum, map_sum]
  refine sum_mem fun m _ => ?_
  rw [jetLin_monomial]
  exact monomial_mem _ ((coeff_isAlgebraic hp m).mul (hJ _))

theorem jetMap_mem (J : (DVar ι a b →₀ ℕ) → ℂ) (hJ : ∀ m, IsAlgebraic ℚ (J m)) (nn : ι → ℕ)
    {P : Pol ℂ ι a} (hP : P ∈ algPol (ι × Fin a × Fin a)) :
    jetMap J nn P ∈ algPol (ι × Fin b × Fin b) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  refine jetLin_mem J hJ (subD_mem (mul_mem hP (prod_mem fun τ _ => pow_mem (frDet_mem τ) _)))

theorem descent {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) (hv : LinearIndependent ℂ v)
    (hvA : ∀ k, v k ∈ algPol σ) (x : κ → ℂ) (hQ : ∑ k, x k • v k ∈ algPol σ) (k : κ) :
    IsAlgebraic ℚ (x k) := by
  set A := algebraicClosure ℚ ℂ
  obtain ⟨pr, hpr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap A ℂ)
    (LinearMap.ker_eq_bot.2 (algebraMap A ℂ).injective)
  have hp : ∀ c : A, pr (algebraMap A ℂ c) = c := fun c => LinearMap.congr_fun hpr c
  have key : ∑ k, x k • v k = ∑ k, (algebraMap A ℂ (pr (x k))) • v k := by
    ext m
    have hcoef : ∀ k, ∃ c : A, (v k).coeff m = algebraMap A ℂ c := fun k => by
      obtain ⟨q, hq⟩ := hvA k
      exact ⟨q.coeff m, by rw [← hq, coeff_map]⟩
    choose c hc using hcoef
    obtain ⟨q, hq⟩ := hQ
    have h1 : (∑ k, x k • v k).coeff m = algebraMap A ℂ (pr ((∑ k, x k • v k).coeff m)) := by
      rw [← hq, coeff_map, hp]
    rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coeff_sum, coeff_smul, smul_eq_mul, hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : x k * algebraMap A ℂ (c k) = c k • x k := by rw [Algebra.smul_def, mul_comm]
    rw [this, map_smul, smul_eq_mul, map_mul, mul_comm]
  have h0 := Fintype.linearIndependent_iff.1 hv (fun k => x k - algebraMap A ℂ (pr (x k)))
    (by simp only [sub_smul, Finset.sum_sub_distrib, key, sub_self]) k
  rw [sub_eq_zero.1 h0]
  exact mem_algebraicClosure_iff.1 (pr (x k)).2

theorem repr_jetOp_isAlgebraic : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight a)
    (lam' : ι → Formalism.BasicNotions.DomWeight b) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ), (∀ m, IsAlgebraic ℚ (J m)) →
    JetInVV ℂ lam lam' nn → ∀ (i : Formalism.L2.DIV.VVIdx lam') (j : Formalism.L2.DIV.VVIdx lam),
    IsAlgebraic ℚ ((Formalism.L2.DIV.bVV ℂ lam').repr (jetOp lam lam' J nn (Formalism.L2.DIV.bVV ℂ lam j)) i) := by
  intro ι _ a b lam lam' J nn hJ hV i j
  have hQV : jetMap J nn (bVVfun ℂ lam j) ∈ VV ℂ lam' :=
    hV J _ (by rw [← bVV_coe]; exact (bVV ℂ lam j).2)
  have hop : jetOp lam lam' J nn (bVV ℂ lam j) = ⟨_, hQV⟩ := by
    simp only [jetOp, retrVV, LinearMap.comp_apply, Submodule.subtype_apply, bVV_coe]
    exact Submodule.projectionOnto_apply_left _ ⟨_, hQV⟩
  rw [hop]
  have hsum : jetMap J nn (bVVfun ℂ lam j) =
      ∑ k, (bVV ℂ lam').repr ⟨_, hQV⟩ k • bVVfun ℂ lam' k := by
    have := congrArg Subtype.val ((bVV ℂ lam').sum_repr ⟨_, hQV⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe] at this
    exact this.symm
  refine descent (bVVfun ℂ lam') (bVVfun_spec ℂ lam').1 (bVVfun_mem lam') _ ?_ i
  rw [← hsum]
  exact jetMap_mem J hJ nn (bVVfun_mem lam j)

end GlobalTheory.JetAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamUnitaryMatrixEqExpLieAlgebra
section
open Matrix

namespace GlobalTheory.OneParamUnitary

open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem oneParam_eq_exp_lieU {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hc : Continuous u) (h0 : u 0 = 1) (hadd : ∀ s t, u (s + t) = u s * u t)
    (hU : ∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) :
    ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have hsm : ContDiff ℝ ∞ u :=
    GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (Fin n) (Fin n) ℂ) u hc h0 hadd
  have hdiff : Differentiable ℝ u := hsm.differentiable (by simp)
  set Y := deriv u 0 with hY
  have hY0 : HasDerivAt u Y 0 := (hdiff 0).hasDerivAt
  have hder : ∀ t, HasDerivAt u (u t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => u (s - t)) Y t :=
      (show HasDerivAt u Y (t - t) by simpa using hY0).comp_sub_const t t
    have h2 := h1.const_mul (u t)
    have h3 : (fun s => u t * u (s - t)) = u := by
      funext s
      rw [← hadd]; congr 1; ring
    rwa [h3] at h2

  have hexp : ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
    set v : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => u t * NormedSpace.exp (t • (-Y)) with hv
    have hvd : ∀ t, HasDerivAt v 0 t := by
      intro t
      have hE := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Y) t
      have := (hder t).mul hE
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel] at this
      exact this
    have hvc : ∀ t, v t = v 0 := fun t =>
      is_const_of_deriv_eq_zero (fun s => (hvd s).differentiableAt) (fun s => (hvd s).deriv) t 0
    have hv0 : v 0 = 1 := by simp [hv, h0]
    intro t
    have hcomm : Commute (t • (-Y)) (t • Y) :=
      ((Commute.refl Y).neg_left.smul_left t).smul_right t
    have hinv : NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    calc u t = u t * (NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y)) := by rw [hinv, Matrix.mul_one]
      _ = v t * NormedSpace.exp (t • Y) := by rw [hv, Matrix.mul_assoc]
      _ = NormedSpace.exp (t • Y) := by rw [hvc t, hv0, Matrix.one_mul]
  refine ⟨Y, ?_, hexp⟩

  show Yᴴ * G + G * Y = 0
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => star A
      map_add' := fun A B => star_add A B
      map_smul' := fun c A => by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul] }
  have hst : HasDerivAt (fun t => star (u t)) (star Y) 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hY0
  have hw := (hst.mul_const G).mul hY0
  have hconst : ((fun t => star (u t) * G) * u) = fun _ => G := by
    funext t; exact hU t
  rw [hconst] at hw
  have := (hasDerivAt_const (0 : ℝ) G).unique hw
  rw [h0, star_one, Matrix.one_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose] at *
  exact this.symm

end GlobalTheory.OneParamUnitary
end

