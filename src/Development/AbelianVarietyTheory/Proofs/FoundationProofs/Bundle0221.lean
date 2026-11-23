module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0216

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremal
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.ExtremalGen

open GlobalTheory.TensorHW (mem_wt diag_comm)

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def Supp (S : Ix p q → Ix p q → Prop) (Z : Mat p q) : Prop := ∀ a b, ¬ S a b → Z a b = 0

lemma supp_Eab {S : Ix p q → Ix p q → Prop} {a b : Ix p q} (h : S a b) : Supp S (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

lemma supp_mul {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : S a c
  · rw [hZ c b (fun hcb => hab (hS.trans hac hcb)), mul_zero]
  · rw [hY a c hac, zero_mul]

lemma supp_comm {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z - Z * Y) := by
  intro a b hab
  rw [Matrix.sub_apply, supp_mul hS hY hZ a b hab, supp_mul hS hZ hY a b hab, sub_zero]

lemma supp_ind {S : Ix p q → Ix p q → Prop} (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, S a b → act (Eab a b) y ∈ N) {Z : Mat p q} (hZ : Supp S Z) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  by_cases hab : S a b
  · have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
      rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (h a b hab)
  · rw [hZ a b hab]
    simp

lemma lie_apply {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (Y Z : Mat p q) (y : V) :
    act Y (act Z y) = act Z (act Y y) + act (Y * Z - Z * Y) y := by
  rw [hL Y Z]
  simp

lemma eig_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (c : Ix p q → ℂ)
    (a b : Ix p q) {t : ℂ} {y : V}
    (hy : y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) t) :
    act (Eab a b) y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (t + (c a - c b)) := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [lie_apply hL, diag_comm, hy, map_smul, map_smul, LinearMap.smul_apply, add_smul]

lemma eig_of_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (c : Ix p q → ℂ) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ wtSub act μ) :
    v ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (∑ a, c a * ((μ a : ℚ) : ℂ)) := by
  rw [mem_wt] at hv
  rw [Module.End.mem_eigenspace_iff]
  have : (Matrix.diagonal c : Mat p q) = ∑ a, c a • Eab a a := by
    ext i j
    simp only [Matrix.sum_apply, Eab, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv, Finset.sum_smul,
    mul_smul]

theorem exists_generated :
    ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  intro p q V _ _ act hL S hS r hr μ v hv hup
  have hv' := mem_wt.1 hv
  set F : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ a b, S a b → r a < r b → ∀ y ∈ N, act (Eab b a) y ∈ N} with hF
  have hG : sInf F ∈ F := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b hab hlt y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b hab hlt y (Submodule.mem_sInf.1 hy M hM)
  have hG' : (sInf F ⊓ ⨅ (Z : Mat p q) (_ : Supp S Z), (sInf F).comap (act Z)) ∈ F := by
    constructor
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      refine ⟨hG.1, fun Z hZ => supp_ind act _ v (fun a b hab => ?_) hZ⟩
      rcases lt_trichotomy (r a) (r b) with h | h | h
      · rw [hup a b hab h]; exact Submodule.zero_mem _
      · obtain rfl := hr h
        rw [hv']; exact Submodule.smul_mem _ _ hG.1
      · exact hG.2 b a (hS.symm hab) h v hG.1
    · intro a b hab hlt y hy
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
      refine ⟨hG.2 a b hab hlt y hy.1, fun Z hZ => ?_⟩
      have hE := supp_Eab (hS.symm hab)
      rw [lie_apply hL]
      exact Submodule.add_mem _ (hG.2 a b hab hlt _ (hy.2 Z hZ)) (hy.2 _ (supp_comm hS hZ hE))
  set c : Ix p q → ℂ := fun a => (r a : ℂ) with hc
  set h : Module.End ℂ V := act (Matrix.diagonal c) with hh
  have hcast : ∀ ν : Ix p q → ℚ,
      ∑ a, c a * ((ν a : ℚ) : ℂ) = ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν; simp [hc]
  have heig : ∀ (ν : Ix p q → ℚ) (x : V), x ∈ wtSub act ν →
      x ∈ h.eigenspace ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν x hx
    rw [← hcast]; exact eig_of_wt c hx
  set m : ℚ := ∑ a, (r a : ℚ) * μ a with hm
  have hvm : v ∈ h.eigenspace (m : ℂ) := heig μ v hv
  set Q : Submodule ℂ V := ⨆ (t : ℚ) (_ : m < t), h.eigenspace (t : ℂ) with hQ
  have hshift : ∀ a b, r a < r b → ∀ t : ℚ, m ≤ t →
      ∀ y ∈ h.eigenspace (t : ℂ), act (Eab b a) y ∈ Q := by
    intro a b hab t ht y hy
    have h1 := eig_shift hL c b a hy
    have h2 : (t : ℂ) + (c b - c a) = ((t + ((r b : ℚ) - (r a : ℚ)) : ℚ) : ℂ) := by simp [hc]
    rw [h2] at h1
    have h3 : (r a : ℚ) < r b := by exact_mod_cast hab
    exact (le_iSup₂_of_le (f := fun (t : ℚ) (_ : m < t) => h.eigenspace (t : ℂ)) _
      (by linarith) le_rfl : _ ≤ Q) h1
  have hlow : ∀ a b, r a < r b → ∀ y ∈ (ℂ ∙ v) ⊔ Q, act (Eab b a) y ∈ Q := by
    intro a b hab
    have : (ℂ ∙ v) ⊔ Q ≤ Q.comap (act (Eab b a)) := by
      refine sup_le ?_ (iSup₂_le fun t ht y hy => hshift a b hab t ht.le y hy)
      rw [Submodule.span_singleton_le_iff_mem]
      exact hshift a b hab m le_rfl v hvm
    exact this
  have hle : sInf F ≤ (ℂ ∙ v) ⊔ Q :=
    sInf_le ⟨Submodule.mem_sup_left (Submodule.mem_span_singleton_self v),
      fun a b _ hab y hy => Submodule.mem_sup_right (hlow a b hab y hy)⟩
  have hQle : ∀ n : ℚ, n ≤ m → Q ≤ ⨆ (j : ℂ) (_ : j ≠ (n : ℂ)), h.eigenspace j := by
    intro n hn
    refine iSup₂_le fun t ht => le_iSup₂_of_le (t : ℂ) ?_ le_rfl
    intro he
    have : t = n := by exact_mod_cast he
    linarith
  have hline : ∀ x ∈ sInf F, x ∈ h.eigenspace (m : ℂ) → ∃ s : ℂ, x = s • v := by
    intro x hx hxm
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hzm : z ∈ h.eigenspace (m : ℂ) := by
      have := Submodule.sub_mem _ hxm (Submodule.smul_mem _ s hvm)
      simpa using this
    have hz0 : z = 0 :=
      Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (m : ℂ)) z hzm
        (hQle m le_rfl hz)
    exact ⟨s, by rw [hz0, add_zero]⟩
  refine ⟨sInf F, hG.1, fun a b hab x hx => ?_, fun U' h1 h2 => sInf_le ⟨h1, h2⟩,
    fun x hx hxμ => hline x hx (heig μ x hxμ), fun ν x hx hx0 hxν => ?_⟩
  · have := sInf_le hG' hx
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at this
    exact this.2 _ (supp_Eab hab)
  · have hxn := heig ν x hxν
    set n : ℚ := ∑ a, (r a : ℚ) * ν a with hn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact Or.inr hlt
    · left
      rw [← heq] at hxn
      obtain ⟨s, hs⟩ := hline x hx hxn
      have hxμ : x ∈ wtSub act μ := hs ▸ Submodule.smul_mem _ s hv
      funext a
      have h1 := mem_wt.1 hxν a
      rw [mem_wt.1 hxμ a] at h1
      have h2 := smul_left_injective ℂ hx0 h1
      exact_mod_cast h2.symm
    · exfalso
      apply hx0
      refine Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (n : ℂ)) x hxn ?_
      refine (sup_le ?_ (hQle n hgt.le) : (ℂ ∙ v) ⊔ Q ≤ _) (hle hx)
      rw [Submodule.span_singleton_le_iff_mem]
      have hne : (m : ℂ) ≠ (n : ℂ) := by exact_mod_cast hgt.ne'
      exact (le_iSup₂_of_le (f := fun (j : ℂ) (_ : j ≠ (n : ℂ)) => h.eigenspace j) (m : ℂ) hne
        le_rfl : _ ≤ _) hvm

end GlobalTheory.ExtremalGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneScalarAvoidingMatrixEigenvalues
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormOneScalar

theorem exists_of_anti {E : Type} [Field E] [CharZero E] (c : E →+* E) (s : E) (hs : s ≠ 0) (hc : c s = -s)
    (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) : ∃ z : E, z * c z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  have hm : ∀ k : ℕ, ((k : E) + 1) - s ≠ 0 := by
    intro k h
    have h1 : s = (k : E) + 1 := by linear_combination -h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  have hp : ∀ k : ℕ, ((k : E) + 1) + s ≠ 0 := by
    intro k h
    have h1 : s = -((k : E) + 1) := by linear_combination h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  let f : ℕ → E := fun k => (((k : E) + 1) + s) / (((k : E) + 1) - s)
  have hf : Function.Injective f := by
    intro a b h
    have h' := (div_eq_div_iff (hm a) (hm b)).1 h
    have : (2 : E) * s * ((a : E) - b) = 0 := by linear_combination -h'
    have h3 : (a : E) - b = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hs)
      · exact h
    exact_mod_cast sub_eq_zero.1 h3
  have hP : γ.charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := γ)
    rw [h] at this
    simp at this
  have hfin : {z : E | γ.charpolyRev.IsRoot z}.Finite := Polynomial.finite_setOfPred_isRoot hP
  obtain ⟨z, ⟨k, rfl⟩, hz⟩ := (Set.infinite_range_of_injective hf).exists_notMem_finite hfin
  refine ⟨f k, ?_, ?_, ?_⟩
  · have h1 := hm k
    have h2 := hp k
    simp only [f, map_div₀, map_add (f := _), map_sub, map_natCast, map_one, hc, sub_neg_eq_add, ← sub_eq_add_neg]
    field_simp
  · intro h
    have h' := (div_eq_one_iff_eq (hm k)).1 h
    apply hs
    have : (2 : E) * s = 0 := by linear_combination h'
    simpa using this
  · intro h
    apply hz
    show Polynomial.eval (f k) γ.charpolyRev = 0
    rw [← h, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij] <;> exact mul_comm _ _

theorem exists_norm_one_det_ne_zero : ∀ (D : D7) (n : ℕ) (γ : Matrix (Fin n) (Fin n) D.host.E),
    ∃ z : D.host.E, z * D.host.conj z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  intro D n γ
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have h1 := D.host.sqrtMinusD_sq
    rw [h] at h1
    have h2 : (D.host.d : D.host.E) = 0 := by linear_combination h1
    exact D.host.hyp.2.1.ne_zero (by exact_mod_cast h2)
  exact exists_of_anti (D.host.conj : D.host.E →+* D.host.E) D.host.sqrtMinusD hs D.host.conj_sqrtMinusD n γ

end GlobalTheory.NormOneScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

theorem exists_periodPair_of_im_ne_zero {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℂ) (a : 𝓞 K) (ha : (σ (a : K)).im ≠ 0) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ a ∈ I, z = σ (a : K) := by
  have hr : Module.finrank ℤ I = 2 :=
    (Ideal.finrank_eq_finrank (RingOfIntegers.basis K) I hI).trans ((RingOfIntegers.rank K).trans hK)
  let b : Module.Basis (Fin 2) ℤ I := Module.finBasisOfFinrankEq ℤ _ hr
  have hs : ∀ x : I, σ ((x : 𝓞 K) : K) =
      b.repr x 0 * σ ((b 0 : 𝓞 K) : K) + b.repr x 1 * σ ((b 1 : 𝓞 K) : K) := by
    intro x
    have := congrArg (fun x : I => σ ((x : 𝓞 K) : K)) (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ ((b 0 : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero]
    have : (b 0 : 𝓞 K) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    exact_mod_cast this
  have h0 : (σ ((b 1 : 𝓞 K) : K) * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im ≠ 0 := by
    intro h0
    have e := hs ⟨a * b 0, I.mul_mem_left a (b 0).2⟩
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e' h0 ha hb0
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨σ ((b 0 : 𝓞 K) : K), σ ((b 1 : 𝓞 K) : K), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 1 : 𝓞 K) : K)).im * e1 - (σ ((b 1 : 𝓞 K) : K)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 0 : 𝓞 K) : K)).re * e2 - (σ ((b 0 : 𝓞 K) : K)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, _, (hs ⟨x, hx⟩).symm⟩

theorem eisG_eq_periodPair_G (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = L.G (2 * k) := by
  have e1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  have e2 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  refine e1.trans (Eq.trans (tsum_congr fun w => ?_) e2.symm)
  by_cases hw : w = 0
  · subst hw
    simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

theorem discr_ne_zero (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) : TaylorLogMetric.discr Λ ≠ 0 := by
  have := g₂_cube_sub_g₃_sq_ne_zero L
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_periodPair_G Λ L h two_ne_zero, eisG_eq_periodPair_G Λ L h three_ne_zero]
  exact this

theorem mem_lamOf_iff (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ z : ℂ) :
    z ∈ lamOf D cc δ ↔ ∃ c ∈ cc, z = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · intro hz
    exact AddSubgroup.subset_closure hz

theorem exists_periodPair_one (D : D7) {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc 1 ↔ z ∈ L.lattice := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  have hK : Module.finrank ℚ D.host.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K hd hb
  let s : D.host.K := ⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hs : s ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa [s] using hb)
  have hint : IsIntegral ℤ s := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hs]
    exact (isIntegral_natCast _).neg
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have him : (σ (((⟨s, hint⟩ : 𝓞 D.host.K) : 𝓞 D.host.K) : D.host.K)).im ≠ 0 := by
    intro h0
    change (σ s).im = 0 at h0
    have e : σ s ^ 2 = -(D.host.d : ℂ) := by rw [← map_pow, hs]; simp
    have e' := congrArg Complex.re e
    simp only [pow_two, Complex.mul_re, h0, Complex.neg_re, Complex.natCast_re] at e'
    have : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    nlinarith [mul_self_nonneg (σ s).re]
  obtain ⟨L, hL⟩ := exists_periodPair_of_im_ne_zero hK σ (⟨s, hint⟩ : 𝓞 D.host.K) him hc
  refine ⟨L, fun z => ?_⟩
  rw [hL, mem_lamOf_iff]
  simp only [one_mul]
  rfl

theorem exists_periodPair_lamOf : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  intro D cc δ h
  obtain ⟨L, hL⟩ := exists_periodPair_one D h.1.1
  have hδ : δ ≠ 0 := by
    rintro rfl
    have e : (0 : ℂ) ^ 12 = TaylorLogMetric.discr (lamOf D cc 1) := h.2
    exact discr_ne_zero _ L hL (by rw [← e]; simp)
  have hind : LinearIndependent ℝ ![δ * L.ω₁, δ * L.ω₂] := by
    have h1 := LinearIndependent.pair_iff.1 L.indep
    rw [LinearIndependent.pair_iff]
    intro x y e
    refine h1 x y (mul_left_cancel₀ hδ ?_)
    simp only [Complex.real_smul] at e ⊢
    linear_combination e
  refine ⟨⟨δ * L.ω₁, δ * L.ω₂, hind⟩, fun z => ?_⟩
  rw [mem_lamOf_iff, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 ((hL _).1 ((mem_lamOf_iff D cc 1 _).2 ⟨c, hc, rfl⟩))
    exact ⟨m, n, by linear_combination δ * e⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨c, hc, e⟩ := (mem_lamOf_iff D cc 1 _).1 ((hL _).2 (PeriodPair.mem_lattice.2 ⟨m, n, rfl⟩))
    exact ⟨c, hc, by linear_combination δ * e⟩

end GlobalTheory.CurveLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockNormExtremalVectorEqBoundedNat
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.ExtremalNorm

theorem weight_colW_apply {r n : ℕ} (mo : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) mo t = ∑ a, mo (a, t) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem fockS_extremal_eq_nat : ∀ (n : ℕ) (lam : DomWeight n) (R : ℕ), (∀ i, lam.natW i ≤ R) → ∃ s : ℕ, 0 < s ∧ s ≤ (n.factorial) ^ (2 * R) * (R.factorial) ^ n ∧ ∀ (K : Type) [Field K] [StarRing K] [CharZero K], fockS (extremal K n lam) (extremal K n lam) = (s : K) := by
  intro n lam R hR
  have hanti := Formalism.L2.DIV.natW_antitone lam
  set f : MvPolynomial (Fin n × Fin n) ℤ := extremal ℤ n lam with hf
  have hmem : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f lam.natW :=
    (Formalism.GradedWeylDivisibility.hwMem ℤ n n le_rfl _ hanti).1
  have hne : f ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℤ n n le_rfl _
  have hl1 : ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs ≤ (n.factorial) ^ R :=
    GlobalTheory.IntMvPolynomialCoeffAbsSum.highestWeightVector_coeff_natAbs_sum_le_factorial_pow n lam.natW R hanti hR
  refine ⟨∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs ^ 2 * mfact mo, ?_, ?_, ?_⟩
  · refine Finset.sum_pos (fun mo hmo => ?_) (support_nonempty.mpr hne)
    have h1 : 0 < (AddMonoidAlgebra.coeff f mo).natAbs := Int.natAbs_pos.mpr (mem_support_iff.mp hmo)
    have h2 : 0 < mfact mo := Finset.prod_pos fun k _ => Nat.factorial_pos _
    positivity
  · calc ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs ^ 2 * mfact mo
        ≤ ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs * (n.factorial ^ R * R.factorial ^ n) := by
          refine Finset.sum_le_sum fun mo hmo => ?_
          have h1 : (AddMonoidAlgebra.coeff f mo).natAbs ≤ n.factorial ^ R :=
            (Finset.single_le_sum (f := fun mo => (AddMonoidAlgebra.coeff f mo).natAbs)
              (fun _ _ => Nat.zero_le _) hmo).trans hl1
          have h2 : mfact mo ≤ R.factorial ^ n := by
            refine GlobalTheory.TestLat.mfact_le_factorial_pow n lam.natW R hR mo fun t => ?_
            rw [← weight_colW_apply, hmem (mem_support_iff.mp hmo)]
          rw [pow_two, mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
      _ ≤ n.factorial ^ R * (n.factorial ^ R * R.factorial ^ n) := by
          rw [← Finset.sum_mul]
          exact Nat.mul_le_mul_right _ hl1
      _ = _ := by rw [two_mul, pow_add, mul_assoc]
  · intro K _ _ _
    have hinj : Function.Injective (Int.castRingHom K) := Int.cast_injective
    rw [← Formalism.L2.DIV.map_extremal (Int.castRingHom K) n lam, ← hf]
    unfold fockS
    rw [support_map_of_injective _ hinj, Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h : (((AddMonoidAlgebra.coeff f m).natAbs ^ 2 : ℕ) : K) = ((AddMonoidAlgebra.coeff f m : ℤ) : K) * ((AddMonoidAlgebra.coeff f m : ℤ) : K) := by
      rw [← Int.cast_natCast, Nat.cast_pow, Int.natAbs_sq, pow_two, Int.cast_mul]
    rw [Nat.cast_mul, h]
    simp only [coeff_map, eq_intCast, star_intCast]

end GlobalTheory.ExtremalNorm
end

