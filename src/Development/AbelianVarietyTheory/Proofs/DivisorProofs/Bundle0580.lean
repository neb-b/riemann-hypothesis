module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualBasisCoordMemMaximalIdealOfForallApply
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dualBasis_coord_mem_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M)) (l : Module.Dual O M), (∀ w, l w ∈ IsLocalRing.maximalIdeal O) → ∀ j, lb.repr l j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ M _ _ _ _ k lb l hl j
  haveI : Module.Free O M := Module.free_of_flat_of_isLocalRing
  let ε := Module.Free.chooseBasis O M
  have hsum : l = ∑ i, l (ε i) • ε.dualBasis i := by
    refine ε.ext fun a => ?_
    simp [Module.Basis.dualBasis_apply_self, Finset.sum_apply, LinearMap.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hl _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEqSmulOfForallDvd
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_eq_smul_of_forall_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) →
      ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  intro O M _ _ _ a ha l hl
  have cancel : ∀ x y : O, a * x = a * y → x = y := by
    intro x y hxy
    have := ha (x - y) (by rw [mul_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  let c : M → O := fun w => Classical.choose (hl w)
  have hc : ∀ w, l w = a * c w := fun w => Classical.choose_spec (hl w)
  refine ⟨{ toFun := c, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply cancel
    rw [mul_add, ← hc, ← hc, ← hc, map_add (f := _)]
  · intro r x
    apply cancel
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hc, map_smul, hc, smul_eq_mul]
    ring
  · ext w
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    exact hc w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualIsConnOfIsEtPDivGroup
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem PDivGroup.dual_isConn_of_isEt (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) : G.IsEt → G.dual.IsConn := by
  intro hG n χ hχ
  have : IsReduced (G.A n) := hG n
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p

  have roots : ∀ r : ℕ, ∀ a : G.A n, ∃ b : G.A n, a = b ^ p ^ r := by
    intro r
    induction r with
    | zero => exact fun a => ⟨a, by simp⟩
    | succ r ih =>
      intro a
      obtain ⟨c, rfl⟩ := ih a
      obtain ⟨b, rfl⟩ := _root_.GlobalTheory.exists_pow_char_eq_of_isReduced_finite p k (G.A n) c
      exact ⟨b, by rw [← pow_mul, pow_succ, mul_comm]⟩

  have h1 : χ 1 = 0 := by
    have hc := (RingHom.mem_ker).1 hχ
    exact hc
  refine ⟨p ^ n, ?_⟩
  apply CartierDual.ext_apply
  intro a
  obtain ⟨b, rfl⟩ := roots n a
  rw [_root_.GlobalTheory.PDivGroup.convPow_primePow_apply_pow p k hp G n n χ b, PDivGroup.mulBy_pow_self, Algebra.algebraMap_eq_smul_one,
    map_smul, h1, smul_zero, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualQuotientFormEqEval
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_quotient_form_eq_eval :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
      [Module.Projective O M] (I : Ideal O) (u : Module.Dual O M →ₗ[O] O ⧸ I),
      ∃ b : M, ∀ φ, u φ = Ideal.Quotient.mk I (φ b) := by
  intro O M _ _ _ _ _ I u
  obtain ⟨v, hv⟩ := Module.projective_lifting_property (Submodule.mkQ I) u
    (Submodule.mkQ_surjective I)
  refine ⟨(Module.evalEquiv O M).symm v, fun φ => ?_⟩
  have h1 : φ ((Module.evalEquiv O M).symm v) = v φ := by
    have := congrArg (fun w : Module.Dual O (Module.Dual O M) => w φ)
      ((Module.evalEquiv O M).apply_symm_apply v)
    simpa using this
  rw [h1, ← hv]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylHighestWeightRestrictionBlockDiagonal
section
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

theorem resT_lpMinor_le (p q s : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hs : s ≤ p) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
  have key : lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ s hs hs) := rfl
  rw [key, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  have hi : (Fin.castLE h1 i : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs i) := Fin.ext rfl
  have hj : (Fin.castLE h2 j : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs j) := Fin.ext rfl
  rw [hi, hj, resT, aeval_X]
  simp [resVarT]

theorem resT_lpMinor_ge (p q u : ℕ) (h1 : p + u ≤ p + q) (h2 : p + u ≤ p + q) (hu : u ≤ q) :
    resT ℚ p q (lpMinor ℚ (p + u) h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  have key : lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ p le_rfl le_rfl) *
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := MvPolynomial (Fin p × Fin p) ℚ))
        (lpMinor ℚ u hu hu) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [key, lpMinor, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₂₁ (B := 0)]
  congr 1
  ext (a | a) (b | b)
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q a := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q b := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]

theorem nuNext_natAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (j : Fin q) :
    nuNext ν (Fin.natAdd p j) = nuNext (fun j => ν (Fin.natAdd p j)) j := by
  unfold nuNext
  simp only [Fin.val_natAdd]
  split_ifs with h h' h'
  · congr 1
  · omega
  · omega
  · rfl

theorem nuNext_castAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (i : Fin p) (hi : (i : ℕ) + 1 < p) :
    nuNext ν (Fin.castAdd q i) = nuNext (fun i => ν (Fin.castAdd q i)) i := by
  unfold nuNext
  simp only [Fin.val_castAdd]
  rw [dite_eq_left (by omega), dite_eq_left hi]
  rfl

theorem sum_sub_nuNext (q : ℕ) (μ : Fin (q + 1) → ℕ) (hμ : Antitone μ) :
    ∑ j, (μ j - nuNext μ j) = μ 0 := by
  induction q with
  | zero => simp [nuNext]
  | succ q ih =>
    rw [Fin.sum_univ_succ]
    have h1 : ∀ j : Fin (q + 1), nuNext μ j.succ = nuNext (fun j => μ j.succ) j := by
      intro j
      unfold nuNext
      simp only [Fin.val_succ]
      split_ifs with h h' h' <;> first | omega | rfl
    simp_rw [h1]
    rw [ih (fun j => μ j.succ) (fun a b hab => hμ (Fin.succ_le_succ_iff.mpr hab))]
    have h0 : nuNext μ 0 = μ (Fin.succ 0) := by
      unfold nuNext; rw [dite_eq_left (by simp)]; rfl
    rw [h0]
    have := hμ (Fin.zero_le (Fin.succ 0 : Fin (q + 2)))
    omega

theorem resT_lpMinor_ge' (p q s u : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hu : u ≤ q) (hs : s = p + u) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  subst hs
  exact resT_lpMinor_ge p q u h1 h2 hu

theorem prod_tmul_prod {ι A B : Type} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (s : Finset ι) (a : ι → A) (b : ι → B) :
    ∏ i ∈ s, (a i ⊗ₜ[ℚ] b i) = (∏ i ∈ s, a i) ⊗ₜ[ℚ] (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.TensorProduct.one_def]
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

theorem hw_first (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) :
    (∏ i : Fin p, lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^
        (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) *
      lpMinor ℚ p le_rfl le_rfl ^ (∑ j : Fin q, (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) := by
  rcases p with _ | p
  · simp [hw, lpMinor, Matrix.det_isEmpty]
  · rw [hw, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
    simp only [Fin.val_last]
    rw [← pow_add]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      rw [nuNext_castAdd (p + 1) q ν k.castSucc (by simp)]
    · have hl : nuNext (fun i => ν (Fin.castAdd q i)) (Fin.last p) = 0 := by
        unfold nuNext; rw [dite_eq_right (by simp)]
      rw [hl, Nat.sub_zero]
      congr 1
      simp_rw [nuNext_natAdd]
      rcases q with _ | q
      · simp [nuNext]
      · rw [sum_sub_nuNext q (fun j => ν (Fin.natAdd (p + 1) j))
          (fun a b hab => hν (by rw [Fin.le_def] at hab ⊢; simp only [Fin.val_natAdd]; omega))]
        have h0 : nuNext ν (Fin.castAdd (q + 1) (Fin.last p)) = ν (Fin.natAdd (p + 1) 0) := by
          unfold nuNext; rw [dite_eq_left (by simp <;> omega)]; congr 1
        have := hν (show Fin.castAdd (q + 1) (Fin.last p) ≤ Fin.natAdd (p + 1) 0 by
          simp [Fin.le_def])
        rw [h0]
        omega

theorem resHw_holds : ResHw := by
  intro p q ν hν
  rw [hw, map_prod, Fin.prod_univ_add]
  have e1 : ∀ i : Fin p, resT ℚ p q (lpMinor ℚ ((Fin.castAdd q i : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) =
      (lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^ (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) ⊗ₜ[ℚ]
        (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
    intro i
    rw [map_pow, resT_lpMinor_le p q _ _ _ (by simp <;> omega), Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  have e2 : ∀ j : Fin q, resT ℚ p q (lpMinor ℚ ((Fin.natAdd p j : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      (lpMinor ℚ p le_rfl le_rfl ^ (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) ⊗ₜ[ℚ]
        (lpMinor ℚ ((j : ℕ) + 1) (by omega) (by omega) ^
          ((fun j => ν (Fin.natAdd p j)) j - nuNext (fun j => ν (Fin.natAdd p j)) j)) := by
    intro j
    rw [map_pow, resT_lpMinor_ge' p q _ ((j : ℕ) + 1) _ _ (by omega) (by simp <;> omega),
      Algebra.TensorProduct.tmul_pow, nuNext_natAdd]
  rw [Finset.prod_congr rfl fun i _ => e1 i, Finset.prod_congr rfl fun j _ => e2 j, prod_tmul_prod,
    prod_tmul_prod, Algebra.TensorProduct.tmul_mul_tmul, Finset.prod_const_one, one_mul,
    Finset.prod_pow_eq_pow_sum, hw_first p q ν hν]
  rfl

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStable
section
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

def colPull {k N : ℕ} (τ : Fin k → Fin N) : (Fin N → ℕ) →+ (Fin k → ℕ) where
  toFun g := g ∘ τ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colPull_single_mem {k N : ℕ} {τ : Fin k → Fin N} (hτ : Function.Injective τ) (s : Fin k) :
    colPull τ (Pi.single (τ s) 1) = Pi.single s 1 := by
  funext t
  change (Pi.single (τ s) 1 : Fin N → ℕ) (τ t) = _
  by_cases h : t = s
  · subst h; simp
  · rw [Pi.single_eq_of_ne (fun h' => h (hτ h')), Pi.single_eq_of_ne h]

theorem colPull_single_not {k N : ℕ} {τ : Fin k → Fin N} {y : Fin N} (hy : y ∉ Set.range τ) :
    colPull τ (Pi.single y 1) = 0 := by
  funext t
  change (Pi.single y 1 : Fin N → ℕ) (τ t) = 0
  exact Pi.single_eq_of_ne (fun h => hy ⟨t, h⟩) _

theorem mem_dualWeyl_iff' {R : Type} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, mem_weightedHomogeneousSubmodule,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]

theorem aeval_isWeightedHomogeneous {R σ ι Mo : Type} [CommRing R] [AddCommMonoid Mo] (w : ι → Mo)
    (φ : σ → MvPolynomial ι R) (ω : σ → Mo) (hφ : ∀ v, IsWeightedHomogeneous w (φ v) (ω v))
    (x : MvPolynomial σ R) (κ : Mo) (hx : IsWeightedHomogeneous ω x κ) :
    IsWeightedHomogeneous w (aeval φ x) κ := by
  conv => enter [2, 2]; rw [x.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial, ← hx (mem_support_iff.mp hd), Finsupp.weight_apply, MvPolynomial.algebraMap_eq]
  refine IsWeightedHomogeneous.C_mul ?_ _
  unfold Finsupp.prod Finsupp.sum
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _

theorem isWeightedHomogeneous_map_weight {R σ M M' : Type} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']
    (π : M →+ M') (w : σ → M) (x : MvPolynomial σ R) (κ : M) (hx : IsWeightedHomogeneous w x κ) :
    IsWeightedHomogeneous (fun v => π (w v)) x (π κ) := by
  intro d hd
  rw [← hx hd, Finsupp.weight_apply, Finsupp.weight_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [map_nsmul]

theorem substMem : SubstMem := by
  intro R _ k N τ hτ ψ h1 h2 h3 ν f hf
  rw [mem_dualWeyl_iff'] at hf ⊢
  have hinj := hτ.injective
  refine ⟨?_, fun l j hlj => ?_⟩
  · have hvar : ∀ v : Fin N × Fin N,
        IsWeightedHomogeneous (colW k k) (ψ v) (colPull τ (colW N N v)) := by
      rintro ⟨x, y⟩
      change IsWeightedHomogeneous _ _ (colPull τ (Pi.single y 1))
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        rw [colPull_single_mem hinj]
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1]
          exact isWeightedHomogeneous_X _ _ _
        · rw [h2 x s hx]
          exact isWeightedHomogeneous_zero _ _ _
      · rw [colPull_single_not hy]
        obtain ⟨c, hc⟩ := h3 x y hy
        rw [hc]
        exact isWeightedHomogeneous_C _ _
    exact aeval_isWeightedHomogeneous (colW k k) ψ _ hvar f _
      (isWeightedHomogeneous_map_weight (colPull τ) _ f ν hf.1)
  · let ψO : Option (Fin N × Fin N) → MvPolynomial (Option (Fin k × Fin k)) R :=
      fun o => o.elim (X none) fun v => rename some (ψ v)
    have hA : (aeval ψO).comp (rename some) = (rename some).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      simp [ψO]
    have hB : (aeval ψO).comp (colAddGen R (r := N) (τ l) (τ j)) = (colAddGen R l j).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      obtain ⟨x, y⟩ := v
      simp only [AlgHom.comp_apply, aeval_X]
      rw [colAddGen, aeval_X]
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1, colAddGen, aeval_X]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h1]
          · simp [ψO, h1]
        · rw [h2 x s hx, map_zero]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h2 x _ hx]
          · simp [ψO, h2 x _ hx]
      · obtain ⟨c, hc⟩ := h3 x y hy
        have hyj : y ≠ τ j := fun h => hy ⟨j, h.symm⟩
        rw [if_neg hyj, hc]
        simp [ψO, hc]
    have e1 := congrArg (fun φ => φ f) hA
    have e2 := congrArg (fun φ => φ f) hB
    simp only [AlgHom.comp_apply] at e1 e2
    rw [← e2, hf.2 (τ l) (τ j) (hτ hlj), e1]

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdSubOfDUnitEq
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CotDualLin

theorem dvd_counit (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Module.Finite O A]
    [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A)
    (h : Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t) :
    q ∣ Coalgebra.counit (R := O) a := by
  have h1 := CartierDual.mul_apply (R := O) (C := A) 1 1 a
  rw [one_mul, h] at h1
  simp only [map_add (f := _), map_smul, CartierDual.pair_tmul_tmul, CartierDual.one_apply, Bialgebra.counit_one] at h1
  exact ⟨-(CartierDual.pair O A A (1 ⊗ₜ 1) t), by rw [smul_eq_mul] at h1; linear_combination -h1⟩

theorem dvd_of_mem_sq (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A] [Module.Finite O A]
    [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A)
    (h : Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t)
    (χ : CartierDual O A) (hχ : χ ∈ RingHom.ker (Bialgebra.counitAlgHom O (CartierDual O A)) ^ 2) :
    q ∣ χ a := by
  rw [pow_two] at hχ
  refine Submodule.mul_induction_on hχ (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have hx1 : x 1 = 0 := hx
    have hy1 : y 1 = 0 := hy
    rw [CartierDual.mul_apply, h]
    simp only [map_add (f := _), map_smul, CartierDual.pair_tmul_tmul, hx1, hy1, mul_zero, zero_mul, zero_add, smul_eq_mul]
    exact dvd_mul_right _ _
  · have e : (x + y) a = x a + y a := rfl
    rw [e]; exact dvd_add hx hy

theorem dvd_sub_of_dUnit_eq : ∀ (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A),
    Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t →
    ∀ φ ψ : CartierDual O A, PDiv.dUnit (R := O) φ = PDiv.dUnit (R := O) ψ → q ∣ φ a - ψ a := by
  intro O A _ _ _ _ _ _ a q t h φ ψ hd
  have h0 : PDiv.dUnit (R := O) (φ - ψ) = 0 := by rw [PDiv.dUnit, map_sub]; exact sub_eq_zero.2 hd
  rw [PDiv.dUnit, AugCot.d_eq_zero_iff] at h0
  have h2 := dvd_of_mem_sq O A a q t h _ h0
  set c := Bialgebra.counitAlgHom O (CartierDual O A) (φ - ψ)
  have h3 : (algebraMap O (CartierDual O A) c) a = c * Coalgebra.counit (R := O) a := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  have e : (φ - ψ - algebraMap O (CartierDual O A) c) a = φ a - ψ a - (algebraMap O (CartierDual O A) c) a := rfl
  rw [e, h3] at h2
  have h4 := dvd_mul_of_dvd_right (dvd_counit O A a q t h) c
  have := dvd_add h2 h4
  rwa [sub_add_cancel] at this

end GlobalTheory.CotDualLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfLocalEqPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ZM.IsGaloisCover

theorem eq_of_local_eq_pullback : ∀ (X Y S Z : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (g : S ⟶ Y) (h₁ h₂ : S ⟶ Z), GlobalTheory.ZM.IsGaloisCover Ga ρ π → (∀ q : ↥(pullback g π), ∃ V : (pullback g π).Opens, q ∈ V ∧ V.ι ≫ pullback.fst g π ≫ h₁ = V.ι ≫ pullback.fst g π ≫ h₂) → h₁ = h₂ := by
  intro X Y S Z π Ga _ ρ g h₁ h₂ h hloc
  have hp : IsPullback (pullback.snd g π) (pullback.fst g π) π g := (IsPullback.of_hasPullback g π).flip
  have : Etale (pullback.fst g π) := MorphismProperty.of_isPullback (P := @Etale) hp h.etale
  have : IsFinite (pullback.fst g π) := MorphismProperty.of_isPullback (P := @IsFinite) hp h.fin
  have : Surjective (pullback.fst g π) := MorphismProperty.of_isPullback (P := @Surjective) hp h.onto
  have e : pullback.fst g π ≫ h₁ = pullback.fst g π ≫ h₂ :=
    Scheme.hom_ext_of_forall _ _ fun q ↦ hloc q
  exact (cancel_epi (pullback.fst g π)).1 e

end GlobalTheory.ZM.IsGaloisCover
end

