module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_cball_addChar_eq_one (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ s : kˣ, ∀ y ∈ cball s, ψ y = 1 := by
  have hU : ψ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : k) := by
    refine ((Circle.isOpen_centeredArc _).preimage hψ).mem_nhds ?_
    rw [Set.mem_preimage, AddChar.map_zero_eq_one]
    exact ⟨0, by simpa using Real.pi_pos, by simp⟩
  obtain ⟨s, hs⟩ := exists_cball_subset hU
  refine ⟨s, fun y hy => Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  refine hs ?_
  clear * - hy
  induction n with
  | zero => simp [cball]
  | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hy

theorem exists_hasConductor_of_continuous (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    ∃ c : kˣ, HasConductor ψ c := by
  classical
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  obtain ⟨y₀, hy₀⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (by ext y; simp [h y])
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy₀ (AddChar.map_zero_eq_one ψ)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hlt : ∀ y : 𝒪[k], y ∈ 𝓂[k] ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hϖ1 : valuation k (ϖ : k) < 1 := (hlt ϖ).mp hϖ.not_isUnit
  have hex : ∃ n : ℕ, ∀ y, valuation k y ≤ valuation k (y₀ * (ϖ : k) ^ n) → ψ y = 1 := by
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ1
      (Units.mk0 (valuation k (y₀⁻¹ * s)) (by simp [hy0]))
    refine ⟨n, fun y hy => hs y (show valuation k y ≤ valuation k (s : k) from hy.trans ?_)⟩
    rw [Units.val_mk0, map_mul, map_inv₀, lt_inv_mul_iff₀ (by simp [zero_lt_iff, hy0])] at hn
    rw [map_mul, map_pow]
    exact hn.le
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    exact hy₀ (hspec y₀ (by simp))
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin := Nat.find_min hex (m := m) (by omega)
  rw [hm] at hspec
  refine ⟨Units.mk0 (y₀ * (ϖ : k) ^ (m + 1)) (mul_ne_zero hy0 (pow_ne_zero _ h0)), fun x => ⟨fun h => ?_,
    fun h y hy => hspec y (hy.trans h)⟩⟩
  by_contra hx
  rw [Units.val_mk0, not_le] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hxp : 0 < valuation k x := by simp [zero_lt_iff, hx0]
  have hxi : valuation k (x⁻¹ * (y₀ * (ϖ : k) ^ (m + 1))) < 1 := by
    rw [map_mul, map_inv₀, inv_mul_lt_iff₀ hxp, mul_one]
    exact hx
  have h2 : valuation k (x⁻¹ * (y₀ * (ϖ : k) ^ (m + 1))) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl
      ⟨_, (Valuation.mem_integer_iff _ _).mpr hxi.le⟩).mpr ((hlt _).mpr hxi)
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ hxp, pow_succ, ← mul_assoc, map_mul,
    mul_le_mul_iff_left₀ (by simp [zero_lt_iff, h0])] at h2
  exact hmin fun y hy => h y (hy.trans h2)

theorem conductor_exists :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [MeasurableSpace k] [BorelSpace k],
      (∀ ψ : AddChar k Circle, Continuous ψ → ψ ≠ 1 → ∃ c : kˣ, HasConductor ψ c) ∧
      (∃ ψ : AddChar k Circle, Continuous ψ ∧ ψ ≠ 1 ∧ HasConductor ψ 1) ∧
      ∃ ν : Measure k, IsUnitVol ν := by
  intro k _ _ _ _ _ _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := exists_hasConductor_one k
  exact ⟨exists_hasConductor_of_continuous, ⟨ψ, hψ.continuous, hψ.ne_one, hψ⟩, exists_isUnitVol k⟩

end GlobalTheory.SplitWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCo
section
open MvPolynomial

namespace GlobalTheory.SubstCoeff

variable {σ : Type}

theorem continuous_coeff_mul {Y : Type} [TopologicalSpace Y] (F G : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (F y) m) (hG : ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (G y) m) (m : σ →₀ ℕ) :
    Continuous fun y => AddMonoidAlgebra.coeff (F y * G y) m := by
  classical
  simp only [coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hF _).mul (hG _)

theorem continuous_coeff_pow {Y : Type} [TopologicalSpace Y] (F : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (F y) m) (e : ℕ) (m : σ →₀ ℕ) :
    Continuous fun y => AddMonoidAlgebra.coeff (F y ^ e) m := by
  induction e generalizing m with
  | zero =>
    classical
    simp only [pow_zero, coeff_one]
    exact continuous_const
  | succ e ih =>
    simp only [pow_succ]
    exact continuous_coeff_mul _ _ ih hF m

theorem continuous_coeff_prod {Y κ : Type} [TopologicalSpace Y] (s : Finset κ) (f : κ → Y → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (f q y) m) (m : σ →₀ ℕ) :
    Continuous fun y => AddMonoidAlgebra.coeff (∏ q ∈ s, f q y) m := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    exact continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact continuous_coeff_mul _ _ (hf a (Finset.mem_insert_self a s))
      (fun m' => ih (fun q hq => hf q (Finset.mem_insert_of_mem hq)) m') m

theorem isAlgebraic_sum {κ : Type} (s : Finset κ) (f : κ → ℂ) (hf : ∀ q ∈ s, IsAlgebraic ℚ (f q)) :
    IsAlgebraic ℚ (∑ q ∈ s, f q) :=
  Finset.sum_induction f (IsAlgebraic ℚ) (fun _ _ ha hb => ha.add hb) isAlgebraic_zero hf

theorem isAlgebraic_coeff_mul (P Q : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff P m)) (hQ : ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff Q m)) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (P * Q) m) := by
  classical
  rw [coeff_mul]
  exact isAlgebraic_sum _ _ fun x _ => (hP _).mul (hQ _)

theorem isAlgebraic_coeff_one (m : σ →₀ ℕ) : IsAlgebraic ℚ (AddMonoidAlgebra.coeff (1 : MvPolynomial σ ℂ) m) := by
  classical
  rw [coeff_one]
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

theorem isAlgebraic_coeff_pow (P : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff P m)) (e : ℕ) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (P ^ e) m) := by
  induction e generalizing m with
  | zero => simpa only [pow_zero] using isAlgebraic_coeff_one m
  | succ e ih =>
    rw [pow_succ]
    exact isAlgebraic_coeff_mul _ _ ih hP m

theorem isAlgebraic_coeff_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff (f q) m)) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (∏ q ∈ s, f q) m) :=
  Finset.prod_induction f (fun P => ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff P m))
    (fun _ _ ha hb => isAlgebraic_coeff_mul _ _ ha hb) isAlgebraic_coeff_one hf m

variable {ι : Type} {N n : ℕ}

theorem substF_monomial_one (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF h g (monomial k 1) = ∏ q ∈ k.support, (GlobalTheory.CompactHowe.substF h g (X q)) ^ k q := by
  rw [monomial_eq, map_mul, C_1, map_one, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow]

theorem continuous_coeff_substF_X (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    Continuous fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) =>
      AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (X q)) m := by
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  refine Continuous.mul (Continuous.mul ?_ ?_) continuous_const
  · exact ((continuous_apply q.1).comp continuous_fst).matrix_elem a q.2.1
  · exact ((continuous_apply q.1).comp continuous_snd).matrix_elem b q.2.2

theorem isAlgebraic_coeff_substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hh : ∀ i a b, IsAlgebraic ℚ (h i a b)) (hg : ∀ i a b, IsAlgebraic ℚ (g i a b))
    (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (X q)) m) := by
  classical
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine isAlgebraic_sum _ _ fun a _ => isAlgebraic_sum _ _ fun b _ => ?_
  refine ((hh _ _ _).mul (hg _ _ _)).mul ?_
  rw [coeff_X']
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

theorem coeff_substF_monomial_continuous_algebraic :
    ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1)) k') ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k') := by
  intro ι N n k k'
  refine ⟨?_, fun h g hh hg => ?_⟩
  · simp only [substF_monomial_one]
    exact continuous_coeff_prod _ _ (fun q _ m => continuous_coeff_pow _ (continuous_coeff_substF_X q) _ m) k'
  · rw [substF_monomial_one]
    exact isAlgebraic_coeff_prod _ _
      (fun q _ m => isAlgebraic_coeff_pow _ (isAlgebraic_coeff_substF_X h g hh hg q) _ m) k'

end GlobalTheory.SubstCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMultilinearMapExtHilbertBasis
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem continuousMultilinearMap_ext_hilbertBasis (ι : Type) [Fintype ι] [DecidableEq ι]
    (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F)
    (h : ∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) : f = g := by
  have key : ∀ s : Finset ι, ∀ y : ∀ i, Hs i,
      (∀ i, i ∉ s → y i ∈ Set.range (e i)) → f y = g y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy
      choose j hj using fun i => hy i (by simp)
      have hy' : y = fun i => e i (j i) := funext fun i => (hj i).symm
      rw [hy']
      exact h j
    | insert a s ha ih =>
      intro y hy
      let L : Hs a →L[ℂ] F := (f - g).toContinuousLinearMap y a
      have hL : Set.EqOn (L : Hs a → F) (0 : Hs a →L[ℂ] F) (Set.range (e a)) := by
        intro z hz
        simp only [L, ContinuousMultilinearMap.toContinuousLinearMap_apply,
          ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_eq_zero]
        apply ih
        intro i hi
        by_cases hia : i = a
        · subst hia
          simpa using hz
        · rw [Function.update_of_ne hia]
          exact hy i (by simp [hia, hi])
      have hdense : Dense (Submodule.span ℂ (Set.range (e a)) : Set (Hs a)) := by
        exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (e a).dense_span
      have hL0 : L = 0 := ContinuousLinearMap.ext_on hdense hL
      have hya := congrArg (fun M : Hs a →L[ℂ] F => M (y a)) hL0
      simp only [L, ContinuousMultilinearMap.toContinuousLinearMap_apply,
        ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_eq_zero,
        Function.update_eq_self] at hya
      exact hya
  ext y
  exact key Finset.univ y (by simp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagPartMulDiagPart
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.BlockLevi

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagPart (f : ι → ℕ) (A : Matrix ι ι k) : Matrix ι ι k :=
  Matrix.of fun r s => if f r = f s then A r s else 0

theorem mul_diagPart_apply (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) {r s : ι} (h : f s ≤ f r) :
    (A * diagPart f B) r s = (A * B) r s := by
  simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with ht
  · rfl
  · rcases lt_or_gt_of_ne ht with h1 | h1
    · rw [hA (lt_of_lt_of_le h1 h)]; simp
    · rw [hB h1]

theorem diagPart_mul_diagPart (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) (hAB : A * B = 1) :
    diagPart f A * diagPart f B = 1 := by
  ext r s
  by_cases h : f r = f s
  · rw [← hAB, ← mul_diagPart_apply f hA hB h.ge]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_pos (h.trans ht.symm)]
    · simp [ht]
  · have hrs : r ≠ s := fun e => h (e ▸ rfl)
    rw [Matrix.one_apply_ne hrs]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_neg (fun e => h (e.trans ht))]; simp
    · simp [ht]

theorem blockTriangular_inv (f : ι → ℕ) (b : GL ι k) (hb : b.val.BlockTriangular f) :
    (b⁻¹).val.BlockTriangular f := by
  letI : Invertible b.val := b.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem exists_unip_mul_levi : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (b : GL (n ⊕ Fin c) k), b.val.BlockTriangular (lev p) → ∃ u ∈ N k n c p, ∃ m : GL (n ⊕ Fin c) k, (∀ r s, lev p r ≠ lev p s → m.val r s = 0) ∧ (∀ r s, lev p r = lev p s → m.val r s = b.val r s) ∧ b = u * m := by
  intro k _ n _ _ c p b hb
  have hi := blockTriangular_inv (lev p) b hb
  let m : GL (n ⊕ Fin c) k := ⟨diagPart (lev p) b.val, diagPart (lev p) (b⁻¹).val,
    diagPart_mul_diagPart _ hb hi b.mul_inv, diagPart_mul_diagPart _ hi hb b.inv_mul⟩
  refine ⟨b * m⁻¹, Subgroup.subset_closure ?_, m, ?_, ?_, by simp⟩
  · intro r s h
    have : (b * m⁻¹).val = b.val * diagPart (lev p) (b⁻¹).val := rfl
    rw [this, mul_diagPart_apply _ hb hi h, b.mul_inv]
  · intro r s h
    simp [m, diagPart, h]
  · intro r s h
    simp [m, diagPart, h]

end GlobalTheory.RootEx.BlockLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.SplitWeil

section
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem om_smul_add (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ) :
    om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ := by
  funext x
  simp only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem eventually_comp_sideMul_eq {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x, Φ (sideMul gh.1 gh.2 x) = Φ x := by
  have hc : Continuous fun q : (GL a k × GL b k) × Matrix b a k => sideMul q.1.1 q.1.2 q.2 := by
    show Continuous fun q : (GL a k × GL b k) × Matrix b a k =>
      (q.1.2⁻¹ : GL b k).val * q.2 * q.1.1.val
    exact ((Units.continuous_coe_inv.comp (continuous_snd.comp continuous_fst)).matrix_mul
      continuous_snd).matrix_mul (Units.continuous_val.comp (continuous_fst.comp continuous_fst))
  have h1 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x ∈ tsupport Φ, Φ (sideMul gh.1 gh.2 x) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (GL a k × GL b k) × Matrix b a k =>
        (Φ (sideMul q.1.1 q.1.2 q.2), Φ q.2) :=
      (hΦ.1.comp_continuous hc).prodMk (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, x)] with q hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
    congr 1
    show ((1 : GL b k)⁻¹ : GL b k).val * x * (1 : GL a k).val = x
    simp
  have h2 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1,
      ∀ x ∈ tsupport Φ, Φ (sideMul gh⁻¹.1 gh⁻¹.2 x) = Φ x := by
    have ht : Filter.Tendsto (fun gh : GL a k × GL b k => gh⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := GL a k × GL b k)).tendsto 1
    exact ht.eventually h1
  filter_upwards [h1, h2] with gh hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : sideMul gh.1 gh.2 x ∈ tsupport Φ
  · rw [← hs' _ hx']
    congr 1
    have := (sideMul gh.1 gh.2).left_inv x
    refine Eq.trans ?_ this
    show (gh.2⁻¹⁻¹ : GL b k).val * sideMul gh.1 gh.2 x * (gh.1⁻¹ : GL a k).val = _
    rw [inv_inv]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem isOpen_valuation_eq_one : IsOpen {x : kˣ | valuation k (x : k) = 1} := by
  have : {x : kˣ | valuation k (x : k) = 1} =
      (fun x : kˣ => (x : k)) ⁻¹' (𝒪[k] : Set k) ∩ (fun x : kˣ => ((x⁻¹ : kˣ) : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
      Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_le_one₀ (by simp [zero_lt_iff])]
    exact le_antisymm_iff
  rw [this]
  exact ((isOpen_int k).preimage Units.continuous_val).inter
    ((isOpen_int k).preimage Units.continuous_coe_inv)

theorem eventually_det_trivial (n : Type*) [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsOpen (μ.ker : Set kˣ)) :
    ∀ᶠ g : GL n k in 𝓝 1, μ (Matrix.GeneralLinearGroup.det g) = 1 ∧
      nabs k (Matrix.GeneralLinearGroup.det g) = 1 := by
  have hU := (hμ.inter isOpen_valuation_eq_one).preimage
    (Matrix.GeneralLinearGroup.continuous_det (n := n) (R := k))
  filter_upwards [hU.mem_nhds (x := 1) (by simp)] with g hg
  exact ⟨hg.1, nabs_eq_one_of_valuation_eq_one hg.2⟩

theorem isOpen_stabilizer_om {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ)) {Φ : Matrix b a k → ℂ}
    (hΦ : Φ ∈ SB (Matrix b a k)) : IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} := by
  let S : Subgroup (GL a k × GL b k) :=
    { carrier := {gh | om μ gh.1 gh.2 Φ = Φ}
      one_mem' := om_one μ Φ
      mul_mem' := fun {x y} hx hy => by
        show om μ (x.1 * y.1) (x.2 * y.2) Φ = Φ
        rw [om_mul, hy, hx]
      inv_mem' := fun {x} hx => by
        show om μ x.1⁻¹ x.2⁻¹ Φ = Φ
        conv_lhs => rw [← hx]
        rw [← om_mul, inv_mul_cancel, inv_mul_cancel, om_one] }
  refine S.isOpen_of_mem_nhds (g := 1) ?_
  have h1 := (continuous_fst.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial a hμ)
  have h2 := (continuous_snd.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial b hμ)
  filter_upwards [h1, h2, eventually_comp_sideMul_eq hΦ] with gh hg hh hs
  show om μ gh.1 gh.2 Φ = Φ
  funext x
  have := hs x
  simp only [om, hg.1, hg.2, hh.1, hh.2, Real.one_rpow, inv_one, Units.val_one, Complex.ofReal_one,
    one_mul]
  exact this

end

theorem om_isSmoothRepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∀ Φ : Matrix b a k → ℂ, om μ 1 1 Φ = Φ) ∧ (∀ (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ), om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ)) ∧ (∀ (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ), om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ) ∧ (∀ (g : GL a k) (h : GL b k), ∀ Φ ∈ SB (Matrix b a k), om μ g h Φ ∈ SB (Matrix b a k)) ∧ ∀ Φ ∈ SB (Matrix b a k), IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} :=
  fun _ _ _ _ _ _ _ _ _ _ _ μ hμ =>
    ⟨om_one μ, om_mul μ, om_smul_add μ, fun g h _ hΦ => om_mem_SB μ g h hΦ,
      fun _ hΦ => isOpen_stabilizer_om hμ hΦ⟩

end GlobalTheory.SplitWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetGeneratingOperatorStableBoundedStatement
section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_generating_operator_stable_bounded : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  first | exact @GlobalTheory.StabGen.exists_finset_generating | exact GlobalTheory.StabGen.exists_finset_generating | (intros; apply GlobalTheory.StabGen.exists_finset_generating <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaximalOperatorStableOfFinsetGeneratingStatement
section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V)) (R : Submodule ℂ V)
    (F : Finset V),
    (∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ GlobalTheory.TensHead.Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, GlobalTheory.TensHead.Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  first | exact @GlobalTheory.TensHead.exists_maximal_stab_of_finset | exact GlobalTheory.TensHead.exists_maximal_stab_of_finset | (intros; apply GlobalTheory.TensHead.exists_maximal_stab_of_finset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapConjNormalizingLatticeEqSelfStatement
section
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) := by
  first | exact @GlobalTheory.UnfoldNormal.map_conj_eq_self | exact GlobalTheory.UnfoldNormal.map_conj_eq_self | (intros; apply GlobalTheory.UnfoldNormal.map_conj_eq_self <;> assumption)
end

