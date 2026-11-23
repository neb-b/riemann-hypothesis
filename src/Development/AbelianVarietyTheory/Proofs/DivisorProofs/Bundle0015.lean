module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
section
namespace GlobalTheory.Div.BlockChangeDet

open Matrix

theorem det_blockDiagonal'_eq_prod {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical
  set f := Fintype.equivFin ι
  let b : (Σ c, κ c) → Fin (Fintype.card ι) := fun p => f p.1
  have hb : (Matrix.blockDiagonal' M).BlockTriangular b := by
    rintro ⟨c, i⟩ ⟨c', j⟩ h
    exact Matrix.blockDiagonal'_apply_ne M i j (fun hc => by subst hc; exact lt_irrefl _ h)
  rw [hb.det_fintype]
  symm
  refine Fintype.prod_equiv f _ _ (fun c => ?_)
  let e : κ c ≃ {p : (Σ c, κ c) // b p = f c} :=
    { toFun := fun i => ⟨⟨c, i⟩, rfl⟩
      invFun := fun p => cast (congrArg κ (f.injective p.2)) p.1.2
      left_inv := fun i => rfl
      right_inv := by
        rintro ⟨⟨c', i⟩, h⟩
        have hc : c' = c := f.injective h
        subst hc
        rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i j
  exact (Matrix.blockDiagonal'_apply_eq M c i j).symm

theorem det_block_change (F : Type) [Field F] {N : Type} [AddCommGroup N] [Module F N]
    {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N)
    (hℓ : ∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F)
    (hU : ∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) (hA : ∀ k, mu k = ∑ l, A k l • nu l)
    (hg : ∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) :
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  classical

  have hli : LinearIndependent F ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 : (0 : N) = ∑ k, (0 : (Σ b, Fin (m b)) → F) k • ℓ k := by simp
    have := (hℓ 0).unique ha.symm h0
    intro i
    exact congrFun this i
  have hsp : ⊤ ≤ Submodule.span F (Set.range ℓ) := by
    intro x _
    obtain ⟨a, ha, -⟩ := hℓ x
    rw [ha]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hfr : Module.finrank F N = n := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_congr e, Fintype.card_fin]
  have hspnu : ⊤ ≤ Submodule.span F (Set.range nu) := by
    refine le_trans hsp (Submodule.span_le.mpr ?_)
    rintro _ ⟨σ, rfl⟩
    rw [hU σ]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hlinu : LinearIndependent F nu :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspnu (by simp [hfr])
  have uniq : ∀ a c : Fin n → F, ∑ k, a k • nu k = ∑ k, c k • nu k → a = c := by
    intro a c h
    have := Fintype.linearIndependent_iff.mp hlinu (a - c)
      (by simp [sub_smul, Finset.sum_sub_distrib, h])
    funext k
    exact sub_eq_zero.mp (this k)

  have hdet : U.det ≠ 0 := by
    have hrows : LinearIndependent F (fun i => U i) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hli' : LinearIndependent F (ℓ ∘ e.symm) := hli.comp e.symm e.symm.injective
      refine Fintype.linearIndependent_iff.mp hli' a ?_
      have hcol : ∀ k, ∑ i, a i * U i k = 0 := by
        intro k
        have := congrFun ha k
        simpa [Finset.sum_apply] using this
      calc ∑ i, a i • (ℓ ∘ e.symm) i
          = ∑ i, a i • ∑ k, U i k • nu k := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp [Function.comp, hU]
        _ = ∑ k, (∑ i, a i * U i k) • nu k := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            exact Finset.sum_comm
        _ = 0 := by simp [hcol]
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact (Matrix.isUnit_iff_isUnit_det U |>.mp hu).ne_zero
  refine ⟨hdet, ?_⟩

  have hent : ∀ σ k, ∑ τ, blockDiagonal' g σ τ * U (e τ) k = ∑ l, C σ l * A l k := by
    rintro ⟨b, i⟩
    have h1 : ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ = ∑ j, g b i j • ℓ ⟨b, j⟩ := by
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single b]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [blockDiagonal'_apply_eq]
      · intro b' _ hb'
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [blockDiagonal'_apply_ne g i j (Ne.symm hb'), zero_smul]
      · intro h; exact absurd (Finset.mem_univ b) h
    have h2 : ∑ k, (∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k) • nu k
        = ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ := by
      simp only [hU, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h3 : ∑ k, (∑ l, C ⟨b, i⟩ l * A l k) • nu k = ∑ l, C ⟨b, i⟩ l • mu l := by
      simp only [hA, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have := uniq (fun k => ∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k)
      (fun k => ∑ l, C ⟨b, i⟩ l * A l k) (by rw [h2, h1, hg b i, ← h3])
    intro k
    exact congrFun this k
  have key : Matrix.reindex e e (blockDiagonal' g) * U
      = (Matrix.of fun i k => C (e.symm i) k) * A := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
    rw [← hent (e.symm i) k]
    exact Fintype.sum_equiv e.symm _ _ (fun x => by simp)
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, det_blockDiagonal'_eq_prod] at this
  exact this

theorem det_block_change' : ∀ {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N),
    (∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) → ∀ (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F),
    (∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) → (∀ k, mu k = ∑ l, A k l • nu l) →
    (∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) →
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  intro F _ N _ _ κ _ m n e ℓ hℓ nu mu U A C g hU hA hg
  exact det_block_change F m e ℓ hℓ nu mu U A C g hU hA hg

end GlobalTheory.Div.BlockChangeDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNearOneMatrixNormBounds
section
open Matrix Polynomial

namespace GlobalTheory

theorem norm_multiset_prod_near_one (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ Multiset.card s ≤ ‖s.prod‖ ∧ ‖s.prod‖ ≤ (3 / 2 : ℝ) ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    obtain ⟨h1, h2⟩ := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
    have hlo : (1 / 2 : ℝ) ≤ ‖a‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - a)
      rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
      linarith
    have hhi : ‖a‖ ≤ 3 / 2 := by
      have := norm_add_le (a - 1) 1
      rw [sub_add_cancel, norm_one] at this
      linarith
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, pow_succ]
    constructor
    · rw [mul_comm ((1 / 2 : ℝ) ^ _)]
      exact mul_le_mul hlo h1 (by positivity) (norm_nonneg _)
    · rw [mul_comm ((3 / 2 : ℝ) ^ _)]
      exact mul_le_mul hhi h2 (norm_nonneg _) (by norm_num)

theorem det_near_one_bounds (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) (hn : (n : ℝ) * ε ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ - 1‖ ≤ 1 / 2 := by
    intro μ hμ
    have hr : A.charpoly.IsRoot μ := isRoot_of_mem_roots hμ
    have hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']; exact hr
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    have hdiag : ‖A k k - 1‖ ≤ ε := by simpa using hA k k
    have h1n : 1 ≤ n := Fin.pos k
    have hoff : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ((n : ℝ) - 1) * ε := by
      have hle : ∀ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ε := by
        intro j hj
        have hjk : k ≠ j := (Finset.ne_of_mem_erase hj).symm
        simpa [Matrix.one_apply_ne hjk] using hA k j
      calc _ ≤ ∑ _j ∈ Finset.univ.erase k, ε := Finset.sum_le_sum hle
        _ = ((n : ℝ) - 1) * ε := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub h1n, Nat.cast_one]
    calc ‖μ - 1‖ = ‖(μ - A k k) + (A k k - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖μ - A k k‖ + ‖A k k - 1‖ := norm_add_le _ _
      _ ≤ ((n : ℝ) - 1) * ε + ε := add_le_add (hk.trans hoff) hdiag
      _ = n * ε := by ring
      _ ≤ 1 / 2 := hn
  have hcard : Multiset.card A.charpoly.roots = n := by
    rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  obtain ⟨h1, h2⟩ := norm_multiset_prod_near_one _ hroot
  rw [hcard, ← Matrix.det_eq_prod_roots_charpoly] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEntryOfSemilinearModSubspace
section
open PowerSeries

namespace GlobalTheory

theorem diagonal_entry_of_semilinear_mod_subspace : ∀ (F : Type) [Field F] (n : ℕ) (θ : PowerSeries F →+* PowerSeries F) (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (W' W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (f' e' f e : Fin n → PowerSeries F) (w' w : (PowerSeries F)ˣ) (k' k m : ℤ) (d : PowerSeries F) (α : LaurentSeries F), ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 → (∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((A.mulVec (fun c => θ (y c)) a : PowerSeries F) : LaurentSeries F)) ∈ W) → (fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((f a : PowerSeries F) : LaurentSeries F)) - (((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k) • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∉ W → (fun a => ((A.mulVec (fun c => θ (f' c)) a : PowerSeries F) : LaurentSeries F)) - ((d : PowerSeries F) : LaurentSeries F) • (fun a => ((f a : PowerSeries F) : LaurentSeries F)) ∈ W → (((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m) • (fun a => ((A.mulVec (fun c => θ (e' c)) a : PowerSeries F) : LaurentSeries F)) - α • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k' * α = ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m := by
  intro F _ n θ A W' W f' e' f e w' w k' k m d α hξ hT hf' hf he hTf hTe
  have hx : ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 := by
    intro h
    apply PowerSeries.X_ne_zero (R := F)
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using h
  set x : LaurentSeries F := ((PowerSeries.X : PowerSeries F) : LaurentSeries F) with hxdef
  set ξ : LaurentSeries F := ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) with hξdef
  obtain ⟨N, j, hj⟩ : ∃ N j : ℕ, (j : ℤ) = (N : ℤ) + k' := ⟨k'.natAbs, (k'.natAbs + k').toNat, by omega⟩
  set a : PowerSeries F := (w' : PowerSeries F) * PowerSeries.X ^ j with hadef
  have ha : ((a : PowerSeries F) : LaurentSeries F) = (w' : LaurentSeries F) * x ^ N * x ^ k' := by
    rw [hadef, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hx, zpow_natCast, mul_assoc]
  have hθa : ((θ a : PowerSeries F) : LaurentSeries F) = ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ξ ^ N * ξ ^ k' := by
    rw [hadef, map_mul, map_pow, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hξ, zpow_natCast, mul_assoc]
  let y : Fin n → PowerSeries F := fun c => PowerSeries.X ^ N * f' c - a * e' c
  have hy : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) ∈ W' := by
    have : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) = (x ^ N) • ((fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * x ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F))) := by
      funext c
      simp only [y, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, ha, ← hxdef]
      ring
    rw [this]; exact W'.smul_mem _ hf'
  have hvec : A.mulVec (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • A.mulVec (fun c => θ (f' c)) - θ a • A.mulVec (fun c => θ (e' c)) := by
    have : (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • (fun c => θ (f' c)) - θ a • (fun c => θ (e' c)) := by
      ext c; simp [y]
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hTy := hT y hy
  set P : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (f' c)) i : PowerSeries F) : LaurentSeries F) with hP
  set Q : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (e' c)) i : PowerSeries F) : LaurentSeries F) with hQ
  set E : Fin n → LaurentSeries F := fun i => ((e i : PowerSeries F) : LaurentSeries F) with hE
  set Fv : Fin n → LaurentSeries F := fun i => ((f i : PowerSeries F) : LaurentSeries F) with hFv
  have h4 : ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q ∈ W := by
    have : (fun i => ((A.mulVec (fun c => θ (y c)) i : PowerSeries F) : LaurentSeries F)) = ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q := by
      funext i
      simp only [hvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, hP, hQ, hξdef]
    rw [← this]; exact hTy
  set c : LaurentSeries F := ((θ a : PowerSeries F) : LaurentSeries F) * α - x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * x ^ k with hc
  have hcE : c • E ∈ W := by
    have h := W.sub_mem (W.sub_mem (W.add_mem (W.smul_mem (x ^ m * ξ ^ N) hTf) (W.smul_mem (x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F)) hf)) (W.smul_mem (((θ a : PowerSeries F) : LaurentSeries F)) hTe)) (W.smul_mem (x ^ m) h4)
    convert h using 1
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, hc]
    ring
  have hc0 : c = 0 := by
    by_contra hne
    apply he
    have := W.smul_mem c⁻¹ hcE
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hξN : ξ ^ N ≠ 0 := pow_ne_zero _ hξ
  rw [hc, hθa, sub_eq_zero] at hc0
  apply mul_right_cancel₀ hξN
  linear_combination hc0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealSmulMemSpanRational
section
open NumberField

namespace GlobalTheory

theorem exists_trace_dual_system (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    ∃ (m : ℕ) (ω : Fin m → 𝓞 L) (η : Fin m → L),
      (∀ i, η i ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ t : L, t = ∑ i, algebraMap K L (Algebra.trace K L (η i * t)) * (ω i : L) := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, F, G, -, -, hFG⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 L)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) L :=
    IsIntegralClosure.isLocalization (𝓞 K) K L (𝓞 L)
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K _
  let f : Fin m → Module.Dual K L := fun i =>
    hbc.lift ((Algebra.linearMap (𝓞 K) K) ∘ₗ (LinearMap.proj i) ∘ₗ G)
  have hf : ∀ i (a : 𝓞 L), f i (a : L) = algebraMap (𝓞 K) K (G a i) := fun i a =>
    hbc.lift_eq _ a
  let η : Fin m → L := fun i =>
    ((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)).symm (f i)
  have hη : ∀ i t, Algebra.trace K L (η i * t) = f i t := fun i t =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate K L) (f i) t
  refine ⟨m, fun i => F (Pi.single i 1), η, fun i => ?_, fun t => ?_⟩
  · rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨G b i, ?_⟩
    rw [Algebra.traceForm_apply, hη]
    exact (hf i b).symm
  · simp_rw [hη]
    have h := hbc.algHom_ext (LinearMap.id : L →ₗ[K] L)
      (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (fun a => by
        have ha : a = ∑ i, G a i • F (Pi.single i 1) := by
          have h1 : a = F (G a) := (LinearMap.congr_fun hFG a).symm
          conv_lhs => rw [h1, LinearMap.pi_apply_eq_sum_univ]
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 2
          ext j
          simp [Pi.single_apply, eq_comm]
        change (a : L) = (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (a : L)
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, hf, algebraMap_smul]
        conv_lhs => rw [ha]
        change algebraMap (𝓞 L) L _ = _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap.map_smul _ _)
    have h2 := LinearMap.congr_fun h t
    simpa [LinearMap.sum_apply, Algebra.smul_def] using h2

open NumberField in
private theorem exists_integral_traceDual_expansion (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    ∃ (N : ℕ) (e : Fin N → 𝓞 L) (c : Fin N → L),
      (∀ k, c k ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ y : L, y = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) • c k := by
  classical
  obtain ⟨N, F, hF⟩ := Module.Finite.exists_fin' (𝓞 K) (𝓞 L)
  have : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  have hP : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨h, hh⟩ := Module.projective_lifting_property F LinearMap.id hF
  obtain ⟨e, hdec⟩ : ∃ e : Fin N → 𝓞 L, ∀ b : 𝓞 L, b = ∑ k, h b k • e k := by
    refine ⟨fun k => F (Pi.single k 1), fun b => ?_⟩
    have hb := LinearMap.congr_fun hh b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hb
    conv_lhs => rw [← hb, ← Finset.univ_sum_single (h b)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Pi.single k (h b k) : Fin N → 𝓞 K) = h b k • Pi.single k 1 by
      rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul]
  let φ : Fin N → (𝓞 L →ₗ[𝓞 K] 𝓞 K) := fun k => LinearMap.proj k ∘ₗ h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin N → Module.Dual K L,
      ∀ k (b : 𝓞 L), ψ k (algebraMap (𝓞 L) L b) = algebraMap (𝓞 K) K (h b k) :=
    ⟨fun k => IsLocalizedModule.mapExtendScalars (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K) K
      (φ k), fun k b => IsLocalizedModule.map_apply (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K)
      (φ k) b⟩
  have hB := traceForm_nondegenerate K L
  obtain ⟨c, hc⟩ : ∃ c : Fin N → L, ∀ k y, Algebra.trace K L (c k * y) = ψ k y :=
    ⟨fun k => ((Algebra.traceForm K L).toDual hB).symm (ψ k), fun k y => by
      rw [← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_toDual_symm_apply _ _⟩
  clear hh hF F this hP
  have hexpO : ∀ b : 𝓞 L,
      algebraMap (𝓞 L) L b = ∑ k, ψ k (algebraMap (𝓞 L) L b) • algebraMap (𝓞 L) L (e k) := by
    intro b
    conv_lhs => rw [hdec b]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L, Algebra.smul_def]
  have hexp : ∀ y : L, y = ∑ k, ψ k y • algebraMap (𝓞 L) L (e k) := by
    intro y
    obtain ⟨⟨b, s⟩, hbs⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) y
    obtain ⟨a, ha, has⟩ := s.2
    have ha0 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    have hy : y = (algebraMap (𝓞 K) K a)⁻¹ • algebraMap (𝓞 L) L b := by
      rw [← hbs, ← has, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L, mul_comm, ← Algebra.smul_def, smul_smul,
        inv_mul_cancel₀ ha0, one_smul]
    clear hbs has
    rw [hy]
    conv_lhs => rw [hexpO b]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_assoc]
  refine ⟨N, e, c, fun k => ?_, fun y => ?_⟩
  · rw [Submodule.mem_traceDual]
    rintro _ ⟨b, rfl⟩
    rw [Algebra.traceForm_apply]
    exact ⟨h b k, by simpa [hψ, Algebra.smul_def, mul_comm] using (hc k (algebraMap (𝓞 L) L b)).symm⟩
  · rw [← sub_eq_zero]
    refine hB.1 _ fun u => ?_
    have h1 : Algebra.trace K L (y * u) = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) *
        Algebra.trace K L (c k * u) := by
      conv_lhs => rw [hexp u]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hc]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm y]; ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, Algebra.traceForm_apply, smul_eq_mul, h1]
    rw [sub_eq_zero]


open NumberField in
theorem _root_.GlobalTheory.differentIdeal_smul_mem_span_rational :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (n : ℕ) (M : Submodule (𝓞 L) (Fin n → L)), (∀ (σ : L ≃ₐ[K] L), ∀ x ∈ M, (fun i => σ (x i)) ∈ M) → ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∀ x ∈ M, d • x ∈ Submodule.span (𝓞 L) {y : Fin n → L | y ∈ M ∧ ∃ y0 : Fin n → K, y = fun i => algebraMap K L (y0 i)} := by
  intro K L _ _ _ _ _ _ n M hM d hd x hx
  classical
  obtain ⟨N, e, c, hcD, hswap⟩ := exists_integral_traceDual_expansion K L
  have hdL : algebraMap (𝓞 L) L d ∈ (1 : Submodule (𝓞 L) L) / Submodule.traceDual (𝓞 K) K 1 := by
    rw [← coeSubmodule_differentIdeal (𝓞 K) K (𝓞 L)]
    exact (IsLocalization.mem_coeSubmodule _ _).mpr ⟨d, hd, rfl⟩
  have hdc : ∀ k, ∃ r : 𝓞 L, algebraMap (𝓞 L) L r = algebraMap (𝓞 L) L d * c k := fun k =>
    Submodule.mem_one.mp (Submodule.mem_div_iff_forall_mul_mem.mp hdL _ (hcD k))
  choose r hr using hdc
  set t : Fin N → Fin n → L :=
    fun k i => algebraMap K L (Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i)) with ht
  have htM : ∀ k, t k ∈ M := by
    intro k
    have : t k = ∑ σ : L ≃ₐ[K] L, fun i => σ ((e k • x) i) := by
      funext i
      simp only [ht, Finset.sum_apply, Pi.smul_apply, trace_eq_sum_automorphisms, Algebra.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun σ _ => hM σ _ (M.smul_mem _ hx)
  have hdx : d • x = ∑ k, r k • t k := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, ht, Algebra.smul_def, hr]
    conv_lhs => rw [hswap (x i)]
    simp only [Finset.mul_sum, Algebra.smul_def]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdx]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨htM k, fun i => Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i), rfl⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivMemOfMulPowDivMemOfRegularPair
section
namespace GlobalTheory

theorem div_mem_of_mul_pow_div_mem_of_regularPair (K : Type) [Field K] (O : Subring K) (s t : K)
    (ht : t ∈ O) (h : ∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) (N : ℕ) :
    ∀ g ∈ O, g * t ^ N / s ∈ O → g / s ∈ O := by
  induction N with
  | zero => intro g _ hg; simpa using hg
  | succ N ih =>
    intro g hg hgN
    apply ih g hg
    apply h _ (O.mul_mem hg (O.pow_mem ht N))
    rwa [mul_assoc, ← pow_succ]

theorem regularPair_pow : ∀ (K : Type) [Field K] (O : Subring K) (s t : K), s ∈ O → t ∈ O → s ≠ 0 → (∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) → ∀ (m N : ℕ), ∀ g ∈ O, g * t ^ N / s ^ m ∈ O → g / s ^ m ∈ O := by
  intro K _ O s t hs ht hs0 h m N
  induction m with
  | zero => intro g hg _; simpa using hg
  | succ m ih =>
    intro g hg hgN
    have h1 : g * t ^ N / s ∈ O := by
      have h2 := O.mul_mem hgN (O.pow_mem hs m)
      have e : g * t ^ N / s ^ (m + 1) * s ^ m = g * t ^ N / s := by
        field_simp
        ring
      rwa [e] at h2
    have h3 := div_mem_of_mul_pow_div_mem_of_regularPair K O s t ht h N g hg h1
    have e1 : g / s * t ^ N / s ^ m = g * t ^ N / s ^ (m + 1) := by
      field_simp
      ring
    have e2 : g / s / s ^ m = g / s ^ (m + 1) := by
      field_simp
      ring
    rw [← e2]
    exact ih _ h3 (by rwa [e1])

end GlobalTheory
end

