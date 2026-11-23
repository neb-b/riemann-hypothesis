module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerBlockLastEqOne
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem blkW_det_eq_one (r p0 : ℕ) (w : Low r → ℂ) : (blkW p0 w).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [blkW, lowMat]
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    simp only [blkW, lowMat]
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals first
      | rfl
      | (exfalso; simp only [Fin.lt_def, Fin.ext_iff] at *; omega)

theorem colGram_blkW_last (r p0 : ℕ) (w : Low r → ℂ) :
    colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  unfold colGram lminor
  have : (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r - 1)).isLt) : Fin (r - 1) → Fin (r - 1)) = id := by
    funext i; ext; simp
  rw [this, Matrix.submatrix_id_id, Matrix.det_mul, Matrix.det_conjTranspose, blkW_det_eq_one]
  simp

theorem colGramLast : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 :=
  colGram_blkW_last

end GlobalTheory.IntBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerThree
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem colGram_three_unitLower : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) →
    (∀ i j : Fin 3, i < j → M i j = 0) →
    colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧
      colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  intro M hd hu
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h01 : M 0 1 = 0 := hu 0 1 (by decide)
  have h02 : M 0 2 = 0 := hu 0 2 (by decide)
  have h12 : M 1 2 = 0 := hu 1 2 (by decide)
  have e1 : lminor (Mᴴ * M) 1 = (Mᴴ * M) 0 0 := by
    unfold lminor
    exact Matrix.det_fin_one _
  have e2 : lminor (Mᴴ * M) 2 =
      (Mᴴ * M) 0 0 * (Mᴴ * M) 1 1 - (Mᴴ * M) 0 1 * (Mᴴ * M) 1 0 := by
    unfold lminor
    exact Matrix.det_fin_two _
  have g1 : lminor (Mᴴ * M) 1 = ((1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have g2 : lminor (Mᴴ * M) 2 =
      ((1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e2]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
      <;> ring
  have pos : ∀ x : ℝ, 0 ≤ x → ‖((1 + x : ℝ) : ℂ)‖ = 1 + x := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine ⟨?_, ?_⟩
  · unfold colGram
    rw [g1, add_assoc, pos _ (by positivity), ← add_assoc]
  · unfold colGram
    rw [g2, add_assoc, pos _ (by positivity), ← add_assoc]

end GlobalTheory.IntBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonResolutionPotentialComparison
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem torusPair_pow_eq_one_iff {F : Type} [Field F] [Finite F] (n : ℕ) (α : AlgebraicClosure F) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ n - 1) = 1 ↔ (minpoly F α).natDegree ∣ n := by
  have hi : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  rw [(minpoly.irreducible hi).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  have hq : 0 < Nat.card F ^ n := pow_pos Nat.card_pos _
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F ^ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  constructor
  · intro h; rw [h, one_mul]
  · intro h; exact mul_right_cancel₀ h0 (h.trans (one_mul α).symm)

theorem torusPair_finite_monic {F : Type} [Field F] [Finite F] (n : ℕ) :
    {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}.Finite := by
  have : Finite (Polynomial.degreeLT F (n + 1)) := Finite.of_equiv _ (degreeLTEquiv F (n + 1)).symm.toEquiv
  have h : (Polynomial.degreeLT F (n + 1) : Set F[X]).Finite := Set.toFinite _
  refine h.subset fun P hP => ?_
  simp only [SetLike.mem_coe, mem_degreeLT]
  exact (degree_le_of_natDegree_le hP.2.1.le).trans_lt (by exact_mod_cast Nat.lt_succ_self n)

theorem torusPair_finite_torus {F : Type} [Field F] [Finite F] (n : ℕ) (hn : 0 < n) :
    {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}.Finite := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  refine (Polynomial.nthRootsFinset (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset
    fun α hα => ?_
  exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset (by omega) _).2 hα)

theorem torusPair_mangoldt_pow {F : Type} [Field F] (s : F[X] → ℂ) (f : F[X]) (hf : f.Monic)
    (hirr : Irreducible f) (r : ℕ) (hr : 0 < r) : mangoldt s (f ^ r) = s f := by
  have hset : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ r' : ℕ, 0 < r' ∧ f ^ r = g ^ r'} = {f} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hg, hgi, r', hr', he⟩
      have h1 : g ∣ f ^ r := he ▸ dvd_pow_self g hr'.ne'
      have h2 : g ∣ f := hgi.prime.dvd_of_dvd_pow h1
      exact eq_of_monic_of_associated hg hf (hgi.associated_of_dvd hirr h2)
    · rintro rfl
      exact ⟨hf, hirr, r, hr, rfl⟩
  rw [mangoldt, hset, finsum_mem_singleton]

theorem torusPair_mangoldt_sum (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n k : ℕ)
    (S : F[X] → ℂ) (hn : 0 < n) :
    ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}, mangoldt (rootSum θ k) P * star (S P) =
      ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
        θ α ^ k * star (S (minpoly F α ^ (n / (minpoly F α).natDegree))) := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have hi : ∀ α : AlgebraicClosure F, IsIntegral F α := fun α => Algebra.IsIntegral.isIntegral α
  have hne : ∀ α : AlgebraicClosure F, α ^ (Nat.card F ^ n - 1) = 1 → α ≠ 0 := by
    rintro α h rfl
    rw [zero_pow (by omega)] at h
    exact zero_ne_one h
  rw [finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic n),
    finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_torus n hn),
    ← Finset.sum_fiberwise_of_maps_to (s := (torusPair_finite_torus (F := F) n hn).toFinset)
      (t := (torusPair_finite_monic (F := F) n).toFinset)
      (g := fun α => minpoly F α ^ (n / (minpoly F α).natDegree))]
  swap
  · intro α hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα ⊢
    have hm := minpoly.monic (hi α)
    refine ⟨hm.pow _, ?_, ?_⟩
    · rw [hm.natDegree_pow, Nat.div_mul_cancel ((torusPair_pow_eq_one_iff n α (hne α hα)).1 hα)]
    · rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
      exact pow_ne_zero _ (minpoly.coeff_zero_ne_zero (hi α) (hne α hα))
  refine Finset.sum_congr rfl fun P hP => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hP, hd, h0⟩ := hP
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
  swap
  · have hempty : {f : F[X] | f.Monic ∧ Irreducible f ∧ ∃ m : ℕ, 0 < m ∧ P = f ^ m} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hf, hirr, m, hm, rfl⟩
      exact hex ⟨f, m, hf, hirr, hm, rfl⟩
    rw [mangoldt, hempty, finsum_mem_empty, zero_mul]
    refine (Finset.sum_eq_zero fun α hα => ?_).symm
    exfalso
    obtain ⟨hα1, hα2⟩ := Finset.mem_filter.1 hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα1
    have hdv := (torusPair_pow_eq_one_iff n α (hne α hα1)).1 hα1
    exact hex ⟨minpoly F α, n / (minpoly F α).natDegree, minpoly.monic (hi α), minpoly.irreducible (hi α),
      Nat.div_pos (Nat.le_of_dvd hn hdv) (minpoly.natDegree_pos (hi α)), hα2.symm⟩
  obtain ⟨f, m, hf, hirr, hm, rfl⟩ := hex
  rw [hf.natDegree_pow] at hd
  have hdiv : n / f.natDegree = m := by
    rw [← hd, Nat.mul_div_cancel _ hirr.natDegree_pos]
  have hmp : ∀ α : AlgebraicClosure F, aeval α f = 0 → minpoly F α = f := fun α h =>
    (minpoly.eq_of_irreducible_of_monic hirr h hf).symm
  have hfib : Finset.filter (fun α : AlgebraicClosure F => minpoly F α ^ (n / (minpoly F α).natDegree) = f ^ m)
      (torusPair_finite_torus (F := F) n hn).toFinset = (f.map (algebraMap F (AlgebraicClosure F))).roots.toFinset := by
    ext α
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset]
    rw [mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : n / (minpoly F α).natDegree ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hn ((torusPair_pow_eq_one_iff n α (hne α h1)).1 h1))
          (minpoly.natDegree_pos (hi α))).ne'
      have h4 := congrArg (aeval α) h2
      rw [map_pow, map_pow, minpoly.aeval, zero_pow h3] at h4
      exact pow_eq_zero_iff hm.ne' |>.1 h4.symm
    · intro h
      have hα : α ≠ 0 := by
        rintro rfl
        apply h0
        rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
        rw [aeval_def, eval₂_at_zero, map_eq_zero] at h
        rw [h, zero_pow hm.ne']
      rw [torusPair_pow_eq_one_iff n α hα, hmp α h, hdiv]
      exact ⟨Dvd.intro_left _ hd, rfl⟩
  have hsep : f.Separable := PerfectField.separable_of_irreducible hirr
  have hnd : (f.map (algebraMap F (AlgebraicClosure F))).roots.Nodup := nodup_roots hsep.map
  rw [hfib, torusPair_mangoldt_pow _ f hf hirr m hm, rootSum,
    ← Multiset.dedup_eq_self.2 hnd, ← Multiset.toFinset_val, ← Finset.sum_eq_multiset_sum,
    Finset.val_toFinset, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap] at hα
  rw [hmp α hα, hdiv]

theorem torusPair_finsum_GL_eq_ipGL (F : Type) [Field F] [Finite F] (m : ℕ) (s S : F[X] → ℂ) :
    ∑ᶠ x : GL (Fin m) F, psiG s m x * star (chG S m x) =
      ipGL (psi s (Fin m → F)) (fun g => S (LinearMap.charpoly g)) := by
  have h : ∀ x : GL (Fin m) F, psiG s m x * star (chG S m x) =
      (fun g => psi s (Fin m → F) g * star (S (LinearMap.charpoly g)))
        (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) := by
    intro x; simp [psiG, chG, Matrix.charpoly_toLin']
  rw [finsum_congr h, ipGL, ← finsum_mem_univ]
  apply finsum_mem_eq_of_bijOn (fun x : GL (Fin m) F => Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))
  · refine ⟨fun x _ => ?_, fun x _ y _ hxy => ?_, fun g hg => ?_⟩
    · have := x.isUnit.map (Matrix.toLinAlgEquiv' (R := F) (n := Fin m))
      simpa using this
    · exact Units.ext (Matrix.toLin'.injective hxy)
    · have hu : IsUnit (LinearMap.toMatrix' g) := by
        have := (show IsUnit g from hg).map (LinearMap.toMatrixAlgEquiv' (R := F) (n := Fin m))
        simpa using this
      exact ⟨hu.unit, Set.mem_univ _, by simp⟩
  · intro x _; rfl

theorem psiG_rootSum_pair_chG_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (m k : ℕ) (S : F[X] → ℂ), 0 < m → ((Nat.card F : ℂ) ^ m - 1) * ∑ᶠ x, psiG (rootSum θ k) m x * star (chG S m x) =
      (Nat.card (GL (Fin m) F) : ℂ) * ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ m - 1) = 1},
        θ α ^ k * star (S (minpoly F α ^ (m / (minpoly F α).natDegree))) := by
  intro F _ _ θ m k S hm
  have hadd := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  have hq1 : 1 < Nat.card F ^ m := Nat.one_lt_pow hm.ne' Finite.one_lt_card
  have hq : (Nat.card F : ℂ) ^ m - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hq1.ne'
  rw [torusPair_finsum_GL_eq_ipGL, ipGL_charpoly_eq_finsum_mass, Module.finrank_fin_fun,
    ← torusPair_mangoldt_sum F θ m k S hm]
  have hterm : ∀ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = m ∧ P.coeff 0 ≠ 0},
      mass (psi (rootSum θ k) (Fin m → F)) P * star (S P) =
        (Nat.card (GL (Fin m) F) : ℂ) * (mangoldt (rootSum θ k) P * star (S P)) / ((Nat.card F : ℂ) ^ m - 1) := by
    intro P hP
    obtain ⟨hPm, hPd, -⟩ := hP
    rw [mass_psi_eq_glCard_mul_mangoldt_div F (Fin m → F) (rootSum θ k) hadd P hPm (by simpa using hPd), hPd,
      glCard]
    ring
  rw [finsum_mem_congr rfl hterm, finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic m),
    finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic m), ← Finset.sum_div, ← Finset.mul_sum,
    mul_div_cancel₀ _ hq]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory

open scoped Pointwise

theorem compact_finite_leftCoset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  intro G _ _ _ K hK C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun g : G => g • (K : Set G)) (fun g => hK.smul g)
    (fun x _ => Set.mem_iUnion.2 ⟨x, Set.mem_smul_set.2 ⟨1, K.one_mem, by simp⟩⟩)
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ K))).image Quotient.out, ?_, ?_⟩
  · intro r hr r' hr' hrr'
    simp only [Finset.mem_image] at hr hr'
    obtain ⟨a, -, rfl⟩ := hr
    obtain ⟨b, -, rfl⟩ := hr'
    have h : (QuotientGroup.mk (Quotient.out a) : G ⧸ K) = QuotientGroup.mk (Quotient.out b) :=
      QuotientGroup.eq.2 hrr'
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    rw [h]
  · intro g hg
    have hm := ht hg
    simp only [Set.mem_iUnion] at hm
    obtain ⟨gi, hgi, hmem⟩ := hm
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hmem
    refine ⟨Quotient.out (QuotientGroup.mk gi : G ⧸ K),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hgi), ?_⟩
    have h1 : (Quotient.out (QuotientGroup.mk gi : G ⧸ K))⁻¹ * gi ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa [smul_eq_mul, mul_assoc] using K.mul_mem h1 hk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimits
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContFin

theorem term_preserves (N : CommRingCat.{0} ⥤ AbCx) (hN : PreservesFilteredColimitsOfSize.{0, 0} N) (n : ℤ) :
    PreservesFilteredColimitsOfSize.{0, 0} (term N n) := by
  constructor
  intro J _ _
  unfold term
  have : PreservesColimitsOfShape J N := hN.preserves_filtered_colimits J
  infer_instance

theorem cohomology_filteredColimit : ∀ (N : CommRingCat.{0} ⥤ AbCx), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ n, PreservesFilteredColimitsOfSize.{0, 0} (term N n)) ∧ (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) := by
  intro N hN
  refine ⟨term_preserves N hN, ?_⟩
  intro J _ _ D c hc n
  have E : ∀ m : ℤ, (∀ x : ((N).obj c.pt).X m, ∃ j y, ((N).map (c.ι.app j)).f m y = x) ∧
      ∀ j (y : ((N).obj (D.obj j)).X m), ((N).map (c.ι.app j)).f m y = 0 → ∃ (k : J) (f : j ⟶ k), ((N).map (D.map f)).f m y = 0 :=
    fun m => ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N m)).mp (term_preserves N hN m)) J D c hc

  have nat : ∀ {a b : CommRingCat.{0}} (g : a ⟶ b) (p q : ℤ) (x : ((N).obj a).X p),
      ((N).map g).f q (((N).obj a).d p q x) = ((N).obj b).d p q (((N).map g).f p x) := by
    intro a b g p q x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ((N).map g).comm]
  have mapf : ∀ {j k : J} (f : j ⟶ k) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (c.ι.app k)).f m (((N).map (D.map f)).f m x) = ((N).map (c.ι.app j)).f m x := by
    intro j k f m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, c.w f]
  have mapcomp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (D.map (f ≫ g))).f m x = ((N).map (D.map g)).f m (((N).map (D.map f)).f m x) := by
    intro j k l f g m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, ← D.map_comp]
  constructor
  · intro z hz
    obtain ⟨j, w, hw⟩ := (E n).1 z
    have h1 : ((N).map (c.ι.app j)).f (n + 1) (((N).obj (D.obj j)).d n (n + 1) w) = 0 := by
      rw [nat, hw]
      exact hz
    obtain ⟨k, f, hf⟩ := (E (n + 1)).2 j _ h1
    refine ⟨k, ((N).map (D.map f)).f n w, 0, ?_, ?_⟩
    · rw [← nat, hf]
    · rw [mapf, hw, map_zero, add_zero]
  · intro j w _ ⟨y, hy⟩
    obtain ⟨j', y', rfl⟩ := (E (n - 1)).1 y
    let k := IsFiltered.max j j'
    let fa : j ⟶ k := IsFiltered.leftToMax j j'
    let fb : j' ⟶ k := IsFiltered.rightToMax j j'
    set u := ((N).map (D.map fa)).f n w - ((N).obj (D.obj k)).d (n - 1) n (((N).map (D.map fb)).f (n - 1) y') with hu
    have h0 : ((N).map (c.ι.app k)).f n u = 0 := by
      rw [hu, map_sub, mapf, ← nat, mapf, hy, nat]
      exact sub_self _
    obtain ⟨l, g, hg⟩ := (E n).2 k u h0
    refine ⟨l, fa ≫ g, ((N).map (D.map g)).f (n - 1) (((N).map (D.map fb)).f (n - 1) y'), ?_⟩
    rw [hu, map_sub, sub_eq_zero] at hg
    rw [mapcomp, hg, nat]

end GlobalTheory.EtC.ContFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeqExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeSeq

variable {R : Type} [CommRing R]

theorem cls_eq {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeSeq

theorem GlobalTheory.EtC.coneSeq_exact : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ), Function.Exact (cpull (mappingCone.inr f) I n) (cpull f I n) ∧ Function.Exact (cpull f I n) (cpre (mappingCone.fst f) I n (n + 1) (by omega)) ∧ Function.Exact (cpre (mappingCone.fst f) I n (n + 1) (by omega)) (cpull (mappingCone.inr f) I (n + 1)) := by
  intro R _ K L f I n
  refine ⟨?_, ?_, ?_⟩
  · intro y
    constructor
    · intro hb
      obtain ⟨b, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ b _) = 0 at hb
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb
      obtain ⟨β, hβ⟩ := hb
      refine ⟨CohomologyClass.mk (mappingCone.descCocycle f (n.negOnePow • β) b (by omega) ?_), ?_⟩
      · rw [δ_units_smul, hβ]; simp [zcomp]
      · change CohomologyClass.mk (zcomp _ _ _) = _
        congr 1; ext1; simp [zcomp]
    · rintro ⟨z, rfl⟩
      obtain ⟨c, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ c _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • (mappingCone.inl f).comp (c : Cochain _ I n) (by omega), ?_⟩
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, smul_smul]
  · intro y
    constructor
    · intro ha
      obtain ⟨a, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ a _) = 0 at ha
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at ha
      obtain ⟨γ, hγ⟩ := ha
      have hβ : δ n (n + 1) ((Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n)) = 0 := by
        rw [δ_ofHom_comp, hγ]; simp [zcomp]
      refine ⟨CohomologyClass.mk (Cocycle.mk (-(n.negOnePow • (Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n))) (n + 1) rfl (by rw [δ_neg, δ_units_smul, hβ]; simp)), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ (n - 1) (by omega) (-((mappingCone.inl f).comp γ (by omega))) ?_
      have key := δ_comp (mappingCone.inl f) γ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) rfl
      rw [hγ] at key
      simp [zcomp] at key
      simp [zcomp, key, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    · rintro ⟨z, rfl⟩
      obtain ⟨b, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ b _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      refine ⟨-(n.negOnePow • (mappingCone.snd f).comp (b : Cochain _ I n) (zero_add n)), ?_⟩
      rw [δ_neg, δ_units_smul, δ_comp _ _ _ 1 (n + 1) (n + 1) rfl (zero_add 1) rfl]
      simp [zcomp, smul_smul, Cochain.comp_assoc_of_second_is_zero_cochain]
  · intro y
    constructor
    · intro hc
      obtain ⟨c, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ c _) = 0 at hc
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at hc
      obtain ⟨β, hβ⟩ := hc
      set a : Cochain K I n := (mappingCone.inl f).comp (c : Cochain _ I (n + 1)) (by omega) +
        n.negOnePow • (Cochain.ofHom f).comp β (zero_add n) with ha_def
      have hsnd := δ_comp (mappingCone.snd f) β (zero_add n) 1 (n + 1) (n + 1) rfl (zero_add 1) rfl
      rw [hβ] at hsnd
      simp [zcomp] at hsnd
      have hdec : (c : Cochain _ I (n + 1)) = (mappingCone.fst f).1.comp a (by omega) +
          δ n (n + 1) ((mappingCone.snd f).comp β (zero_add n)) := by
        rw [mappingCone.ext_cochain_from_iff f n (n + 1) rfl]
        constructor
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
      have hcoc : δ n (n + 1) a = 0 := by
        have h1 := congrArg (δ (n + 1) (n + 2)) hdec
        rw [δ_add, δ_δ, add_zero, Cocycle.δ_eq_zero c (n + 2)] at h1
        rw [δ_comp _ _ _ 2 (n + 1) (n + 2) (by omega) rfl rfl] at h1
        simp at h1
        have h2 := congrArg (fun x => (mappingCone.inl f).comp x (show -1 + (n + 2) = n + 1 by omega)) h1
        simpa using h2.symm
      refine ⟨CohomologyClass.mk (Cocycle.mk a (n + 1) rfl hcoc), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ n rfl (-((mappingCone.snd f).comp β (zero_add n))) ?_
      simp [zcomp, hdec]
    · rintro ⟨z, rfl⟩
      obtain ⟨a, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ a _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      exact ⟨0, by simp [zcomp]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleOfMapToDegreeOneTermStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_of_map_to_degreeOne_term : ∀ (C : Shv ℤ) (I : Cx ℤ) (ψ : C ⟶ I.X 1), ψ ≫ I.d 1 2 = 0 → ∃ w : Cocycle (sgl C) I 1, sglι C ≫ w.1.v 0 1 (zero_add 1) = ψ := by
  first | (exact @GlobalTheory.EtC.exists_cocycle_of_map_to_X_one) | (exact GlobalTheory.EtC.exists_cocycle_of_map_to_X_one) | (intros; apply GlobalTheory.EtC.exists_cocycle_of_map_to_X_one  <;> assumption)
end

