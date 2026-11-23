module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeight
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPos
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CompanionTheory.Iwasawa

theorem continuous_of_mul_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P K : Set G} {f : G → ℝ}
    (hP : IsClosed P) (hK : IsCompact K) (hf : ContinuousOn f P)
    (hd : ∀ x, ∃ p ∈ P, ∃ k ∈ K, x = p * k) (hv : ∀ p ∈ P, ∀ k ∈ K, f (p * k) = f p) : Continuous f := by
  refine continuous_iff_isClosed.2 fun C hC => ?_
  have hD : IsClosed (P ∩ f ⁻¹' C) := hf.preimage_isClosed_of_isClosed hP hC
  convert hD.mul_right_of_isCompact hK using 1
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, k, hk, rfl⟩ := hd x
    exact Set.mem_mul.2 ⟨p, ⟨hp, by simpa [Set.mem_preimage, hv p hp k hk] using hx⟩, k, hk, rfl⟩
  · rintro ⟨p, ⟨hp, hc⟩, k, hk, rfl⟩
    simpa [Set.mem_preimage, hv p hp k hk] using hc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem topRing_AE : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)

theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  exact GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)

theorem topologicalGroup_unitary_double : IsTopologicalGroup (G2 σ Y) := by
  haveI := topRing_AE (F := F) (E := E)
  infer_instance

def parT (x : G2 σ Y) : Matrix (Fin n) (Fin n) (AE F E) := (mat2 x * dC n (AE F E)).toRows₁

theorem continuous_mat2 : Continuous (mat2 : G2 σ Y → _) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_parT : Continuous (parT : G2 σ Y → _) := by
  haveI := topRing_AE (F := F) (E := E)
  have h : Continuous fun x : G2 σ Y => mat2 x * dC n (AE F E) := continuous_mat2.matrix_mul continuous_const
  exact continuous_matrix fun i j => h.matrix_elem _ _

theorem parT_eq {p : G2 σ Y} {t : GL (Fin n) (AE F E)} (h : IsPar p t) : parT p = t.1 := by
  rw [parT, isPar_iff.1 h, dC, diagCols, Matrix.fromRows_mul, Matrix.one_mul, Matrix.toRows₁_fromRows]

theorem exists_isPar_iff {x : G2 σ Y} : (∃ t, IsPar x t) ↔ mat2 x * dC n (AE F E) = dC n (AE F E) * parT x ∧
    mat2 x⁻¹ * dC n (AE F E) = dC n (AE F E) * parT x⁻¹ ∧ parT x * parT x⁻¹ = 1 ∧ parT x⁻¹ * parT x = 1 := by
  constructor
  · rintro ⟨t, h⟩
    have h' := IsPar.inv h
    rw [parT_eq h, parT_eq h']
    exact ⟨isPar_iff.1 h, isPar_iff.1 h', Units.mul_inv t, Units.inv_mul t⟩
  · rintro ⟨h1, -, h3, h4⟩
    exact ⟨⟨parT x, parT x⁻¹, h3, h4⟩, isPar_iff.2 h1⟩

theorem isClosed_siegel_stabiliser : IsClosed (par2 σ Y : Set (G2 σ Y)) := by
  haveI := topRing_AE (F := F) (E := E)
  haveI := t2Space_cm_host_adeles (F := F) (E := E)
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  have ci : Continuous fun x : G2 σ Y => parT x⁻¹ := continuous_parT.comp continuous_inv
  have cm : Continuous fun x : G2 σ Y => mat2 x⁻¹ := continuous_mat2.comp continuous_inv
  have e : (par2 σ Y : Set (G2 σ Y)) = {x | mat2 x * dC n (AE F E) = dC n (AE F E) * parT x} ∩
      ({x | mat2 x⁻¹ * dC n (AE F E) = dC n (AE F E) * parT x⁻¹} ∩
      ({x | parT x * parT x⁻¹ = 1} ∩ {x | parT x⁻¹ * parT x = 1})) := by
    ext x
    exact mem_parabolic_GL2_iff.trans exists_isPar_iff
  rw [e]
  exact (isClosed_eq (continuous_mat2.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_parT)).inter
    ((isClosed_eq (cm.matrix_mul continuous_const) (continuous_const.matrix_mul ci)).inter
    ((isClosed_eq (continuous_parT.matrix_mul ci) continuous_const).inter
    (isClosed_eq (ci.matrix_mul continuous_parT) continuous_const)))

def parU (p : par2 σ Y) : GL (Fin n) (AE F E) :=
  ⟨parT p.1, parT p.1⁻¹, (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).2.2.1, (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).2.2.2⟩

theorem isPar_parU (p : par2 σ Y) : IsPar p.1 (parU p) := isPar_iff.2 (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).1

theorem continuous_parU : Continuous (parU : par2 σ Y → GL (Fin n) (AE F E)) := by
  haveI := topRing_AE (F := F) (E := E)
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  exact Units.continuous_iff.2 ⟨continuous_parT.comp continuous_subtype_val,
    continuous_parT.comp (continuous_inv.comp continuous_subtype_val)⟩

theorem continuous_detGL : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE F E) → (AE F E)ˣ) := by
  haveI := topRing_AE (F := F) (E := E)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · exact Units.continuous_coe_inv.matrix_det

theorem continuous_pos {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) : Continuous a ∧ ∀ x, 0 < a x := by
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  have v1 : ∀ p t, IsPar p t → a p = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := fun p t h => by
    simpa using ha.val p t h 1 K.one_mem
  refine ⟨continuous_of_mul_compact (P := par2 σ Y) isClosed_siegel_stabiliser hK ?_ ?_ ?_, fun x => ?_⟩
  · refine continuousOn_iff_continuous_restrict.2 ?_
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (continuous_detGL.comp continuous_parU))).congr
      fun p => (v1 _ _ (isPar_parU p)).symm
  · intro x
    obtain ⟨p, t, h, k, hk, e⟩ := ha.iwa x
    exact ⟨p, mem_parabolic_GL2_iff.2 ⟨t, h⟩, k, hk, e⟩
  · intro p hp k hk
    obtain ⟨t, h⟩ := mem_parabolic_GL2_iff.1 hp
    rw [ha.val p t h k hk, v1 p t h]
  · obtain ⟨p, t, h, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t h k hk]
    have u : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := fun h0 => by
      have e := map_mul (absE F E) (Matrix.GeneralLinearGroup.det t) (Matrix.GeneralLinearGroup.det t)⁻¹
      rw [mul_inv_cancel, map_one, h0, zero_mul] at e
      exact one_ne_zero e
    exact_mod_cast pos_iff_ne_zero.2 u

theorem height_continuous_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x :=
  fun F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha =>
    continuous_pos (GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s hB hn hY b K a hb hK ha) ha

end GlobalTheory.CompanionTheory.Iwasawa
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def starLoc (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : R → ℂ) (dx : Measure (Fin n → Fin M → R ⊗[F] E))
    (Φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (b : HermR R σ n) : ℂ :=
  ∫ X, Φ X * ψR (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J X))) ∂dx

def psiFin (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def hermInf (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Ainf F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

def hermFin (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Af F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockSolutionExists
section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

section Sel

variable {K : Type} [Field K]

def selE (K : Type) [Field K] (r n : ℕ) : Matrix (Fin r) (Fin n) K :=
  fun i j => if (j : ℕ) = i then 1 else 0

theorem selE_mul_transpose {r n : ℕ} (hr : r ≤ n) :
    selE K r n * (selE K r n)ᵀ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selE, Matrix.one_apply]
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]
  · by_cases hik : i = k
    · subst hik; simp
    · have hne : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
      simp [hik, hne]
  · intro j _ hj
    have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem transpose_selE_mul {r n : ℕ} (hr : r ≤ n) :
    (selE K r n)ᵀ * selE K r n = eId K n r := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selE, eId, Matrix.diagonal_apply]
  by_cases hj : (j : ℕ) < r
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · by_cases hjk : j = k
      · subst hjk; simp [hj]
      · have hne : (k : ℕ) ≠ j := fun h => hjk (Fin.ext h.symm)
        simp [hjk, hne]
    · intro i _ hi
      have hne : (j : ℕ) ≠ i := fun h => hi (Fin.ext h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · simp [hj]
    · intro i _
      have hne : (j : ℕ) ≠ i := fun h => hj (h ▸ i.2)
      simp [hne]

theorem cT_selE (σ : K →+* K) {r n : ℕ} : cT σ (selE K r n) = (selE K r n)ᵀ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, selE]
  split_ifs <;> simp

theorem extB_eq_selE {r n : ℕ} (hr : r ≤ n) (b : Matrix (Fin r) (Fin r) K) :
    extB (n := n) b = (selE K r n)ᵀ * b * selE K r n := by
  ext i j
  simp only [extB, Matrix.mul_apply, Matrix.transpose_apply, selE]
  by_cases hi : (i : ℕ) < r
  · by_cases hj : (j : ℕ) < r
    · rw [dite_eq_left ⟨hi, hj⟩]
      have e1 : ∀ l : Fin r, (∑ k : Fin r, (if (i : ℕ) = k then (1 : K) else 0) * b k l) = b ⟨i, hi⟩ l := by
        intro l
        rw [Finset.sum_eq_single ⟨i, hi⟩]
        · simp
        · intro k _ hk
          have hne : (i : ℕ) ≠ k := fun h => hk (Fin.ext h.symm)
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [e1]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro l _ hl
        have hne : (j : ℕ) ≠ l := fun h => hl (Fin.ext h.symm)
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dite_eq_right (fun h => hj h.2)]
      symm
      apply Finset.sum_eq_zero
      intro l _
      have hne : (j : ℕ) ≠ l := fun h => hj (h ▸ l.2)
      simp [hne]
  · rw [dite_eq_right (fun h => hi h.1)]
    symm
    apply Finset.sum_eq_zero
    intro l _
    rw [Finset.sum_eq_zero, zero_mul]
    intro k _
    have hne : (i : ℕ) ≠ k := fun h => hi (h ▸ k.2)
    simp [hne]

theorem selE_mul_of_isCompl {r n : ℕ} (hr : r ≤ n) {c : Matrix (Fin r) (Fin n) K}
    {a : Matrix (Fin n) (Fin n) K} (h : IsCompl c a) : selE K r n * a = c := by
  ext i j
  simp only [Matrix.mul_apply, selE]
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]
  · have key := congrFun (h.2 ⟨i, lt_of_lt_of_le i.2 hr⟩ i.2) j
    simpa using key
  · intro k _ hk
    have hne : (k : ℕ) ≠ i := fun h' => hk (Fin.ext h')
    simp [hne]
  · intro h'; exact absurd (Finset.mem_univ _) h'

end Sel

theorem exists_hermitian_lowerLeft :
    ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n r : ℕ}, r ≤ n →
      ∀ (c : Matrix (Fin r) (Fin n) K) (a C D : Matrix (Fin n) (Fin n) K)
        (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
        IsCompl c a → C = T * c → L * T = 1 → C * cT σ D = D * cT σ C →
        ∃ b : Matrix (Fin r) (Fin r) K, cT σ b = b ∧
          C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  intro K _ σ hσ n r hr c a C D T L hc hC hLT hH
  have hca : c = selE K r n * a := (selE_mul_of_isCompl hr hc).symm
  have ha : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hc.1
  have hcTc : cT σ c = cT σ a * (selE K r n)ᵀ := by rw [hca, cT_mul, cT_selE]
  have hcTT : cT σ T * cT σ L = 1 := by rw [← cT_mul, hLT, cT_one]
  have h1 : T * c * cT σ D = D * cT σ a * (selE K r n)ᵀ * cT σ T := by
    rw [← hC, hH, hC, cT_mul, hcTc]
    simp only [Matrix.mul_assoc]
  have hM : D * cT σ a * (selE K r n)ᵀ = T * (c * cT σ D * cT σ L) := by
    calc D * cT σ a * (selE K r n)ᵀ = D * cT σ a * (selE K r n)ᵀ * (cT σ T * cT σ L) := by
          rw [hcTT, Matrix.mul_one]
      _ = T * c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, ← h1]
      _ = T * (c * cT σ D * cT σ L) := by simp only [Matrix.mul_assoc]
  refine ⟨c * cT σ D * cT σ L, ?_, ?_⟩
  · rw [cT_mul, cT_mul, cT_cT σ hσ, cT_cT σ hσ, hcTc]
    calc L * (D * (cT σ a * (selE K r n)ᵀ)) = L * (T * (c * cT σ D * cT σ L)) := by
          rw [← hM]; simp only [Matrix.mul_assoc]
      _ = c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, hLT, Matrix.one_mul]
  · have hSP : selE K r n * eId K n r = selE K r n := by
      rw [← transpose_selE_mul hr, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]
    have hSB : selE K r n * extB (n := n) (c * cT σ D * cT σ L) = (c * cT σ D * cT σ L) * selE K r n := by
      rw [extB_eq_selE hr, ← Matrix.mul_assoc, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]
    have hCa : C * a⁻¹ = T * selE K r n := by
      rw [hC, hca, Matrix.mul_assoc T, Matrix.mul_assoc, ha, Matrix.mul_one]
    rw [hCa, Matrix.mul_assoc T (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_one, hSP, hSB,
      sub_self, zero_sub, Matrix.mul_neg, ← transpose_selE_mul hr, ← Matrix.mul_assoc (D * cT σ a), hM]
    simp only [Matrix.mul_assoc, neg_add_cancel]

end GlobalTheory.CompanionTheory.BruhatCell
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianScalarSequenceTendsZero
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path

variable {F : Type} [Field F] [NumberField F]

def invInf (F : Type) [Field F] [NumberField F] (n : ℕ) : Ainf F :=
  fun w => ((n : w.Completion) + 1)⁻¹

omit [NumberField F] in
theorem norm_natCast_add_one (w : NumberField.InfinitePlace F) (n : ℕ) :
    ‖((n : w.Completion) + 1)‖ = (n : ℝ) + 1 := by
  have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _) ((n : w.Completion) + 1)
  rw [← h, map_add (f := _), map_natCast, map_one]
  have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_natCast]
  push_cast; ring

theorem natCast_add_one_ne_zero (w : NumberField.InfinitePlace F) (n : ℕ) :
    ((n : w.Completion) + 1) ≠ 0 := by
  intro h
  have := norm_natCast_add_one w n
  rw [h, norm_zero] at this
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem mul_invInf (n : ℕ) : ((n : Ainf F) + 1) * invInf F n = 1 := by
  have key : ((n : ∀ w : NumberField.InfinitePlace F, w.Completion) + 1) *
      (fun w : NumberField.InfinitePlace F => ((n : w.Completion) + 1)⁻¹) = 1 := by
    funext w
    simp only [Pi.mul_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
    exact mul_inv_cancel₀ (natCast_add_one_ne_zero w n)
  exact key

theorem tendsto_invInf : Filter.Tendsto (invInf F) Filter.atTop (nhds 0) := by
  refine tendsto_pi_nhds.2 fun w => ?_
  have key : Filter.Tendsto (fun n : ℕ => ((n : w.Completion) + 1)⁻¹) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ n : ℕ, ‖((n : w.Completion) + 1)⁻¹‖ = 1 / ((n : ℝ) + 1) := fun n => by
      rw [norm_inv, norm_natCast_add_one, one_div]
    simp only [e]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact key

def seqA (F : Type) [Field F] [NumberField F] (n : ℕ) : AF F := pairA F (invInf F n) 0

theorem tendsto_seqA : Filter.Tendsto (seqA F) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun n => (invInf F n, (0 : Af F))) Filter.atTop (nhds ((0 : Ainf F), (0 : Af F))) :=
    tendsto_invInf.prodMk_nhds tendsto_const_nhds
  exact this

def seqE (D : D7) (r n : ℕ) : Mx D r r :=
  Matrix.diagonal fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)

theorem seqE_mem (D : D7) (r n : ℕ) : seqE D r n ∈ hermA D r := by
  show GlobalTheory.MixModel.adj (seqE D r n) = seqE D r n
  ext i j
  by_cases h : i = j
  · subst h
    simp [GlobalTheory.MixModel.adj, seqE, sigR]
  · simp [GlobalTheory.MixModel.adj, seqE, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem tendsto_seqE (D : D7) (r : ℕ) : Filter.Tendsto (seqE D r) Filter.atTop (nhds 0) := by
  have hc : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Filter.Tendsto (fun n => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) Filter.atTop (nhds (0 : AE D)) := by
    have h2 : Filter.Tendsto (fun n => seqA D.host.F n • (1 : AE D)) Filter.atTop (nhds ((0 : AF D.host.F) • (1 : AE D))) :=
      tendsto_seqA.smul_const _
    rw [zero_smul] at h2
    refine h2.congr fun n => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  show Filter.Tendsto (fun n => seqE D r n i j) Filter.atTop (nhds (0 : AE D))
  by_cases h : i = j
  · subst h
    refine h1.congr fun n => ?_
    exact (Matrix.diagonal_apply_eq (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) i).symm
  · refine (tendsto_const_nhds (x := (0 : AE D))).congr fun n => ?_
    exact (Matrix.diagonal_apply_ne (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) h).symm

theorem theta_seqE (D : D7) (θ : InfFam D) (ρ : D.what₂.Tau) (n : ℕ) :
    θ ρ (infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E))) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  have e1 : infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [e1]
  have e2 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * (invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_invInf, mul_one]; rfl
  have e3 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((n : Ainf D.host.F ⊗[D.host.F] D.host.E) + 1) := by
    rw [TensorProduct.add_tmul, ← Algebra.TensorProduct.one_def]
    congr 1
  have e4 := congrArg (θ ρ) e2
  rw [e3, map_mul, map_add (f := _), map_natCast, map_one] at e4
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp
  linear_combination e4

theorem exists_herm_seq : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r : ℕ, ∃ e : ℕ → Mx D r r, (∀ n, e n ∈ hermA D r) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ (n : ℕ) (ρ : D.what₂.Tau), compAt θ ρ (e n) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  intro D θ _ r
  refine ⟨seqE D r, seqE_mem D r, tendsto_seqE D r, fun n ρ => ?_⟩
  ext i j
  by_cases h : i = j
  · subst h
    simp only [compAt, seqE, Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq]
    rw [theta_seqE]; simp
  · simp [compAt, seqE, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeightStatement
section
open PositivityTheory.RgBcC.RealD (IsLev)
open GlobalTheory.CompanionTheory.ModelS (SmF fRaw Kf muZ)

theorem GlobalTheory.T.inducedFunction_k_highest_weight :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam →
      ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : SmF n, F.1 = fRaw lam lev →
        (∀ a b : Fin n, a < b → Kf a b F = 0) ∧
          ∀ a : Fin n, Kf a a F = (muZ lam lev a : ℂ) • F :=
  GlobalTheory.CompanionTheory.ModelS.f_highest
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitDom
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.WeilM Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

namespace GlobalTheory.CompanionTheory.ThetaCoord

variable {F : Type} [Field F] [NumberField F] {κ : Type}



def finOf (a : κ → AF F) : κ → FiniteAdeleRing (𝓞 F) F := fun i => (a i).2

def infOf (a : κ → AF F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

end GlobalTheory.CompanionTheory.ThetaCoord

end
end

