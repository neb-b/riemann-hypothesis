module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
section
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

section Index

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]

variable [IsDomain R] [IsDiscreteValuationRing R]

end Index

section Points

variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]

theorem det_algHom_basis_ne_zero (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : (Matrix.of fun i j => P j (e i)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc, hc₀⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hli := (linearIndependent_algHom_toLinearMap R S L).comp P hP
  rw [Fintype.linearIndependent_iff] at hli
  refine hc (funext (hli c (e.ext fun i => ?_)))
  have := congrFun hc₀ i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this


omit [IsDomain L] in
theorem algHom_matrix_mul_leftMulMatrix (e : Basis ι R S) (P : ι → (S →ₐ[R] L)) (x : S) :
    (Matrix.of fun j i => P j (e i)) * (Algebra.leftMulMatrix e x).map (algebraMap R L) =
      Matrix.diagonal (fun j => P j x) * Matrix.of fun j i => P j (e i) := by
  ext j k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.diagonal_mul, Matrix.of_apply, ← map_mul, ← e.sum_repr (x * e k), map_sum,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Matrix.of_apply, mul_comm]

theorem map_charpoly_leftMulMatrix_eq_prod_algHom (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    (Algebra.leftMulMatrix e x).charpoly.map (algebraMap R L) = ∏ j, (X - C (P j x)) := by
  set Q : Matrix ι ι L := Matrix.of fun j i => P j (e i) with hQ
  have hQ₀ : Q.det ≠ 0 := by
    rw [← Matrix.det_transpose]
    exact det_algHom_basis_ne_zero e hP
  have h := algHom_matrix_mul_leftMulMatrix e P x
  rw [← hQ] at h
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal]
  set A := (Algebra.leftMulMatrix e x).map (algebraMap R L)
  set D := Matrix.diagonal fun j => P j x
  have h₁ : (C : L →+* L[X]).mapMatrix Q * A.charmatrix =
      D.charmatrix * (C : L →+* L[X]).mapMatrix Q := by
    simp only [Matrix.charmatrix, mul_sub, sub_mul, ← map_mul, h]
    congr 1
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm
  have h₂ := congrArg Matrix.det h₁
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, mul_comm] at h₂
  exact mul_right_cancel₀ (C_ne_zero.mpr hQ₀) h₂

theorem algebraMap_trace_eq_sum_algHom_of_basis (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  have h := map_charpoly_leftMulMatrix_eq_prod_algHom e hP x
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal] at h
  rw [Algebra.trace_eq_matrix_trace e, ← Matrix.trace_diagonal,
    Matrix.trace_eq_neg_charpoly_nextCoeff (Matrix.diagonal _), ← h,
    ← Matrix.trace_eq_neg_charpoly_nextCoeff, AddMonoidHom.map_trace]

theorem map_traceMatrix_eq_mul_transpose_of_basis {κ : Type*} (e : Basis ι R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (v : κ → S) :
    (Algebra.traceMatrix R v).map (algebraMap R L) =
      (Matrix.of fun i j => P j (v i)) * (Matrix.of fun i j => P j (v i)).transpose := by
  ext i k
  simp [algebraMap_trace_eq_sum_algHom_of_basis e hP, Matrix.mul_apply]

theorem algebraMap_discr_eq_det_sq_of_basis (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (v : ι → S) :
    algebraMap R L (Algebra.discr R v) = (Matrix.of fun i j => P j (v i)).det ^ 2 := by
  rw [Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply,
    map_traceMatrix_eq_mul_transpose_of_basis e hP, Matrix.det_mul, Matrix.det_transpose, pow_two]

theorem algebraMap_discr_basis_ne_zero (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : algebraMap R L (Algebra.discr R e) ≠ 0 := by
  rw [algebraMap_discr_eq_det_sq_of_basis e hP]
  exact pow_ne_zero _ (det_algHom_basis_ne_zero e hP)

variable [Module.Free R S] [Module.Finite R S]



omit [DecidableEq ι] in
theorem algebraMap_trace_eq_sum_algHom_of_card (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  classical
  have := (algebraMap R L).domain_nontrivial
  exact algebraMap_trace_eq_sum_algHom_of_basis
    ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP x

end Points

section Count

theorem etale_of_isReduced_of_perfectField (K S : Type*) [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Module.Finite K S] [IsReduced S] : Algebra.Etale K S := by
  have : IsArtinianRing S := .of_finite K S
  have (I : MaximalSpectrum S) : Algebra.FormallyEtale K (S ⧸ I.asIdeal) := by
    letI := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyEtale.of_isSeparable K (S ⧸ I.asIdeal)
  exact ⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars K).symm,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

variable (R S L : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field L] [Algebra R L]

theorem natCard_algHom_eq_finrank_of_etale_baseChange [Module.Free R S] [Module.Finite R S]
    [IsSepClosed L] [Algebra.FormallyEtale L (L ⊗[R] S)] :
    Nat.card (S →ₐ[R] L) = finrank R S := by
  have := (algebraMap R L).domain_nontrivial
  have : IsArtinianRing (L ⊗[R] S) := .of_finite L _
  have := Fintype.ofFinite (PrimeSpectrum (L ⊗[R] S))
  rw [Nat.card_congr (AlgHom.liftEquiv R L S L),
    Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[R] S)),
    ← Module.finrank_baseChange (R := L) (S := R) (M' := S),
    (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[R] S)).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem natCard_algHom_eq_finrank_of_isReduced_baseChange [Module.Free R S] [Module.Finite R S]
    [IsAlgClosed L] [IsReduced (L ⊗[R] S)] : Nat.card (S →ₐ[R] L) = finrank R S :=
  have := etale_of_isReduced_of_perfectField L (L ⊗[R] S)
  natCard_algHom_eq_finrank_of_etale_baseChange R S L

end Count

section Etale

variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]


variable (S) in
theorem natCard_algHom_eq_finrank_of_etale : Nat.card (S →ₐ[K] L) = finrank K S :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  natCard_algHom_eq_finrank_of_etale_baseChange K S L


variable {K L} {ι : Type*} [Fintype ι]

end Etale

section Reduced

variable {K S L ι : Type*} [Field K] [PerfectField K] [CommRing S] [Algebra K S]
  [Module.Finite K S] [IsReduced S] [Field L] [Algebra K L] [IsSepClosed L] [Fintype ι]
  [DecidableEq ι]

end Reduced

section Both

variable {R S L ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [Algebra R S] [CommRing L] [IsDomain L] [Algebra R L] [Fintype ι] [DecidableEq ι]

end Both

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TopClassSurjective
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory.CubeTop

variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]


omit [LinearOrder ι] in
theorem univ_subset {n : ℕ} (hn : Fintype.card ι = n) (s : {s : Finset ι // s.card = n}) :
    (Finset.univ : Finset ι) ⊆ s.1 :=
  (Finset.eq_univ_of_card s.1 (s.2.trans hn.symm)).ge

def topTerm (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    A.obj Finset.univ →ₗ[R] Cube.Term A n :=
  LinearMap.pi fun s => Cube.res A (univ_subset hn s)


omit [LinearOrder ι] in
theorem topTerm_surjective (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    Function.Surjective (topTerm A hn) := by
  intro x
  refine ⟨x ⟨Finset.univ, hn⟩, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  exact Cube.res_self A _ _

theorem topTerm_res_mem (A : Cube.{0} ι R) {p : ℕ} (hn : Fintype.card ι = p + 1) (i : ι)
    (x : A.obj (Finset.univ.erase i)) :
    ∃ y, Cube.d A p y = topTerm A hn (Cube.res A (Finset.erase_subset i _) x) := by
  let y : ∀ s, A.obj s := Pi.single (Finset.univ.erase i) (cubeSign Finset.univ i • x)
  refine ⟨fun s => y s.1, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  rw [Cube.d_apply_eq_totalD A _ y (fun _ => rfl), Cube.totalD_apply, Finset.sum_eq_single i]
  · simp only [y, Pi.single_eq_same, map_zsmul, cubeSign_smul_smul]
    exact (Cube.res_self A _ _).symm
  · intro j _ hji
    have : (Finset.univ.erase j : Finset ι) ≠ Finset.univ.erase i := fun h => by
      have : j ∈ (Finset.univ.erase i : Finset ι) := by simp [hji]
      rw [← h] at this
      simp at this
    simp only [y, Pi.single_eq_of_ne this, map_zero, smul_zero]
  · simp

theorem d_top (A : Cube.{0} ι R) :
    (cubeComplex A).d (Fintype.card ι) (Fintype.card ι + 1) = 0 := by
  rw [cubeComplex_d]
  have := Cube.subsingleton_term A (Nat.lt_succ_self (Fintype.card ι))
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

def topClass (A : Cube.{0} ι R) :
    A.obj Finset.univ →ₗ[R] (cubeComplex A).homology (Fintype.card ι) :=
  ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv).hom ∘ₗ topTerm A rfl

theorem topClass_surjective (A : Cube.{0} ι R) : Function.Surjective (topClass A) :=
  ((ModuleCat.epi_iff_surjective ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv)).1 inferInstance).comp (topTerm_surjective A rfl)

theorem topClass_res (A : Cube.{0} ι R) (i : ι) (x : A.obj (Finset.univ.erase i)) :
    topClass A (Cube.res A (Finset.erase_subset i _) x) = 0 := by
  have key : ∀ (n : ℕ) (hn : Fintype.card ι = n), ((cubeComplex A).pOpcycles n).hom
      (topTerm A hn (Cube.res A (Finset.erase_subset i _) x)) = 0 := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 :=
      Nat.exists_eq_succ_of_ne_zero (hn ▸ (Fintype.card_pos_iff.2 ⟨i⟩).ne')
    obtain ⟨y, hy⟩ := topTerm_res_mem A hn i x
    have := (cubeComplex A).d_pOpcycles p (p + 1)
    rw [cubeComplex_d] at this
    rw [← hy]
    exact congr(($this).hom y)
  have := key _ rfl
  let g := ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
    (d_top A)).inv.hom
  exact (congrArg g this).trans (map_zero g)

theorem span_topClass {κ : Type} (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) :
    Submodule.span R ((fun a : κ => topClass A (b Finset.univ ⟨a, Finset.subset_univ _⟩)) ''
      {a | T a = Finset.univ}) = ⊤ := by
  rw [eq_top_iff, ← LinearMap.range_eq_top.2 (topClass_surjective A), LinearMap.range_eq_map,
    ← (b Finset.univ).span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  by_cases h : T a.1 = Finset.univ
  · exact Submodule.subset_span ⟨a.1, h, rfl⟩
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ T a.1 := by
      simpa [Finset.eq_univ_iff_forall] using h
    have := topClass_res A i (b _ ⟨a.1, Finset.subset_erase.2 ⟨Finset.subset_univ _, hi⟩⟩)
    rw [hb] at this
    rw [this]
    exact zero_mem _

theorem main : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R) (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s)), (∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}), Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) → ((∀ a, T a ≠ Finset.univ) → (cubeComplex A).ExactAt (Fintype.card ι)) ∧ ({a | T a = Finset.univ}.Finite → Module.Finite R ((cubeComplex A).homology (Fintype.card ι))) := by
  intro ι _ _ R _ κ T A b hb
  have h := span_topClass T A b hb
  refine ⟨fun hT => ?_, fun hT => ⟨h ▸ Submodule.fg_span (hT.image _)⟩⟩
  · rw [Set.eq_empty_of_forall_notMem (s := {a | T a = Finset.univ}) hT, Set.image_empty,
      Submodule.span_empty] at h
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have := (Submodule.subsingleton_iff R).1 (subsingleton_of_bot_eq_top h)
    exact ModuleCat.isZero_of_subsingleton _

end GlobalTheory.CubeTop
end
end

