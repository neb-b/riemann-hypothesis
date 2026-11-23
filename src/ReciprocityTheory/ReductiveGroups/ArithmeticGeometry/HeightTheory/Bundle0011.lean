module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.SemistableReduction.Bundle0017
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionSheafQuotient
public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

noncomputable def hTX5 {κ : Type} [Fintype κ] (f : MvPolynomial κ K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w f)) +
      ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)

noncomputable def bilinearSubstitution {D N : ℕ} (f : KTp K D N) :
    MvPolynomial ((Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) K :=
  MvPolynomial.aeval (fun t : TVar D N =>
    MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
      MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2))) f

section Gen

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] {P I : Type*} [Fintype P]
  [Fintype I]

theorem aeval_elim_mul_of_xhom (f : P → S) (g : I → S) (t : S) (n : ℕ) (Q : MvPolynomial (P ⊕ I) R)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = n) :
    MvPolynomial.aeval (Sum.elim f (fun i => t * g i)) Q =
      t ^ n * MvPolynomial.aeval (Sum.elim f g) Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hQ s hs]
  ring

end Gen

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def affineCoord (c : ι) (j : Fin (d.N + 1)) : Ω c :=
  ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)

noncomputable def linearSubstitution (c : ι) :
    MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K]
      MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X p
    | Sum.inr i => ∑ j, MvPolynomial.X (i, j) * MvPolynomial.C (d.affineCoord c j)

noncomputable def scaledSubstitution (c : ι) :
    MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K]
      MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X (some p)
    | Sum.inr i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j)

theorem scaledSubstitution_eq (c : ι) : d.scaledSubstitution c = MvPolynomial.aeval (Sum.elim (fun p => MvPolynomial.X (some p))
    (fun i => MvPolynomial.X none *
      ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) := by
  unfold scaledSubstitution
  congr 1
  funext v
  cases v <;> rfl

theorem aeval_elim_eq_rename_linearSubstitution (c : ι)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) :
    MvPolynomial.aeval (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) Q =
      MvPolynomial.rename some (d.linearSubstitution c Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [linearSubstitution, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    cases v <;> simp [linearSubstitution, map_mul, hp, map_sum]

theorem scaledSubstitution_of_homogeneous (c : ι) (n : ℕ)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = n) :
    d.scaledSubstitution c Q = MvPolynomial.X none ^ n * MvPolynomial.rename some (d.linearSubstitution c Q) := by
  rw [scaledSubstitution_eq, aeval_elim_mul_of_xhom _ _ _ n Q hQ, aeval_elim_eq_rename_linearSubstitution]

theorem eq_zero_of_xhom_zero (c : ι)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = 0) (h : d.linearSubstitution c Q = 0) : Q = 0 := by
  have hvars : (↑Q.vars : Set ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2))) ⊆ Set.range Sum.inl := by
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    cases x with
    | inl p => exact ⟨p, rfl⟩
    | inr i =>
      exfalso
      have h0 := (Finset.sum_eq_zero_iff.mp (hQ s hs)) i (Finset.mem_univ _)
      exact (Finsupp.mem_support_iff.mp hxs) h0
  obtain ⟨Q0, rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q Sum.inl Sum.inl_injective hvars
  have hmap : ∀ q : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) K,
      MvPolynomial.aeval (fun p => (MvPolynomial.X p : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c))) q =
        MvPolynomial.map (algebraMap K (Ω c)) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [MvPolynomial.algebraMap_eq]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p v hp => simp [map_mul, hp]
  have e : d.linearSubstitution c (MvPolynomial.rename Sum.inl Q0) = MvPolynomial.map (algebraMap K (Ω c)) Q0 := by
    rw [← hmap, linearSubstitution, MvPolynomial.aeval_rename]
    rfl
  rw [e] at h
  have hQ0 : Q0 = 0 := MvPolynomial.map_injective _ (algebraMap K (Ω c)).injective (by rw [h, map_zero])
  rw [hQ0, map_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GenericSectionOfAxioms
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def htOf (hd : d.AxH 𝒜) (h : d.S1) : Formalism.MainNotions.Gaps.HeightData.HtData where
  K := K
  D := d.D
  δ := d.del
  i := d.i
  g0 := d.g0
  L := d.wsize d.wL
  G := d.Gc
  PH := d.PHc
  Prw := d.Prw
  Pet := d.Pet
  S := fun k => meanK fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))
  etaPart := True
  Op := fun la => Op d.D d.N la
  SectionSheafQuotient := fun _ => ∀ c, OmS (Ω c) d.D d.N
  mA := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    inferInstance
  A0 := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)
  t := fun _ => d.bvecG hd.sel hd.a4.choose
  Pts := fun la => Σ c, {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) // w ∈ d.PlOver la c}
  ep := fun _ _ => 1
  f := fun _ ζ => d.fze h ζ.1 ζ.2.1
  vEt := fun _ ζ => (d.ord ζ.1 (d.Wres ζ.1 ζ.2.1) (d.n1 • d.wde) (d.et ζ.1) : ℝ)

theorem genericSection_of_axioms (hd : d.AxH 𝒜) : d.S1 := by
  intro c
  have hS := (ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) (hd.fg c) (hd.trdeg c)
    (hd.a1 c)).1
  have key : ∀ {M : Type} (j0 : Fin (d.N + 1)) (a : M) (f : Fin d.N → M),
      Fin.succAboveCases (α := fun _ => M) j0 a f j0 = a ∧
      ∀ k, Fin.succAboveCases (α := fun _ => M) j0 a f (j0.succAbove k) = f k :=
    fun j0 a f => ⟨by exact Fin.insertNth_apply_same (α := fun _ => _) j0 a f,
      fun k => by exact Fin.insertNth_apply_succAbove (α := fun _ => _) j0 a f k⟩
  let σ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.succAboveCases (α := fun _ => Fin (d.N + 1)) (d.jc c) 0 Fin.succ
  let ρ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.cases (motive := fun _ => Fin (d.N + 1)) (d.jc c) (d.jc c).succAbove
  have hρσ : Function.LeftInverse ρ σ := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [σ, ρ, (key _ _ _).1, Fin.cases_zero]
    · simp only [σ, ρ, (key _ _ _).2, Fin.cases_succ]
  let g : TVar d.D d.N → Fin (d.D + 1) × Fin (d.N + 1) := fun p => (p.1, σ p.2)
  have hg : Function.Injective g := by
    intro p q hpq
    simp only [g, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (hρσ.injective hpq.2)
  have heq : ∀ p, sImg (d.jc c) (d.x c) p = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) (g p) := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).1, Fin.cases_zero]
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).2, Fin.cases_succ]
  have hfun : sImg (d.jc c) (d.x c) = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) ∘ g := funext heq
  have hI : AlgebraicIndependent K (sImg (D := d.D) (d.jc c) (d.x c)) := by
    rw [hfun]
    exact hS.comp g hg
  exact hI

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscLat

open Module

theorem det_blockDiagonal' {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type*} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical

  have hblk : ∀ c, (Matrix.toSquareBlock (Matrix.blockDiagonal' M) Sigma.fst c).det =
      (M c).det := by
    intro c
    let e : κ c ≃ {s : (Σ c, κ c) // s.1 = c} :=
      { toFun := fun k => ⟨⟨c, k⟩, rfl⟩
        invFun := fun s => cast (congrArg κ s.2) s.1.2
        left_inv := fun k => rfl
        right_inv := by
          rintro ⟨⟨a, k⟩, rfl⟩
          rfl }
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext k k'
    show Matrix.blockDiagonal' M ⟨c, k⟩ ⟨c, k'⟩ = M c k k'
    first
      | exact Matrix.blockDiagonal'_apply_eq M c k k'
      | simp [Matrix.blockDiagonal'_apply]
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  first
    | rw [(Matrix.blockTriangular_blockDiagonal' M).det]
    | rw [Matrix.BlockTriangular.det (Matrix.blockTriangular_blockDiagonal' M)]
  rw [Finset.prod_congr rfl (fun c _ => hblk c)]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro c _ hc
  haveI : IsEmpty (κ c) :=
    ⟨fun k => hc (Finset.mem_image.2 ⟨⟨c, k⟩, Finset.mem_univ _, rfl⟩)⟩
  exact Matrix.det_isEmpty

theorem gram_mul {F L : Type*} [Field F] [Field L] [Algebra F L] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (a : Basis κ F L) (h : L) :
    (Matrix.of fun p q => Algebra.trace F L (h * a p * a q)).det =
      Algebra.norm F h * Algebra.discr F a := by

  rw [Algebra.discr_def, Algebra.norm_eq_matrix_det a h,
    ← Matrix.det_transpose (Algebra.leftMulMatrix a h), ← Matrix.det_mul]
  congr 1
  ext p q
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [← a.sum_repr (h * a p)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]

theorem length_quot {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    {CC V : Type*} [AddCommGroup CC] [Module R CC] [AddCommGroup V] [Module R V]
    {κ : Type*} [Fintype κ] [DecidableEq κ] (α : Basis κ R CC) (φ : CC →ₗ[R] V)
    (hφ : Function.Injective φ) (SA : Submodule R V) (hSA : SA = LinearMap.range φ)
    {m : ℕ} (b' : Fin m → CC) (hli : LinearIndependent R b') (σ : κ ≃ Fin m) :
    ∃ n : ℕ, ∃ u : Rˣ,
      Module.length R (SA ⧸ (Submodule.span R (Set.range (φ ∘ b'))).comap SA.subtype) = n ∧
      α.det (b' ∘ σ) = u * ϖ ^ n := by
  classical
  set N := Submodule.span R (Set.range b')
  have hrank : finrank R N = finrank R CC := by
    rw [finrank_span_eq_card hli, finrank_eq_card_basis α, Fintype.card_fin, Fintype.card_congr σ,
      Fintype.card_fin]
  set s := Submodule.smithNormalFormCoeffs α hrank
  have hlen : Module.length R (CC ⧸ N) = ∑ i, IsDiscreteValuationRing.addVal R (s i) := by
    rw [(Submodule.quotientEquivPiSpan N α hrank).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (α.det (b' ∘ σ)) (∏ i, s i) := by
    have key := ReciprocityTheory.MultiplicativeHeights.det_subtype_comp_associated_prod α N hrank (α.equiv (Basis.span hli) σ)
    convert key using 1
    rw [← LinearMap.det_toMatrix α, Basis.det_apply]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, Basis.toMatrix_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply,
      Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  have hne : (∏ i, s i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Submodule.smithNormalFormCoeffs_ne_zero α hrank i
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hval : ∑ i, IsDiscreteValuationRing.addVal R (s i) = n := by
    rw [← ReciprocityTheory.MultiplicativeHeights.addVal_prod, hu, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp
  let E : CC ≃ₗ[R] SA := (LinearEquiv.ofInjective φ hφ).trans (LinearEquiv.ofEq _ _ hSA.symm)
  have hE : ∀ y, (E y : V) = φ y := fun y => rfl
  have hmap : N.map (E : CC →ₗ[R] SA) =
      (Submodule.span R (Set.range (φ ∘ b'))).comap SA.subtype := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    rw [Set.range_comp, ← Submodule.map_span]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change φ y ∈ _
      exact Submodule.mem_map_of_mem hy
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, Subtype.ext (by change φ y = _; exact hyx)⟩
  obtain ⟨v, hv⟩ := hdet.symm
  refine ⟨n, u * v, ?_, ?_⟩
  · rw [← (Submodule.Quotient.equiv N _ E hmap).length_eq, hlen, hval]
  · rw [← hv, hu, Units.val_mul]
    ring

end HDiscLat

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscDefs
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def unif (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 𝓞 K :=
  open Classical in
  if h : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 then h.choose else 0

noncomputable def gOrd (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (q : KTf K d.D d.N) : ℤ :=
  open Classical in
  if h : ∃ m : ℤ, ∃ u : Op d.D d.N la, IsUnit u ∧
      q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u
  then h.choose else 0

noncomputable def De (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N :=
  Matrix.det (Matrix.of fun k l : Fin d.del => ∑ c,
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    Algebra.trace (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c))

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormDefs
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def tOf (z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1)) : Fin d.D → Fin (d.N + 1) → ℂ :=
  fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j

noncomputable def evT (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (q : KTp K d.D d.N) : ℂ :=
  MvPolynomial.eval₂ sg (fun v : TVar d.D d.N => Fin.cases (t0 v.2) (fun i => t i v.2) v.1) q

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

