module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCoordinatesCellChangeBirational
section
namespace GlobalTheory.Reg.CellChange

open Matrix

theorem exists_algEquiv_of_generates {κ ι : Type} [Field κ] [Finite ι] (y : ι → FractionRing (MvPolynomial ι κ))
    (hy : ∀ v, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v) ∈
      IntermediateField.adjoin κ (Set.range y)) :
    ∃ e : FractionRing (MvPolynomial ι κ) ≃ₐ[κ] FractionRing (MvPolynomial ι κ),
      ∀ v, e (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v := by
  have htop : IntermediateField.adjoin κ (Set.range y) = ⊤ := by
    have hp : ∀ p : MvPolynomial ι κ, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) p ∈
        IntermediateField.adjoin κ (Set.range y) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ a
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p v hp => rw [map_mul]; exact mul_mem hp (hy v)
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial ι κ) x
    exact div_mem (hp a) (hp b)
  have hX : AlgebraicIndependent κ (fun v : ι =>
      algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v)) :=
    (MvPolynomial.algebraicIndependent_X ι κ).map'
      (f := IsScalarTower.toAlgHom κ (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)))
      (IsFractionRing.injective _ _)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin κ (Set.range y)) (FractionRing (MvPolynomial ι κ)) := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop]
    exact ⟨fun x => isAlgebraic_algebraMap (⟨x, trivial⟩ : (⊤ : IntermediateField κ _))⟩
  have hind : AlgebraicIndependent κ y :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite κ y hX.cardinalMk_le_trdeg).1
  have hinj : Function.Injective (MvPolynomial.aeval y : MvPolynomial ι κ →ₐ[κ] _) :=
    algebraicIndependent_iff_injective_aeval.1 hind
  let f : FractionRing (MvPolynomial ι κ) →ₐ[κ] FractionRing (MvPolynomial ι κ) :=
    IsFractionRing.liftAlgHom hinj
  have hf : ∀ v, f (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v := by
    intro v
    simp [f]
  have hs : Function.Surjective f := by
    have : IntermediateField.adjoin κ (Set.range y) ≤ f.fieldRange := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨v, rfl⟩
      exact ⟨_, hf v⟩
    intro x
    exact this (htop ▸ IntermediateField.mem_top)
  exact ⟨AlgEquiv.ofBijective f ⟨f.injective, hs⟩, hf⟩

theorem minors_iff {R : Type} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) :
    (∀ k (hk : k ≤ n), IsUnit (g.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) ↔
      ∃ u b : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ g = u * b :=
  (GlobalTheory.cell_coordinates_exists_unique R n n (Function.Embedding.refl _) g).1

theorem upper_inv {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) : b⁻¹.BlockTriangular id ∧ (∀ i, IsUnit (b⁻¹ i i)) ∧ b * b⁻¹ = 1 := by
  have hd := GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu
  have hbi : b⁻¹.BlockTriangular id := by
    let _ := Matrix.invertibleOfIsUnitDet b hd
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨hbi, fun i => ?_, Matrix.mul_nonsing_inv _ hd⟩
  have h1 : IsUnit b⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hd
  rw [Matrix.det_of_isUpperTriangular hbi] at h1
  exact IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)

theorem upper_mul_diag {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) (hc : c.BlockTriangular id) (hv : ∀ i, IsUnit (c i i)) (i : Fin n) :
    IsUnit ((b * c) i i) := by
  have h1 : IsUnit (b * c).det := by
    rw [Matrix.det_mul]
    exact (GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu).mul (GlobalTheory.isUnit_det_of_upper_of_isUnit_diag c hc hv)
  rw [Matrix.det_of_isUpperTriangular (hb.mul hc)] at h1
  exact IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)

theorem lower_mem_range {F K : Type} [Field F] [Field K] (φ : F →+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (l b : Matrix (Fin n) (Fin n) K) (h0 : ∀ i j : Fin n, i < j → l i j = 0) (h1 : ∀ i, l i i = 1)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) (h : M.map φ = l * b) (i j : Fin n) :
    ∃ x, φ x = l i j := by
  have hm := (minors_iff (M.map φ)).2 ⟨l, b, h0, h1, hb, hu, h⟩
  obtain ⟨u, c, hu0, hu1, hc, hcu, hM⟩ := (minors_iff M).1 (fun k hk => by
    have h2 := hm k hk
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
    rw [isUnit_iff_ne_zero] at h2 ⊢
    intro h3
    exact h2 (by rw [h3, map_zero]))
  have := (GlobalTheory.cell_coordinates_exists_unique K n n (Function.Embedding.refl _) l).2 l (u.map φ) b (c.map φ)
    ⟨h0, h1⟩ ⟨fun i j hij => by simpa using hu0 i j hij, fun i => by simp [hu1 i]⟩ hb
    (hc.map φ) hu (by rw [← h, hM, Matrix.map_mul])
  exact ⟨u i j, by rw [this.1]; rfl⟩

theorem exists_lower_minors {κ : Type} [Field κ] {n : ℕ} (A : Matrix (Fin n) (Fin n) κ) (hA : IsUnit A.det) :
    ∃ l : Matrix (Fin n) (Fin n) (RatFunc κ), (∀ i j : Fin n, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧
      ∀ k (hk : k ≤ n), IsUnit ((A.map (algebraMap κ (RatFunc κ)) * l).submatrix
        (Fin.castLE hk) (Fin.castLE hk)).det := by
  have key : ∀ M : Matrix (Fin n) (Fin n) (Polynomial κ),
      (∀ k (hk : k ≤ n), (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      ∀ k (hk : k ≤ n), IsUnit ((M.map (algebraMap _ (RatFunc κ))).submatrix
        (Fin.castLE hk) (Fin.castLE hk)).det := by
    intro M hM k hk
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (hM k hk)
  obtain ⟨l, b, h0, h1, hb, hu, h⟩ := (minors_iff _).1 (key (Matrix.charmatrix (-A⁻¹)) (fun k hk => by
    have : (Matrix.charmatrix (-A⁻¹)).submatrix (Fin.castLE hk) (Fin.castLE hk) =
        Matrix.charmatrix ((-A⁻¹).submatrix (Fin.castLE hk) (Fin.castLE hk)) := by
      ext i j : 2
      simp [Matrix.charmatrix_apply, Matrix.diagonal_apply]
    rw [this]
    exact (Matrix.charpoly_monic _).ne_zero))
  obtain ⟨u, c, hu0, hu1, hc, hcu, h'⟩ := (minors_iff _).1
    (key (1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C) (fun k hk h2 => by
      have h3 := congrArg (Polynomial.evalRingHom (0 : κ)) h2
      rw [RingHom.map_det, map_zero] at h3
      have : (Polynomial.evalRingHom (0 : κ)).mapMatrix ((1 + (Polynomial.X : Polynomial κ) •
          A.map Polynomial.C).submatrix (Fin.castLE hk) (Fin.castLE hk)) = 1 := by
        ext i j
        simp [Matrix.one_apply, apply_ite]
      rw [this, Matrix.det_one] at h3
      exact one_ne_zero h3))
  obtain ⟨hbi, hbu, hbb⟩ := upper_inv b hb hu
  refine ⟨l, h0, h1, (minors_iff _).2 ⟨u, c * b⁻¹, hu0, hu1, hc.mul hbi, upper_mul_diag _ _ hc hcu hbi hbu, ?_⟩⟩
  have e1 : A.map Polynomial.C * Matrix.charmatrix (-A⁻¹) = 1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C := by
    rw [Matrix.charmatrix, Matrix.mul_sub, map_neg, Matrix.mul_neg, RingHom.mapMatrix_apply, ← Matrix.map_mul,
      Matrix.mul_nonsing_inv _ hA, sub_neg_eq_add, add_comm, Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j : 2
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
  have e2 : A.map (algebraMap κ (RatFunc κ)) = (A.map Polynomial.C).map (algebraMap _ (RatFunc κ)) := by
    ext i j
    exact IsScalarTower.algebraMap_apply κ (Polynomial κ) (RatFunc κ) (A i j)
  rw [← Matrix.mul_assoc, ← h', ← e1, Matrix.map_mul, h, ← e2, Matrix.mul_assoc, Matrix.mul_assoc, hbb,
    Matrix.mul_one]

section Low
variable {T S S' : Type} [CommRing S] [CommRing S'] {r : T → ℕ}

theorem lowM_upper (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) (i j : Fin (r τ))
    (h : i < j) : lowM x τ i j = 0 := by
  simp [lowM, h.not_gt, h.ne']

theorem lowM_diag (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) (i : Fin (r τ)) :
    lowM x τ i i = 1 := by
  simp [lowM]

theorem lowM_entry (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S)
    (v : Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) : lowM x v.1 v.2.1.2 v.2.1.1 = x v := by
  obtain ⟨τ, ⟨i, j⟩, h⟩ := v
  exact dite_eq_left h

theorem lowM_map (f : S →+* S') (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) :
    (lowM x τ).map f = lowM (fun v => f (x v)) τ := by
  ext i j
  simp only [lowM, Matrix.map_apply]
  split_ifs <;> simp

theorem lowM_of_lower (l : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) S) (τ : T)
    (h0 : ∀ i j, i < j → l τ i j = 0) (h1 : ∀ i, l τ i i = 1) :
    lowM (fun v : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) => l v.1 v.2.1.2 v.2.1.1) τ = l τ := by
  ext i j
  simp only [lowM]
  split_ifs with h h'
  · rfl
  · rw [h', h1]
  · exact (h0 i j (lt_of_le_of_ne (not_lt.1 h) (Ne.symm h'))).symm

end Low

theorem generic_minors {κ T : Type} [Field κ] {r : T → ℕ} (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ)
    (hA : ∀ τ, IsUnit (A τ).det) (τ : T) (k : ℕ) (hk : k ≤ r τ) :
    (((A τ).map (algebraMap κ (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) *
      lowM MvPolynomial.X τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  choose l h0 h1 hm using fun τ => exists_lower_minors (A τ) (hA τ)
  intro h
  let φ : MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ →ₐ[κ] RatFunc κ :=
    MvPolynomial.aeval (fun v => l v.1 v.2.1.2 v.2.1.1)
  have h2 := congrArg φ.toRingHom h
  rw [RingHom.map_det, map_zero, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, lowM_map] at h2
  apply (hm τ k hk).ne_zero
  rw [← h2, ← lowM_of_lower l τ (h0 τ) (h1 τ)]
  congr 3
  · ext i j
    exact (φ.commutes _).symm
  · congr 1
    funext v
    simp [φ]

end GlobalTheory.Reg.CellChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.cell_change_birational :
    ∀ (κ T : Type) [Field κ] [Infinite κ] [Finite T] (r : T → ℕ) (G : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ) (σ : ∀ τ, Equiv.Perm (Fin (r τ))), (∀ τ, IsUnit (G τ).det) → ∃ (e : FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ) ≃ₐ[κ] FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) (b : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) (FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ))), (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) ∧ ∀ τ, (G τ).map (algebraMap κ _) * lowM (fun v => algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v)) τ = (lowM (fun v => e (algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v))) τ).submatrix (σ τ).symm id * b τ := by
  intro κ T _ _ _ r G σ hG
  let P := MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ
  let K := FractionRing P
  let A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ := fun τ => (G τ).submatrix (σ τ) id
  have hA : ∀ τ, IsUnit (A τ).det := fun τ => by
    simp only [A]
    rw [Matrix.det_permute]
    exact (((Equiv.Perm.sign (σ τ)).isUnit).map (Int.castRingHom κ)).mul (hG τ)
  have hdec := fun τ => (CellChange.minors_iff ((A τ).map (algebraMap κ K) *
      lowM (fun v => algebraMap P K (MvPolynomial.X v)) τ)).1 (fun k hk => by
    have h := (map_ne_zero_iff (algebraMap P K) (IsFractionRing.injective _ _)).2
      (CellChange.generic_minors A hA τ k hk)
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, CellChange.lowM_map,
      Matrix.map_map] at h
    exact isUnit_iff_ne_zero.2 h)
  choose l b h0 h1 hb hu h using hdec
  obtain ⟨e, he⟩ := CellChange.exists_algEquiv_of_generates
    (fun v : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) => l v.1 v.2.1.2 v.2.1.1) (fun v => by
      set y : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → K := fun v => l v.1 v.2.1.2 v.2.1.1 with hy
      let F := IntermediateField.adjoin κ (Set.range y)
      obtain ⟨hbi, hbu, hbb⟩ := CellChange.upper_inv _ (hb v.1) (hu v.1)
      obtain ⟨x, hx⟩ := CellChange.lower_mem_range (algebraMap F K)
        ((A v.1)⁻¹.map (algebraMap κ F) * lowM (fun w => (⟨y w, IntermediateField.subset_adjoin _ _ ⟨w, rfl⟩⟩ : F)) v.1)
        (lowM (fun v => algebraMap P K (MvPolynomial.X v)) v.1) (b v.1)⁻¹
        (CellChange.lowM_upper _ _) (CellChange.lowM_diag _ _) hbi hbu (by
          rw [Matrix.map_mul, CellChange.lowM_map, Matrix.map_map]
          change (A v.1)⁻¹.map (algebraMap κ K) * lowM y v.1 = _
          rw [hy, CellChange.lowM_of_lower l v.1 (h0 _) (h1 _), ← Matrix.mul_one (l v.1), ← hbb,
            ← Matrix.mul_assoc (l v.1), ← h, Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul,
            Matrix.nonsing_inv_mul _ (hA _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul])
        v.2.1.2 v.2.1.1
      rw [CellChange.lowM_entry] at hx
      have hx' : (x : K) ∈ F := x.2
      exact hx ▸ hx')
  refine ⟨e, b, fun τ => ⟨hb τ, fun i => (hu τ i).ne_zero⟩, fun τ => ?_⟩
  simp only [he]
  rw [CellChange.lowM_of_lower l τ (h0 τ) (h1 τ)]
  ext i j
  have := congrFun (congrFun (h τ) ((σ τ).symm i)) j
  simpa [A, Matrix.mul_apply] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IdemMulMemCusp
section
noncomputable section

namespace GlobalTheory.Reg.IdemCusp

section Model

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsIdemFn (X : Data E r) (χ : Frame X.Ψ r → ℂ) : Prop :=
  (∀ x ∈ X.dom, χ x = 0 ∨ χ x = 1) ∧ DifferentiableOn ℂ χ X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, χ (rmul x b) = χ x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, χ (lact γ x) = χ x

theorem flow_const (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℝ) :
    χ (X.flow ξ (fun τ => (s τ : ℂ)) x) = χ x := by
  have hpath : Continuous fun t : ℝ => CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x :=
    ((CuspCoefficientFlow.cont_flowL X ξ).comp
      (continuous_pi fun τ => continuous_id.mul continuous_const)).clm_apply continuous_const
  have hin : ∀ t : ℝ, CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x ∈ X.dom := fun t => by
    rw [CuspCoefficientFlow.flowL_apply]
    exact (FlowCoefficientBounds.flow_real X hξ hx (fun τ => t * s τ) 0).1
  set g : ℝ → ℂ := fun t => χ (CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x) with hg
  have hcont : Continuous g := hχ.2.1.continuousOn.comp_continuous hpath hin
  have hzo : ∀ t : ℝ, g t = 0 ∨ g t = 1 := fun t => hχ.1 _ (hin t)

  have hre : Continuous fun t => (g t).re := Complex.continuous_re.comp hcont
  have hsame : g 1 = g 0 := by
    by_contra hne
    have hhalf : (1 / 2 : ℝ) ∈ Set.uIcc (g 0).re (g 1).re := by
      rcases hzo 0 with h0 | h0 <;> rcases hzo 1 with h1 | h1 <;>
        simp_all <;> norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hre.continuousOn hhalf
    rcases hzo t with h | h <;> simp [h] at ht
  have h1 : g 1 = χ (X.flow ξ (fun τ => (s τ : ℂ)) x) := by
    simp only [hg, CuspCoefficientFlow.flowL_apply, one_mul]
  have h0 : g 0 = χ x := by
    simp only [hg, CuspCoefficientFlow.flowL_apply, zero_mul, Complex.ofReal_zero]
    exact congrArg χ (EmbeddingHermitianPairs.flow_zero X ξ x)
  rw [← h1, hsame, h0]

theorem fj_mul (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ) (la : Wt X.Ψ r)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj la ξ 0 (χ * P) x = χ x * X.fj la ξ 0 P x := by
  unfold Data.fj
  split_ifs
  · simp only [Pi.mul_apply, flow_const X hχ hξ hx, mul_assoc, integral_const_mul]
    ring
  · simp
  · simp

theorem mul_mem_SS (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : χ * P ∈ X.SS la := by
  simp only [Data.SS, Set.mem_ofPred_eq] at hP ⊢
  obtain ⟨⟨⟨hd, hB, hΓ⟩, C, hC⟩, hcusp⟩ := hP
  refine ⟨⟨⟨hχ.2.1.mul hd, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, C, fun x hx => ?_⟩,
    fun ξ hξ x hx => ?_⟩
  · simp only [Pi.mul_apply]
    rw [hχ.2.2.1 x hx b hb, hB x hx b hb]
    ring
  · simp only [Pi.mul_apply]
    rw [hχ.2.2.2 γ hγ x hx, hΓ γ hγ x hx]
    ring
  · have hnorm : X.pnorm la (χ * P) x = ‖χ x‖ * X.pnorm la P x := by
      simp only [Data.pnorm, Pi.mul_apply, norm_mul, mul_assoc]
    have h1 : ‖χ x‖ ≤ 1 := by
      rcases hχ.1 x hx with h | h <;> simp [h]
    have h0 : 0 ≤ X.pnorm la P x := by
      unfold Data.pnorm
      positivity
    rw [hnorm]
    exact (mul_le_of_le_one_left h0 h1).trans (hC x hx)
  · rw [fj_mul X hχ la hξ P hx, hcusp ξ hξ x hx, mul_zero]

def mulL {ι : Type} (X : ι → Data E r) (χ : Formalism.L2.PjFree.FDSec X) :
    Formalism.L2.PjFree.FDSec X →ₗ[ℂ] Formalism.L2.PjFree.FDSec X where
  toFun P := fun k => χ k * P k
  map_add' P Q := by
    funext k x
    simp [mul_add]
  map_smul' a P := by
    funext k x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem mul_mem_holSub {ι : Type} (X : ι → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    (χ : Formalism.L2.PjFree.FDSec X) (hχ : ∀ k, IsIdemFn (X k) (χ k)) {P : Formalism.L2.PjFree.FDSec X}
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) : (fun k => χ k * P k) ∈ Formalism.L2.PjFree.holSub X la := by
  have hle : (Formalism.L2.PjFree.holSub X la).map (mulL X χ) ≤ Formalism.L2.PjFree.holSub X la := by
    unfold Formalism.L2.PjFree.holSub
    rw [Submodule.map_span_le]
    intro Q hQ
    exact Submodule.subset_span fun k => mul_mem_SS (X k) (hχ k) (la k) (hQ k)
  exact hle (Submodule.mem_map_of_mem hP)

theorem chi_zero (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  have hsq : X.χ 0 γ * X.χ 0 γ = X.χ 0 γ := by
    have h := X.χ_add 0 0 γ hγ
    rw [add_zero] at h
    exact h.symm
  obtain ⟨n, hn, hpow⟩ := X.χ_fin 0
  have hne : X.χ 0 γ ≠ 0 := by
    intro h0
    have h := hpow γ hγ
    rw [h0, zero_pow hn.ne'] at h
    exact zero_ne_one h
  exact mul_left_cancel₀ hne (by rw [hsq, mul_one])

theorem isIdemFn_of_isSec (X : Data E r) {χ : Frame X.Ψ r → ℂ} (h : X.IsSec 0 χ) (hi : χ * χ = χ) :
    IsIdemFn X χ := by
  obtain ⟨hd, hB, hΓ⟩ := h
  refine ⟨fun x _ => ?_, hd, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hx2 : χ x * χ x = χ x := congrFun hi x
    by_cases h0 : χ x = 0
    · exact Or.inl h0
    · exact Or.inr (mul_left_cancel₀ h0 (by rw [hx2, mul_one]))
  · rw [hB x hx b hb]
    simp [bchar]
  · rw [hΓ γ hγ x hx, chi_zero X hγ, one_mul]

end Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

section Read

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem rdU_mul (U : Formalism.L2.PjFree.Unf Xo c σ r) (f g : Rul Xo c) :
    Formalism.L2.PjFree.rdU U (f * g) = fun k => Formalism.L2.PjFree.rdU U f k * Formalism.L2.PjFree.rdU U g k := by
  funext k x
  simp only [Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply]
  by_cases h : x ∈ (U.X k).dom
  · simp only [dif_pos h]
    unfold Formalism.L2.PjFree.toC evR evalAt
    split_ifs with h1
    · exact map_mul _ _ _
    · exact (mul_zero _).symm
  · simp only [dif_neg h, mul_zero]

theorem laU_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) : Formalism.L2.PjFree.laU U 0 0 k = 0 := by
  unfold Formalism.L2.PjFree.laU
  funext τ j
  simp

end Read

theorem idem_mul_mem_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ χ ∈ sec Xo c 0 0, χ * χ = χ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, χ * g ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  intro E _ _ _ H Dw l Xo c r U hU χ hχ hi a n g hg
  have hχ' := hχ
  unfold sec secW at hχ'
  obtain ⟨hχn, hχw⟩ := hχ'
  unfold Formalism.L2.PjFree.cusp at hg ⊢
  obtain ⟨hgs, hgc⟩ := Submodule.mem_inf.mp hg
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  ·
    have hgs' := hgs
    unfold sec secW at hgs' ⊢
    obtain ⟨hgn, hgw⟩ := hgs'
    refine ⟨fun p q φ y z hyz => ?_, fun p t y y' hyy => ?_⟩
    · show χ q z * g q z = φ (χ p y * g p y)
      rw [hχn p q φ y z hyz, hgn p q φ y z hyz, map_mul]
    · show χ p y' * g p y' = _ * (χ p y * g p y)
      rw [hχw p t y y' hyy, hgw p t y y' hyy]
      have h1 : wchar (ex Dw 0 0) t = 1 := by simp [wchar, ex]
      rw [h1]
      ring
  ·
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hgc ⊢
    intro σ hσ
    have hsec := (hU σ hσ).2.2.2.2.1 0 0 (by unfold Formalism.L2.Pj.Dom; simp [antitone_const]) χ hχ
    rw [rdU_mul]
    refine mul_mem_holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (Formalism.L2.PjFree.rdU (U σ) χ)
      (fun k => ?_) (hgc σ hσ)
    apply isIdemFn_of_isSec
    · have hk := hsec k
      rwa [laU_zero] at hk
    · have hk := congrFun (rdU_mul (U σ) χ χ) k
      rw [hi] at hk
      exact hk.symm

end GlobalTheory.Reg.IdemCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.evR_baseChange_of_isReduced :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (S T : Type) [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c f z = φ (evR Xo c f y) := by
  intro E _ _ _ H Dw l Xo c hL a n f hf S T _ _ _ _ _ φ y z hm
  have hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y := hL.test S y
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y z hy' hm⟩
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact hL.wd f hf.1 T _ _ _ _ _ _ z hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y z hT1.choose_spec.choose_spec.choose_spec hm)
end

