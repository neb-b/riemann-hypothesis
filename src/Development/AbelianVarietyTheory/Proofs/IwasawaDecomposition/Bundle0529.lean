module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinatePolynomialBound
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.PolyBd

section Gen

variable {P : Type} {A : P → ℝ}

def PB (A : P → ℝ) (f : P → ℂ) : Prop := ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ p, ‖f p‖ ≤ C * A p ^ k

theorem PB.const (a : ℂ) : PB A fun _ => a := ⟨‖a‖, 0, norm_nonneg _, fun _ => by simp⟩

theorem PB.of_le {f : P → ℂ} (h : ∀ p, ‖f p‖ ≤ A p) : PB A f := ⟨1, 1, zero_le_one, fun p => by simpa using h p⟩

theorem PB.mul {f g : P → ℂ} (hf : PB A f) (hg : PB A g) : PB A fun p => f p * g p := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, n, hD, h'⟩ := hg
  refine ⟨C * D, k + n, mul_nonneg hC hD, fun p => ?_⟩
  rw [norm_mul, pow_add]
  calc _ ≤ (C * A p ^ k) * (D * A p ^ n) :=
        mul_le_mul (h p) (h' p) (norm_nonneg _) ((norm_nonneg _).trans (h p))
    _ = _ := by ring

theorem PB.both (hA : ∀ p, 1 ≤ A p) {f g : P → ℂ} (hf : PB A f) (hg : PB A g) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ p, ‖f p‖ ≤ C * A p ^ k ∧ ‖g p‖ ≤ C * A p ^ k := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, n, hD, h'⟩ := hg
  refine ⟨max C D, max k n, le_max_of_le_left hC, fun p => ⟨(h p).trans ?_, (h' p).trans ?_⟩⟩
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ (hA p) (le_max_left _ _))
      (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)
  · exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ (hA p) (le_max_right _ _))
      (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)

theorem PB.add (hA : ∀ p, 1 ≤ A p) {f g : P → ℂ} (hf : PB A f) (hg : PB A g) : PB A fun p => f p + g p := by
  obtain ⟨C, k, hC, h⟩ := hf.both hA hg
  refine ⟨2 * C, k, by positivity, fun p => (norm_add_le _ _).trans ?_⟩
  linarith [(h p).1, (h p).2]

theorem PB.sum (hA : ∀ p, 1 ≤ A p) {I : Type} (s : Finset I) {f : I → P → ℂ} (hf : ∀ i, PB A (f i)) :
    PB A fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PB.const (A := A) 0
  | insert a s ha ih => simpa [Finset.sum_insert ha] using (hf a).add hA ih

theorem PB.prod {I : Type} (s : Finset I) {f : I → P → ℂ} (hf : ∀ i, PB A (f i)) :
    PB A fun p => ∏ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PB.const (A := A) 1
  | insert a s ha ih => simpa [Finset.prod_insert ha] using (hf a).mul ih

theorem PB.det (hA : ∀ p, 1 ≤ A p) {I : Type} [Fintype I] [DecidableEq I] {M : P → Matrix I I ℂ}
    (hM : ∀ i j, PB A fun p => M p i j) : PB A fun p => (M p).det := by
  simp only [Matrix.det_apply']
  exact PB.sum hA _ fun s => (PB.const _).mul (PB.prod _ fun i => hM _ _)

theorem PB.matMul (hA : ∀ p, 1 ≤ A p) {a b d : Type} [Fintype b] {M : P → Matrix a b ℂ} {N : P → Matrix b d ℂ}
    (hM : ∀ i j, PB A fun p => M p i j) (hN : ∀ i j, PB A fun p => N p i j) (i : a) (j : d) :
    PB A fun p => (M p * N p) i j := by
  simp only [Matrix.mul_apply]
  exact PB.sum hA _ fun k => (hM _ _).mul (hN _ _)

theorem horVal_bound (hA : ∀ p, 1 ≤ A p) {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {K : P → Matrix (m ⊕ n) m ℂ} {C : P → Matrix n (m ⊕ n) ℂ} {R : P → Matrix m (m ⊕ n) ℂ}
    {S : P → Matrix (m ⊕ n) n ℂ} (h : ∀ p, C p * K p = 0) (hR : ∀ p, R p * K p = 1) (hS : ∀ p, C p * S p = 1)
    (bK : ∀ i j, PB A fun p => K p i j) (bC : ∀ i j, PB A fun p => C p i j) (bR : ∀ i j, PB A fun p => R p i j)
    (bS : ∀ i j, PB A fun p => S p i j) :
    ∃ (D : ℝ) (k : ℕ), 0 ≤ D ∧ ∀ p, ‖horVal (K p) (C p)‖ ≤ D * A p ^ k ∧ ‖(horVal (K p) (C p))⁻¹‖ ≤ D * A p ^ k := by
  have h1 : PB A fun p => horVal (K p) (C p) := by
    simp only [fun p => horVal_eq (h p) (hR p) (hS p)]
    refine PB.det hA fun i j => ?_
    rcases i with i | i
    · simpa using bR i j
    · simpa using bC i j
  have h2 : PB A fun p => (horVal (K p) (C p))⁻¹ := by
    simp only [fun p => inv_eq_of_mul_eq_one_right (horVal_mul (h p) (hR p) (hS p))]
    refine PB.det hA fun i j => ?_
    rcases j with j | j
    · simpa using bK i j
    · simpa using bS i j
  exact h1.both hA h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Di : Datum H}

theorem exists_comb {J : Type} [Fintype J] (x : J → Di.La) (f : (E →+* ℂ) → (E →+* ℂ)) (v : Di.La)
    (hv : ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x)) :
    ∃ B : (E →+* ℂ) → J → ℂ, ∀ Q : Di.La →+ (Letter Dw → ℂ),
      (∀ (a : 𝓞 E) v (z : Letter Dw), Q (a • v) z = f z.1 (a : E) * Q v z) →
      ∀ z : Letter Dw, Q v z = ∑ k, B z.1 k * Q (x k) z := by
  obtain ⟨n, hn, hv⟩ := hv
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  refine ⟨fun t k => (n : ℂ)⁻¹ * f t (a k : E), fun Q hQ z => ?_⟩
  have h := congrArg (fun w => Q w z) ha
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_apply, hQ, map_nsmul, Pi.smul_apply, nsmul_eq_mul] at h
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [_root_.mul_assoc]
  rw [← Finset.mul_sum, h, inv_mul_cancel_left₀ hn']

theorem perVal_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La)
    (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (g r : ℕ) (T₀ : Di.La ≃+ (Fin r → ℤ)) (ρ : Fin g → Fin r → ℂ)
    (hx : IsPerBasis Di x hm) : ∃ (C : ℝ) (k : ℕ), ∀ (Q : Di.La →+ (Letter Dw → ℂ))
      (W : Matrix (Letter Dw) (Fin g) ℂ) (Wi : Matrix (Fin g) (Letter Dw) ℂ) (lam : Fin r → Fin g → ℂ) (A : ℝ),
      GoodPer c σ τ x hm Q → W * Wi = 1 → Wi * W = 1 → (∀ v, ∑ z, Q v z • W z = ∑ m, T₀ v m • lam m) →
      (∀ j, ∑ m, ρ j m • lam m = Pi.single j 1) → 1 ≤ A → (∀ z j, ‖W z j‖ ≤ A) → (∀ j z, ‖Wi j z‖ ≤ A) →
      (∀ m j, ‖lam m j‖ ≤ A) → ‖perVal c σ τ x hm Q‖ ≤ C * A ^ k ∧ ‖(perVal c σ τ x hm Q)⁻¹‖ ≤ C * A ^ k := by
  let P : Type := {p : (Di.La →+ (Letter Dw → ℂ)) × Matrix (Letter Dw) (Fin g) ℂ × Matrix (Fin g) (Letter Dw) ℂ ×
      (Fin r → Fin g → ℂ) × ℝ // GoodPer c σ τ x hm p.1 ∧ p.2.1 * p.2.2.1 = 1 ∧
      (∀ v, ∑ z, p.1 v z • p.2.1 z = ∑ m, T₀ v m • p.2.2.2.1 m) ∧
      (∀ j, ∑ m, ρ j m • p.2.2.2.1 m = Pi.single j 1) ∧ 1 ≤ p.2.2.2.2 ∧ (∀ z j, ‖p.2.1 z j‖ ≤ p.2.2.2.2) ∧
      (∀ j z, ‖p.2.2.1 j z‖ ≤ p.2.2.2.2) ∧ (∀ m j, ‖p.2.2.2.1 m j‖ ≤ p.2.2.2.2)}
  let A : P → ℝ := fun p => p.1.2.2.2.2
  have hA : ∀ p, 1 ≤ A p := fun p => p.2.2.2.2.2.1
  choose B hB using fun m : Fin r =>
    exists_comb (Dw := Dw) x (Formalism.L2.PjFree.relab c σ) (T₀.symm (Pi.single m 1)) (hx.2.1 _)
  have hQ : ∀ (p : P) v z, p.1.1 v z = ∑ j, (∑ m, (T₀ v m : ℂ) * p.1.2.2.2.1 m j) * p.1.2.2.1 j z := by
    rintro ⟨⟨Q, W, Wi, lam, a⟩, -, h1, h2, -⟩ v z
    dsimp only at h1 h2 ⊢
    have h3 : ∀ j, ∑ m, (T₀ v m : ℂ) * lam m j = (Q v ᵥ* W) j := fun j => by
      have := congrFun (h2 v) j
      simp only [Finset.sum_apply, Pi.smul_apply] at this
      simp only [smul_eq_mul, zsmul_eq_mul] at this
      rw [← this]; rfl
    simp only [h3]
    have : Q v = (Q v ᵥ* W) ᵥ* Wi := by rw [Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
    exact congrFun this z
  have bQ : ∀ v z, PB A fun p => p.1.1 v z := fun v z => by
    simp only [hQ]
    exact PB.sum hA _ fun j => (PB.sum hA _ fun m => (PB.const _).mul (PB.of_le fun p => p.2.2.2.2.2.2.2.2 m j)).mul
      (PB.of_le fun p => p.2.2.2.2.2.2.2.1 j z)
  let S : ∀ t : E →+* ℂ, P → Matrix (Idx Dw τ) (Fin (Dw.mult t)) ℂ := fun t p =>
    Matrix.of fun k i => ∑ j, p.1.2.1 ⟨t, i⟩ j * ∑ m, ρ j m * B m t k
  have bS : ∀ t k i, PB A fun p => S t p k i := fun t k i => by
    simp only [S, Matrix.of_apply]
    exact PB.sum hA _ fun j => (PB.of_le fun p => p.2.2.2.2.2.2.1 _ j).mul (PB.const _)
  have hS : ∀ t (p : P), perMat x p.1.1 t * S t p = 1 := by
    intro t p
    have h4 : ∀ j z, ∑ m, ρ j m * p.1.1 (T₀.symm (Pi.single m 1)) z = p.1.2.2.1 j z := by
      intro j z
      have h5 : ∀ j', ∑ m, ρ j m * p.1.2.2.2.1 m j' = (Pi.single j (1 : ℂ) : Fin g → ℂ) j' := fun j' => by
        simpa [Finset.sum_apply] using congrFun (p.2.2.2.2.1 j) j'
      simp only [hQ, AddEquiv.apply_symm_apply, Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul,
        _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← _root_.mul_assoc, ← Finset.sum_mul, h5, Pi.single_apply, ite_mul,
        _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ext i i'
    have h6 := congrFun (congrFun p.2.2.1 ⟨t, i'⟩) ⟨t, i⟩
    have h7 : (1 : Matrix (Letter Dw) (Letter Dw) ℂ) ⟨t, i'⟩ ⟨t, i⟩ =
        (1 : Matrix (Fin (Dw.mult t)) (Fin (Dw.mult t)) ℂ) i i' := by
      simp [Matrix.one_apply, eq_comm]
    rw [← h7, ← h6]
    simp only [Matrix.mul_apply, ← h4, hB _ _ p.2.1.1, perMat, S, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdet : IsUnit ((hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ).det := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero _).2 hx.2.2.2).isUnit
  obtain ⟨D, k, -, h⟩ := horVal_bound hA (K := fun p => kerMat c σ τ x hm p.1.1) (C := fun p => perMat x p.1.1 τ)
    (R := fun p => (S (conjEmb τ) p)ᵀ * (hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ) (S := S τ)
    (fun p => p.2.1.2.1)
    (fun p => by
      rw [kerMat, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet, ← Matrix.transpose_mul, hS,
        Matrix.transpose_one])
    (hS τ) (PB.matMul hA (fun _ _ => PB.const _) fun i j => bQ _ _) (fun i j => bQ _ _)
    (PB.matMul hA (fun i j => bS _ _ _) fun _ _ => PB.const _) (bS τ)
  exact ⟨D, k, fun Q W Wi lam a h1 h2 _ h3 h4 h5 h6 h7 h8 =>
    h ⟨⟨Q, W, Wi, lam, a⟩, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

end GlobalTheory.ShFam.Hor.PolyBd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdlAlongEqIdealAlong
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem stalkId_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) (y : Y) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.ofIdealTop K) y = K.map (Y.presheaf.germ ⊤ y trivial).hom := by
  rw [ds_stalkId_eq_map _ ⟨⊤, isAffineOpen_top Y⟩ y trivial, Scheme.IdealSheafData.ofIdealTop_ideal,
    Ideal.map_map, ← CommRingCat.hom_comp]
  congr 2
  exact Y.presheaf.germ_res (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) y (by trivial)

theorem ideal_top_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop K).ideal ⟨⊤, isAffineOpen_top Y⟩ = K := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  have : Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [← Y.presheaf.map_id]; rfl
  rw [this]
  simp

theorem comap_eq_ofIdealTop (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    J.comap χ = Scheme.IdealSheafData.ofIdealTop ((J.ideal U).map (χ.appLE U.1 ⊤ hle).hom) := by
  refine (GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm
  have hz : χ z ∈ U.1 := hle trivial
  rw [stalkId_ofIdealTop, ds_stalkId_eq_map J U _ hz, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]
  congr 3
  exact (Sp R).presheaf.germ_res (homOfLE hle) z (by trivial)

theorem idlAlong_eq_idealAlong (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) : idlAlong J χ = idealAlong J χ := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  unfold idlAlong idealAlong
  rw [comap_eq_ofIdealTop X J R χ ⟨U, hU⟩ hle, ideal_top_ofIdealTop, ds_stalkId_eq_map J ⟨U, hU⟩ _ hx,
    Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

section Models

variable {F : Type} [Field F] [NumberField F]

abbrev PtFn (Y : Var F) : Type := ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ

end Models

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def IsTanBasis {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ} (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (e i)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Sp (DualNumber S) ⟶ t.G.left),
    IsTanAtG t (spMap φ ≫ x) w →
      ∃! a : Fin g → S, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) a w

def IsIndep {R : Type} [CommRing R] (x : Sp R ⟶ X) {m : ℕ} (u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def minor {R : Type} [CommRing R] {m g k : ℕ} (a : Fin m → Fin g → R) (hk : k ≤ m) (s : Fin k → Fin g) : R :=
  (Matrix.of fun l i => a (Fin.castLE hk l) (s i)).det

def DlogIs {O : Type} [CommRing O] {x : Sp O ⟶ X} (p n : ℕ) (c : TorsChar t x (p ^ n)) {g : ℕ}
    (e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)) (h : Fin g → O) : Prop :=
  ∀ (a : Fin g → O) (v : Sp (DualNumber O) ⟶ t.G.left), IsCombAtG t x e a v →
    ∀ w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ x) ⟶ t.G,
      w.left = spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}))) ≫ v →
        (c.χ _ w : DualNumber (O ⧸ Ideal.span {(p : O) ^ n})).snd =
          Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) (∑ i, h i * a i)

def Thru {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (u : Sp B ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : R →+* S) (w : Sp S ⟶ t.G.left) : Prop :=
  ∃ β : B →+* S, β.comp (algebraMap R B) = φ ∧ spMap β ≫ u = w

structure IsFinPart {R : Type} [CommRing R] (x : Sp R ⟶ X) (q : ℕ) {B : Type} [CommRing B] [Algebra R B]
    (u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G) : Prop where
  finite : Module.Finite R B
  free : Module.Free R B
  tors : u ^ q = 1
  mono : ∀ (S : Type) [CommRing S] (β β' : B →+* S), β.comp (algebraMap R B) = β'.comp (algebraMap R B) →
    spMap β ≫ u.left = spMap β' ≫ u.left → β = β'
  isOpen : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Over.mk (spMap φ ≫ x) ⟶ t.G), w ^ q = 1 →
    (∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      Thru t u.left ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ w.left)) → Thru t u.left φ w.left
  one : ∀ (S : Type) [CommRing S] (φ : R →+* S), Thru t u.left φ (1 : Over.mk (spMap φ ≫ x) ⟶ t.G).left
  mul : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G),
    Thru t u.left φ w.left → Thru t u.left φ w'.left → Thru t u.left φ (w * w').left
  sect : ∀ (k : Type) [Field k] (β : B →+* k), ∃ σ : B →ₐ[R] R, β = (β.comp (algebraMap R B)).comp σ.toRingHom
  inj : ∀ b : B, (∀ σ : B →ₐ[R] R, σ b = 0) → b = 0

variable {F : Type} [Field F] [NumberField F] {Y : Var F}


end Tangent

end GlobalTheory.LineNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open TopologicalSpace
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.SharedLaws

section Top

variable {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

theorem exists_finite_generic {F : Set X} (hF : IsClosed F) :
    ∃ G : Set X, G.Finite ∧ G ⊆ F ∧ ∀ x ∈ F, ∃ g ∈ G, g ⤳ x := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  choose η hη using fun t (ht : t ∈ S) => QuasiSober.sober (hi t ht) (hc t ht)
  haveI := hS.to_subtype
  refine ⟨Set.range fun t : S => η t.1 t.2, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨t.1, t.2, (hη t.1 t.2).mem⟩
  · rintro x ⟨t, ht, hx⟩
    exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, (hη t ht).specializes hx⟩

theorem mem_of_maximal {x : X} (hx : ∀ x' : X, x' ⤳ x → x' = x) {U : Set X} (hU : IsOpen U) (hd : Dense U) :
    x ∈ U := by
  obtain ⟨G, hG, -, h⟩ := exists_finite_generic (isClosed_univ (X := X))
  have hC : IsClosed (⋃ g ∈ G \ {x}, closure ({g} : Set X)) :=
    (hG.subset Set.diff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  obtain ⟨y, hy, hyU⟩ := hd.inter_open_nonempty _ hC.isOpen_compl ⟨x, fun hm => by
    obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 hm
    exact hg.2 (hx g (specializes_iff_mem_closure.2 hgx))⟩
  obtain ⟨g, hg, hgy⟩ := h y trivial
  by_cases e : g = x
  · exact (e ▸ hgy).mem_open hU hyU
  · exact absurd (Set.mem_iUnion₂.2 ⟨g, ⟨hg, e⟩, specializes_iff_mem_closure.1 hgy⟩) hy

end Top

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_nonunits_V {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem isProper_toroidalModel_structureMap (Z : Mdl Y i₀) : IsProper Z.s := by
  have := isProper_str (Z.i.c.V W) Z.n
  unfold Pre.s
  infer_instance

theorem noetherianSpace (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : NoetherianSpace Z.X := by
  haveI := Z.i.c.fin
  haveI : NumberField Z.i.c.F := {}
  haveI := (isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp
    (mem_nonunits_V Z.i.c hp hW)).1
  haveI := isProper_toroidalModel_structureMap Z
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  haveI : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  haveI : IsNoetherian Z.X := {}
  infer_instance

theorem abP_of_isGenP (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (x : Z.X) (hx : Z.isGenP x) :
    Z.abP x := by
  haveI := noetherianSpace hp hW Z
  have ho : IsOpen Z.opn := by
    rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.2
  obtain ⟨z, hz⟩ := mem_of_maximal hx ho Z.dense
  have : (Y Z.i).jQ z ∈ pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype) ⁻¹' abLocus (Y Z.i).t.G := by
    rw [(Y Z.i).ab_gen]
    exact ⟨z, rfl⟩
  unfold Mdl.abP
  rw [← hz]
  exact this

end Free

end GlobalTheory.LocM.SharedLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KTrivAndPolAtTensAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.PolFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
  {t : SAB H S} {K : Type} [Field K] {x : Sp K ⟶ S} {u : SAB H (Sp K)}

theorem exists_to_fibre (m : SABMap u t x) :
    ∃ φ : u.G.left ⟶ ((Over.pullback x).obj t.G).left, IsGrpPullback u.G ((Over.pullback x).obj t.G) (𝟙 _) φ ∧
      LBIso u.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull φ) := by
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x) (m.cart.congr (Category.id_comp _).symm rfl)
    (isGrpPullback_pullback t.G x) t.PP.isLB hM u.PP.isLB (GlobalTheory.Ex.UnifModel.iso_of_map m)
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩
  exact ⟨φ, hφ, e⟩

theorem exists_of_fibre (m : SABMap u t x) :
    ∃ φ : ((Over.pullback x).obj t.G).left ⟶ u.G.left, IsGrpPullback ((Over.pullback x).obj t.G) u.G (𝟙 _) φ ∧
      LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (u.PP.L.pull φ) := by
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) m.cart t.PP.isLB u.PP.isLB hM
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩ (GlobalTheory.Ex.UnifModel.iso_of_map m)
  exact ⟨φ, hφ, e⟩

theorem ample_kTriv_of_polAt (m : SABMap u t x) (hp : GlobalTheory.LN.PolAt t x) :
    RelAmple u.G u.PP.L ∧ KTriv u.G u.PP.L := by
  obtain ⟨φ, hφ, e⟩ := exists_to_fibre m
  exact amplePt _ _ (𝟙 _) _ _ φ hφ _ _ (LB.isLB_pull t.PP.isLB _) u.PP.isLB e hp.2.1 hp.2.2

theorem polAt_of_map (m : SABMap u t x) (hp : IsProper (pullback.snd t.G.hom x)) (hA : RelAmple u.G u.PP.L)
    (hK : KTriv u.G u.PP.L) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨φ, hφ, e⟩ := exists_of_fibre m
  have h := amplePt _ _ (𝟙 _) _ _ φ hφ _ _ u.PP.isLB (LB.isLB_pull t.PP.isLB _) e hA hK
  exact ⟨hp, h.1, h.2⟩

end GlobalTheory.LocM.PolFibre
end
end

