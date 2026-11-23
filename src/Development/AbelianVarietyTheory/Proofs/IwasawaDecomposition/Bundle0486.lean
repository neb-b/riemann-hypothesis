module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0474
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaTameRoot

theorem exists_inertia_moves_root : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] [CharZero W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] [IsAlgClosure (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ k : ℕ, IsUnit (k : W) → ∃ (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F),
      IsLocalHom φ ∧ (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) ∧
      (∀ x ∈ O, O.valuation (σ x - x) < 1) ∧ π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ∧
      IsPrimitiveRoot (σ π / π) k := by
  intro W _ _ _ _ _ F _ _ _ ϖ hϖ k hk
  let K := FractionRing W
  letI : Algebra W F := ((algebraMap K F).comp (algebraMap W K)).toAlgebra
  haveI : IsScalarTower W K F := .of_algebraMap_eq fun _ => rfl
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := W) (by simpa using hk)
  let f : W →+* F := algebraMap W F
  have hf : Function.Injective f := (algebraMap K F).injective.comp (IsFractionRing.injective W K)
  obtain ⟨O, hO⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨h1, hloc⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff_isLocalHom f O).1 hO
  have h2 := ((GlobalTheory.localSubring_range_le_valuationSubring_iff f O).1 hO).2
  haveI : CharZero K := inferInstance
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : IsAlgClosed F := IsAlgClosure.isAlgClosed K
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (f ϖ) (Nat.pos_of_ne_zero hk0)
  haveI : NeZero (k : F) := ⟨by exact_mod_cast hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0, eq_comm, map_eq_zero_iff f hf] at hπ
    exact hϖ.ne_zero hπ
  have hmin := GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := π) hπ
  have hmin' := GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := ζ * π)
    (by rw [mul_pow, hζ.pow_eq_one, _root_.one_mul]; exact hπ)
  haveI : IsGalois K F := {}
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) F (x := ζ * π) (y := π)).1
    (hmin'.trans hmin.symm)
  change g π = ζ * π at hg

  let S := integralClosure W F
  have hc : SMulCommClass (F ≃ₐ[K] F) W F := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    simp only [AlgEquiv.smul_def, Algebra.smul_def, _root_.map_mul, AlgEquiv.commutes]⟩
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  haveI : ContinuousSMul (F ≃ₐ[K] F) S := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : F)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  let H := MulAction.stabilizer (F ≃ₐ[K] F) π
  have hH : IsClosed (H : Set (F ≃ₐ[K] F)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := K) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let φ : W →+* O := f.codRestrict O h1
  letI : Algebra W O := φ.toAlgebra
  haveI : IsScalarTower W O F := .of_algebraMap_eq fun _ => rfl
  have hSO : ∀ b : F, IsIntegral W b → b ∈ O := by
    intro b hb
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := F)).mp hb.tower_top
    rw [← hy]
    exact y.2
  let incl : S →+* O := (S.val.toRingHom).codRestrict O (fun b => hSO b b.2)
  let Q : Ideal S := (maximalIdeal O).comap incl
  have hQ : ∀ b : S, b ∈ Q ↔ O.valuation (b : F) < 1 := fun b =>
    ValuationSubring.valuation_lt_one_iff O (incl b)
  obtain ⟨a₁, ha₁, a₂, ha₂, hcong⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := W) H Q g
    (fun b hb => by
      rw [hQ]
      refine _root_.GlobalTheory.RootOfUniformiserDVR.cong_on_adjoin W F O h1 h2 ϖ hϖ k hk0 π hπ g b ?_ ((O.valuation_le_one_iff _).mpr (hSO b b.2))
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin K {π}),
        IntermediateField.mem_fixedField_iff]
      intro e he
      exact congrArg Subtype.val (hb e (he ⟨π, IntermediateField.mem_adjoin_simple_self K π⟩)))
  let σ := a₂ * g * a₁
  have hσπ : σ π = a₂ ζ * π := by
    have e1 : a₁ π = π := ha₁
    have e2 : a₂ π = π := ha₂
    simp only [σ, AlgEquiv.mul_apply, e1, hg, map_mul, e2]
  have hσS : ∀ b : F, IsIntegral W b → O.valuation (σ b - b) < 1 := fun b hb =>
    (hQ (σ • ⟨b, hb⟩ - ⟨b, hb⟩)).1 (hcong ⟨b, hb⟩)
  refine ⟨O, φ, σ.toAlgHom, π, hloc, fun w => rfl, fun x hx => ?_, hπ, ?_⟩
  · obtain ⟨s, t, hs, ht, hs1, e⟩ := _root_.GlobalTheory.DomValInt.exists_integral_quotient W F O h1 h2 x hx
    change O.valuation (σ x - x) < 1
    have hs' := hσS s hs
    have ht' := hσS t ht
    have htv : O.valuation t ≤ 1 := (O.valuation_le_one_iff _).mpr (hSO t ht)
    have hσs : O.valuation (σ s) = 1 := by
      have : σ s = s + (σ s - s) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hs1]; exact hs'), hs1]
    have key : s * σ s * (σ x - x) = s * (σ t - t) - t * (σ s - s) := by
      rw [← e, map_mul]; ring
    have hv : O.valuation (s * σ s * (σ x - x)) < 1 := by
      rw [key]
      refine Valuation.map_sub_lt _ ?_ ?_
      · rw [map_mul, hs1, _root_.one_mul]; exact ht'
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' htv) hs'
    rwa [map_mul, map_mul, hs1, hσs, _root_.one_mul, _root_.one_mul] at hv
  · change IsPrimitiveRoot (σ π / π) k
    rw [hσπ, mul_div_cancel_right₀ _ hπ0]
    exact hζ.map_of_injective a₂.injective

end GlobalTheory.InertiaTameRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMeasurePreservingRowSucc
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal Nat

namespace GlobalTheory.HuaIntegral

open GlobalTheory.FlagVolume

theorem exists_factor {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) :
    ∃ R : Matrix (Fin q) (Fin q) ℂ, R.det ≠ 0 ∧ A = Rᴴ * R := by
  open scoped MatrixOrder in
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
  refine ⟨R, fun h0 => ?_, hR⟩
  have := hA.det_pos.ne'
  rw [hR, det_mul, h0, mul_zero] at this
  exact this rfl

theorem det_conjTranspose_mul_re {q : ℕ} (R : Matrix (Fin q) (Fin q) ℂ) : (Rᴴ * R).det.re = ‖R.det‖ ^ 2 := by
  rw [det_mul, det_conjTranspose, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem det_add_row {q : ℕ} (R : Matrix (Fin q) (Fin q) ℂ) (y : Fin q → ℂ) :
    (Rᴴ * R + vecMulVec (star (vecMul y R)) (vecMul y R)).det.re = ‖R.det‖ ^ 2 * (1 + ∑ k, ‖y k‖ ^ 2) := by
  have h : Rᴴ * R + vecMulVec (star (vecMul y R)) (vecMul y R) =
      Rᴴ * (1 + replicateCol Unit (star y) * replicateRow Unit y) * R := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ R, ← replicateCol_mulVec, ← replicateRow_vecMul, ← star_vecMul, vecMulVec_eq Unit]
  have h2 : (1 + y ⬝ᵥ star y : ℂ) = ((1 + ∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) := by
    simp [dotProduct, Complex.mul_conj']
  rw [h, det_mul, det_mul, det_one_add_replicateCol_mul_replicateRow, mul_right_comm, ← det_mul, h2,
    Complex.re_mul_ofReal, det_conjTranspose_mul_re]

theorem lintegral_add_row {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (m : ℕ) :
    ∫⁻ u : Fin q → ℂ, ENNReal.ofReal (((A + vecMulVec (star u) u).det.re ^ (m + q + 1))⁻¹) =
      ENNReal.ofReal ((A.det.re ^ (m + q))⁻¹) * ENNReal.ofReal (Real.pi ^ q * m ! / (m + q)!) := by
  obtain ⟨R, hR, rfl⟩ := exists_factor hA
  have hc : Continuous fun u : Fin q → ℂ => (Rᴴ * R + vecMulVec (star u) u).det.re := by
    refine Complex.continuous_re.comp (Continuous.matrix_det (continuous_const.add ?_))
    refine continuous_matrix fun i j => ?_
    simp only [vecMulVec_apply, Pi.star_apply]
    fun_prop
  have hp : 0 < ‖R.det‖ ^ 2 := by positivity
  rw [lintegral_comp_vecMul R hR (by exact (hc.measurable.pow_const _).inv.ennreal_ofReal), det_conjTranspose_mul_re]
  simp only [det_add_row, mul_pow, mul_inv,
    ENNReal.ofReal_mul (show 0 ≤ ((‖R.det‖ ^ 2) ^ (m + q + 1))⁻¹ by positivity)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_pi_inv_pow q m one_pos, ← mul_assoc,
    ← ENNReal.ofReal_mul hp.le]
  congr 2
  · field_simp
    ring
  · simp

def rowSucc (p q : ℕ) : (Fin p × Fin q) ⊕ Fin q → Fin (p + 1) × Fin q
  | .inl a => (a.1.castSucc, a.2)
  | .inr j => (Fin.last p, j)

theorem rowSucc_bijective (p q : ℕ) : Function.Bijective (rowSucc p q) := by
  constructor
  · rintro (⟨a, b⟩ | j) (⟨a', b'⟩ | j') hh <;>
      simp_all [rowSucc, (Fin.castSucc_ne_last _).symm]
  · rintro ⟨a, b⟩
    induction a using Fin.lastCases with
    | last => exact ⟨.inr b, rfl⟩
    | cast a => exact ⟨.inl (a, b), rfl⟩

theorem exists_measurePreserving_rowSucc (p q : ℕ) :
    ∃ Φ : (Fin p × Fin q → ℂ) × (Fin q → ℂ) → (Fin (p + 1) × Fin q → ℂ),
      MeasurePreserving Φ ∧ ∀ v u, (∀ a b, Φ (v, u) (a.castSucc, b) = v (a, b)) ∧
        ∀ j, Φ (v, u) (Fin.last p, j) = u j := by
  let e := Equiv.ofBijective _ (rowSucc_bijective p q)
  refine ⟨_, (volume_measurePreserving_piCongrLeft (fun _ ↦ ℂ) e).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ ↦ ℂ)), fun u b ↦
    ⟨fun a c ↦ ?_, fun j ↦ ?_⟩⟩
  · exact MeasurableEquiv.piCongrLeft_apply_apply e _ (.inl (a, c))
  · exact MeasurableEquiv.piCongrLeft_apply_apply e _ (.inr j)

theorem lintegral_det_inv_pow (m q p : ℕ) :
    ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal
        (((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ (m + p + q))⁻¹) =
      ENNReal.ofReal (∏ i ∈ Finset.range p, (Real.pi ^ q * (m + i)! / (m + i + q)!)) := by
  have hm : ∀ p s : ℕ, Measurable fun v : Fin p × Fin q → ℂ => ENNReal.ofReal
      (((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ s)⁻¹) := by
    intro p s
    have hc : Continuous fun v : Fin p × Fin q → ℂ => (Matrix.of fun a b => v (a, b)) :=
      continuous_matrix fun i j => by simp only [of_apply]; fun_prop
    exact ((Complex.continuous_re.comp
      (continuous_const.add (hc.matrix_conjTranspose.matrix_mul hc)).matrix_det).measurable.pow_const
        s).inv.ennreal_ofReal
  induction p with
  | zero => simp [volume_pi]
  | succ p ih =>
    obtain ⟨Φ, hΦ, hΦ'⟩ := exists_measurePreserving_rowSucc p q
    rw [← hΦ.lintegral_comp (hm _ _), Measure.volume_eq_prod,
      lintegral_prod _ (by exact ((hm _ _).comp hΦ.measurable).aemeasurable)]
    have h : ∀ (v : Fin p × Fin q → ℂ) (u : Fin q → ℂ),
        1 + (Matrix.of fun a b => Φ (v, u) (a, b))ᴴ * (Matrix.of fun a b => Φ (v, u) (a, b)) =
        (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))) + vecMulVec (star u) u := by
      intro v u
      rw [add_assoc]
      congr 1
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc, (hΦ' v u).1, (hΦ' v u).2, vecMulVec_apply]
    have hpos : ∀ v : Fin p × Fin q → ℂ,
        (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).PosDef := fun v =>
      PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self _)
    simp only [h, show m + (p + 1) + q = (m + p) + q + 1 by ring, lintegral_add_row (hpos _)]
    rw [lintegral_mul_const _ (hm _ _), ih, Finset.prod_range_succ, ENNReal.ofReal_mul (by positivity)]

theorem dual_mass : ∀ p q : ℕ, ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (grassConst p q)⁻¹ := by
  intro p q
  have h := lintegral_det_inv_pow 0 q p
  simp only [zero_add] at h
  simp only [_root_.zpow_neg, _root_.zpow_natCast]
  rw [h, grassConst, inv_div, div_eq_mul_inv, ← Finset.prod_inv_distrib, mul_comm p q, pow_mul,
    ← Finset.card_range p, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [inv_div, add_comm q i, mul_div_assoc]

end GlobalTheory.HuaIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMoebZero
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx.FrameOnto

theorem exists_congr_one {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.PosDef) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ Sᴴ * M * S = 1 := by
  classical
  set U : Matrix n n ℂ := (hM.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hD : star U * M * U = diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) := by
    have h := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    exact h
  set c : n → ℂ := fun i => (RCLike.ofReal ((Real.sqrt (hM.1.eigenvalues i))⁻¹) : ℂ) with hc
  refine ⟨U * diagonal c, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine IsUnit.mul (isUnit_det_of_left_inverse (Unitary.coe_star_mul_self _)) ?_
    refine Ne.isUnit (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    exact RCLike.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr (hM.eigenvalues_pos i)))
  · have hs : (U * diagonal c)ᴴ * M * (U * diagonal c) = diagonal (star c) * (star U * M * U) * diagonal c := by
      rw [conjTranspose_mul, diagonal_conjTranspose, ← star_eq_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [hs, hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hl := hM.eigenvalues_pos i
    have hr : (Real.sqrt (hM.1.eigenvalues i))⁻¹ * hM.1.eigenvalues i * (Real.sqrt (hM.1.eigenvalues i))⁻¹ = 1 := by
      have h0 : Real.sqrt (hM.1.eigenvalues i) ≠ 0 := Real.sqrt_ne_zero'.mpr hl
      have h2 := Real.mul_self_sqrt hl.le
      field_simp
      linarith
    simp only [hc, Pi.star_apply, Function.comp_apply, RCLike.star_def, RCLike.conj_ofReal]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, hr, RCLike.ofReal_one]

private lemma posDef_one_sub_mul_conjTranspose_of_posDef {p q : ℕ} {z : Matrix (Fin p) (Fin q) ℂ} (hz : (1 - zᴴ * z).PosDef) :
    (1 - z * zᴴ).PosDef := by
  have hsd : (1 - z * zᴴ).PosSemidef := by
    haveI : Invertible (1 : Matrix (Fin p) (Fin p) ℂ) := invertibleOne
    haveI : Invertible (1 : Matrix (Fin q) (Fin q) ℂ) := invertibleOne
    have h1 : (fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) z zᴴ 1).PosSemidef := by
      rw [PosDef.fromBlocks₁₁ (A := (1 : Matrix (Fin p) (Fin p) ℂ)) z 1 PosDef.one]
      simpa using hz.posSemidef
    rw [PosDef.fromBlocks₂₂ 1 z (D := (1 : Matrix (Fin q) (Fin q) ℂ)) PosDef.one] at h1
    simpa using h1
  rw [hsd.posDef_iff_det_ne_zero]
  have hu : IsUnit (1 - zᴴ * z).det := (isUnit_iff_isUnit_det _).mp hz.isUnit
  refine (isUnit_det_of_right_inverse (B := 1 + z * (1 - zᴴ * z)⁻¹ * zᴴ) ?_).ne_zero
  have h := mul_nonsing_inv _ hu
  calc (1 - z * zᴴ) * (1 + z * (1 - zᴴ * z)⁻¹ * zᴴ)
      = 1 - z * zᴴ + z * ((1 - zᴴ * z) * (1 - zᴴ * z)⁻¹) * zᴴ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
          Matrix.one_mul, Matrix.mul_assoc]
    _ = 1 := by
        rw [h, Matrix.mul_one]
        abel

theorem exists_moeb_zero {p q : ℕ} {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    ∃ g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, gᴴ * Jpq p q * g = Jpq p q ∧ moeb g 0 = z := by
  classical
  have hQ : (1 - zᴴ * z).PosDef := hz
  obtain ⟨S, hSu, hS⟩ := exists_congr_one hQ
  obtain ⟨T, hTu, hT⟩ := exists_congr_one (posDef_one_sub_mul_conjTranspose_of_posDef hQ)
  have hJ : Jpq p q = fromBlocks 1 0 0 (-1) := rfl
  refine ⟨fromBlocks T (z * S) (zᴴ * T) S, ?_, ?_⟩
  · rw [hJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · refine Eq.trans ?_ hT
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · refine Eq.trans ?_ (congrArg Neg.neg hS)
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
  · unfold moeb
    rw [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
      Matrix.mul_zero, Matrix.mul_zero, zero_add, zero_add, Matrix.mul_assoc, mul_nonsing_inv _ hSu,
      Matrix.mul_one]

private lemma gram_eq_upper_bounds {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma coe_idx_symm_inl {r j : ℕ} (hj : j ≤ r) (a : Fin j) :
    (((idx hj).symm (Sum.inl a) : Fin r) : ℕ) = r - j + a := by
  unfold idx
  simp

private lemma coe_idx_symm_inr {r j : ℕ} (hj : j ≤ r) (b : Fin (r - j)) :
    (((idx hj).symm (Sum.inr b) : Fin r) : ℕ) = b := by
  unfold idx
  simp

private lemma reindex_diagonal_sgn_eq_neg_Jpq {r j : ℕ} (hj : j ≤ r) :
    reindex (idx hj) (idx hj) (diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (r - j) a : ℝ) : ℂ)) =
      -Jpq j (r - j) := by
  have hJ : Jpq j (r - j) = fromBlocks 1 0 0 (-1) := rfl
  rw [hJ]
  ext (a | a) (b | b) <;>
    simp [reindex_apply, diagonal_apply, coe_idx_symm_inl, coe_idx_symm_inr, ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.one_apply] <;>
    split_ifs <;> simp

theorem frame_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z ∈ DomI Tau j (r - j), ∃ x ∈ X.dom, domPt X hj κ x = z := by
  intro E _ _ _ r j X hj Tau _ κ hp z hz
  classical
  have hz' : ∀ t, z t ∈ hcDom j (r - j) := hz
  choose g hg hgz using fun t => exists_moeb_zero (hz' t)
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) with hD
  have hDJ : reindex (idx hj) (idx hj) D = -Jpq j (r - j) := by
    rw [hD, hp]
    exact reindex_diagonal_sgn_eq_neg_Jpq hj
  have hD' : D = reindex (idx hj).symm (idx hj).symm (-Jpq j (r - j)) := by
    rw [← hDJ]
    simp [reindex_apply, Matrix.submatrix_submatrix]
  have hDT : Dᵀ = D := by
    rw [hD]
    exact diagonal_transpose _
  have hx0 : ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ).det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ) = D := fun τ => (X.signature τ).choose_spec
  have hgy : ∀ t, (reindex (idx hj).symm (idx hj).symm (g t))ᴴ * D * reindex (idx hj).symm (idx hj).symm (g t) = D := by
    intro t
    rw [hD']
    simp only [reindex_apply, Equiv.symm_symm, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [Matrix.mul_neg, Matrix.neg_mul, hg t]
  have hT : ∀ y : Matrix (Fin r) (Fin r) ℂ,
      yᵀ * D * y.map (starRingEnd ℂ) = (yᴴ * Dᵀ * y)ᵀ := by
    intro y
    have h1 : (yᴴ)ᵀ = y.map (starRingEnd ℂ) := by
      ext a b
      simp
    rw [transpose_mul, transpose_mul, transpose_transpose, h1, Matrix.mul_assoc]
  let x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := fun τ =>
    (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)) : Matrix (Fin r) (Fin r) ℂ)
  have hm : ∀ τ, ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)) :=
    fun τ => rfl
  have hgram : ∀ τ : X.Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = D := by
    intro τ
    have h0 := (hx0 τ).2
    rw [hm, gram_eq_upper_bounds]
    rw [gram_eq_upper_bounds] at h0
    have hre : (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)))ᵀ * X.Gm.map τ.1 *
        (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ))).map (starRingEnd ℂ) =
        (reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)))ᵀ * ((ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ)ᵀ * X.Gm.map τ.1 *
          (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ).map (starRingEnd ℂ)) *
          (reindex (idx hj).symm (idx hj).symm (g (κ.symm τ))).map (starRingEnd ℂ) := by
      rw [transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    rw [hre, h0, hT, hDT, hgy, hDT]
  refine ⟨x, ?_, ?_⟩
  · show ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re
    intro τ
    have hsg : ∀ a : ℕ, ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0 := by
      intro a
      unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
      split_ifs <;> norm_num
    refine ⟨?_, ?_⟩
    · intro hdet
      have h := congrArg Matrix.det (hgram τ)
      rw [gram_eq_upper_bounds, det_mul, det_mul, det_transpose, hdet, zero_mul, zero_mul, hD,
        det_diagonal] at h
      exact (Finset.prod_ne_zero_iff.mpr fun (a : Fin r) _ => Complex.ofReal_ne_zero.mpr (hsg a)) h.symm
    · intro i
      have hl : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i = ((ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ) := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.dmin ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.psgn
        rw [hgram τ, hD, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal]
        simp only [Function.comp_apply, Fin.coe_castLE]
        rw [Fin.prod_univ_eq_prod_range (fun a => ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) (i : ℕ),
          Complex.ofReal_prod]
      have hps : ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i ≠ 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.psgn
        exact Finset.prod_ne_zero_iff.mpr fun a _ => hsg a
      rw [hl, Complex.ofReal_re]
      exact mul_self_pos.mpr hps
  · funext t
    have hf : frameCo X hj x (κ t) = g t := by
      unfold frameCo
      rw [hm, ← Matrix.mul_assoc, nonsing_inv_mul _ (hx0 (κ t)).1.isUnit, Matrix.one_mul,
        Equiv.symm_apply_apply]
      simp [reindex_apply, Matrix.submatrix_submatrix]
    show moeb (frameCo X hj x (κ t)) 0 = z t
    rw [hf, hgz t]

end GlobalTheory.TrueCx.FrameOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionMap_uniformisation_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∃ f : QkPt P.D.toPre F k → (TF (R := R) F ⟶ t.G),
      (∀ q v, GlobalTheory.FlatTors.IsImage P F k q v ↔ v = (f q).left) ∧ (∀ q, f q ^ k = 1) ∧ (∀ x, x ^ k = 1 → ∃ q, f q = x) ∧
      (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧
      (∀ p p' τ, p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        GlobalTheory.UU.CubWeil t.cub k (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y)))) ∧
      ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
  first | exact @GlobalTheory.GenTors.exists_torsMap_generic | exact GlobalTheory.GenTors.exists_torsMap_generic | (intros; apply GlobalTheory.GenTors.exists_torsMap_generic <;> assumption)
end

