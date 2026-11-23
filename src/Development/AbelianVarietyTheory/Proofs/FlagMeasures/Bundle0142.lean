module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.StatementU
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankAndDetOfRealBasisSkewPart
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RealFormBasis

variable {n : ℕ} (ε : Fin n → Bool)

private theorem Jm_mul_self_eq_one' {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTransposeFlagMeasures {n : ℕ} (ε : Fin n → Bool) :
    (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem Jm_mul_Jm_mul' {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_mul_self_eq_one', Matrix.one_mul]

theorem inG_iff_adj (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε X ↔ Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε = -X := by
  unfold Formalism.REAL.inG
  constructor
  · intro h

    have h' := congrArg (fun M => Formalism.REAL.Jm ε * M) h
    simp only [Matrix.mul_add, Matrix.mul_zero, Jm_mul_Jm_mul'] at h'
    rw [← Matrix.mul_assoc] at h'
    exact eq_neg_of_add_eq_zero_left h'
  · intro h
    have h' := congrArg (fun M => Formalism.REAL.Jm ε * M) h
    simp only [Matrix.mul_assoc, Jm_mul_Jm_mul', Matrix.mul_neg] at h'
    rw [h', neg_add_cancel]

theorem adj_adj (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε = X := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Jm_conjTransposeFlagMeasures]
  simp only [Matrix.mul_assoc, Jm_mul_Jm_mul', Jm_mul_self_eq_one', Matrix.mul_one]

theorem finrank_and_det (n : ℕ) (ε : Fin n → Bool) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ X ∈ N, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N) (hE : LinearIndependent ℝ E)
    (hs : ∀ X, (X ∈ N ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) :
    Module.finrank ℂ N = d ∧ ∀ (φ : N →ₗ[ℂ] N) (L : Matrix (Fin d) (Fin d) ℝ),
      (∀ (k : Fin d) (h : E k ∈ N), ((φ ⟨E k, h⟩ : N) : Matrix (Fin n) (Fin n) ℂ) = ∑ i, L i k • E i) →
      LinearMap.det φ = ((L.det : ℝ) : ℂ) := by
  classical

  have hS_add : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X + Y)ᴴ * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by
    intro X Y
    rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  have hS_sub : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X - Y)ᴴ * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε - Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by
    intro X Y
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hS_smul : ∀ (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.Jm ε * (c • X)ᴴ * Formalism.REAL.Jm ε =
      star c • (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) := by
    intro c X
    rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hS_sum : ∀ g : Fin d → ℂ, Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε =
      ∑ i, star (g i) • (Formalism.REAL.Jm ε * (E i)ᴴ * Formalism.REAL.Jm ε) := by
    intro g
    rw [Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hS_smul (g i) (E i)

  have hEmem : ∀ k, E k ∈ N ∧ Formalism.REAL.inG ε (E k) := fun k =>
    (hs (E k)).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hEadj : ∀ k, Formalism.REAL.Jm ε * (E k)ᴴ * Formalism.REAL.Jm ε = -E k := fun k =>
    (inG_iff_adj ε (E k)).1 (hEmem k).2

  have hLI : LinearIndependent ℂ E := by
    rw [Fintype.linearIndependent_iff] at hE ⊢
    intro g hg i
    have h1 : ∑ i, star (g i) • E i = 0 := by
      have h : Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε =
          Formalism.REAL.Jm ε * (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε := by rw [hg]
      rw [hS_sum, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul] at h
      simpa only [hEadj, smul_neg, Finset.sum_neg_distrib, neg_eq_zero] using h
    have hre : ∑ i, (2 * (g i).re) • E i = 0 := by
      have h2 : ∑ i, (2 * (g i).re) • E i = (∑ i, g i • E i) + ∑ i, star (g i) • E i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← add_smul, ← Complex.coe_smul]
        congr 1
        apply Complex.ext <;> simp <;> ring
      rw [h2, hg, h1, add_zero]
    have him : ∑ i, (2 * (g i).im) • E i = 0 := by
      have h2 : ∑ i, (2 * (g i).im) • E i =
          (-Complex.I) • ((∑ i, g i • E i) - ∑ i, star (g i) • E i) := by
        rw [← Finset.sum_sub_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, smul_smul, ← Complex.coe_smul]
        congr 1
        apply Complex.ext <;> simp <;> ring
      rw [h2, hg, h1, sub_zero, smul_zero]
    have a := hE _ hre i
    have b := hE _ him i
    apply Complex.ext <;> simp <;> linarith

  have hspan : N = Submodule.span ℂ (Set.range E) := by
    apply le_antisymm
    · intro X hX
      have hSX : Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N := hN X hX
      have hSS := adj_adj ε X
      have hA : (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈
          Submodule.span ℝ (Set.range E) := by
        refine (hs _).1 ⟨N.smul_mem _ (N.sub_mem hX hSX), ?_⟩
        rw [inG_iff_adj, hS_smul, hS_sub, hSS, ← smul_neg, neg_sub]
        congr 1
        simp
      have hB : (-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈
          Submodule.span ℝ (Set.range E) := by
        refine (hs _).1 ⟨N.smul_mem _ (N.add_mem hX hSX), ?_⟩
        rw [inG_iff_adj, hS_smul, hS_add, hSS, add_comm (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) X,
          ← neg_smul]
        congr 1
        apply Complex.ext <;> simp <;> norm_num
      have hA' := Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hA
      have hB' := Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hB
      have hX_eq : X = (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) +
          Complex.I • ((-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)) := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hX_eq]
      exact Submodule.add_mem _ hA' (Submodule.smul_mem _ _ hB')
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact (hEmem k).1
  have hfin : Module.finrank ℂ N = d := by
    rw [hspan, finrank_span_eq_card hLI, Fintype.card_fin]
  refine ⟨hfin, ?_⟩
  intro φ L hφ

  let E' : Fin d → N := fun k => ⟨E k, (hEmem k).1⟩
  have hLI' : LinearIndependent ℂ E' := LinearIndependent.of_comp N.subtype hLI
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range E') := by
    rintro ⟨X, hX⟩ -
    have hX' : X ∈ Submodule.span ℂ (Set.range E) := by rw [← hspan]; exact hX
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hX'
    have hXc : (⟨X, hX⟩ : N) = ∑ i, c i • E' i := by
      apply Subtype.ext
      simp [E', ← hc]
    rw [hXc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b := Module.Basis.mk hLI' hsp
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b φ = L.map (fun r : ℝ => (r : ℂ)) := by
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    have hφk : φ (b k) = ∑ j, ((L j k : ℝ) : ℂ) • b j := by
      apply Subtype.ext
      have h := hφ k (hEmem k).1
      simp only [b, Module.Basis.mk_apply, E', Submodule.coe_sum, Submodule.coe_smul] at h ⊢
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.coe_smul]
    rw [hφk]
    have hc : ∑ j, ((L j k : ℝ) : ℂ) • b j = b.equivFun.symm (fun j => ((L j k : ℝ) : ℂ)) := by
      rw [Module.Basis.equivFun_symm_apply]
    rw [hc, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [hM]
  exact (RingHom.map_det Complex.ofRealHom L).symm

end GlobalTheory.RealFormBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLayerProductMeasureMulProdLocal
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem layerProd_eq_pow (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) :
    layerProd n f j τ id = layerProd n 1 j (fun i => τ i ^ f) id := by
  unfold layerProd
  simp only [id, mul_one]
  congr 1
  · refine prod_congr rfl fun i _ => prod_congr rfl fun k _ => ?_
    ring
  · refine prod_congr rfl fun i _ => ?_
    ring

noncomputable def layerHom (n : ℕ) {a : ℕ} (j : Fin a → ℕ) : (Fin a → ℝ) →* ℝ where
  toFun τ := layerProd n 1 j τ id
  map_one' := by simp [layerProd]
  map_mul' σ τ := by
    unfold layerProd
    simp only [id, Pi.mul_apply]
    rw [mul_mul_mul_comm]
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun k _ => ?_
      rw [mul_div_mul_comm, mul_mul_mul_comm (σ i) (τ i), mul_pow (σ i / σ k), mul_pow (σ i * σ k)]
      ring
    · rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [mul_pow (σ i) (τ i) 2, mul_pow (σ i), mul_pow (σ i ^ 2)]
      ring

theorem layerProd_mul_prod : ∀ (ι : Type) [Fintype ι] (n f a : ℕ) (j : Fin a → ℕ) (s s₁ : Fin a → ℝ)
    (loc : ι → Fin a → ℝ), (∀ i, s i ^ f = s₁ i ^ f * ∏ v, loc v i) →
    layerProd n f j s id = layerProd n f j s₁ id * ∏ v, layerProd n 1 j (loc v) id := by
  intro ι _ n f a j s s₁ loc h

  have hs : (fun i => s i ^ f) = (fun i => s₁ i ^ f) * ∏ v, loc v := by
    funext i
    rw [h i, Pi.mul_apply, Finset.prod_apply]
  have key : ∀ τ : Fin a → ℝ, layerHom n j τ = layerProd n 1 j τ id := fun τ => rfl
  rw [layerProd_eq_pow, layerProd_eq_pow n f j s₁, ← key, ← key, hs, map_mul, map_prod]
  simp only [key]

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CasimirEigen

variable {n : ℕ}

theorem gelfVal_two_eq (χ : Fin n → ℂ) :
    gelfVal χ 2 = ∑ a, χ a * χ a - ∑ a, (Formalism.QuantumDeterminants.rhoStd n a : ℂ) * (Formalism.QuantumDeterminants.rhoStd n a : ℂ) := by
  rw [gelfVal_succ χ 1, pow_one]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul]
  have e : ∀ a : Fin n, (if a = b then χ a + ((n : ℂ) - 1) / 2 else if a < b then -1 else 0) =
      (if a = b then χ a + ((n : ℂ) - 1) / 2 else 0) - (if a ∈ Finset.Iio b then 1 else 0) := by
    intro a
    by_cases h1 : a = b
    · subst h1; simp
    · by_cases h2 : a < b <;> simp [h1, h2]
  simp only [Amat, Matrix.of_apply, e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Fin.card_Iio, Formalism.QuantumDeterminants.rhoStd]
  push_cast
  ring

theorem gelfVal_two_eq_cvalR (ε : Fin n → Bool) (lam : Fin n → ℝ) :
    gelfVal (fun a => (lam a : ℂ)) 2 = ((cvalR ε lam : ℝ) : ℂ) := by
  rw [gelfVal_two_eq]
  simp only [cvalR, nsq, dot, Pi.add_apply, half_sum_roots_standard n ε, Formalism.QuantumDeterminants.rhoStd]
  push_cast
  rfl

theorem gelf_one_eq (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    gelf ε 1 f g = ∑ a, ∑ b, Eab ε a b (Eab ε b a f) g := by
  unfold gelf
  rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rfl

theorem inner_eabV {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f : Matrix (Fin n) (Fin n) ℂ → H} (hf : SmoothOnGV ε f) (y : H) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Eab ε a b (fun x => ⟪y, f x⟫_ℂ) g = ⟪y, EabV ε a b f g⟫_ℂ := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have k1 := (rdVPair_of vector_right_derivative_extends n ε H ℂ (innerSL ℂ y) f _ g hf h1 hg).2
  have k2 := (rdVPair_of vector_right_derivative_extends n ε H ℂ (innerSL ℂ y) f _ g hf h2 hg).2
  simp only [innerSL_apply_apply, rdV_eq] at k1 k2
  simp only [Eab, Ec, EabV, EcV, inner_add_right, inner_smul_right, k1, k2]

theorem cas_eq_of_isZEigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Vs : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ Vs) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → ((∀ u, u ∈ Vs ↔ SmoothOnGV ε (fun g => σ g u)) ∧ GlRel E ∧ IsUnitary ε E ∧ (∀ X, inG ε X → ∀ u : Vs, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0) ∧ ∀ a b (u : Vs), ∀ g ∈ UJset ε, σ g (E a b u) = EabV ε a b (fun g => σ g u) g) → ∀ u : Vs, (∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g u⟫_ℂ)) → Cas E u = ((cvalR ε lam : ℝ) : ℂ) • u := by
  intro n ε H _ _ _ σ Vs E lam hσ ⟨hV, _, _, _, hE⟩ u hu
  have hone : ∀ v, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := GlobalTheory.SmoothVecMod.inUJ_one
  have key : ∀ (y : H) (a b : Fin n) (v : Vs) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Eab ε a b (fun x => ⟪y, σ x v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ := by
    intro y a b v g hg
    rw [hE a b v g hg]
    exact inner_eabV ((hV v).1 v.2) y a b hg
  apply Subtype.ext
  refine ext_inner_left ℂ fun y => ?_
  have h := (hu y).2 1 1 h1
  rw [gelf_one_eq, gelfVal_two_eq_cvalR ε lam] at h
  have e : ∀ a b : Fin n, Eab ε a b (Eab ε b a (fun x => ⟪y, σ x u⟫_ℂ)) 1 =
      ⟪y, ((E a b (E b a u) : Vs) : H)⟫_ℂ := by
    intro a b
    have := GlobalTheory.SmoothVecMod.eabV_congr (E := ℂ) (key y b a u) a b h1
    rw [eabV_eq, eabV_eq] at this
    rw [this, key y a b _ 1 h1, hone]
  simp only [e, hone] at h
  simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, inner_sum, Submodule.coe_smul,
    inner_smul_right]
  exact h

end GlobalTheory.CasimirEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramSchmidtLengths
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramFlag


open InnerProductSpace in
theorem sub_gs_mem {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r) :
    f a - gramSchmidt ℂ f a ∈ Submodule.span ℂ (f '' Set.Iio a) := by
  have h := gramSchmidt_def'' (𝕜 := ℂ) f a
  have hs : f a - gramSchmidt ℂ f a = ∑ i ∈ Finset.Iio a,
      (⟪gramSchmidt ℂ f i, f a⟫_ℂ / (‖gramSchmidt ℂ f i‖ : ℂ) ^ 2) • gramSchmidt ℂ f i := by
    rw [sub_eq_iff_eq_add']
    exact h
  rw [hs, ← span_gramSchmidt_Iio (𝕜 := ℂ) f a]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩)


open InnerProductSpace in
theorem norm_gs_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r)
    {w : E} (hw : w ∈ Submodule.span ℂ (f '' Set.Iio a)) : ‖gramSchmidt ℂ f a‖ ≤ ‖f a - w‖ := by
  have horth : ∀ v ∈ Submodule.span ℂ (f '' Set.Iio a), ⟪gramSchmidt ℂ f a, v⟫_ℂ = 0 := by
    intro v hv
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) f a] at hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact gramSchmidt_orthogonal (𝕜 := ℂ) f (ne_of_gt (Set.mem_Iio.1 hi))
    | zero => exact inner_zero_right _
    | add y y' _ _ hy hy' => rw [inner_add_right, hy, hy', add_zero]
    | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]
  have hy : (f a - gramSchmidt ℂ f a) - w ∈ Submodule.span ℂ (f '' Set.Iio a) :=
    Submodule.sub_mem _ (sub_gs_mem f a) hw
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (gramSchmidt ℂ f a) _ (horth _ hy)
  have heq : gramSchmidt ℂ f a + ((f a - gramSchmidt ℂ f a) - w) = f a - w := by abel
  rw [heq] at hpy
  nlinarith [norm_nonneg (gramSchmidt ℂ f a), norm_nonneg (f a - w),
    mul_self_nonneg ‖(f a - gramSchmidt ℂ f a) - w‖]


open InnerProductSpace in
theorem exists_upper {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) :
    ∃ u : UT r → ℂ, ∀ a, ∑ b, upper u b a • f b = gramSchmidt ℂ f a := by
  classical
  choose l hl hlx using fun a => (Finsupp.mem_span_image_iff_linearCombination ℂ).1 (sub_gs_mem f a)
  refine ⟨fun p => -(l p.1.2 p.1.1), fun a => ?_⟩
  have hz : ∀ b, a ≤ b → l a b = 0 := by
    intro b hab
    by_contra hne
    have hb := (Finsupp.mem_supported ℂ (l a)).1 (hl a) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
    exact absurd (Set.mem_Iio.1 hb) (not_lt.2 hab)
  have hc : ∀ b, upper (fun p : UT r => -(l p.1.2 p.1.1)) b a = (if b = a then 1 else 0) - l a b := by
    intro b
    rcases lt_trichotomy b a with hba | hba | hba
    · simp [upper, hba, hba.ne]
    · subst hba
      simp [upper, hz b le_rfl]
    · simp [upper, not_lt.2 hba.le, hba.ne', hz b hba.le]
  have hsum := hlx a
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℂ (f i))] at hsum
  simp_rw [hc, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hsum, sub_sub_cancel]

theorem eucl_eq {N : ℕ} (v : Fin N → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq, eucl]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem gramSchmidt_lengths : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), ∀ x ∈ GG k r, ∃ u : UT r → ℂ, (∀ a : Fin r, eucl (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = lA k r z x a.castSucc ∧ 0 < lA k r z x a.castSucc) ∧ ∀ a a' : Fin r, a ≠ a' → star (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) ⬝ᵥ (∑ b, upper u b a' • (x⁻¹ *ᵥ bvec (eI k r b))) = 0 := by
  intro k r z x hx
  classical
  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    obtain ⟨-, hsq, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
    have h := congrArg Matrix.det hsq
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.2 ⟨_, h⟩
  have hxu : IsUnit x.det := ((Formalism.QuantumDeterminants.uHGroup _ _ hH).2.2 x hx).1
  let L : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin x⁻¹
  have hLapp : ∀ v, L v = WithLp.toLp 2 (x⁻¹ *ᵥ v) := fun v => rfl
  let e : Fin r → Fin (2 * r + k + 1) → ℂ := fun b => bvec (eI k r b)
  let F : Fin r → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun b => L (e b)
  have hLinj : Function.Injective L := by
    intro v w hvw
    rw [hLapp, hLapp] at hvw
    have h1 : x⁻¹ *ᵥ v = x⁻¹ *ᵥ w := congrArg WithLp.ofLp hvw
    have h2 := congrArg (fun t => x *ᵥ t) h1
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hxu] using h2
  have heinj : Function.Injective (eI k r) := fun a b h => Fin.ext (by have h' := congrArg Fin.val h; exact h')
  have hlie : LinearIndependent ℂ e := by
    have h0 := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp _ heinj
    convert h0 using 1
    funext b
    simp [e, bvec]
  have hli : LinearIndependent ℂ F := hlie.map' L (LinearMap.ker_eq_bot.2 hLinj)
  obtain ⟨u, hu⟩ := exists_upper F
  have hG : ∀ a, WithLp.toLp 2 (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = InnerProductSpace.gramSchmidt ℂ F a := by
    intro a
    have htl : ∀ v : Fin (2 * r + k + 1) → ℂ,
        WithLp.toLp 2 v = (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm v := fun v => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hu a, htl, map_sum]
    simp only [map_smul]
    rfl
  have hset : ∀ a : Fin r, (Set.range fun b : {b : Fin r // b.val < (a.castSucc : Fin (r + 1)).val} =>
      bvec (eI k r b.1)) = e '' Set.Iio a := by
    intro a
    ext v
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.1, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hlA : ∀ a : Fin r, lA k r z x a.castSucc = ‖InnerProductSpace.gramSchmidt ℂ F a‖ := by
    intro a
    have hf : Formalism.QuantumDeterminants.fvec k r z a.castSucc = e a := by
      rw [Formalism.QuantumDeterminants.fvec, dite_eq_left (show (a.castSucc : Fin (r + 1)).val < r from a.isLt)]
      rfl
    have hspan : Submodule.span ℂ (F '' Set.Iio a) = (Submodule.span ℂ (e '' Set.Iio a)).map L := by
      rw [Submodule.map_span, Set.image_image]
    unfold lA
    rw [hf, hset a]
    apply IsLeast.csInf_eq
    constructor
    · have hm := sub_gs_mem F a
      rw [hspan] at hm
      obtain ⟨y, hy, hyL⟩ := Submodule.mem_map.1 hm
      refine ⟨y, hy, ?_⟩
      rw [eucl_eq, ← hLapp, map_sub, hyL]
      show _ = ‖F a - (F a - InnerProductSpace.gramSchmidt ℂ F a)‖
      rw [sub_sub_cancel]
    · rintro t ⟨y, hy, rfl⟩
      rw [eucl_eq, ← hLapp, map_sub]
      exact norm_gs_le F a (w := L y) (by rw [hspan]; exact Submodule.mem_map_of_mem hy)
  refine ⟨u, fun a => ⟨by rw [eucl_eq, hG a, hlA a], ?_⟩, fun a a' haa' => ?_⟩
  · rw [hlA a]
    exact norm_pos_iff.2 (InnerProductSpace.gramSchmidt_ne_zero (𝕜 := ℂ) a hli)
  · rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, hG a, hG a']
    exact InnerProductSpace.gramSchmidt_orthogonal (𝕜 := ℂ) F haa'

end GlobalTheory.Amp.GramFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocalStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_mass_eq_finprod_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → {p | (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) ≠ (G.S p).K0}.Finite ∧ G.mu Λ = ∏ᶠ p, (G.S p).mu (A.lat p Λ) := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  exact GlobalTheory.HL.MassProduct.mass_eq_finprod A r k G hk Λ
    (by first | exact hΛ | exact hΛ.toIsLattice)
end

