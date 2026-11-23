module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0202
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0204

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.G2AddWeierstrassPRowSum
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma summable_weierstrassP_terms (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 := by
  have h := (L.hasSum_weierstrassPExcept 0 z).summable
  refine (h.add (summable_of_ne_finset_zero (s := {0})
    (f := fun l : L.lattice => if (l : ℂ) = 0 then 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 else 0)
    ?_)).congr ?_
  · intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [hl]
  · intro l
    by_cases hl : (l : ℂ) = 0 <;> simp [hl]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma latticeEquivProd_symm_coe (L : PeriodPair) (p : ℤ × ℤ) :
    (L.latticeEquivProd.symm p : ℂ) = p.1 * L.ω₁ + p.2 * L.ω₂ := by
  simp [PeriodPair.latticeEquivProd, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    PeriodPair.latticeBasis]


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
lemma _root_.GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * τ + m) ^ 2)
      (EisensteinSeries.G2 τ + (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP z) := by
  set L := _root_.GlobalTheory.QFam.tauPair τ with hLdef
  have hω₁ : L.ω₁ = τ := rfl
  have hω₂ : L.ω₂ = 1 := rfl
  set f : ℤ × ℤ → ℂ := fun p => 1 / (z - (p.1 * τ + p.2)) ^ 2 - 1 / ((p.1 : ℂ) * τ + p.2) ^ 2
    with hfdef
  have hg : HasSum (fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2) (L.weierstrassP z) :=
    (summable_weierstrassP_terms L z).hasSum
  have hf : HasSum f (L.weierstrassP z) := by
    have := (L.latticeEquivProd.symm.toEquiv.hasSum_iff).mpr hg
    convert this using 1
    funext p
    simp [hfdef, latticeEquivProd_symm_coe, hω₁, hω₂]
  have hrow : HasSum (fun n : ℤ => ∑' m : ℤ, f (n, m)) (L.weierstrassP z) :=
    hf.prod_fiberwise fun n => (hf.summable.prod_factor n).hasSum
  have hG : HasSum (fun n : ℤ => EisensteinSeries.e2Summand n τ) (EisensteinSeries.G2 τ) := by
    rw [← _root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.tsum_e2Summand τ]
    exact (_root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand τ).hasSum
  have hsum := hG.add hrow
  have hF : HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z - (n * τ + m)) ^ 2)
      (EisensteinSeries.G2 τ + L.weierstrassP z) := by
    convert hsum using 1
    funext n
    have ha : Summable fun m : ℤ => 1 / ((n : ℂ) * τ + m) ^ 2 := by
      have := EisensteinSeries.linear_right_summable (τ : ℂ) n (k := 2) le_rfl
      convert this using 1
      funext m
      simp [zpow_ofNat]
    have hba : Summable fun m : ℤ => f (n, m) := hf.summable.prod_factor n
    have he : EisensteinSeries.e2Summand n τ = ∑' m : ℤ, 1 / ((n : ℂ) * τ + m) ^ 2 := by
      unfold EisensteinSeries.e2Summand
      congr 1
      funext m
      simp [EisensteinSeries.eisSummand]
    rw [he]
    have := (ha.hasSum.add hba.hasSum).tsum_eq
    simp only [hfdef, add_sub_cancel] at this
    exact this
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr hF
  convert hneg using 1
  funext n
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext m
  simp only [Equiv.neg_apply, Int.cast_neg, Function.comp_apply]
  ring

end GlobalTheory.WpFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentSemilinearBijectiveStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisDescent_sum_basis_smul_ker_bijective : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (V : Type) [AddCommGroup V] [Module F' V] [Module F V] [IsScalarTower F F' V] (T : Module.End F V), (∀ (c : F') (v : V), T (c • v) = s c • T v) → T ^ Module.finrank F F' = 1 → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι F F'), Function.Bijective (fun v : ι → LinearMap.ker (T - 1) => ∑ i, b i • (v i : V)) := by
  first | (exact @GlobalTheory.Shin.galoisDescent_semilinear_bijective) | (exact GlobalTheory.Shin.galoisDescent_semilinear_bijective) | (intros; apply GlobalTheory.Shin.galoisDescent_semilinear_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisElementDvdOfFormallyUnramifiedStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisElement_dvd_of_formallyUnramified : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    [Algebra.FormallyUnramified O (O ⊗[R] C)] [Algebra.EssFiniteType O (O ⊗[R] C)]
    (G : Type) [Group G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (b : R) (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) →
    ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) →
    ∀ h : G, ∃ m' : O ⊗[R] C, GlobalTheory.GoodEtale.galElt act σ x y h = algebraMap R O b • m' := by
  first | (exact @GlobalTheory.GoodEtale.galElt_dvd_of_unramified) | (exact GlobalTheory.GoodEtale.galElt_dvd_of_unramified) | (intros; apply GlobalTheory.GoodEtale.galElt_dvd_of_unramified  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicPropertiesStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisTwistedNormGL_basic_properties : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  first | (exact @GlobalTheory.Shin.NrmBasic.main) | (exact GlobalTheory.Shin.NrmBasic.main) | (intros; apply GlobalTheory.Shin.NrmBasic.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLDiagonalBlocksStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisTwistedNormGL_diagonal_blocks : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (γ : GL (Fin n) F) (δ : GL (Fin n) F'), InPar a γ → InPar a δ → nrm s δ = incl F F' n γ → nrm s (tlG a δ) = incl F F' a (tlG a γ) ∧ nrm s (brG a b δ) = incl F F' b (brG a b γ) := by
  first | (exact @GlobalTheory.ShinBlock.nrm_blocks) | (exact GlobalTheory.ShinBlock.nrm_blocks) | (intros; apply GlobalTheory.ShinBlock.nrm_blocks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPairingUnitaryGroupTwoThree
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.GaussPairing

section Coord

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type} [Fintype ι]

theorem norm_sq_eq_dot (e : V ≃L[ℝ] (ι → ℂ)) (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) (v : V) :
    (‖v‖ : ℂ) ^ 2 = star (e v) ⬝ᵥ e v := by
  have h : ((‖v‖ ^ 2 : ℝ) : ℂ) = ((∑ i, ‖e v i‖ ^ 2 : ℝ) : ℂ) := by rw [he v]
  push_cast at h
  rw [h, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Complex.conj_mul' _).symm

theorem inner_eq_dot (e : V ≃L[ℝ] (ι → ℂ)) (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) (x y : V) :
    ((⟪x, y⟫ : ℝ) : ℂ) = (1 / 2 : ℂ) * (star (e x) ⬝ᵥ e y + star (e y) ⬝ᵥ e x) := by
  have h : ((‖x + y‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_add_sq_real]
  push_cast at h
  rw [norm_sq_eq_dot e he (x + y), norm_sq_eq_dot e he x, norm_sq_eq_dot e he y, map_add (f := _), star_add,
    add_dotProduct, dotProduct_add, dotProduct_add] at h
  linear_combination (-1 / 2 : ℂ) * h

theorem star_mulVec_dot (g : Matrix ι ι ℂ) (z w : ι → ℂ) :
    star (g *ᵥ z) ⬝ᵥ w = star z ⬝ᵥ gᴴ *ᵥ w := by
  rw [star_mulVec, dotProduct_mulVec]

end Coord

theorem posDef_one_add {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (g : Matrix κ ι ℂ) :
    (1 + gᴴ * g).PosDef :=
  PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self g)

theorem integral_sum_elim {ι : Type} [Fintype ι] (F : (ι ⊕ ι → ℂ) → ℂ) (hF : Integrable F) :
    ∫ z : ι → ℂ, ∫ w : ι → ℂ, F (Sum.elim z w) = ∫ x, F x := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℂ)
  have hF' : Integrable (fun p => F ((MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℂ).symm p))
      ((volume : Measure (ι → ℂ)).prod volume) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  rw [← hmp.integral_comp' F, Measure.volume_eq_prod, integral_prod _ hF']
  rfl

private lemma half_smul_add_conjTranspose_eq_of_hermitian {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (hX : Xᴴ = X) :
    (1 / 2 : ℂ) • X + ((1 / 2 : ℂ) • X)ᴴ = X := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, hX, h2, ← smul_add, GlobalTheory.RealWeil.PosDet.half_add_self]

private lemma half_cross_add_conjTranspose_eq_mul {ι : Type} [Fintype ι] [DecidableEq ι] (s a b : Matrix ι ι ℂ) (hs : sᴴ = s) :
    (1 / 2 : ℂ) • (aᴴ * (1 + s) * b) + ((1 / 2 : ℂ) • (bᴴ * (1 - s) * a))ᴴ = 0 + aᴴ * b := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_sub, conjTranspose_one, hs, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, zero_add]
  module

private lemma half_cross_add_conjTranspose_eq_mul_swap {ι : Type} [Fintype ι] [DecidableEq ι] (s a b : Matrix ι ι ℂ) (hs : sᴴ = s) :
    (1 / 2 : ℂ) • (bᴴ * (1 - s) * a) + ((1 / 2 : ℂ) • (aᴴ * (1 + s) * b))ᴴ = 0 + bᴴ * a := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_add, conjTranspose_one, hs, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, zero_add]
  module

theorem lam_mu_eq : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι] (e : V ≃L[ℝ] (ι → ℂ)), (∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) → ∀ (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 → ∀ J : V ≃ₗᵢ[ℝ] V, (∀ v, e (J v) = I • s *ᵥ e v) → (∀ (g : Matrix ι ι ℂ) (k : V → V), gᴴ * s * g = s → (∀ v, e (k v) = g *ᵥ e v) → dP s g ≠ 0 ∧ dP s g⁻¹ = star (dP s g) ∧ lam k = (dP s g * dP s g⁻¹)⁻¹) ∧ ∀ (g₁ g₂ : Matrix ι ι ℂ) (k₁ k₂ : V → V), g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s → (∀ v, e (k₁ v) = g₁ *ᵥ e v) → (∀ v, e (k₂ v) = g₂ *ᵥ e v) → mu J k₁ k₂ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by
  intro V _ _ _ _ _ ι _ _ e he s hs hss J hJ
  have hmp := GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords V ι e he
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  obtain ⟨hd1, hd2⟩ := GlobalTheory.RealWeil.PosDet.detPlus_identities ι s hs hss
  have hHerm : ∀ g : Matrix ι ι ℂ, (1 + gᴴ * g)ᴴ = 1 + gᴴ * g := fun g => by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
  refine ⟨fun g k hg hk => ?_, fun g₁ g₂ k₁ k₂ hg₁ hg₂ hk₁ hk₂ => ?_⟩
  · obtain ⟨A, hA⟩ : ∃ A : Matrix ι ι ℂ, A = (1 / 2 : ℂ) • (1 + gᴴ * g) := ⟨_, rfl⟩
    have hAA : A + Aᴴ = 1 + gᴴ * g := by rw [hA]; exact half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g)
    obtain ⟨hA0, -, hAint⟩ := GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part ι A (by rw [hAA]; exact posDef_one_add g)
    obtain ⟨hstar, hdet⟩ := hd1 g hg
    rw [← hA] at hdet
    have hpt : ∀ u, gau u * gau (k u) = cexp (-(π : ℂ) * (star (e u) ⬝ᵥ A *ᵥ e u)) := by
      intro u
      simp only [gau, ← Complex.exp_add]
      congr 1
      rw [norm_sq_eq_dot e he u, norm_sq_eq_dot e he (k u), hk u, star_mulVec_dot, hA, smul_mulVec,
        dotProduct_smul, add_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add, smul_eq_mul]
      ring
    have hlam : lam k = A.det⁻¹ :=
      calc lam k = ∫ u, cexp (-(π : ℂ) * (star (e u) ⬝ᵥ A *ᵥ e u)) := by
            unfold lam
            congr 1
            funext u
            exact hpt u
        _ = ∫ z, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) :=
            hmp.integral_comp hme (fun z => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)))
        _ = A.det⁻¹ := hAint
    refine ⟨fun h0 => hA0 (by rw [hdet, h0, zero_mul]), hstar, ?_⟩
    rw [hlam, hdet]
  · obtain ⟨M, hM⟩ : ∃ M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ, M =
        fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
          ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂)) := ⟨_, rfl⟩
    have hdet2 := hd2 g₁ g₂ hg₁ hg₂
    rw [← hM] at hdet2
    have hMM : M + Mᴴ = 1 + (fromCols g₁ g₂)ᴴ * fromCols g₁ g₂ := by
      rw [hM, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
        fromBlocks_conjTranspose, fromBlocks_add, ← fromBlocks_one, fromBlocks_add,
        half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g₁), half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g₂), half_cross_add_conjTranspose_eq_mul s g₁ g₂ hs,
        half_cross_add_conjTranspose_eq_mul_swap s g₁ g₂ hs]
    obtain ⟨-, hMi, hMint⟩ := GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part (ι ⊕ ι) M (by rw [hMM]; exact posDef_one_add _)
    have hpt : ∀ u v, gau u * gau v * (cexp (π * I * (omJ J (k₁ u) (k₂ v) : ℂ)) * gau (k₁ u + k₂ v)) =
        cexp (-(π : ℂ) * (star (Sum.elim (e u) (e v)) ⬝ᵥ M *ᵥ Sum.elim (e u) (e v))) := by
      intro u v
      simp only [gau, ← Complex.exp_add]
      congr 1
      have hsum : star (Sum.elim (e u) (e v)) = Sum.elim (star (e u)) (star (e v)) := by
        funext i
        cases i <;> rfl
      have hA1 : ∀ (g : Matrix ι ι ℂ) (z : ι → ℂ),
          star z ⬝ᵥ ((1 / 2 : ℂ) • (1 + gᴴ * g)) *ᵥ z = 1 / 2 * (star z ⬝ᵥ z + star (g *ᵥ z) ⬝ᵥ g *ᵥ z) := by
        intro g z
        rw [smul_mulVec, dotProduct_smul, add_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add,
          ← star_mulVec_dot, smul_eq_mul]
      have hB1 : star (e u) ⬝ᵥ ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂)) *ᵥ e v =
          1 / 2 * (star (g₁ *ᵥ e u) ⬝ᵥ g₂ *ᵥ e v + star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v)) := by
        rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dot,
          add_mulVec, one_mulVec, dotProduct_add, smul_eq_mul]
      have hC1 : star (e v) ⬝ᵥ ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) *ᵥ e u =
          1 / 2 * (star (g₂ *ᵥ e v) ⬝ᵥ g₁ *ᵥ e u - star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u)) := by
        rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dot,
          sub_mulVec, one_mulVec, dotProduct_sub, smul_eq_mul]
      have hJ1 : star (g₁ *ᵥ e u) ⬝ᵥ I • s *ᵥ (g₂ *ᵥ e v) = I * (star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v)) := by
        rw [dotProduct_smul, smul_eq_mul]
      have hJ2 : star (I • s *ᵥ (g₂ *ᵥ e v)) ⬝ᵥ g₁ *ᵥ e u =
          -I * (star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u)) := by
        rw [star_smul, smul_dotProduct, star_mulVec_dot, hs, smul_eq_mul, Complex.star_def, Complex.conj_I]
      have hN : star (g₁ *ᵥ e u + g₂ *ᵥ e v) ⬝ᵥ (g₁ *ᵥ e u + g₂ *ᵥ e v) =
          star (g₁ *ᵥ e u) ⬝ᵥ g₁ *ᵥ e u + star (g₁ *ᵥ e u) ⬝ᵥ g₂ *ᵥ e v +
            (star (g₂ *ᵥ e v) ⬝ᵥ g₁ *ᵥ e u + star (g₂ *ᵥ e v) ⬝ᵥ g₂ *ᵥ e v) := by
        rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add]
      unfold omJ
      rw [inner_eq_dot e he, hJ, norm_sq_eq_dot e he u, norm_sq_eq_dot e he v,
        norm_sq_eq_dot e he (k₁ u + k₂ v), map_add, hk₁, hk₂, hJ1, hJ2, hN, hM, hsum, fromBlocks_mulVec,
        sumElim_dotProduct_sumElim]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_add]
      rw [hA1, hA1, hB1, hC1]
      linear_combination ((π : ℂ) / 2 * (star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v) -
        star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u))) * Complex.I_sq
    calc mu J k₁ k₂ = ∫ u, ∫ v, cexp (-(π : ℂ) * (star (Sum.elim (e u) (e v)) ⬝ᵥ M *ᵥ Sum.elim (e u) (e v))) := by
          unfold mu
          congr 1
          funext u
          congr 1
          funext v
          exact hpt u v
      _ = ∫ u, ∫ w, cexp (-(π : ℂ) * (star (Sum.elim (e u) w) ⬝ᵥ M *ᵥ Sum.elim (e u) w)) := by
          congr 1
          funext u
          exact hmp.integral_comp hme (fun w => cexp (-(π : ℂ) * (star (Sum.elim (e u) w) ⬝ᵥ M *ᵥ Sum.elim (e u) w)))
      _ = ∫ z, ∫ w, cexp (-(π : ℂ) * (star (Sum.elim z w) ⬝ᵥ M *ᵥ Sum.elim z w)) :=
          hmp.integral_comp hme (fun z => ∫ w, cexp (-(π : ℂ) * (star (Sum.elim z w) ⬝ᵥ M *ᵥ Sum.elim z w)))
      _ = ∫ x, cexp (-(π : ℂ) * (star x ⬝ᵥ M *ᵥ x)) := integral_sum_elim _ hMi
      _ = M.det⁻¹ := hMint
      _ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by rw [hdet2]

end GlobalTheory.RealWeil.GaussPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapAlgebraMap
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocAcyc

def genFibMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E] [Algebra T O]
    (ψ : E →ₐ[T] O) : GenFib T E →+* GenFib T O :=
  IsLocalization.map (M := Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (T := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (GenFib T O) ψ.toRingHom (by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (ψ.commutes t).symm⟩)

theorem genFibMap_algebraMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) :
    genFibMap ψ (algebraMap E (GenFib T E) e) = algebraMap O (GenFib T O) (ψ e) := by
  simp [genFibMap, IsLocalization.map_eq]

theorem genFib_ringHom_ext {T E C : Type} [CommRing T] [CommRing E] [CommRing C] [Algebra T E]
    {f g : GenFib T E →+* C} (h : ∀ e : E, f (algebraMap E _ e) = g (algebraMap E _ e)) : f = g :=
  IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (RingHom.ext h)

end GlobalTheory.LocAcyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionKernelStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibreLocalization_directedUnion_kernel : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ k, Function.Injective (e k)) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ (f : ∀ k l, k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l)))),
      (∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y))) →
    ∀ k (x : GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))), g k x = 0 →
      ∃ l, ∃ hkl : k ≤ l, f k l hkl x = 0 := by
  first | (exact @GlobalTheory.genFib_colim_ker) | (exact GlobalTheory.genFib_colim_ker) | (intros; apply GlobalTheory.genFib_colim_ker  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionSurjectiveStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibreLocalization_directedUnion_surjective : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ b : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q), ∃ k x, g k x = b := by
  first | (exact @GlobalTheory.genFib_colim_surj) | (exact GlobalTheory.genFib_colim_surj) | (intros; apply GlobalTheory.genFib_colim_surj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLCommStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
private lemma hc_conj_invariant {F : Type} [Field F] (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x p : GL (Fin n) F) :
    hc a b α β n (p * x * p⁻¹) = hc a b α β n x := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  congr 1
  rw [← finsum_comp_equiv (Equiv.mulLeft p)]
  congr 1
  funext y
  have h : ((Equiv.mulLeft p) y)⁻¹ * (p * x * p⁻¹) * (Equiv.mulLeft p) y = y⁻¹ * x * y := by
    change (p * y)⁻¹ * (p * x * p⁻¹) * (p * y) = y⁻¹ * x * y
    simp [mul_assoc]
  rw [h]

private lemma inPar_swap_eq_inPar_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (z : GL (Fin (a + b)) F) :
    (if InPar b z then β (tlG b z) * α (brG b a z) else 0) =
      (if InPar a (GlobalTheory.HCCommF.aflipG z) then
        α (tlG a (GlobalTheory.HCCommF.aflipG z)) * β (brG a b (GlobalTheory.HCCommF.aflipG z)) else 0) := by
  obtain ⟨w, rfl⟩ : ∃ w, z = GlobalTheory.HCCommF.aflipG w :=
    ⟨GlobalTheory.HCCommF.aflipG z, (GlobalTheory.HCCommF.aflipG_aflipG z).symm⟩
  rw [GlobalTheory.HCCommF.aflipG_aflipG, GlobalTheory.HCCommF.inPar_aflip]
  unfold tlG brG
  rw [GlobalTheory.HCCommF.aflipG_coe, GlobalTheory.HCCommF.tl_aflip, GlobalTheory.HCCommF.br_aflip,
    GlobalTheory.HCCommF.class_aflip hβ, GlobalTheory.HCCommF.class_aflip hα, mul_comm (β _)]

private lemma hc_swap_eq_hc_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (x : GL (Fin (a + b)) F) :
    hc b a β α (a + b) x = hc a b α β (a + b) (GlobalTheory.HCCommF.aflipG x) := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  have hcard : Nat.card {p : GL (Fin (a + b)) F // InPar b p} =
      Nat.card {p : GL (Fin (a + b)) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquiv (GlobalTheory.HCCommF.aflipE (F := F) (a + b)) (fun p => by
      show InPar b p ↔ InPar a (GlobalTheory.HCCommF.aflipG p)
      conv_lhs => rw [← GlobalTheory.HCCommF.aflipG_aflipG p]
      exact GlobalTheory.HCCommF.inPar_aflip _))
  rw [hcard]
  congr 1
  conv_rhs => rw [← finsum_comp_equiv ((GlobalTheory.HCCommF.aflipE (F := F) (a + b)).trans (Equiv.inv _))]
  congr 1
  funext y
  rw [inPar_swap_eq_inPar_aflipG a b α β hα hβ]
  have h : GlobalTheory.HCCommF.aflipG (y⁻¹ * x * y) =
      ((GlobalTheory.HCCommF.aflipG y)⁻¹)⁻¹ * GlobalTheory.HCCommF.aflipG x * (GlobalTheory.HCCommF.aflipG y)⁻¹ := by
    rw [inv_inv, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_inv, mul_assoc]
  rw [h]
  rfl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_comm : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → n = a + b → hc a b α β n = hc b a β α n := by
  intro F _ _ a b n α β hα hβ hn
  subst hn
  funext x
  rw [hc_swap_eq_hc_aflipG a b α β hα hβ x]
  obtain ⟨p, hp⟩ := GlobalTheory.HCCommF.aflipG_conj x
  rw [hp, hc_conj_invariant]
end

