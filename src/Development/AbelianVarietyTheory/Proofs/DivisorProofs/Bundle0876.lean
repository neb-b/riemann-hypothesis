module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import GroundTheory.Brauer.BaseChangeCSA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPosDenominatorOfIsCompactFiniteAdele
section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical RestrictedProduct

namespace GlobalTheory.AfPCpctDen

theorem natCast_mul_apply {p : ℕ} (n : ℕ) (a : AfP p) (v : AwayP p) :
    (LevelExists.rp ((n : AfP p) * a)).1 v = (n : v.1.adicCompletion ℚ) * (LevelExists.rp a).1 v :=
  rfl

theorem natCast_mem_int (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
  natCast_mem _ n

theorem exists_nat_local (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b.natAbs, Int.natAbs_pos.mpr hb0, ?_⟩
  rcases Int.natAbs_eq b with h | h
  · have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) b := by
      conv_rhs => rw [h]
      simp
    rw [e, mul_comm]
    exact hbx
  · have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = -algebraMap ℤ (v.adicCompletion ℚ) b := by
      conv_rhs => rw [h]
      simp
    rw [e, neg_mul, mul_comm]
    exact neg_mem hbx

theorem exists_nat_adele {p : ℕ} (a : AfP p) :
    ∃ n : ℕ, 0 < n ∧ (n : AfP p) * a ∈ LevelExists.intAfP p := by
  choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 ((LevelExists.rp a).1 v)
  have hS : {v : AwayP p | ¬ (LevelExists.rp a).1 v ∈ v.1.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp (LevelExists.rp a).2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [natCast_mul_apply]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]
    exact mul_mem (natCast_mem_int w.1 k) (hm w)
  · have hw' : (LevelExists.rp a).1 w ∈ w.1.adicCompletionIntegers ℚ := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem_int w.1 _) hw'

theorem exists_den (p : ℕ) (S : Set (AfP p)) (hS : IsCompact S) :
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p := by
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' (LevelExists.intAfP p : Set (AfP p)))
    (fun a => (LevelExists.isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := Set.mem_iUnion₂.mp (ht hf)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hfa' : (m a : AfP p) * f ∈ LevelExists.intAfP p := hfa
  rw [hk, Nat.cast_mul, mul_comm ((m a : ℕ) : AfP p), mul_assoc]
  exact mul_mem (natCast_mem _ k) hfa'

theorem main : ∀ (p : ℕ) (S : Set (AfP p)), IsCompact S → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p :=
  exists_den

end GlobalTheory.AfPCpctDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjCentralizerLeBlockDiagonalLevi
section
open MeasureTheory Matrix
open scoped Classical

noncomputable section
open Polynomial

namespace GlobalTheory.OrbDesc

theorem commute_aeval_of_commute {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {F f : Module.End K V} (h : Commute F f) (p : K[X]) : Commute F (aeval f p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right c F).mul_right (h.pow_right n)

theorem natDegree_pos_of_not_isUnit {K : Type} [Field K] {p : K[X]} (hp0 : p ≠ 0)
    (hp : ¬ IsUnit p) : 0 < p.natDegree := by
  by_contra h
  push_neg at h
  apply hp
  rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hp0]
  simp only [Nat.cast_eq_zero]
  omega

theorem exists_conj_cent_le_blockLevi : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (γ : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∃ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a ∧ 0 < b ∧ ∃ c : GL ι K,
    GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) (c⁻¹ * γ * c) ≤ GlobalTheory.OrbDesc.blockLevi e := by
  intro K _ ι _ _ _ γ hsep hirr
  set M : Matrix ι ι K := (γ : Matrix ι ι K) with hMdef
  have hχ0 : M.charpoly ≠ 0 := M.charpoly_monic.ne_zero
  have hχu : ¬ IsUnit M.charpoly := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Matrix.charpoly_natDegree_eq_dim] at h1
    exact Fintype.card_ne_zero h1
  obtain ⟨p, q, hpq, hp, hq⟩ : ∃ p q, M.charpoly = p * q ∧ ¬ IsUnit p ∧ ¬ IsUnit q := by
    by_contra hc
    push_neg at hc
    exact hirr (irreducible_iff.mpr ⟨hχu, fun p q h => by
      by_contra h'
      push_neg at h'
      exact h'.2 (hc p q h h'.1)⟩)
  have hcop : IsCoprime p q := (hpq ▸ hsep).isCoprime
  have hp0 : p ≠ 0 := by rintro rfl; rw [zero_mul] at hpq; exact hχ0 hpq
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hpq; exact hχ0 hpq
  have hpd := natDegree_pos_of_not_isUnit hp0 hp
  have hqd := natDegree_pos_of_not_isUnit hq0 hq
  let f : Module.End K (ι → K) := Matrix.toLin' M
  have haev : ∀ r : K[X], aeval f r = Matrix.toLin' (aeval M r) := fun r =>
    aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)) M r
  have hχf : aeval f M.charpoly = 0 := by rw [haev, Matrix.aeval_self_charpoly, map_zero]
  set V₁ := LinearMap.ker (aeval f p) with hV₁
  set V₂ := LinearMap.ker (aeval f q) with hV₂
  have hc : IsCompl V₁ V₂ := ⟨Polynomial.disjoint_ker_aeval_of_isCoprime f hcop, by
    rw [codisjoint_iff, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop, ← hpq, hχf,
      LinearMap.ker_zero]⟩
  have hcharf : LinearMap.charpoly f = M.charpoly := Matrix.charpoly_toLin' M
  have hdvd : M.charpoly ∣ minpoly K f := by
    have := GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable f (by rw [hcharf]; exact hsep)
    rwa [hcharf] at this
  have hV1 : V₁ ≠ ⊥ := by
    intro h
    have h2 : V₂ = ⊤ := by
      have := hc.sup_eq_top
      rwa [h, bot_sup_eq] at this
    have h3 : aeval f q = 0 := LinearMap.ker_eq_top.mp h2
    have h4 := Polynomial.natDegree_le_of_dvd (hdvd.trans (minpoly.dvd K f h3)) hq0
    rw [hpq, Polynomial.natDegree_mul hp0 hq0] at h4
    omega
  have hV2 : V₂ ≠ ⊥ := by
    intro h
    have h2 : V₁ = ⊤ := by
      have := hc.sup_eq_top
      rwa [h, sup_bot_eq] at this
    have h3 : aeval f p = 0 := LinearMap.ker_eq_top.mp h2
    have h4 := Polynomial.natDegree_le_of_dvd (hdvd.trans (minpoly.dvd K f h3)) hp0
    rw [hpq, Polynomial.natDegree_mul hp0 hq0] at h4
    omega
  let φ := Submodule.prodEquivOfIsCompl V₁ V₂ hc
  let b1 := Module.finBasis K V₁
  let b2 := Module.finBasis K V₂
  let b0 := (b1.prod b2).map φ
  let e : ι ≃ Fin (Module.finrank K V₁) ⊕ Fin (Module.finrank K V₂) :=
    (b0.indexEquiv (Pi.basisFun K ι)).symm
  let bb := b0.reindex e.symm
  have hbb : ∀ i, bb i = b0 (e i) := fun i => by
    simp [bb, Module.Basis.reindex_apply]
  have hbbr : ∀ v i, bb.repr v i = b0.repr v (e i) := fun v i => by
    simp [bb, Module.Basis.repr_reindex_apply]
  have hmem1 : ∀ k, b0 (Sum.inl k) ∈ V₁ := fun k => by
    simp [b0, φ, Submodule.coe_prodEquivOfIsCompl']
  have hmem2 : ∀ k, b0 (Sum.inr k) ∈ V₂ := fun k => by
    simp [b0, φ, Submodule.coe_prodEquivOfIsCompl']
  have hrep1 : ∀ v ∈ V₁, ∀ k, b0.repr v (Sum.inr k) = 0 := fun v hv k => by
    have : φ.symm v = (⟨v, hv⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left V₁ V₂ hc ⟨v, hv⟩
    simp [b0, Module.Basis.map_repr, this]
  have hrep2 : ∀ v ∈ V₂, ∀ k, b0.repr v (Sum.inl k) = 0 := fun v hv k => by
    have : φ.symm v = (0, ⟨v, hv⟩) := Submodule.prodEquivOfIsCompl_symm_apply_right V₁ V₂ hc ⟨v, hv⟩
    simp [b0, Module.Basis.map_repr, this]
  let std := Pi.basisFun K ι
  let c : GL ι K := ⟨std.toMatrix bb, bb.toMatrix std,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨_, _, e, Module.finrank_pos_iff.mpr ?_, Module.finrank_pos_iff.mpr ?_, c, ?_⟩
  · exact Submodule.nontrivial_iff_ne_bot.mpr hV1
  · exact Submodule.nontrivial_iff_ne_bot.mpr hV2
  intro g hg
  have hg' : g * (c⁻¹ * γ * c) = (c⁻¹ * γ * c) * g := hg
  have hN : (c * g * c⁻¹) * γ = γ * (c * g * c⁻¹) := by
    calc (c * g * c⁻¹) * γ = c * (g * (c⁻¹ * γ * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * γ * c) * g) * c⁻¹ := by rw [hg']
      _ = γ * (c * g * c⁻¹) := by group
  let F : Module.End K (ι → K) := Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K)
  have hC : Commute F f := by
    show Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K) ∘ₗ Matrix.toLin' (γ : Matrix ι ι K)
      = Matrix.toLin' (γ : Matrix ι ι K) ∘ₗ Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K)
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Units.val_mul, ← Units.val_mul, hN]
  have hF1 : ∀ v ∈ V₁, F v ∈ V₁ := fun v hv => by
    rw [hV₁, LinearMap.mem_ker] at hv ⊢
    have := LinearMap.congr_fun (commute_aeval_of_commute hC p).eq v
    simp only [Module.End.mul_apply, hv, map_zero] at this
    exact this.symm
  have hF2 : ∀ v ∈ V₂, F v ∈ V₂ := fun v hv => by
    rw [hV₂, LinearMap.mem_ker] at hv ⊢
    have := LinearMap.congr_fun (commute_aeval_of_commute hC q).eq v
    simp only [Module.End.mul_apply, hv, map_zero] at this
    exact this.symm
  have hg2 : g = c⁻¹ * (c * g * c⁻¹) * c := by group
  have hgm : (g : Matrix ι ι K) = bb.toMatrix std * ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K) * std.toMatrix bb := by
    conv_lhs => rw [hg2]
    rfl
  have hgF : (g : Matrix ι ι K) = LinearMap.toMatrix bb bb F := by
    rw [hgm, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bb std bb std F,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hz : ∀ i j, side e i ≠ side e j → (g : Matrix ι ι K) i j = 0 := by
    intro i j hij
    rw [hgF, LinearMap.toMatrix_apply, hbb, hbbr]
    cases hi : e i with
    | inl k =>
      cases hj : e j with
      | inl k' => simp [side, hi, hj] at hij
      | inr k' => exact hrep2 _ (hF2 _ (hmem2 k')) k
    | inr k =>
      cases hj : e j with
      | inl k' => exact hrep1 _ (hF1 _ (hmem1 k')) k
      | inr k' => simp [side, hi, hj] at hij
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show (g : Matrix ι ι K).BlockTriangular (side e)
    intro i j hlt
    apply hz
    intro heq
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · show (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i))
    intro i j hlt
    apply hz
    intro heq
    simp only [] at hlt
    rw [heq] at hlt
    exact lt_irrefl _ hlt

end GlobalTheory.OrbDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvalu
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem similitude_eigvec_orthogonal : ∀ {n : ℕ} (h g : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ), h.IsHermitian → h.det ≠ 0 → c ≠ 0 → gᴴ * h * g = (c : ℂ) • h → Function.Injective lam → (∀ i, ‖lam i‖ ^ 2 = c) → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧ (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  intro n h g c Z lam hh hdet hc hg hinj hnorm hgZ
  set M : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hM
  set H : Matrix (Fin n) (Fin n) ℂ := Mᴴ * h * M with hH
  have hHherm : H.IsHermitian := by
    simp only [hH, IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hh.eq, Matrix.mul_assoc]
  have key : (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam = (c : ℂ) • H := by
    have e1 : (M * Matrix.diagonal lam)ᴴ * h * (M * Matrix.diagonal lam) = (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam := by
      simp only [hH, conjTranspose_mul, Matrix.mul_assoc]
    rw [← e1, ← hgZ]
    simp only [hH, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc (gᴴ * h), hg]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hc' : ∀ i, (starRingEnd ℂ) (lam i) * lam i = (c : ℂ) := by
    intro i
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast hnorm i
  have hlam0 : ∀ i, lam i ≠ 0 := by
    intro i h0
    have := hnorm i
    rw [h0, norm_zero] at this
    exact hc (by simpa using this.symm)
  have hoff : ∀ i j, i ≠ j → H i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun key i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul] at e
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    have hne : lam j - lam i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h).symm)
    have hstar : (starRingEnd ℂ) (lam i) ≠ 0 := by simpa using hlam0 i
    have e2 : (starRingEnd ℂ) (lam i) * (lam j - lam i) * H i j = 0 := by
      rw [← hc' i] at e
      simp only [Pi.star_apply] at e
      have : star (lam i) = (starRingEnd ℂ) (lam i) := rfl
      rw [this] at e
      linear_combination e
    rcases mul_eq_zero.mp e2 with h1 | h1
    · exact absurd h1 (mul_ne_zero hstar hne)
    · exact h1
  have hdiag : H = Matrix.diagonal (fun i => (((H i i).re : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      exact (hHherm.coe_re_apply_self i).symm
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  refine ⟨fun i => (H i i).re, ?_, hdiag⟩
  have hdetH : H.det ≠ 0 := by
    have hMdet : M.det ≠ 0 := by
      rw [hM]; exact (Matrix.isUnit_iff_isUnit_det _).mp Z.isUnit |>.ne_zero
    simp only [hH, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (by simpa using hMdet) hdet) hMdet
  intro i hi
  rw [hdiag, Matrix.det_diagonal] at hdetH
  apply hdetH
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsi
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem roots_eig : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F) (w : ℂ),
    P.pol.eval₂ v.embedding w = 0 → ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v P.γ *ᵥ x = w • x := by
  intro p _ G P v w hw
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hτ : algebraMap G.F ℂ = v.embedding := rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v P.γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF ((P.γ : G.C) ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) (P.γ : G.C))
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => (1 : ℂ) ⊗ₜ[G.F] ((P.γ : G.C) ^ (i : ℕ))) =
        fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hd : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hpm : P.pol.Monic := minpoly.monic hint
  set Q := P.pol.map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = G.n := by rw [hQ, hpm.natDegree_map]; exact P.reg.1
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF (P.γ : G.C)) P.pol = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [Pair.pol, minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = G.n - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F (P.γ : G.C)).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), hd, ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel G.n_pos]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum ⟨G.n - 1, by rw [hd]; have := G.n_pos; omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreGenericPointDvrOfPrime
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

theorem exists_fibre_generic_of_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (π : R), Prime π → ∃ ξ : X, (q ξ).asIdeal = Ideal.span {π} ∧ (∀ x : X, (q x).asIdeal = Ideal.span {π} → ξ ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧ Irreducible (X.presheaf.germ ⊤ ξ trivial (constFn q ⊤ π)) := by
  intro R _ _ _ _ X _ q _ _ π hπp
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπp.ne_zero).2 hπp
  let v : Sp R := ⟨Ideal.span {π}, hP⟩
  let V := Localization.AtPrime v.asIdeal
  have hmax : IsLocalRing.maximalIdeal V = Ideal.span {algebraMap R V π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hne : algebraMap R V π ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective V v.asIdeal.primeCompl_le_nonZeroDivisors)).2 hπp.ne_zero
  have : IsNoetherianRing V := IsLocalization.isNoetherianRing v.asIdeal.primeCompl V inferInstance
  have hnf : ¬ IsField V := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact hne
  have hpr : Submodule.IsPrincipal (IsLocalRing.maximalIdeal V) := ⟨⟨_, hmax⟩⟩
  have : IsDiscreteValuationRing V :=
    ((IsDiscreteValuationRing.TFAE V hnf).out 1 5).mpr hpr
  have hπ : Irreducible (algebraMap R V π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  let l := spMap (algebraMap R V)
  have : Flat l := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : IsPreimmersion l := IsPreimmersion.of_isLocalization v.asIdeal.primeCompl
  have H := IsPullback.of_hasPullback q l
  set ψ := pullback.fst q l
  set f := pullback.snd q l
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks ψ
  obtain ⟨h₁, h₂⟩ := DvrModel.isDiscreteValuationRing_stalk_generic hπ hs
  have h₃ := DvrModel.notMem_basicOpen_iff_specializes hπ hs
  have hlv : l (IsLocalRing.closedPoint V) = v :=
    PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := v.asIdeal))
  have h₄ := (DvrModel.notMem_basicOpen_iff f hπ _).1 ((h₃ _).2 specializes_rfl)
  generalize (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))) (genericPoint _) = ξ
    at h₁ h₂ h₃ h₄
  let E := (asIso (ψ.stalkMap ξ)).commRingCatIsoToRingEquiv
  refine ⟨ψ ξ, ?_, fun x hx => ?_,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.symm, ?_⟩
  · rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, h₄, hlv]
  · obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback H x (IsLocalRing.closedPoint V)
      ((PrimeSpectrum.ext hx).trans hlv.symm)
    exact ((h₃ y).1 ((DvrModel.notMem_basicOpen_iff f hπ y).2 hy)).map ψ.continuous
  · rw [← MulEquiv.irreducible_iff E.toMulEquiv]
    convert h₂ using 1
    exact (ψ.germ_stalkMap_apply ⊤ ξ trivial _).trans
      (congrArg _ ((app_constFn H.w π).trans (constFn_top _ _)))

end GlobalTheory.VerticalUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIsoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryGroup_iso : ∀ {D : D7} (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (j' : Matrix (Fin V.rank) (Fin V'.rank) (EAf D)), HMul.hMul j j' = 1 → HMul.hMul j' j = 1 → HMul.hMul (HMul.hMul (Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) j) (V'.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))) j = V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) → ∃ Φ : GfC V ≃ₜ* GfC V', ∀ g : GfC V, HMul.hMul (finE V' (Φ g : GA D V')).val j = HMul.hMul j (finE V (g : GA D V)).val := by
  first | exact @GlobalTheory.FinIsoGrp.exists_finIso | exact GlobalTheory.FinIsoGrp.exists_finIso | (intros; apply GlobalTheory.FinIsoGrp.exists_finIso <;> assumption)
end

