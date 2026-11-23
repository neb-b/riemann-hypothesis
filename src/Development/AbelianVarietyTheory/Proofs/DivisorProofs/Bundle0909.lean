module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import GroundTheory.Brauer.TensorSimple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactModNormOneKernelInvolution
section
open Filter Topology

namespace GlobalTheory.InvolutionNorm

theorem exists_compact_mod_kernel : ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z], (∀ a b : Z, a * b = b * a) → ∀ τ : Z →* Z, Continuous τ → (∀ z, τ (τ z) = z) → (∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s) → ∀ D : Set Z, IsCompact D → ∃ B : Set Z, IsCompact B ∧ ∀ z : Z, τ z * z ∈ D → ∃ t : Z, τ t * t = 1 ∧ ∃ b ∈ B, z = t * b := by
  intro Z _ _ _ _ _ _ hc τ hτ hinv hW D hD
  obtain ⟨W, hW1, hWs⟩ := hW
  let N : Z →* Z :=
    { toFun := fun z => τ z * z
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        rw [mul_assoc, mul_assoc, ← mul_assoc (τ b) a b, hc (τ b) a, mul_assoc] }
  have hN : Continuous N := hτ.mul continuous_id
  have hNval : ∀ z, N z = τ z * z := fun _ => rfl
  let I : Subgroup Z := N.range
  have hIH : ∀ y ∈ I, τ y = y := by
    rintro _ ⟨z, rfl⟩
    rw [hNval, map_mul, hinv, hc]
  have hHcl : IsClosed {y : Z | τ y = y} := isClosed_eq hτ continuous_id
  have hIcl : IsClosed (I : Set Z) := by
    refine closure_subset_iff_isClosed.1 fun x hx => ?_
    have hxH : τ x = x := closure_minimal (fun y hy => hIH y hy) hHcl hx
    have hnb : (fun y => x⁻¹ * y) ⁻¹' W ∈ 𝓝 x := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hW1
    obtain ⟨i, hiW, hiI⟩ := mem_closure_iff_nhds.1 hx _ hnb
    have hiH : τ i = i := hIH i hiI
    obtain ⟨r, hr, hrr⟩ := hWs _ hiW (by rw [map_mul, map_inv, hxH, hiH])
    have hNr : N r = x⁻¹ * i := by rw [hNval, hr, hrr]
    have : x = i * (N r)⁻¹ := by rw [hNr]; group
    rw [this]
    exact I.mul_mem hiI (I.inv_mem ⟨r, rfl⟩)
  let f : Z →* I := N.rangeRestrict
  have hfc : Continuous f := hN.subtype_mk _
  have hfs : Function.Surjective f := N.rangeRestrict_surjective
  have : LocallyCompactSpace I := hIcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hopen : IsOpenMap f := f.isOpenMap_of_sigmaCompact hfs hfc
  have hK' : IsCompact (Subtype.val ⁻¹' D : Set I) :=
    hIcl.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  have key : ∃ C : Set Z, IsCompact C ∧ (Subtype.val ⁻¹' D : Set I) ⊆ f '' C := by
    refine hK'.induction_on (p := fun s => ∃ C : Set Z, IsCompact C ∧ s ⊆ f '' C)
      ⟨∅, isCompact_empty, Set.empty_subset _⟩ (fun s t hst ⟨C, hC, h⟩ => ⟨C, hC, hst.trans h⟩) ?_ ?_
    · rintro s t ⟨C, hC, h⟩ ⟨D, hD, h'⟩
      exact ⟨C ∪ D, hC.union hD, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
    · intro y _
      obtain ⟨g, rfl⟩ := hfs y
      obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hg), C, hC, subset_rfl⟩
  obtain ⟨C, hC, hCD⟩ := key
  refine ⟨C, hC, fun z hz => ?_⟩
  obtain ⟨c, hcC, e⟩ := hCD (a := f z) hz
  have e' : N c = N z := congrArg Subtype.val e
  refine ⟨z * c⁻¹, ?_, c, hcC, by group⟩
  rw [← hNval, map_mul, map_inv, e', mul_inv_cancel]

end GlobalTheory.InvolutionNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvaluStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_congr_of_similitude_distinct_eigenvalues : ∀ {n : ℕ} (h g : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ), h.IsHermitian → h.det ≠ 0 → c ≠ 0 → gᴴ * h * g = (c : ℂ) • h → Function.Injective lam → (∀ i, ‖lam i‖ ^ 2 = c) → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧ (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  first | (exact @GlobalTheory.similitude_eigvec_orthogonal) | (exact GlobalTheory.similitude_eigvec_orthogonal) | (intros; apply GlobalTheory.similitude_eigvec_orthogonal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRoots
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

theorem charpoly_psi_eq_map_pol (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F) :
    (G.psi v (P.γ : G.C)).charpoly = P.pol.map v.embedding := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a :=
    fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ := { G.psi v with commutes' := hg }
  let L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  set γ : G.C := (P.γ : G.C) with hγ
  have hdeg : (minpoly G.F γ).natDegree = G.n := P.reg.1
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral ℂ (G.psi v γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℂ (G.psi v γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.psi v γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.psi v γ) (P.pol.map v.embedding) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : (P.pol.map v.embedding).Monic := (minpoly.monic hFint).map _
  have hn1 : (P.pol.map v.embedding).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem psi_eigenbasis : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    ∃ (Z : GL (Fin G.n) ℂ) (lam : Fin G.n → ℂ), Function.Injective lam ∧
      (∀ z : ℂ, P.pol.eval₂ v.embedding z = 0 ↔ ∃ i, lam i = z) ∧
      G.psi v (P.γ : G.C) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal lam := by
  intro p _ G P v
  set Q := P.pol.map v.embedding with hQ
  obtain ⟨hcard, hmon⟩ := GlobalTheory.LKMid.Pair.card_roots_map_pol p G P v.embedding
  have hsep : Q.Separable := P.reg.2.map
  have hnd : Q.roots.Nodup := Polynomial.nodup_roots hsep
  have hQm : Q.Monic := hmon.map _
  have hne : P.pol ≠ 0 := hmon.ne_zero
  let e : Fin G.n ≃ {x // x ∈ Q.roots.toFinset} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)).symm
  let lam : Fin G.n → ℂ := fun i => (e i : ℂ)
  have hlam : Function.Injective lam := fun i j h => e.injective (Subtype.ext h)
  have hprod : Q = ∏ k, (X - C (lam k)) := by
    have h1 : Q = (Q.roots.map (fun a => X - C a)).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm
        (IsAlgClosed.card_roots_eq_natDegree)).symm
    rw [h1]
    have h2 : (Q.roots.map (fun a => X - C a)).prod = ∏ a ∈ Q.roots.toFinset, (X - C a) := by
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
    rw [h2, ← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hcp : (G.psi v (P.γ : G.C)).charpoly = ∏ k, (X - C (lam k)) := by
    rw [charpoly_psi_eq_map_pol, ← hQ, ← hprod]
  obtain ⟨Z, hZ⟩ := GlobalTheory.matrix_diagonalizable_of_charpoly_eq_prod_distinct ℂ G.n _ lam hlam hcp
  refine ⟨Z, lam, hlam, fun z => ?_, hZ⟩
  rw [← Polynomial.mem_roots_map_of_injective v.embedding.injective hne, ← hQ, ← Multiset.mem_toFinset]
  constructor
  · intro hz
    exact ⟨e.symm ⟨z, hz⟩, by simp [lam]⟩
  · rintro ⟨i, rfl⟩
    exact (e i).2

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsiStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenvector_of_minpoly_root_hermitianPsi : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F) (w : ℂ),
    P.pol.eval₂ v.embedding w = 0 → ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v P.γ *ᵥ x = w • x := by
  first | (exact @GlobalTheory.LKMid.roots_eig) | (exact GlobalTheory.LKMid.roots_eig) | (intros; apply GlobalTheory.LKMid.roots_eig  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory

theorem outsideS_elt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  intro E _ _ a S k
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨k, fun w _ => rfl, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w S hwS ih =>
    obtain ⟨k', h1, h2⟩ := ih
    refine ⟨k' * (locGL E a w (GeneralLinearGroup.map (pLoc E w) k'))⁻¹, ?_, ?_⟩
    · intro v hv
      have hvw : v ≠ w := fun e => hv (e ▸ Finset.mem_insert_self _ _)
      rw [map_mul, map_inv, pLoc_locGL_of_ne hvw, inv_one, mul_one]
      exact h1 v (fun h => hv (Finset.mem_insert_of_mem h))
    · intro v hv
      rw [map_mul, map_inv]
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL, mul_inv_cancel]
      · rw [pLoc_locGL_of_ne hvw, inv_one, mul_one]
        exact h2 v ((Finset.mem_insert.1 hv).resolve_left hvw)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.FinIsoExists

theorem exists_isometry {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (σ : A →+* A) {n n' : ℕ} (h : n = n')
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n') (Fin n') A) (β : GL (Fin n) A) (β' : GL (Fin n') A)
    (u : GL (Fin n) R) (u' : GL (Fin n') R)
    (hu : Formalism.UG.cT σ (β * Formalism.UG.bc φ u).val * J * (β * Formalism.UG.bc φ u).val = 1)
    (hu' : Formalism.UG.cT σ (β' * Formalism.UG.bc φ u').val * J' * (β' * Formalism.UG.bc φ u').val = 1) :
    ∃ u₀ : GL (Fin n') R, ∀ y : GL (Fin n') R, β' * Formalism.UG.bc φ y * β'⁻¹ ∈ Formalism.UG.UJ σ J' →
      ∃ (j : Matrix (Fin n') (Fin n) A) (j' : Matrix (Fin n) (Fin n') A), j * j' = 1 ∧ j' * j = 1 ∧
        Formalism.UG.cT σ j * J' * j = J ∧ j * β.val = (β' * Formalism.UG.bc φ (y * u₀)).val.submatrix id (Fin.cast h) := by
  subst h
  refine ⟨u' * u⁻¹, fun y hy => ?_⟩
  set k := β' * Formalism.UG.bc φ y * β'⁻¹ with hk
  set B := β * Formalism.UG.bc φ u with hB
  set B' := β' * Formalism.UG.bc φ u' with hB'
  have hy' : Formalism.UG.cT σ k.val * J' * k.val = J' := hy
  refine ⟨(k * B' * B⁻¹).val, (k * B' * B⁻¹)⁻¹.val, Units.mul_inv _, Units.inv_mul _, ?_, ?_⟩
  · calc Formalism.UG.cT σ (k * B' * B⁻¹).val * J' * (k * B' * B⁻¹).val
        = Formalism.UG.cT σ B⁻¹.val * (Formalism.UG.cT σ B'.val * (Formalism.UG.cT σ k.val * J' * k.val) * B'.val) * B⁻¹.val := by
          simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ B⁻¹.val * (Formalism.UG.cT σ B.val * J * B.val) * B⁻¹.val := by rw [hy', hu, hu']
      _ = Formalism.UG.cT σ (B.val * B⁻¹.val) * J * (B.val * B⁻¹.val) := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · have e : k * B' * B⁻¹ * β = β' * Formalism.UG.bc φ (y * (u' * u⁻¹)) := by
      rw [hk, hB, hB', map_mul, map_mul, map_inv]
      group
    rw [← Units.val_mul, e]
    rfl

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have hg : g ∈ blockTri (κ := κ) (blk2 n) := by
    rw [mem_blockTri]
    intro i j hij
    simp [blk2] at hij
  apply Units.ext
  rw [upper_block_val_submatrix hr hg]
  rfl

theorem exists_isFinIso : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (β' : GL (Fin V'.rank) (EAf D)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N' : ℕ) (Pg : Finset (Pl D.host.E)), V.rank = V'.rank → IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl PP PP') → ∃ j Φ, IsFinIso V V' β β' Pg j Φ := by
  intro D V V' β Λ N β' Λ' N' Pg h hβ hβ' hPg
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integral_change_baseFrame_orthonormal V β Λ N hβ
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_integral_change_baseFrame_orthonormal V' β' Λ' N' hβ'
  obtain ⟨u₀, hu₀⟩ := exists_isometry (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) h _ _ β β' u u' hu hu'
  have hL := _root_.GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty V' β' (datW V'.rank Pg (LevelP.triv Pg V'.rank ℂ) Frm.B) Λ' N' hβ' rfl hPg
  obtain ⟨κ, -, hκ, hred⟩ := hL (fun PP => (Formalism.UG.bc (resS D.host.F PP.1) u₀)⁻¹)
  obtain ⟨y, hy⟩ := parLev_St hκ
  have hU : β' * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype y * β'⁻¹ ∈
      UA D.sp.cm V'.gram := by
    have h1 := parLev_UA hκ
    rw [← hy] at h1
    exact h1
  obtain ⟨j, j', h1, h2, h3, h4⟩ := hu₀ y hU
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryGroup_iso V V' j j' h1 h2 h3
  refine ⟨j, Φ, h3, hΦ, h, y * u₀, h4, fun PP hPP => ?_⟩
  have h5 : upperLeftBlock le_rfl (redFn β' PP (finE V' κ)) = (Formalism.UG.bc (resS D.host.F PP) u₀)⁻¹ := congrFun hred ⟨PP, hPP⟩
  have h6 : redFn β' PP (finE V' κ) = Formalism.UG.bc (resS D.host.F PP) y :=
    (congrArg (redFn β' PP) hy).symm.trans (redFn_frGL β' PP y)
  have h7 : Formalism.UG.bc (resS D.host.F PP) y = (Formalism.UG.bc (resS D.host.F PP) u₀)⁻¹ :=
    h6.symm.trans ((restrictedBlock_self_apply _ _).symm.trans h5)
  exact (map_mul _ y u₀).trans (mul_eq_one_iff_eq_inv.2 h7)

end GlobalTheory.FinIsoExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueRigidifiedLineBundleClassesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_rigidified_line_bundle_classes : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → FnBij p → ∀ (Ix : Type) (X' : Ix → Scheme.{0}) (f : ∀ i, X' i ⟶ X) (V : Ix → Y.Opens) (c : ∀ i, Pic (X' i)), (∀ i, IsOpenImmersion (f i)) → (∀ i x, x ∈ Set.range (f i) ↔ p x ∈ V i) → (∀ y, ∃ i, y ∈ V i) → (∀ (i : Ix) (T : Scheme.{0}) (t : T ⟶ X' i) (s : T ⟶ Y), t ≫ f i = s ≫ e → GlobalTheory.CechPic.pull t (c i) = 0) → (∀ (i k : Ix) (T : Scheme.{0}) (a : T ⟶ X' i) (b : T ⟶ X' k), a ≫ f i = b ≫ f k → GlobalTheory.CechPic.pull a (c i) = GlobalTheory.CechPic.pull b (c k)) → ∃ c₀ : Pic X, GlobalTheory.CechPic.pull e c₀ = 0 ∧ ∀ i, GlobalTheory.CechPic.pull (f i) c₀ = c i := by
  first | exact @GlobalTheory.PicGlue.exists_glue_rigidified | exact GlobalTheory.PicGlue.exists_glue_rigidified | (intros; apply GlobalTheory.PicGlue.exists_glue_rigidified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentCutoffTendstoAdelicUnitary
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.UnitaryCutoff

section Mix

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def mix (e : R) (A : Matrix ι ι R) : Matrix ι ι R := e • A + (1 - e) • (1 : Matrix ι ι R)

theorem mix_mul_mul {e : R} (he : e * e = e) (A C B : Matrix ι ι R) :
    mix e A * C * mix e B = e • (A * C * B) + (1 - e) • C := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [mix, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem mix_mul {e : R} (he : e * e = e) (A B : Matrix ι ι R) :
    mix e A * mix e B = e • (A * B) + (1 - e) • (1 : Matrix ι ι R) := by
  have := mix_mul_mul he A 1 B
  rwa [Matrix.mul_one, Matrix.mul_one] at this

theorem mix_transpose (e : R) (A : Matrix ι ι R) : (mix e A)ᵀ = mix e Aᵀ := by
  simp [mix, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]

theorem mix_map {S : Type} [CommRing S] [Algebra S R] (c : R →ₐ[S] R) {e : R} (hc : c e = e) (A : Matrix ι ι R) :
    (mix e A).map c = mix e (A.map c) := by
  ext i j
  simp only [mix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp [hc]

end Mix

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_mix_fin {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (AE F E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
      mix (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) M) atTop (𝓝 M) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (GlobalTheory.LocalGlobalChar.tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix ι ι (AE F E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Adele

theorem exists_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧ Tendsto q atTop (𝓝 g) := by
  intro F E _ _ _ _ _ σ ι _ _ J₀ g
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AE F E := fun S => algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)
  have he : ∀ S, e S * e S = e S := fun S => by
    simp only [e]; rw [← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hc : ∀ S, cA σ (e S) = e S := fun S => (cA σ).commutes _
  have hg : (g.1.1)ᵀ * J₀ * (g.1.1).map (cA σ) = J₀ := g.2
  have hs : ∀ S, e S • (1 : Matrix ι ι (AE F E)) + (1 - e S) • 1 = 1 := fun S => by
    rw [← add_smul, add_sub_cancel, one_smul]
  let u : Finset (HeightOneSpectrum (𝓞 F)) → GL ι (AE F E) := fun S =>
    ⟨mix (e S) g.1.1, mix (e S) g.1.inv, by rw [mix_mul (he S), g.1.val_inv, hs],
      by rw [mix_mul (he S), g.1.inv_val, hs]⟩
  have hu : ∀ S, u S ∈ UG (cA σ) J₀ := fun S => by
    show (mix (e S) g.1.1)ᵀ * J₀ * (mix (e S) g.1.1).map (cA σ) = J₀
    rw [mix_transpose, mix_map (cA σ) (hc S), mix_mul_mul (he S), hg,
      ← add_smul, add_sub_cancel, one_smul]
  refine ⟨fun S => ⟨u S, hu S⟩, fun S => rfl, ?_⟩
  refine (Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  refine Tendsto.prodMk_nhds (tendsto_mix_fin g.1.1) ?_
  exact (MulOpposite.continuous_op.tendsto _).comp (tendsto_mix_fin g.1.inv)

end GlobalTheory.UnitaryCutoff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntSmulIsAdicIntegralInTensorBasis
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_int_smul_mem_adicCompletionIntegers_of_elt (v : HeightOneSpectrum ℤ) (a : v.adicCompletion ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ (d : v.adicCompletion ℚ) * a ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨d, hd, h⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  rw [mul_comm]
  simpa using h

theorem exists_int_smul_isIntB : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M)
    (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] M), ∃ D : ℤ, D ≠ 0 ∧ IsIntB v b (D • y) := by
  intro M _ _ κ b v y
  choose d hd0 hd using exists_int_smul_mem_adicCompletionIntegers_of_elt v
  set c := (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y with hc
  refine ⟨∏ i ∈ c.support, d (c i), Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _, fun i => ?_⟩
  rw [map_zsmul, ← hc, Finsupp.smul_apply, zsmul_eq_mul]
  by_cases hi : i ∈ c.support
  · rw [← Finset.prod_erase_mul _ _ hi, Int.cast_mul, mul_assoc]
    exact mul_mem (intCast_mem _ _) (hd _)
  · rw [Finsupp.notMem_support_iff.mp hi, mul_zero]
    exact zero_mem _

end GlobalTheory.AdicSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerDenominatorNotMemOfValuationLeOne
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.IntegralDenom

theorem exists_denom_not_mem : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  intro E _ _ w a ha
  exact GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem w a ha

end GlobalTheory.IntegralDenom
end

