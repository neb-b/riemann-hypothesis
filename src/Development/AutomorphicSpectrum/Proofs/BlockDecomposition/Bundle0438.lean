module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPositiveHermitianForm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.TraceHerm

def toep {K : Type} [CommRing K] {n : ℕ} (M M' : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun j k => Matrix.trace (M ^ (k : ℕ) * M' ^ (j : ℕ))

theorem toep_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ} (f : K →+* L) (M M' : Matrix (Fin n) (Fin n) K) :
    (toep M M').map f = toep (M.map f) (M'.map f) := by
  ext j k
  simp only [toep, Matrix.map_apply, Matrix.of_apply]
  rw [← Matrix.map_pow, ← Matrix.map_pow, ← Matrix.map_mul]
  exact AddMonoidHom.map_trace f.toAddMonoidHom _

theorem pow_mul_eq {n : ℕ} {A T : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ} (h : A * T = T * diagonal z) (k : ℕ) :
    A ^ k * T = T * diagonal (fun i => z i ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h, Matrix.mul_assoc, diagonal_mul_diagonal]
    congr 2
    ext i
    rw [pow_succ']

theorem core {n : ℕ} (A A' T : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) (v : Fin n → ℂ) (hAA : A' * A = 1)
    (hT : A * T = T * diagonal z) (hv : v = T *ᵥ 1) (hz : ∀ i, ‖z i‖ = 1)
    (hB : (GlobalTheory.ClassParam.krylov A v).det ≠ 0) :
    (((GlobalTheory.ClassParam.krylov A v)⁻¹)ᴴ * toep A A' * (GlobalTheory.ClassParam.krylov A v)⁻¹).PosDef ∧
      Aᴴ * (((GlobalTheory.ClassParam.krylov A v)⁻¹)ᴴ * toep A A' * (GlobalTheory.ClassParam.krylov A v)⁻¹) * A =
        ((GlobalTheory.ClassParam.krylov A v)⁻¹)ᴴ * toep A A' * (GlobalTheory.ClassParam.krylov A v)⁻¹ := by
  set B := GlobalTheory.ClassParam.krylov A v with hBdef
  let V : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => z i ^ (k : ℕ)
  let zc : Fin n → ℂ := fun i => starRingEnd ℂ (z i)
  have hzz : ∀ i, z i * zc i = 1 := by
    intro i
    simp only [zc]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz i]
    simp
  have hDD : diagonal z * diagonal zc = 1 := by
    rw [diagonal_mul_diagonal]
    simp [hzz]
  have hBTV : B = T * V := by
    ext i k
    have h1 := pow_mul_eq hT (k : ℕ)
    have h2 : ((A ^ (k : ℕ)) *ᵥ v) = (T * diagonal (fun i => z i ^ (k : ℕ))) *ᵥ 1 := by
      rw [hv, Matrix.mulVec_mulVec, h1]
    simp only [hBdef, GlobalTheory.ClassParam.krylov, Matrix.of_apply]
    rw [h2]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, V, Matrix.diagonal_apply]
  have hdet : T.det * V.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hBTV]; exact hB
  have hTd : IsUnit T.det := (isUnit_iff_ne_zero).2 (left_ne_zero_of_mul hdet)
  have hVd : IsUnit V.det := (isUnit_iff_ne_zero).2 (right_ne_zero_of_mul hdet)
  have hA' : A' * T = T * diagonal zc := by
    calc A' * T = A' * (T * (diagonal z * diagonal zc)) := by rw [hDD, Matrix.mul_one]
      _ = A' * A * T * diagonal zc := by
          rw [Matrix.mul_assoc A' A T, hT]; simp only [Matrix.mul_assoc]
      _ = T * diagonal zc := by rw [hAA, Matrix.one_mul]
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hTd
  have hTT' : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ hTd
  have hG : toep A A' = Vᴴ * V := by
    ext j k
    have h1 : A ^ (k : ℕ) * A' ^ (j : ℕ) * T =
        T * diagonal (fun i => z i ^ (k : ℕ) * zc i ^ (j : ℕ)) := by
      rw [Matrix.mul_assoc, pow_mul_eq hA', ← Matrix.mul_assoc, pow_mul_eq hT, Matrix.mul_assoc,
        diagonal_mul_diagonal]
    have h2 : A ^ (k : ℕ) * A' ^ (j : ℕ) =
        T * (diagonal (fun i => z i ^ (k : ℕ) * zc i ^ (j : ℕ)) * T⁻¹) := by
      rw [← Matrix.mul_assoc, ← h1, Matrix.mul_assoc, hTT, Matrix.mul_one]
    simp only [toep, Matrix.of_apply]
    rw [h2, Matrix.trace_mul_comm, Matrix.mul_assoc, hTT', Matrix.mul_one, Matrix.trace_diagonal]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply, zc]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have hQ : V * B⁻¹ = T⁻¹ := by
    rw [hBTV, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hVd, Matrix.one_mul]
  have hP : (B⁻¹)ᴴ * toep A A' * B⁻¹ = (T⁻¹)ᴴ * T⁻¹ := by
    rw [hG, ← hQ, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hP]
  have hQA : T⁻¹ * A = diagonal z * T⁻¹ := by
    calc T⁻¹ * A = T⁻¹ * A * (T * T⁻¹) := by rw [hTT, Matrix.mul_one]
      _ = T⁻¹ * (A * T) * T⁻¹ := by simp only [Matrix.mul_assoc]
      _ = diagonal z * T⁻¹ := by rw [hT, ← Matrix.mul_assoc, hTT', Matrix.one_mul]
  refine ⟨Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_), ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).2 (by rw [Matrix.det_nonsing_inv]; simpa using hTd)
  · have hDc : (diagonal z)ᴴ * diagonal z = 1 := by
      rw [Matrix.diagonal_conjTranspose, diagonal_mul_diagonal]
      have h1 : (fun i => (star z) i * z i) = fun _ => (1 : ℂ) :=
        funext fun i => by rw [Pi.star_apply, mul_comm]; exact hzz i
      rw [h1]
      exact diagonal_one
    calc Aᴴ * ((T⁻¹)ᴴ * T⁻¹) * A = (T⁻¹ * A)ᴴ * (T⁻¹ * A) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (T⁻¹)ᴴ * ((diagonal z)ᴴ * diagonal z) * T⁻¹ := by
          rw [hQA, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (T⁻¹)ᴴ * T⁻¹ := by rw [hDc, Matrix.mul_one]

theorem exists_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hs : A.charpoly.Separable) (v : Fin n → ℂ) :
    ∃ (T : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ),
      A * T = T * diagonal z ∧ v = T *ᵥ 1 ∧ ∀ i, z i ∈ A.charpoly.roots := by
  have hnd : A.charpoly.roots.Nodup := nodup_roots hs
  have hcard := splits_iff_card_roots.1 (IsAlgClosed.splits A.charpoly)
  have hdeg : A.charpoly.natDegree = n := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  set s := A.charpoly.roots.toFinset with hs_def
  have hsc : Fintype.card s = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard, hdeg]
  let e := Fintype.equivFinOfCardEq hsc
  let z : Fin n → ℂ := fun a => ((e.symm a : s) : ℂ)
  have hprod : A.charpoly = ∏ a, (X - C (z a)) := by
    rw [Equiv.prod_comp e.symm (fun r : s => X - C (r : ℂ)), Finset.prod_coe_sort s (fun r => X - C r),
      Finset.prod_eq_multiset_prod, hs_def, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd,
      prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _) hcard]
  have hch : (diagonal z).charpoly = A.charpoly := by rw [charpoly_diagonal, hprod]
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := diagonal z) (N := A)
    (by rw [GlobalTheory.Orb.IsRegSS, hch]; exact hs) hch.symm
  let w : Fin n → ℂ := ((x⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v
  refine ⟨(x : Matrix (Fin n) (Fin n) ℂ) * diagonal w, z, ?_, ?_, fun i => ?_⟩
  · rw [← Matrix.mul_assoc, hx, Matrix.mul_assoc, Matrix.mul_assoc, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2
    ext i
    exact mul_comm _ _
  · have h1 : diagonal w *ᵥ (1 : Fin n → ℂ) = w := by
      ext i
      simp [Matrix.mulVec_diagonal]
    rw [← Matrix.mulVec_mulVec, h1]
    simp only [w]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
    simp
  · have : (e.symm i : ℂ) ∈ s := (e.symm i).2
    exact Multiset.mem_toFinset.1 this

theorem exists_posDef_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (N : GL (Fin n) E),
  N.val.charpoly.Separable → (∀ τ : E →+* ℂ, ∀ z ∈ (N.val.charpoly.map τ).roots, ‖z‖ = 1) →
  ∃ H : Matrix (Fin n) (Fin n) E, IsUnit H.det ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
    N ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ ∀ τ : E →+* ℂ, (H.map τ).PosDef := by
  intro E _ _ _ n N hs hr
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hc
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field N.val hs
  set B := GlobalTheory.ClassParam.krylov N.val v with hB
  set N' : Matrix (Fin n) (Fin n) E := ((N⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hN'
  have hN'N : N' * N.val = 1 := by
    rw [hN', ← Units.val_mul, inv_mul_cancel]; rfl
  have hcT : ∀ (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) E), (cT c M).map τ = (M.map τ)ᴴ := by
    intro τ M
    ext i j
    simp only [cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    exact IsCMField.complexEmbedding_complexConj E τ (M j i)
  have hinv : ∀ τ : E →+* ℂ, (B⁻¹).map τ = (B.map τ)⁻¹ := by
    intro τ
    have h1 : (B⁻¹).map τ * B.map τ = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ ((isUnit_iff_ne_zero).2 hv)]
      simp
    exact (Matrix.inv_eq_left_inv h1).symm
  let H : Matrix (Fin n) (Fin n) E := cT c B⁻¹ * toep N.val N' * B⁻¹
  have hkey : ∀ τ : E →+* ℂ, (H.map τ).PosDef ∧ (N.val.map τ)ᴴ * H.map τ * N.val.map τ = H.map τ := by
    intro τ
    have hHτ : H.map τ = ((GlobalTheory.ClassParam.krylov (N.val.map τ) (τ ∘ v))⁻¹)ᴴ *
        toep (N.val.map τ) (N'.map τ) * (GlobalTheory.ClassParam.krylov (N.val.map τ) (τ ∘ v))⁻¹ := by
      simp only [H]
      rw [Matrix.map_mul, Matrix.map_mul, hcT, toep_map, hinv, hB, GlobalTheory.ClassParam.krylov_map]
    have hsτ : (N.val.map τ).charpoly.Separable := by
      rw [Matrix.charpoly_map]; exact hs.map
    obtain ⟨T, z, h1, h2, h3⟩ := exists_diag (N.val.map τ) hsτ (τ ∘ v)
    have hz : ∀ i, ‖z i‖ = 1 := fun i => hr τ (z i) (by rw [← Matrix.charpoly_map]; exact h3 i)
    have hdet : (GlobalTheory.ClassParam.krylov (N.val.map τ) (τ ∘ v)).det ≠ 0 := by
      rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero τ).2 hv
    rw [hHτ]
    exact core _ _ T z _ (by rw [← Matrix.map_mul, hN'N]; simp) h1 h2 hz hdet
  have hhermτ : ∀ τ : E →+* ℂ, (cT c H).map τ = H.map τ := fun τ => by
    rw [hcT]; exact (hkey τ).1.isHermitian.eq
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) E => M.map τ₀) :=
    Matrix.map_injective τ₀.injective
  refine ⟨H, ?_, hinj (hhermτ τ₀), ?_, fun τ => (hkey τ).1⟩
  · have h := (hkey τ₀).1.det_pos.ne'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
    exact (isUnit_iff_ne_zero).2 (fun h0 => h (by rw [h0, map_zero]))
  · change cT c N.val * H * N.val = H
    apply hinj
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, hcT]
    exact (hkey τ₀).2

end GlobalTheory.CompanionTheory.TraceHerm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFibreFunctionsCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibFin

theorem finite_image_of_rightInvariant {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) (hS : IsOpen (S : Set G)) {K : Set G} (hK : IsCompact K) (F : G → X)
    (hF : ∀ g, ∀ s ∈ S, F (g * s) = F g) : (F '' K).Finite := by
  have hcover : K ⊆ ⋃ g : K, (fun x => (g : G) * x) '' (S : Set G) := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, 1, S.one_mem, mul_one x⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun g : K => (fun x => (g : G) * x) '' (S : Set G))
    (fun g => (Homeomorph.mulLeft (g : G)).isOpenMap _ hS) hcover
  apply (T.finite_toSet.image (fun g : K => F g)).subset
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (hT hx)
  obtain ⟨s, hs, rfl⟩ := hxg
  exact ⟨g, hg, (hF g s hs).symm⟩

theorem finite_fibV_image (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) :
    ((fun κ : GL (Fin (i + t)) k => fibV f κ) ''
      (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
  have hst : IsOpen {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} :=
    GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd (GlobalTheory.BZMir.Leib.HPG k i t)
      (GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ) f
  let H : Subgroup (GL (Fin (i + t)) k) :=
    { carrier := {g | ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * g) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ}
      mul_mem' := by
        intro a b ha hb κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        have hb' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * b) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := hb
        rw [← mul_assoc, hb', ha']
      one_mem' := by
        intro κ
        rw [mul_one]
      inv_mem' := by
        intro a ha κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        rw [← ha' (κ * a⁻¹), mul_assoc, inv_mul_cancel, mul_one] }
  have hcont := GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k (i + t)
  have hO := hcont.isOpen_preimage _ hst
  have hone : (1 : GL (Fin (i + t)) k) ∈ GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} := by
    show GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) 1) f = f
    rw [map_one, map_one]
    rfl
  have hsub : GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} ⊆ (H : Set _) := by
    intro g hg κ
    have hg' : GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) g) f = f := hg
    funext v
    have h1 := congrArg (fun φ => GlobalTheory.CompanionTheory.BZPsiPG.fibV φ κ v) hg'
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.fibV, map_mul, ← mul_assoc] at h1 ⊢
    exact h1
  have hHopen : IsOpen (H : Set (GL (Fin (i + t)) k)) :=
    Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds hone) hsub)
  have hF : ∀ g : GL (Fin (i + t)) k, ∀ s ∈ H,
      GlobalTheory.CompanionTheory.BZPsiPG.fibV f (g * s) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f g := fun g s hs => hs g
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_image_of_rightInvariant H hHopen GlobalTheory.SplitFlip.isCompact_KO _ hF

end GlobalTheory.CompanionTheory.BZPsiPG.FibFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecomposition
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl Formalism.L2.Host

namespace GlobalTheory.CompanionTheory.CuspTwist

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def conjChi (a : ℕ) (χ : HChar E) : Module.End ℂ (Sm E a) ≃ₐ[ℂ] Module.End ℂ (Sm E a) :=
  LinearEquiv.conjAlgEquiv ℂ (mulChi a χ)

theorem conjChi_apply (χ : HChar E) (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjChi a χ z (mulChi a χ φ) = mulChi a χ (z φ) := by
  simp [conjChi, LinearEquiv.conjAlgEquiv_apply]

theorem conjChi_cap (χ : HChar E) (τ : E →+* ℂ) (u : ℂ) :
    conjChi a χ (cap τ (u + expo χ τ)) = cap τ u := by
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨φ, rfl⟩ := (mulChi a χ).surjective ψ
  rw [conjChi_apply, cap_mulChi]

theorem map_Zalg (χ : HChar E) : (Zalg E a).map (conjChi a χ : _ →ₐ[ℂ] _) = Zalg E a := by
  rw [Zalg, AlgHom.map_adjoin]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨τ, u, rfl⟩, rfl⟩
    exact ⟨τ, u - expo χ τ, by
      have := conjChi_cap (a := a) χ τ (u - expo χ τ)
      rw [sub_add_cancel] at this
      exact this⟩
  · rintro ⟨τ, u, rfl⟩
    exact ⟨_, ⟨τ, u + expo χ τ, rfl⟩, conjChi_cap χ τ u⟩

theorem cofin_conj (χ : HChar E) {J : Set (Module.End ℂ (Sm E a))} (hJ : Cofin J) :
    Cofin (conjChi a χ '' J) := by
  obtain ⟨hsub, V, hV, hz⟩ := hJ
  have hm : ∀ z ∈ Zalg E a, conjChi a χ z ∈ Zalg E a := fun z h => by
    rw [← map_Zalg (a := a) χ]
    exact ⟨z, h, rfl⟩
  refine ⟨?_, V.map (conjChi a χ).toLinearMap, inferInstance, fun z h => ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact hm _ (hsub hj)
  · rw [← map_Zalg (a := a) χ] at h
    obtain ⟨w, hw, rfl⟩ := h
    have h1 := Submodule.mem_map_of_mem (f := (conjChi a χ).toLinearMap) (hz w hw)
    rw [Submodule.map_sup, Submodule.map_span] at h1
    obtain ⟨y, hy, y', hy', e⟩ := Submodule.mem_sup.1 h1
    refine Submodule.mem_sup.2 ⟨y, hy, y', Submodule.span_mono ?_ hy', e⟩
    rintro _ ⟨_, ⟨x, hx, j, hj, rfl⟩, rfl⟩
    exact ⟨conjChi a χ x, hm _ hx, conjChi a χ j, ⟨j, hj, rfl⟩, map_mul (conjChi a χ) x j⟩

theorem chiDet_absC_cpt (s : ℂ) (k : Kinf E a) :
    chiDet a (Model.absC E s) (infGL E a (Unitary.toUnits k)) = 1 := by
  have h1 : chiDet a (Model.absC E s) (infGL E a (Unitary.toUnits k)) =
      (Model.absC E s).1 (infId E (Matrix.GeneralLinearGroup.det (Unitary.toUnits k))) :=
    congrArg (Model.absC E s).1 (det_infGL _)
  rw [h1]
  refine Units.ext ?_
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E _)) = 1
  rw [Model.logNorm_infId]
  have hd : star (k.1.det) * k.1.det = 1 := (Matrix.det_of_mem_unitary k.2).1
  have hn : ∀ w, ‖(k.1.det : Cinf E) w‖ = 1 := fun w => by
    have := congrFun hd w
    have h2 : ‖(k.1.det : Cinf E) w‖ * ‖(k.1.det : Cinf E) w‖ = 1 := by
      have h3 := congrArg norm this
      simpa using h3
    nlinarith [norm_nonneg ((k.1.det : Cinf E) w)]
  have e : ∀ w, ‖((Matrix.GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) w‖ = 1 := hn
  simp [hn]

theorem dchi_absC_trace (s : ℂ) :
    dchi (Model.absC E s) (Matrix.of (oneL E a)).trace = s * (a * (2 * Fintype.card (InfinitePlace E))) := by
  have e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E) := by
    change Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _
    simp
  rw [e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one]
  simp
  ring

theorem twist_central : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W),
    GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ c : ℂ,
    ∃ (χ : Formalism.L2.Host.HChar E) (L' : Subgroup (GL (Fin a) (Af E))) (J' : Set (Module.End ℂ (Sm E a))),
      IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ Cofin J' ∧ ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 →
        lie E a (oneL E a) φ = c • φ →
        mulChi a χ φ ∈ genSpace L' ρ J' ∧ IsCuspidal (mulChi a χ φ).1 ∧ lie E a (oneL E a) (mulChi a χ φ) = 0 := by
  intro E _ _ _ a ha L hL W _ _ _ ρ _ J hJ c
  have hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set s : ℂ := -c / (a * (2 * Fintype.card (InfinitePlace E))) with hs
  have hd : dchi (Model.absC E s) (Matrix.of (oneL E a)).trace = -c := by
    rw [dchi_absC_trace, hs]
    field_simp
  refine ⟨Model.absC E s, L ⊓ GlobalTheory.Published.AutFinGL.Model.kerL a (Model.absC E s), conjChi a (Model.absC E s) '' J,
    ?_, cofin_conj _ hJ, fun φ hφ hc he => ⟨⟨(IsCuspForm.mulChi (⟨hφ.1, hc⟩ : IsCuspForm φ) _).1, fun k hk => ?_, fun g => ?_, ?_⟩, ?_, ?_⟩⟩
  · exact hL.inter (GlobalTheory.Published.AutFinGL.Model.isOpen_kerL _)
  · have h2 : chiDet a (Model.absC E s) (finGL E a k) = 1 := hk.2
    change rt E a (finGL E a k) _ = _
    rw [rt_mulChi, h2, Units.val_one, one_smul]
    exact congrArg (mulChi a (Model.absC E s)) (hφ.2.1 k hk.1)
  · have h3 := hφ.2.2.1 g
    have e : (fun k : Kinf E a => (cptRep E a k (mulChi a (Model.absC E s) φ)).1 g) =
        ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) • fun k : Kinf E a => (cptRep E a k φ).1 g := by
      funext k
      change (mulChi a (Model.absC E s) φ).1 (g * infGL E a (Unitary.toUnits k)) =
        ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) * φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mulChi_apply, map_mul, chiDet_absC_cpt, mul_one, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ _ h3
  · rintro _ ⟨j, hj, rfl⟩
    rw [conjChi_apply, hφ.2.2.2 j hj, map_zero]
  · exact (IsCuspForm.mulChi (⟨hφ.1, hc⟩ : IsCuspForm φ) _).2
  · rw [lie_mulChi, he, hd, neg_smul, add_neg_cancel, map_zero]

end GlobalTheory.CompanionTheory.CuspTwist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteHalfOfTwist
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinHalfAsm

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

theorem cptPart_le' {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T := by
  unfold GlobalTheory.BCT.cptPart
  exact (Subgroup.closure_le _).mpr fun t ht => ht.1

theorem mass_inf_twCent {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (Γ : Subgroup G) (δ : G) :
    mass θ (Γ ⊓ twCent θ δ) δ = mass θ Γ δ := by
  have h1 : (Γ ⊓ GlobalTheory.BCT.twCent θ δ).subgroupOf (GlobalTheory.BCT.twCent θ δ) = Γ.subgroupOf (GlobalTheory.BCT.twCent θ δ) :=
    Subgroup.inf_subgroupOf_right _ _
  have h2 : Γ ⊓ GlobalTheory.BCT.twCent θ δ ⊓ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)
      = Γ ⊓ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ) := by
    rw [inf_assoc, inf_eq_right.mpr (cptPart_le' _)]
  unfold GlobalTheory.BCT.mass
  rw [h1, h2]

theorem index_rStab_orbit {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K U : Subgroup G)
    (f : G → ℂ) (δ : G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G))
    (hf : ∀ u ∈ U, ∀ y, f (u⁻¹ * y * θ u) = f y) (x : G) :
    (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hU.preimage continuous_subtype_val
  have hle : U.subgroupOf K ≤ GlobalTheory.BCT.rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k)) := by
    intro k' hk'
    rw [Subgroup.mem_subgroupOf] at hk'
    change ∀ y : K, f ((x * ↑(y * k'))⁻¹ * δ * θ (x * ↑(y * k'))) = f ((x * ↑y)⁻¹ * δ * θ (x * ↑y))
    intro y
    rw [← hf (k' : G) hk' ((x * ↑y)⁻¹ * δ * θ (x * ↑y))]
    congr 1
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI := Subgroup.finiteIndex_of_le hle
  exact Subgroup.FiniteIndex.index_ne_zero

theorem range_pair (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) :
    ((ratF E a).prodMap (ratF E b)).range = (ratF E a).range.prod (ratF E b).range := by
  exact MonoidHom.range_prodMap _ _

theorem finHalfOf : FinHalfOf := by
  unfold PositivityTheory.Rg.BcB.G8.Fin.FinHalfOf PositivityTheory.Rg.BcB.G8.Fin.DcCount PositivityTheory.Rg.BcB.G8.Fin.MassProd
    PositivityTheory.Rg.BcB.G8.Fin.RatFin PositivityTheory.Rg.BcB.G8.Fin.SuppFin PositivityTheory.Rg.BcB.G8.Fin.EulerFin
    PositivityTheory.Rg.BcB.G8.KfOC PositivityTheory.Rg.BcB.G8.FinLevel PositivityTheory.Rg.BcB.G8.FinHalf
  intro hDc hMP hRat hSupp hEuler hKf hFL E _ _ _ hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2
  obtain ⟨hGood, hfin1, hfin2, hfin3⟩ := hRat E hUnr a b δ₁ δ₂ h1 h2
  obtain ⟨hsupp, hsuppG⟩ := hSupp E hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2
  obtain ⟨U, hUo, hUinv⟩ := hFL E hUnr a b S φ₁ φ₂ hT1 hT2
  have hKo : IsOpen (((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b) :
      Subgroup (PositivityTheory.Rg.BcB.G8.Gf E a b)) : Set (PositivityTheory.Rg.BcB.G8.Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact (hKf E a).1.prod (hKf E b).1
  have hKc : IsCompact (((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b) :
      Subgroup (PositivityTheory.Rg.BcB.G8.Gf E a b)) : Set (PositivityTheory.Rg.BcB.G8.Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact (hKf E a).2.prod (hKf E b).2
  have hdc := hDc (PositivityTheory.Rg.BcB.G8.Gf E a b) (PositivityTheory.Rg.BcB.G8.thP E a b)
    ((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b)) (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
    ((GlobalTheory.BCT.ratF E a) δ₁, (GlobalTheory.BCT.ratF E b) δ₂) (PositivityTheory.Rg.BcB.G8.finFn S φ₁ φ₂)
    hKo hKc hGood inf_le_right hfin1 hfin2 hfin3
    (fun x0 => index_rStab_orbit _ _ U _ _ hKc hUo hUinv (x0 : PositivityTheory.Rg.BcB.G8.Gf E a b)) hsupp
  have hdc' : PositivityTheory.Rg.BcB.G8.dcSum (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
      ((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b)) (PositivityTheory.Rg.BcB.G8.orbFn S φ₁ φ₂ δ₁ δ₂) = _ := hdc
  have hmass : GlobalTheory.BCT.mass (PositivityTheory.Rg.BcB.G8.thP E a b) (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
      ((GlobalTheory.BCT.ratF E a) δ₁, (GlobalTheory.BCT.ratF E b) δ₂) =
      GlobalTheory.BCT.mass (GlobalTheory.BCT.thF E a) (GlobalTheory.BCT.ratF E a).range ((GlobalTheory.BCT.ratF E a) δ₁) *
        GlobalTheory.BCT.mass (GlobalTheory.BCT.thF E b) (GlobalTheory.BCT.ratF E b).range ((GlobalTheory.BCT.ratF E b) δ₂) := by
    unfold PositivityTheory.Rg.BcB.G8.gam
    rw [mass_inf_twCent, range_pair]
    exact hMP _ _ (GlobalTheory.BCT.thF E a) (GlobalTheory.BCT.thF E b) _ _ _ _
  refine ⟨hsuppG, hfin1, ?_⟩
  rw [hdc', hmass, hEuler E hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2]

end GlobalTheory.CompanionTheory.FinHalfAsm

end
end

