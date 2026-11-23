module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.MirPsiPair

section Det

variable {k : Type} [Field k]

theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  have hsub : (glEmbMat k n A).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    simp [glEmbMat]
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  simp [glEmbMat, hsub]

theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
  have htri : (((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    have hj : j ≠ Fin.last n := fun h => by
      subst h
      exact absurd hij' (not_lt.2 (Fin.le_last i))
    simp [unip, colMat, hj, one_apply, hij'.ne']
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  induction i using Fin.lastCases with
  | last => simp [unip, colMat]
  | cast i => simp [unip, colMat, Fin.castSucc_ne_last]

end Det

section Fix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thetaA_zero (ψ : AddChar k Circle) (n : ℕ) : thetaA k ψ (0 : Fin n → k) = 1 := by
  ext u
  simp [thetaA, chrA]

theorem unip_fixes (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) (n : ℕ) {V : Type}
    [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T)
    (hsub : Subsingleton (TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n)))
    (u : MirUin k (n + 1)) (v : V) : T (u : Mir k (n + 1)) v = v := by
  have htop : twKer T (MirUin k (n + 1)) (mirChar k ψ n) = ⊤ :=
    (Submodule.eq_top_iff' ).2 fun x => (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  have hall : ∀ a : Fin (n + 1) → k,
      T (u : Mir k (n + 1)) v - v ∈ twKer T (MirUin k (n + 1)) (thetaA k ψ a) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [thetaA_zero]
      exact Submodule.subset_span ⟨u, v, by simp⟩
    · obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.LinAlg.exists_GL_lastRow_eq k n a ha
      rw [← hm]
      refine (GlobalTheory.CompanionTheory.BZMirabolic.twKerConj k ψ (n + 1) V T (Pi.single (Fin.last n) 1) m _).2 ?_
      rw [← GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single k ψ n, htop]
      trivial
  exact sub_eq_zero.1 (GlobalTheory.CompanionTheory.MirFourier.fourier k ψ hψ h1 (n + 1) V T hT _ hall)

theorem psiMinus_mk {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (g : GL (Fin n) k) (v : V) :
    psiMinus k τ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (τ (levi k n g) v) := rfl

theorem detChar_unip (χ : kˣ →* ℂˣ) (n : ℕ) (u : MirUin k n) :
    detChar (Fin (n + 1)) χ ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hdet : Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
    ext
    rw [hv']
    simpa using det_unip n v
  rw [detChar_apply, hdet, map_one]

theorem detChar_levi (χ : kˣ →* ℂˣ) (n : ℕ) (g : GL (Fin n) k) :
    detChar (Fin (n + 1)) χ ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = detChar (Fin n) χ g := by
  have hdet : Matrix.GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) =
      Matrix.GeneralLinearGroup.det g := by
    ext
    exact det_glEmbMat n (g : Matrix (Fin n) (Fin n) k)
  rw [detChar_apply, detChar_apply, hdet]

end Fix

section Descent

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem exists_descent (N : Subgroup G) (T : Representation ℂ G V) (T' : Representation ℂ G V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hfix : ∀ (u : N) v, T (u : G) v = v)
    (hinv : ∀ (u : N) v x, B v (T' (u : G) x) = B v x) :
    ∃ B' : TwJacquet T N 1 →ₗ[ℂ] TwJacquet T' N 1 →ₗ[ℂ] ℂ,
      ∀ v v', B' (Submodule.Quotient.mk v) (Submodule.Quotient.mk v') = B v v' := by
  have hR : twKer T' N 1 ≤ LinearMap.ker B.flip := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, x, rfl⟩
    refine LinearMap.mem_ker.2 (LinearMap.ext fun v => ?_)
    simp [hinv u v x]
  let Bq := (twKer T' N 1).liftQ B.flip hR
  have hL : twKer T N 1 ≤ LinearMap.ker Bq.flip := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, x, rfl⟩
    simp [hfix u x]
  exact ⟨(twKer T N 1).liftQ Bq.flip hL, fun v v' => rfl⟩

end Descent


set_option maxHeartbeats 2000000 in
theorem pair_psi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    Subsingleton (TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n)) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) 1 →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (psiMinus k T g w) (psiMinus k T' g w') =
        ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ hψ h1 n s V V' _ _ _ _ T T' hT _ B hB hnd hsub
  have hfix := unip_fixes ψ hψ h1 n T hT hsub

  have hinv : ∀ (u : MirUin k (n + 1)) v x, B v (T' (u : Mir k (n + 1)) x) = B v x := by
    intro u v x
    have h := hB (u : Mir k (n + 1)) v x
    rw [hfix u v, detChar_unip] at h
    simpa using h
  obtain ⟨B', hB'⟩ := exists_descent (MirUin k (n + 1)) T T' B hfix hinv
  refine ⟨B', ?_, ?_⟩
  · intro g w w'
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    have h := hB (levi k (n + 1) g) v v'
    rw [detChar_levi] at h
    rw [psiMinus_mk, psiMinus_mk, hB', hB', h]
  · intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hv : v ≠ 0 := fun h => hw (by rw [h]; exact Submodule.Quotient.mk_zero _)
    obtain ⟨v', hv'⟩ := hnd v hv
    exact ⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩

end GlobalTheory.CompanionTheory.MirPsiPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

section Abs
variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

def IsBump (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (c : G) (v : W) (B : cIndSpace H ρ) : Prop :=
  (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * c * x) = ρ a v) ∧
    ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x) → B.1.1.1 g = 0

end Abs

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 100000 in
def sO (i t : ℕ) : Mir k (i + (t + 1)) →* Mir k ((i + 1) + t + 1) :=
  (sEmb k ((i + 1) + t)).comp (castM k (by omega : i + (t + 1) = (i + 1) + t)).toMonoidHom

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedParabolicMulEmbeddedMirabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Closed

open GlobalTheory.CompanionTheory.BZPhiPhi

section LinAlg

variable {k : Type} [Field k]

theorem exists_GL_row (N m : ℕ) (r : Fin (N + 1) → k) (hr0 : ∀ l : Fin (N + 1), l.val < m → r l = 0)
    (hr : r ≠ 0) :
    ∃ A : GL (Fin (N + 1)) k, (A : Matrix (Fin (N + 1)) (Fin (N + 1)) k) (Fin.last N) = r ∧
      ∀ i l : Fin (N + 1), m ≤ i.val → l.val < m → (A : Matrix (Fin (N + 1)) (Fin (N + 1)) k) i l = 0 := by
  classical
  obtain ⟨l0, hl0⟩ : ∃ l, r l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  have hml : m ≤ l0.val := by
    by_contra h
    exact hl0 (hr0 l0 (by omega))
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) k := (1 : Matrix _ _ k).updateRow l0 r
  have hB : B.det = r l0 := by
    have h1 := Matrix.cramer_apply (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k) r l0
    rw [Matrix.cramer_one] at h1
    have h2 := Matrix.updateRow_transpose (M := (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k)) (j := l0) (c := r)
    rw [Matrix.transpose_one] at h2
    show ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k).updateRow l0 r).det = r l0
    rw [h2, Matrix.det_transpose, ← h1]
    rfl
  let σ : Equiv.Perm (Fin (N + 1)) := Equiv.swap l0 (Fin.last N)
  let A : Matrix (Fin (N + 1)) (Fin (N + 1)) k := B.submatrix σ id
  have hA : A.det ≠ 0 := by
    have : A.det = _ := Matrix.det_permute σ B
    rw [this, hB]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, hl0]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, ?_, ?_⟩
  · funext l
    show B (σ (Fin.last N)) l = r l
    simp [σ, B]
  · intro i l hi hl
    show B (σ i) l = 0
    have hs : m ≤ (σ i).val := by
      simp only [σ, Equiv.swap_apply_def]
      split_ifs
      · have := Fin.is_lt l
        have h3 : l0.val ≤ N := by omega
        simp only [Fin.val_last]
        omega
      · exact hml
      · exact hi
    simp only [B, Matrix.updateRow_apply]
    split_ifs
    · exact hr0 l hl
    · rw [Matrix.one_apply_ne]
      intro e
      rw [e] at hs
      omega

theorem levi_val (n : ℕ) (A : GL (Fin n) k) :
    (((levi k n A : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (A : Matrix (Fin n) (Fin n) k) := rfl

theorem mirProj_val (n : ℕ) (g : Mir k n) (i l : Fin n) :
    ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l =
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc l) := rfl

theorem glEmbMat_last_cast (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (l : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc l) = 0 := by
  simp [glEmbMat]

theorem mirProj_levi_eq (n : ℕ) (A : GL (Fin n) k) : mirabolicProjection k n (levi k n A) = A := by
  ext i l
  rw [mirProj_val, levi_val]
  simp [glEmbMat]

theorem rowQ_ne_zero (n : ℕ) (p : Mir k (n + 1)) : rowQ k n p ≠ 0 := by
  intro h
  have key : vecMul (eLast k n) ((mirabolicProjection k (n + 1) p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      rowQ k n p := by
    rw [vecMul_eLast]
    rfl
  have h2 : eLast k n = 0 := by
    have h3 := congrArg (fun v => vecMul v ((((mirabolicProjection k (n + 1) p)⁻¹ : GL (Fin (n + 1)) k)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k)) key
    simp only [h, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, zero_vecMul] at h3
    exact h3
  have h4 := congrFun h2 (Fin.last n)
  simp [eLast] at h4

theorem entry_of_mirProj_eq_one (n : ℕ) (u : Mir k n) (hu : mirabolicProjection k n u = 1) (i l : Fin (n + 1))
    (hil : i ≠ l) (hl : l ≠ Fin.last n) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i l = 0 := by
  obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.2 hl
  induction i using Fin.lastCases with
  | last =>
    rw [(mem_Mir_iff k _).1 u.2]
    simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
  | cast i =>
    rw [← mirProj_val, hu]
    have : i ≠ l' := fun e => hil (by rw [e])
    simp [Matrix.one_apply, this]

theorem row_levi (n : ℕ) (y : Mir k n) (t : Fin (n + 2)) :
    (((levi k (n + 1) (y : GL (Fin (n + 1)) k) : Mir k (n + 1)) : GL (Fin (n + 2)) k) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) t =
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) t := by
  rw [levi_val]
  have hy := (mem_Mir_iff k _).1 y.2
  induction t using Fin.lastCases with
  | last => simp [glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last]
  | cast t =>
    simp only [glEmbMat, Fin.lastCases_castSucc]
    rw [hy]
    by_cases h : t = Fin.last n
    · subst h; simp [eLast]
    · have : (Fin.last n) ≠ t := fun e => h e.symm
      simp [eLast, Pi.single_apply, h, Matrix.one_apply, this]

end LinAlg

section Conc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_mirabolicParabolic_iff_lt (m j : ℕ) (g : Mir k (m + (j + 1))) :
    g ∈ MirabolicParabolic k m (j + 1) ↔ ∀ i l : Fin (m + (j + 1) + 1), m ≤ i.val → l.val < m →
      ((g : GL (Fin (m + (j + 1) + 1)) k) : Matrix (Fin (m + (j + 1) + 1)) (Fin (m + (j + 1) + 1)) k) i l = 0 := by
  rw [mem_mirabolicParabolic_iff]
  constructor
  · intro h i l hi hl
    have hb : i.val - m < j + 1 + 1 := by have := i.2; omega
    have h1 := h ⟨i.val - m, hb⟩ ⟨l.val, hl⟩
    have e1 : eGP m (j + 1) ⟨true, ⟨i.val - m, hb⟩⟩ = i := Fin.ext (by rw [blockIndex_true_val]; simp; omega)
    have e2 : eGP m (j + 1) ⟨false, ⟨l.val, hl⟩⟩ = l := Fin.ext (by rw [blockIndex_false_val])
    rwa [e1, e2] at h1
  · intro h b a
    apply h
    · rw [blockIndex_true_val]; omega
    · rw [blockIndex_false_val]; exact a.2

theorem set_eq (m j : ℕ) :
    {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} =
      {g | ∀ l : Fin (m + j + 1), l.val < m → rowQ k (m + j) g⁻¹ l = 0} := by
  ext g
  constructor
  · rintro ⟨h, hh, x, rfl⟩ l hl
    have e : (h * embedding₂ k (m + j) x)⁻¹ = embedding₂ k (m + j) x⁻¹ * h⁻¹ := by
      rw [_root_.mul_inv_rev, map_inv]
    rw [e]
    have hi := (mem_mirabolicParabolic_iff_lt k m j h⁻¹).1 (inv_mem hh)
    show ((embedding₂ k (m + j) x⁻¹).1.1 * (h⁻¹ : Mir k (m + j + 1)).1.1)
        (Fin.castSucc (Fin.last (m + j))) (Fin.castSucc l) = 0
    rw [Matrix.mul_apply]
    simp only [embedding₂, MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [row_levi, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hi _ _ (by simp) (by simpa using hl)
  · intro hg
    obtain ⟨A, hA1, hA2⟩ := exists_GL_row (m + j) m (rowQ k (m + j) g⁻¹) hg (rowQ_ne_zero _ _)
    let d : Mir k (m + (j + 1)) := levi k (m + j + 1) A
    have hd : d ∈ MirabolicParabolic k m (j + 1) := by
      rw [mem_mirabolicParabolic_iff_lt]
      intro i l hi hl
      have hl' : l ≠ Fin.last (m + j + 1) := by
        intro e; rw [e] at hl; simp at hl; omega
      obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.2 hl'
      show (levi k (m + j + 1) A).1.1 i _ = 0
      rw [levi_val]
      induction i using Fin.lastCases with
      | last => exact glEmbMat_last_cast _ _ _
      | cast i =>
        simp only [glEmbMat, Fin.lastCases_castSucc]
        exact hA2 i l' (by simpa using hi) (by simpa using hl)
    have rd : rowQ k (m + j) d = rowQ k (m + j) g⁻¹ := by
      funext l
      have : rowQ k (m + j) d l = (A : Matrix _ _ k) (Fin.last (m + j)) l := by
        show (levi k (m + j + 1) A).1.1 _ _ = _
        rw [levi_val]
        simp [glEmbMat]
      rw [this, hA1]
    have hq : g⁻¹ * d⁻¹ ∈ Q k (m + j) := mul_inv_mem_Q_of_rowQ_eq _ _ _ rd.symm
    have hq' : (g⁻¹ * d⁻¹)⁻¹ ∈ Q k (m + j) := inv_mem hq
    let y : Mir k (m + j) := ⟨mirabolicProjection k (m + j + 1) (g⁻¹ * d⁻¹)⁻¹, hq'⟩
    let u : Mir k (m + j + 1) := (g⁻¹ * d⁻¹)⁻¹ * (embedding₂ k (m + j) y)⁻¹
    have hu : mirabolicProjection k (m + j + 1) u = 1 := by
      simp only [u, map_mul, map_inv (mirabolicProjection k (m + j + 1)) (embedding₂ k (m + j) y)]
      have : mirabolicProjection k (m + j + 1) (embedding₂ k (m + j) y) = mirabolicProjection k (m + j + 1) (g⁻¹ * d⁻¹)⁻¹ :=
        mirProj_levi_eq _ _
      rw [this]
      simp
    have huH : u ∈ MirabolicParabolic k m (j + 1) := by
      rw [mem_mirabolicParabolic_iff_lt]
      intro i l hi hl
      refine entry_of_mirProj_eq_one _ u hu i l ?_ ?_
      · intro e; rw [e] at hi; omega
      · intro e; rw [e] at hl; simp at hl; omega
    refine ⟨d⁻¹ * u, mul_mem (inv_mem hd) huH, y, ?_⟩
    simp only [u]
    group

theorem isClosed_HGP_iota (m j : ℕ) :
    IsClosed {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  rw [set_eq]
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun l => isClosed_iInter fun _ =>
    isClosed_eq (((continuous_apply l).comp (continuous_rowQ (m + j))).comp continuous_inv) continuous_const

end Conc

end GlobalTheory.CompanionTheory.LeibPhi.Closed

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRegEllIffMemEll
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.NormPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem norm_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    (d * u⁻¹) * thE E n (d * u⁻¹) = nrm d := by
  obtain ⟨h1, h2⟩ := hu
  have hθ : thetaE E n u = u⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [h1, map_mul, map_inv, hθ, inv_inv, nrm]
  group

theorem polE_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    polE (d * u⁻¹) = (nrm d).val.charpoly := by
  rw [polE, norm_translate hu]

theorem map_thetaE (τ : E →+* ℂ) (d : GL (Fin n) E) :
    GeneralLinearGroup.map τ (thetaE E n d) =
      thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d) := by
  apply Units.ext
  ext i j
  have hv : ∀ g : GL (Fin n) E, ((GeneralLinearGroup.map τ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = g.val.map τ := fun _ => rfl
  rw [hv, thetaR_val, thetaR_val, ← map_inv, hv]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  exact IsCMField.complexEmbedding_complexConj E τ _

theorem charpoly_map_nrm (τ : E →+* ℂ) (d : GL (Fin n) E) :
    (GeneralLinearGroup.map τ d * thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d)).val.charpoly =
      (nrm d).val.charpoly.map τ := by
  rw [← map_thetaE, ← map_mul, ← Matrix.charpoly_map]
  rfl

theorem isRegEll_iff_mem_Ell (d : GL (Fin n) E) : IsRegEll d ↔ (nrm d).val.charpoly ∈ Ell E n := by
  have hm : (nrm d).val.charpoly.Monic := Matrix.charpoly_monic _
  constructor
  · intro h
    refine ⟨hm, by simp, h.1, fun τ z hz => ?_⟩
    exact h.2 τ z (Polynomial.isRoot_of_mem_roots hz)
  · rintro ⟨-, -, hs, hr⟩
    exact ⟨hs, fun τ z hz => hr τ z ((Polynomial.mem_roots (hm.map τ).ne_zero).2 hz)⟩

theorem polEq : PolEq := by
  intro E _ _ _ n u hu d
  rw [polE_translate hu]
  refine ⟨isRegEll_iff_mem_Ell d, fun v => ⟨charpoly_map_nrm v.embedding d, fun h => ?_⟩⟩
  unfold EllC
  rw [charpoly_map_nrm]
  exact ⟨h.1.map, fun z hz => h.2 v.embedding z hz⟩

end GlobalTheory.CompanionTheory.NormPoly
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotentStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_of_simple_lowering_nilpotent : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n), IsAdW μ x → (∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) → x ∉ Jp n → (j : ℕ) = i + 1 → (∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) → ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | exact GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | (intros; apply GlobalTheory.CompanionTheory.PresRho.natural_of_primitive <;> assumption)
end

