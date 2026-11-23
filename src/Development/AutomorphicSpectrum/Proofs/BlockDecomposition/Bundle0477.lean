module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0473
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0420
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesOneParameterFlow
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Flow

section Abstract

variable {A : Type} [Ring A] [Algebra ℂ A]

def HD (f f' : ℝ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (p p' : ι → ℝ → ℂ) (C : ι → A),
    (∀ i s, HasDerivAt (p i) (p' i s) s) ∧ (∀ s, f s = ∑ i, p i s • C i) ∧ ∀ s, f' s = ∑ i, p' i s • C i

theorem HD.congr {f f' g g' : ℝ → A} (h : HD f f') (e : ∀ s, g s = f s) (e' : ∀ s, g' s = f' s) : HD g g' := by
  obtain ⟨ι, i, p, p', C, h1, h2, h3⟩ := h
  exact ⟨ι, i, p, p', C, h1, fun s => (e s).trans (h2 s), fun s => (e' s).trans (h3 s)⟩

theorem HD.const (C : A) : HD (fun _ => C) (fun _ => 0) :=
  ⟨Unit, inferInstance, fun _ _ => 1, fun _ _ => 0, fun _ => C, fun _ s => hasDerivAt_const s 1, by simp, by simp⟩

theorem HD.add {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s + g s) (fun s => f' s + g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim p q, Sum.elim p' q', Sum.elim C D, ?_, ?_, ?_⟩
  · rintro (i | j) s
    · exact h1 i s
    · exact k1 j s
  · intro s; simp [h2, k2]
  · intro s; simp [h3, k3]

theorem HD.mul {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s * g s) (fun s => f' s * g s + f s * g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι × κ, inferInstance, fun x s => p x.1 s * q x.2 s,
    fun x s => p' x.1 s * q x.2 s + p x.1 s * q' x.2 s, fun x => C x.1 * D x.2, ?_, ?_, ?_⟩
  · intro x s; exact (h1 x.1 s).mul (k1 x.2 s)
  · intro s
    simp only [h2, k2, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm]
  · intro s
    simp only [h2, h3, k2, k3, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm, add_smul,
      Finset.sum_add_distrib]

theorem HD.const_of_zero {f : ℝ → A} (h : HD f (fun _ => 0)) (l : A →ₗ[ℂ] ℂ) (s t : ℝ) : l (f s) = l (f t) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  have hd : ∀ s, HasDerivAt (fun s => l (f s)) 0 s := by
    intro s
    have h4 : HasDerivAt (fun s => ∑ i, p i s * l (C i)) (∑ i, p' i s * l (C i)) s :=
      HasDerivAt.fun_sum fun i _ => (h1 i s).mul_const _
    have e1 : (fun s => l (f s)) = fun s => ∑ i, p i s * l (C i) := by
      funext s; simp [h2, map_sum]
    have e2 : ∑ i, p' i s * l (C i) = 0 := by
      have := congrArg l (h3 s)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum] using this.symm
    rw [e1]
    rwa [e2] at h4
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) s t

theorem hd_adjoin (R Q : ℝ → A) (hRQ : ∀ s, R s * Q s = 1) (hQR : ∀ s, Q s * R s = 1) (L : A) (G : Set A)
    (hG : ∀ B ∈ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s)) :
    ∀ B ∈ Algebra.adjoin ℂ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s) := by
  have hmul : ∀ s x y, R s * x * Q s * (R s * y * Q s) = R s * (x * y) * Q s := by
    intro s x y
    calc R s * x * Q s * (R s * y * Q s) = R s * x * (Q s * R s) * y * Q s := by simp only [mul_assoc]
      _ = R s * (x * y) * Q s := by rw [hQR]; simp only [mul_assoc, mul_one]
  intro B hB
  induction hB using Algebra.adjoin_induction with
  | mem x hx => exact hG x hx
  | algebraMap r =>
    refine (HD.const (algebraMap ℂ A r)).congr (fun s => ?_) (fun s => ?_)
    · rw [← Algebra.commutes, mul_assoc, hRQ, mul_one]
    · rw [Algebra.commutes, sub_self]; simp
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr (fun s => ?_) (fun s => ?_)
    · noncomm_ring
    · noncomm_ring
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr (fun s => ?_) (fun s => ?_)
    · rw [hmul]
    · rw [hmul, hmul, ← add_mul, ← mul_add]
      congr 2
      noncomm_ring

end Abstract

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem Zalg_le : Zalg E a ≤ Algebra.adjoin ℂ (Set.range (lie E a)) := by
  set S := Algebra.adjoin ℂ (Set.range (lie E a)) with hSdef
  have hL : ∀ X, lie E a X ∈ S := fun X => Algebra.subset_adjoin ⟨X, rfl⟩
  have hS : ∀ i j x, lieS E a i j x ∈ S := fun i j x => by rw [lieS_apply]; exact hL _
  have hE : ∀ (τ : E →+* ℂ) i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hS _ _ _) (S.smul_mem (hS _ _ _) _)) _
  refine Algebra.adjoin_le ?_
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem hd_lie {F F' : ℝ → Lie E a} (h : ∀ s, HasDerivAt F (F' s) s) :
    HD (fun s => lie E a (F s)) (fun s => lie E a (F' s)) := by
  classical
  let b := Module.finBasis ℝ (Lie E a)
  have hsum : ∀ X : Lie E a, lie E a X = ∑ m, ((b.repr X m : ℝ) : ℂ) • lie E a (b m) := by
    intro X
    conv_lhs => rw [← b.sum_repr X]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul]
    exact (algebraMap_smul ℂ _ _).symm
  refine ⟨_, inferInstance, fun m s => ((b.repr (F s) m : ℝ) : ℂ), fun m s => ((b.repr (F' s) m : ℝ) : ℂ),
    fun m => lie E a (b m), fun m s => ?_, fun s => hsum _, fun s => hsum _⟩
  have hl := (LinearMap.toContinuousLinearMap (b.coord m)).hasFDerivAt.comp_hasDerivAt s (h s)
  exact hl.ofReal_comp

theorem hasDerivAt_matMul {u v : ℝ → Lie E a} {u' v' : Lie E a} {s : ℝ} (hu : HasDerivAt u u' s)
    (hv : HasDerivAt v v' s) :
    HasDerivAt (fun t => toL (Matrix.of (u t) * Matrix.of (v t)))
      (toL (Matrix.of u' * Matrix.of (v s) + Matrix.of (u s) * Matrix.of v')) s := by
  rw [hasDerivAt_pi] at hu hv ⊢
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hu' := fun k => (hasDerivAt_pi.1 (hu i)) k
  have hv' := fun k => (hasDerivAt_pi.1 (hv k)) j
  have := HasDerivAt.fun_sum (u := Finset.univ) fun k (_ : k ∈ Finset.univ) => (hu' k).mul (hv' k)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using this

theorem zalg_comm_rt_curve : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g)) → ∀ z : Module.End ℂ (Sm E a), z ∈ Zalg E a → (∀ X : Lie E a, z * lie E a X = lie E a X * z) → ∀ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 → (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) → (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) → z * rt E a (infGL E a (c 1)) = rt E a (infGL E a (c 1)) * z := by
  intro E _ _ _ a hconj z hz hcomm c Y h0 hc hci
  let R : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s))
  let Q : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s)⁻¹)
  have hRQ : ∀ s, R s * Q s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hQR : ∀ s, Q s * R s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have hconj' : ∀ s X, R s * lie E a X * Q s =
      lie E a (toL ((c s).val * Matrix.of X * ((c s)⁻¹).val)) := by
    intro s X
    change rt E a (infGL E a (c s)) * lie E a X * Q s = _
    rw [hconj (c s) X, mul_assoc]
    rw [show rt E a (infGL E a (c s)) * Q s = 1 from hRQ s, mul_one]
  have hG : ∀ B ∈ Set.range (lie E a), HD (fun s => R s * B * Q s)
      (fun s => R s * (lie E a Y * B - B * lie E a Y) * Q s) := by
    rintro _ ⟨X, rfl⟩
    let W : Lie E a := toL (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y)
    have hW : lie E a Y * lie E a X - lie E a X * lie E a Y = lie E a W := by
      rw [lie_comm]
      exact (map_sub (lie E a) _ _).symm
    refine (hd_lie (F := fun s => toL ((c s).val * Matrix.of X * ((c s)⁻¹).val))
      (F' := fun s => toL ((c s).val * Matrix.of W * ((c s)⁻¹).val)) fun s => ?_).congr
      (fun s => hconj' s X) (fun s => by rw [hW]; exact hconj' s W)
    have h1 := hasDerivAt_matMul (hc s) (hasDerivAt_const s X)
    have h2 := hasDerivAt_matMul h1 (hci s)
    refine HasDerivAt.congr_deriv h2 ?_
    change toL (((c s).val * Matrix.of Y * Matrix.of X + (c s).val * 0) * ((c s)⁻¹).val +
      ((c s).val * Matrix.of X) * (-(Matrix.of Y * ((c s)⁻¹).val))) =
      toL ((c s).val * (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y) * ((c s)⁻¹).val)
    congr 1
    noncomm_ring
  have h := hd_adjoin R Q hRQ hQR (lie E a Y) _ hG z (Zalg_le hz)
  have h' : HD (fun s => R s * z * Q s) (fun _ => 0) :=
    h.congr (fun _ => rfl) fun s => by rw [hcomm Y, sub_self, mul_zero, zero_mul]
  let l : Sm E a → GA E a → (Module.End ℂ (Sm E a) →ₗ[ℂ] ℂ) := fun φ x =>
    { toFun := fun B => (B φ).1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have e1 : R 1 * z * Q 1 = R 0 * z * Q 0 :=
    LinearMap.ext fun φ => Subtype.ext <| funext fun x => h'.const_of_zero (l φ x) 1 0
  have hR0 : R 0 = 1 := by
    change rt E a (infGL E a (c 0)) = 1
    rw [h0, map_one, map_one]
  have hQ0 : Q 0 = 1 := by
    change rt E a (infGL E a (c 0)⁻¹) = 1
    rw [h0, inv_one, map_one, map_one]
  rw [hR0, hQ0, one_mul, mul_one] at e1
  change z * R 1 = R 1 * z
  calc z * R 1 = R 1 * z * Q 1 * R 1 := by rw [e1]
    _ = R 1 * z * (Q 1 * R 1) := by simp only [mul_assoc]
    _ = R 1 * z := by rw [hQR, mul_one]

end GlobalTheory.CompanionTheory.SmoothRep.Flow
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationInduced
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.MemC
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cocompact (i t : ℕ) : ∃ C : Set (Mir k ((i + 1) + t)), IsCompact C ∧
    ∀ g : Mir k ((i + 1) + t), ∃ h ∈ MirabolicParabolic k (i + 1) t, ∃ c ∈ C, g = h * c := _root_.GlobalTheory.CompanionTheory.BZPhiPG.Coc.hgp_cocompact k i t

theorem smooth_eC {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) :
    IsOpen {g : Mir k ((i + 1) + t) | ∀ m, eC ψ f (m * g) = eC ψ f m} := _root_.GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.isOpen_eC_invariant k i t ψ τ σ f

theorem conj_data {i t : ℕ} (h : MirabolicParabolic k (i + 1) t) :
    ∃ η : HPG k (i + 1) (t + 1), (η : Mir k ((i + 1) + t + 1)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∧
      pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1,
        (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)) := _root_.GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_HGP_mem_HPG k i t h

theorem conj_d {i t : ℕ} (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k) :
    ∃ u : HPG k (i + 1) (t + 1), (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1) ∧ (pgProj k (i + 1) (t + 1) u).2 = 1 ∧
      dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) =
        sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * (u : Mir k ((i + 1) + t + 1)) *
          dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) := _root_.GlobalTheory.CompanionTheory.BZPhiPG.DConj.dEmb_mul_sEmb k i t h d

theorem qC_sigX_unip {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : HPG k (i + 1) (t + 1))
    (h1 : (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1)) (h2 : (pgProj k (i + 1) (t + 1) u).2 = 1)
    (w : τ.V ⊗[ℂ] σ.V) : qC τ σ (sigX τ σ u w) = qC τ σ w := _root_.GlobalTheory.CompanionTheory.BZPhiPG.qC_sigX_unip k i t τ σ u h1 h2 w

theorem qC_sigX_levi {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (h : MirabolicParabolic k (i + 1) t) (η : HPG k (i + 1) (t + 1))
    (hη : pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1,
        (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k))) (w : τ.V ⊗[ℂ] σ.V) :
    qC τ σ (sigX τ σ η w) =
      ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 *
        dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) •
      sigC τ σ h (qC τ σ w) := _root_.GlobalTheory.CompanionTheory.BZPhiPG.QLevi.qC_sigX k i t τ σ h η hη w

theorem dpowM_hgp {i t : ℕ} (s : ℝ) (h : MirabolicParabolic k (i + 1) t) :
    dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) =
      dpow (i + 1) s (gpProj k (i + 1) t h).1 *
        dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := _root_.GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp k i t s h

theorem smInt_scale {t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (A : GL (Fin t) k) (φ : (Fin t → k) → W)
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k t) (fun d => φ ((A⁻¹ : GL (Fin t) k).val *ᵥ d)) =
      ((dpow t 1 A : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k t) φ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec k t W A φ l c

theorem integrand_lc {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}
    (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) ∧
    HasCompactSupport (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) := _root_.GlobalTheory.CompanionTheory.BZPhiPG.TwFibre.twisted_fibre_isLocallyConstant_hasCompactSupport k i t ψ hψ τ σ f y

theorem dpow_add (n : ℕ) (a b : ℝ) (g : GL (Fin n) k) : dpow n (a + b) g = dpow n a g * dpow n b g := by
  unfold dpow
  rw [Complex.ofReal_add, absPow_add]
  rfl

theorem dpow_zero (n : ℕ) (g : GL (Fin n) k) : dpow n 0 g = 1 := by
  unfold dpow
  rw [Complex.ofReal_zero, absPow_zero]
  rfl

theorem isFinite_muD (t : ℕ) : @MeasureTheory.IsFiniteMeasureOnCompacts (Fin t → k) (_root_.borel _) _ (muD k t) := by
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem eval_mul {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (h : HPG k (i + 1) (t + 1))
    (x : Mir k ((i + 1) + (t + 1))) : evX f ((h : Mir k ((i + 1) + (t + 1))) * x) = sigX τ σ h (evX f x) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 h x

theorem pointwise {i t : ℕ} (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (h : MirabolicParabolic k (i + 1) t) (y : Mir k ((i + 1) + t + 1)) (d : Fin (t + 1) → k) :
    qC τ σ (evX f (dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * y)) =
      ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 *
        dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) •
      sigC τ σ h (qC τ σ (evX f (dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) * y))) := by
  obtain ⟨η, hη1, hη2⟩ := conj_data h
  obtain ⟨u, hu1, hu2, hu3⟩ := conj_d h d
  rw [hu3, ← hη1, mul_assoc, mul_assoc]
  have e1 := eval_mul f η ((u : Mir k ((i + 1) + t + 1)) * (dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) * y))
  have e2 := eval_mul f u (dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) * y)
  refine (congrArg (qC τ σ) e1).trans ?_
  rw [qC_sigX_levi τ σ h η hη2]
  refine congrArg _ (congrArg _ ?_)
  refine (congrArg (qC τ σ) e2).trans ?_
  exact qC_sigX_unip τ σ u hu1 hu2 _

theorem last_inv {t : ℕ} (p : Mir k t) (d : Fin (t + 1) → k) :
    (((p : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) (Fin.last t) = d (Fin.last t) :=
  mulVec_last_of_mem k _ (inv_mem p.2) d

theorem scalar_one {i t : ℕ} (g : GL (Fin (i + 1)) k) (A : GL (Fin (t + 1)) k) :
    (dpow (i + 1) (-1 / 2) g * dpow (t + 1) (-1 / 2) A) * (dpow (t + 1) 1 A * (dpow (i + 1) (1 / 2) g * dpow (t + 1) (-1 / 2) A)) = 1 := by
  have h1 : dpow (i + 1) (-1 / 2) g * dpow (i + 1) (1 / 2) g = 1 := by
    rw [← dpow_add, show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, dpow_zero]
  have h2 : dpow (t + 1) (-1 / 2) A * dpow (t + 1) (-1 / 2) A * dpow (t + 1) 1 A = 1 := by
    rw [← dpow_add, ← dpow_add, show (-1 / 2 + -1 / 2 + 1 : ℝ) = 0 by norm_num, dpow_zero]
  calc _ = (dpow (i + 1) (-1 / 2) g * dpow (i + 1) (1 / 2) g) * (dpow (t + 1) (-1 / 2) A * dpow (t + 1) (-1 / 2) A * dpow (t + 1) 1 A) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = 1 := by rw [h1, h2, one_mul]

theorem equiv_eC {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (h : MirabolicParabolic k (i + 1) t) (m : Mir k ((i + 1) + t)) :
    eC ψ f ((h : Mir k ((i + 1) + t)) * m) = sigC τ σ h (eC ψ f m) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := _root_.borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI := isFinite_muD (k := k) (t + 1)
  obtain ⟨g, hg⟩ : ∃ g, g = (gpProj k (i + 1) t h).1 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin (t + 1)) k, A = (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = sEmb k ((i + 1) + t) m := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂˣ, κ = dpow (i + 1) (1 / 2) g * dpow (t + 1) (-1 / 2) A := ⟨_, rfl⟩
  have hp := fun d => pointwise ψ f h y d
  rw [← hη, ← hg, ← hA, ← hκ] at hp
  obtain ⟨l, c⟩ := integrand_lc ψ hψ f y
  obtain ⟨l', c'⟩ := integrand_lc ψ hψ f (η * y)
  let T : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (psiN τ).V ⊗[ℂ] σ.V := (κ : ℂ) • ((sigC τ σ h) ∘ₗ (qC τ σ))
  have e1 : qC τ σ (intC ψ f (η * y)) = ((dpow (t + 1) 1 A : ℂˣ) : ℂ) • T (intC ψ f y) := by
    have a1 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) (qC τ σ) l' c'
    have a2 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T l c
    have a3 := smInt_scale A (T ∘ fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y))
      (IsLocallyConstant.comp l T) (c.comp_left (map_zero T))
    refine a1.symm.trans (Eq.trans ?_ (a3.trans (congrArg _ a2)))
    congr 1
    funext d
    have b := hp d
    rw [mul_assoc] at b
    simp only [Function.comp, map_smul]
    rw [b, hA, last_inv, ← hA]
    simp only [T, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, Units.smul_def]
  have key : (((dpow (i + 1) (-1 / 2) g * dpow (t + 1) (-1 / 2) A : ℂˣ) : ℂ)) * (((dpow (t + 1) 1 A : ℂˣ) : ℂ) * (κ : ℂ)) = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (scalar_one g A)
    simpa only [Units.val_mul, Units.val_one, hκ] using this
  show ((dpowM ((i + 1) + t) (-1 / 2) ((h : Mir k ((i + 1) + t)) * m) : ℂˣ) : ℂ) •
      qC τ σ (intC ψ f (sEmb k _ ((h : Mir k ((i + 1) + t)) * m))) =
    sigC τ σ h (((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m)))
  rw [map_mul (sEmb k ((i + 1) + t)), ← hη, ← hy, e1, map_mul (dpowM ((i + 1) + t) (-1 / 2)), dpowM_hgp, ← hg, ← hA, map_smul]
  simp only [T, LinearMap.smul_apply, LinearMap.comp_apply, smul_smul, Units.val_mul] at key ⊢
  congr 1
  linear_combination ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) * key

theorem memC : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ),
    ∃ y : cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ), (y : smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).1.1 = eC ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ f
  have hind : eC ψ f ∈ indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ) := fun h g => equiv_eC ψ hψ f h g
  have hsm : (⟨eC ψ f, hind⟩ : indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)) ∈ smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ)) := by
    show IsOpen {g | ind (MirabolicParabolic k (i + 1) t) (sigC τ σ) g ⟨eC ψ f, hind⟩ = ⟨eC ψ f, hind⟩}
    convert smooth_eC ψ τ σ f using 3 with g
    rw [Subtype.ext_iff, funext_iff]
    rfl
  obtain ⟨C, hC, hcov⟩ := cocompact (k := k) i t
  exact ⟨⟨⟨_, hsm⟩, C, hC, fun g _ => hcov g⟩, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPG.MemC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSpanFiniteDimStable
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_skew_curve {E : Type} [Field E] [NumberField E] {a : ℕ} (S : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).val) (toL S) 0 ∧
      (S.conjTranspose = -S → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  refine ⟨fun t => (Matrix.isUnit_exp (t • S)).unit, Units.ext (by simp), ?_, fun hS t => ?_⟩
  · open scoped Matrix.Norms.Operator in
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) S (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  · rw [IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hS, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • S)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem liB_skew_mem_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  intro E _ _ _ a φ Z hZ hfd ψ hψ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hW
  have hst : ∀ k : Kinf E a, ∀ w ∈ W, cptRep E a k w ∈ W := by
    intro k w hw
    refine Submodule.span_induction (p := fun w _ => cptRep E a k w ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      change cptRep E a (k * k') φ = cptRep E a k (cptRep E a k' φ)
      rw [map_mul, Module.End.mul_apply]
    · rw [map_zero]; exact W.zero_mem
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact W.add_mem hx hy
    · intro r x _ hx; rw [map_smul]; exact W.smul_mem r hx
  let S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of (mMap E a (Z : ArchMatrix E a))
  have hS : S.conjTranspose = -S := by
    ext i j w
    have h := congrFun (congrFun hZ i) j
    have h2 := congrFun (congrArg Prod.snd h) ⟨w, IsTotallyComplex.isComplex w⟩
    exact h2
  obtain ⟨c, h0, hc, hu⟩ := exists_skew_curve S
  let W' : Submodule ℂ (GA E a → ℂ) := W.map (Sm E a).subtype
  have hW' : FiniteDimensional ℂ W' := inferInstance
  have hF : ∀ t, (fun g => ψ.1 (g * infGL E a (c t))) ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hS t⟩ ψ, hst _ _ hψ, funext fun g => by
      have e : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E a) = c t := Units.ext rfl
      change ψ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [e]⟩
  have hd : ∀ g : GA E a, HasDerivAt (fun t : ℝ => ψ.1 (g * infGL E a (c t))) ((liB Z ψ).1 g) 0 :=
    fun g => hasDerivAt_curve ψ g c (toL S) h0 hc
  obtain ⟨w, hw, e⟩ := AutomorphicForm.mem_of_hasDerivAt W' hF hd
  rwa [show liB Z ψ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.HCRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionSplitCentreInvariant
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem convR_lift_splitCentre_mul (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (F : L2 (latticeGL E a) μ) (hF : F ∈ L2cusp μ) (t : ℝ) (x : GA E a) :
    convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) =
      convR μ f (lift (latticeGL E a) F) x := by
  have hR := R_splitCentre (μ := μ) t hF
  have h1 := GlobalTheory.AutomorphicL2Unitary.lift_R (Γ := latticeGL E a) (μ := μ) (splitCentre E a t) F
  rw [hR] at h1
  have h2 := (measurePreserving_mul_left μ x).quasiMeasurePreserving.ae_eq h1
  unfold convR
  refine integral_congr_ae ?_
  filter_upwards [h2] with y hy
  have e : splitCentre E a t * x * y = x * y * splitCentre E a t := by
    rw [splitCentre_comm t x, mul_assoc, splitCentre_comm t y, ← mul_assoc]
  rw [e]
  exact congrArg (f y * ·) hy.symm

end GlobalTheory.CompanionTheory.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleAnnihilatorEqSelfStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_annihilator_eq_self : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ U : Submodule (ZMod n) X, (⨅ y ∈ (⨅ x ∈ U, LinearMap.ker (B.flip x)), LinearMap.ker (B y)) = U := by
  first | exact @GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator | exact GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator | (intros; apply GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator <;> assumption)
end

