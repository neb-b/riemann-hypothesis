module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDichotomy
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Dich

open GlobalTheory.CompanionTheory.BZPhiPhi GlobalTheory.CompanionTheory.BZPhiPG.Cells

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blockIndex_false_eq (m j : ℕ) (a : Fin m) :
    eGP m j ⟨false, a⟩ = Fin.castSucc (⟨a.1, by have := a.2; omega⟩ : Fin (m + j)) :=
  Fin.ext (blockIndex_false_val m j a)

theorem blockIndex_true_castSucc (m j : ℕ) (b : Fin (j + 1)) :
    eGP m (j + 1) ⟨true, Fin.castSucc b⟩ =
      Fin.castSucc (⟨m + b.1, by have := b.2; omega⟩ : Fin (m + (j + 1))) :=
  Fin.ext (blockIndex_true_val m (j + 1) _)

theorem mem_mirabolicParabolic_of (m j : ℕ) (x : Mir k (m + (j + 1)))
    (h : ∀ r c : Fin (m + j + 1), ¬ r.val < m → c.val < m →
      ((x : GL (Fin (m + (j + 1) + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) = 0) :
    x ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff]
  intro b a
  rw [blockIndex_false_eq]
  induction b using Fin.lastCases with
  | last =>
    rw [blockIndex_true_last, (mem_Mir_iff k _).1 x.2]
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last _) _
  | cast b =>
    rw [blockIndex_true_castSucc]
    exact h _ _ (by simp) (by simp)

theorem unip_mem_HGP (m j : ℕ) (x : Mir k (m + (j + 1))) (v : Fin (m + (j + 1)) → k)
    (hx : (x : GL (Fin (m + (j + 1) + 1)) k) = unip k (m + (j + 1)) (Multiplicative.ofAdd v)) :
    x ∈ MirabolicParabolic k m (j + 1) := by
  refine mem_mirabolicParabolic_of m j x fun r c hr hc => ?_
  rw [hx]
  refine unip_castSucc_castSucc _ v _ _ ?_
  rintro rfl
  exact hr hc

theorem unip_entry (n : ℕ) (v : Fin n → k) (i c : Fin (n + 1))
    (h : c = Fin.last n → ∀ r : Fin n, i = Fin.castSucc r → v r = 0) :
    (unip k n (Multiplicative.ofAdd v)).val i c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i c := by
  show (1 + colMat k n v) i c = _
  rw [Matrix.add_apply]
  by_cases hc : c = Fin.last n
  · induction i using Fin.lastCases with
    | last => simp [colMat, hc]
    | cast r => simp [colMat, hc, h hc r rfl]
  · simp [colMat, hc]

theorem gpProj_unip (m j : ℕ) (y : MirabolicParabolic k m (j + 1)) (v : Fin (m + (j + 1)) → k)
    (hv : ∀ r : Fin (m + (j + 1)), ¬ r.val < m → v r = 0)
    (hy : ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k) =
      unip k (m + (j + 1)) (Multiplicative.ofAdd v)) :
    gpProj k m (j + 1) y = 1 := by
  have hone : ∀ (x : Bool) (a b : Two (Fin m) (Fin (j + 1 + 1)) x),
      (1 : Matrix _ _ k) (eGP m (j + 1) ⟨x, a⟩) (eGP m (j + 1) ⟨x, b⟩) =
        (1 : Matrix (Two (Fin m) (Fin (j + 1 + 1)) x) _ k) a b := by
    intro x a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
      intro e
      exact hab (by simpa using (eGP m (j + 1)).injective e)
  refine Prod.ext ?_ (Subtype.ext ?_)
  · apply Units.ext
    ext a b
    show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨false, a⟩)
      (eGP m (j + 1) ⟨false, b⟩) = _
    rw [hy, unip_entry, hone]
    · rfl
    · intro e
      exact absurd e (blockIndex_false_ne_last m (j + 1) b)
  · apply Units.ext
    ext a b
    show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨true, a⟩)
      (eGP m (j + 1) ⟨true, b⟩) = _
    rw [hy, unip_entry, hone]
    · rfl
    · intro _ r e
      refine hv r ?_
      have := congrArg Fin.val e
      rw [blockIndex_true_val] at this
      simp at this
      omega

end

section

variable {k : Type} [Field k]

theorem conj_unip (n : ℕ) (g : Mir k (n + 1)) (w : Fin (n + 1) → k) :
    ((g⁻¹ * unipM k n (Multiplicative.ofAdd w) * g : Mir k (n + 1)) : GL (Fin (n + 2)) k) =
      unip k (n + 1) (Multiplicative.ofAdd
        (((mirabolicProjection k (n + 1) g⁻¹ : GL (Fin (n + 1)) k) : Matrix _ _ k).mulVec w)) := by
  obtain ⟨v, A, hp, hA⟩ : ∃ v A, (g : GL (Fin (n + 2)) k) = unip k (n + 1) v * glEmb k (n + 1) A ∧
      A = mirabolicProjection k (n + 1) g := ⟨_, _, eq_unip_glEmb g, rfl⟩
  rw [map_inv (mirabolicProjection k (n + 1)) g, ← hA]
  have e := glEmb_mul_unip' k (n + 1) A⁻¹ (Multiplicative.ofAdd w)
  have c : (unip k (n + 1) v)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) * unip k (n + 1) v =
      unip k (n + 1) (Multiplicative.ofAdd w) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_comm _ (Multiplicative.ofAdd w), mul_assoc]
    simp
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, unipM_val, hp]
  simp only [toAdd_ofAdd] at e
  calc (unip k (n + 1) v * glEmb k (n + 1) A)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) *
        (unip k (n + 1) v * glEmb k (n + 1) A)
      = (glEmb k (n + 1) A)⁻¹ * ((unip k (n + 1) v)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) *
          unip k (n + 1) v) * glEmb k (n + 1) A := by group
    _ = glEmb k (n + 1) A⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) * glEmb k (n + 1) A := by
        rw [c, map_inv]
    _ = _ := by
        rw [e, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

end

theorem dichotomy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), ψ ≠ 1 → ∀ (m j : ℕ) (g : Mir k (m + (j + 1))),
    (∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x) ∨
    ∃ u : MirUin k (m + (j + 1)), ∃ hx : g * (u : Mir k (m + (j + 1))) * g⁻¹ ∈ MirabolicParabolic k m (j + 1),
      gpProj k m (j + 1) ⟨_, hx⟩ = 1 ∧ mirChar k ψ (m + j) u ≠ 1 := by
  intro k _ _ _ _ ψ hψ m j g
  by_cases hl : ∃ l : Fin (m + j + 1), l.val < m ∧ rowQ k (m + j) g⁻¹ l ≠ 0
  · obtain ⟨l, hlm, hrl⟩ := hl
    obtain ⟨t, ht⟩ := (AddChar.ne_one_iff).1 hψ
    let w : Fin (m + j + 1) → k := Pi.single l (t / rowQ k (m + j) g⁻¹ l)
    let X : Mir k (m + j + 1) := unipM k (m + j) (Multiplicative.ofAdd w)
    have hu := conj_unip (m + j) g w
    have hmem : g⁻¹ * X * g ∈ MirUin k (m + j + 1) := ⟨_, hu.symm⟩
    have hgx : g * (g⁻¹ * X * g) * g⁻¹ = X := by group
    have hX : X ∈ MirabolicParabolic k m (j + 1) := unip_mem_HGP m j X w rfl
    have hw : ∀ r : Fin (m + (j + 1)), ¬ r.val < m → w r = 0 := by
      intro r hr
      refine Pi.single_eq_of_ne ?_ _
      rintro rfl
      exact hr hlm
    refine Or.inr ⟨⟨g⁻¹ * X * g, hmem⟩, hgx.symm ▸ hX, ?_, ?_⟩
    · refine gpProj_unip m j _ w hw ?_
      show ((g * (g⁻¹ * X * g) * g⁻¹ : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) = _
      rw [hgx]
      rfl
    · rw [mirChar_eq k ψ (m + j) _ _ hu]
      have e : (((mirabolicProjection k (m + j + 1) g⁻¹ : GL (Fin (m + j + 1)) k) : Matrix _ _ k).mulVec w)
          (Fin.last (m + j)) = t := by
        show rowQ k (m + j) g⁻¹ ⬝ᵥ w = t
        simp only [w, dotProduct_single]
        field_simp
      simp only [toAdd_ofAdd, e]
      intro h
      apply ht
      have := congrArg Units.val h
      exact Circle.ext (by simpa using this)
  · have hr0 : ∀ l : Fin (m + j + 1), l.val < m → rowQ k (m + j) g⁻¹ l = 0 := by
      intro l hlm
      by_contra h
      exact hl ⟨l, hlm, h⟩
    obtain ⟨c, hc⟩ := row_ne_zero (mirabolicProjection k (m + j + 1) g⁻¹) (Fin.last (m + j))
    have hc' : rowQ k (m + j) g⁻¹ c ≠ 0 := hc
    have hcs : ¬ c.val < m := fun h => hc' (hr0 c h)
    have hlast : ¬ (Fin.last (m + j)).val < m := by simp
    obtain ⟨B, hBj, hB⟩ := exists_row (fun x : Fin (m + j + 1) => x.val < m) (rowQ k (m + j) g⁻¹) c
      (Fin.last (m + j)) hc' (by simp only [hcs, hlast]) (fun _ x hx => hr0 x hx)
    let d : Mir k (m + j + 1) := levi k (m + j + 1) B
    have hd : d ∈ MirabolicParabolic k m (j + 1) := by
      refine mem_mirabolicParabolic_of m j d fun r c hr hc => ?_
      exact (glEmb_castSucc_castSucc _ B _ _).trans (hB _ _ hr hc)
    have hrow : rowQ k (m + j) g⁻¹ = rowQ k (m + j) d := by
      funext c
      exact (congrFun hBj c).symm.trans (glEmb_castSucc_castSucc _ B _ _).symm
    have hQ := mul_inv_mem_Q_of_rowQ_eq (m + j) g⁻¹ d hrow
    have hQ' : d * g ∈ Q k (m + j) := by
      have := (Q k (m + j)).inv_mem hQ
      simpa using this
    obtain ⟨v, hp⟩ : ∃ v, ((d * g : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) =
        unip k (m + j + 1) (Multiplicative.ofAdd v) * glEmb k (m + j + 1) (mirabolicProjection k (m + j + 1) (d * g)) :=
      ⟨_, eq_unip_glEmb (d * g)⟩
    let uM : Mir k (m + j + 1) := unipM k (m + j) (Multiplicative.ofAdd v)
    have huM : uM ∈ MirabolicParabolic k m (j + 1) := unip_mem_HGP m j uM v rfl
    refine Or.inl ⟨d⁻¹ * uM, (MirabolicParabolic k m (j + 1)).mul_mem ((MirabolicParabolic k m (j + 1)).inv_mem hd) huM,
      qProj k (m + j) ⟨d * g, hQ'⟩, ?_⟩
    have e : d * g = uM * embedding₂ k (m + j) (qProj k (m + j) ⟨d * g, hQ'⟩) := Subtype.ext hp
    rw [mul_assoc, ← e]
    group

end GlobalTheory.CompanionTheory.LeibPhi.Dich
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicExtensionExact
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem ses_of_subQuot {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {ρ₃ : Representation ℂ G V₃} (S : Subrepresentation ρ₂) (e₁ : (subQuot S ⊥).Equiv ρ₁)
    (e₂ : (subQuot ⊤ S).Equiv ρ₃) : Ses ρ₁ ρ₂ ρ₃ := by
  let p : Submodule ℂ S.toSubmodule :=
    (⊥ : Subrepresentation ρ₂).toSubmodule.comap S.toSubmodule.subtype
  have hp : p = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext hs)
  let q : S.toSubmodule ≃ₗ[ℂ] (S.toSubmodule ⧸ p) :=
    LinearEquiv.ofBijective p.mkQ ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]; exact hp, p.mkQ_surjective⟩
  have hq : ∀ (x : G) (w : S.toSubmodule ⧸ p),
      (q.symm (subQuot S ⊥ x w) : V₂) = ρ₂ x (q.symm w : V₂) := by
    intro x w
    obtain ⟨s, rfl⟩ := q.surjective w
    have : subQuot S ⊥ x (q s) = q (S.toRepresentation x s) := rfl
    rw [this, q.symm_apply_apply, q.symm_apply_apply]
    rfl
  let t : V₂ →ₗ[ℂ] (⊤ : Subrepresentation ρ₂).toSubmodule :=
    LinearMap.codRestrict _ LinearMap.id (fun _ => trivial)
  let r : Submodule ℂ (⊤ : Subrepresentation ρ₂).toSubmodule :=
    S.toSubmodule.comap (⊤ : Subrepresentation ρ₂).toSubmodule.subtype
  let f : V₁ →ₗ[ℂ] V₂ :=
    S.toSubmodule.subtype ∘ₗ q.symm.toLinearMap ∘ₗ e₁.toLinearEquiv.symm.toLinearMap
  let g : V₂ →ₗ[ℂ] V₃ := e₂.toLinearEquiv.toLinearMap ∘ₗ r.mkQ ∘ₗ t
  have hf1 : ∀ v, f v = (q.symm (e₁.symm v) : V₂) := fun _ => rfl
  have hg1 : ∀ v, g v = e₂ (r.mkQ (t v)) := fun _ => rfl
  refine ⟨f, g, fun x v => ?_, fun x v => ?_, ?_, ?_, ?_⟩
  · rw [hf1, hf1, eint e₁.symm, hq]
  · rw [hg1, hg1, ← eint e₂]
    rfl
  · intro a b hab
    exact e₁.symm.injective (q.symm.injective (Subtype.ext hab))
  · intro c
    obtain ⟨w, rfl⟩ := e₂.surjective c
    obtain ⟨⟨v, hv⟩, rfl⟩ := r.mkQ_surjective w
    exact ⟨v, rfl⟩
  · ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [LinearMap.mem_ker, hg1, hf1]
      have : r.mkQ (t (q.symm (e₁.symm a) : V₂)) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (q.symm (e₁.symm a)).2
      rw [this, map_zero]
    · intro hv
      rw [LinearMap.mem_ker, hg1] at hv
      have h0 : r.mkQ (t v) = 0 := e₂.injective (hv.trans (map_zero e₂).symm)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      have hvS : v ∈ S.toSubmodule := h0
      refine ⟨e₁ (q ⟨v, hvS⟩), ?_⟩
      rw [hf1, e₁.symm_apply_apply, q.symm_apply_apply]

theorem ses_of_mext (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (A B C : MRep k n) : MExt A B C → Ses A.ρ B.ρ C.ρ := by
  rintro ⟨S, ⟨e₁⟩, ⟨e₂⟩⟩
  exact ses_of_subQuot S e₁ e₂

end GlobalTheory.CompanionTheory.LeibOrd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelNonvanishing
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.AvgBox

theorem setIntegral_eq_sum_reps {E : Type} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    (μ : Measure E) [μ.IsAddLeftInvariant] (D M : AddSubgroup E) (hD : MeasurableSet (D : Set E))
    (hfin : μ (D : Set E) ≠ ⊤) (hDM : D ≤ M) (S : Finset E) (hSM : ∀ s ∈ S, s ∈ M)
    (hS : ∀ x ∈ M, ∃! s, s ∈ S ∧ x - s ∈ D) (f : E → ℂ) (hf : ∀ x, ∀ d ∈ D, f (x + d) = f x) :
    ∫ x in (M : Set E), f x ∂μ = ((μ.real (D : Set E) : ℝ) : ℂ) * ∑ s ∈ S, f s := by
  classical
  set A : E → Set E := fun s => (fun x => -s + x) ⁻¹' (D : Set E) with hA
  have hAm : ∀ s, MeasurableSet (A s) := fun s => (measurable_const_add (-s)) hD
  have hmem : ∀ s x, x ∈ A s ↔ x - s ∈ D := by
    intro s x
    simp only [hA, Set.mem_preimage, SetLike.mem_coe, neg_add_eq_sub]
  have hAM : ∀ s ∈ S, ∀ x ∈ A s, x ∈ M := by
    intro s hs x hx
    have := M.add_mem (hDM ((hmem s x).1 hx)) (hSM s hs)
    simpa using this
  have hU : (M : Set E) = ⋃ s ∈ S, A s := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    constructor
    · intro hx
      obtain ⟨s, ⟨hs, hxs⟩, -⟩ := hS x hx
      exact ⟨s, hs, (hmem s x).2 hxs⟩
    · rintro ⟨s, hs, hx⟩
      exact hAM s hs x hx
  have hdisj : Set.Pairwise (S : Set E) (Function.onFun Disjoint A) := by
    intro s hs s' hs' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    exact (hS x (hAM s hs x hx)).unique ⟨hs, (hmem s x).1 hx⟩ ⟨hs', (hmem s' x).1 hx'⟩
  have hconst : ∀ s, Set.EqOn (fun _ => f s) f (A s) := by
    intro s x hx
    have := hf s (x - s) ((hmem s x).1 hx)
    simpa using this.symm
  have hvol : ∀ s, μ (A s) = μ (D : Set E) := fun s => measure_preimage_add μ (-s) _
  rw [hU, integral_biUnion_finset S (fun s _ => hAm s) hdisj ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← setIntegral_congr_fun (hAm s) (hconst s), setIntegral_const]
    simp [Measure.real, hvol]
  · intro s _
    refine IntegrableOn.congr_fun ?_ (hconst s) (hAm s)
    exact integrableOn_const (by rw [hvol]; exact hfin)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem uM_add (n : ℕ) (x y : Fin n → k) : uM n (x + y) = uM n x * uM n y := by
  simp only [uM, ofAdd_add, map_mul]

theorem continuous_uM (n : ℕ) : Continuous (uM (k := k) n) :=
  (continuous_unipIn n).comp continuous_ofAdd

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem sub_smul_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (y : Fin (n + 1) → k) (v : V) :
    T (uM (n + 1) y) v - ((ψ (y (Fin.last n)) : Circle) : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  let x : MirUin k (n + 1) := ⟨uM (n + 1) y, Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd y, rfl⟩⟩
  have hx := mirChar_eq k ψ n x (Multiplicative.ofAdd y) rfl
  refine Submodule.subset_span ⟨x, v, ?_⟩
  rw [hx]
  rfl

theorem wt_mul_psi (ψ : AddChar k Circle) (y : Fin (n + 1) → k) :
    wt ψ n y * ((ψ (y (Fin.last n)) : Circle) : ℂ) = 1 := by
  rw [wt, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  simp

theorem avg_sub_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (S : Finset (Fin (n + 1) → k)) (v : V) :
    (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  have h : (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v =
      ∑ s ∈ S, wt ψ n s • (T (uM (n + 1) s) v - ((ψ (s (Fin.last n)) : Circle) : ℂ) • v) := by
    simp only [smul_sub, smul_smul, wt_mul_psi, one_smul, Finset.sum_sub_distrib, Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (sub_smul_mem_twKer ψ T s v)

theorem integrand_add (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (v : V) (v' : V') (x d : Fin (n + 1) → k) (hd : T (uM (n + 1) d) v = v)
    (hψ : ψ (d (Fin.last n)) = 1) :
    wt ψ n (x + d) * coef T B v v' (x + d) = wt ψ n x * coef T B v v' x := by
  have h1 : wt ψ n (x + d) = wt ψ n x := by
    simp only [wt, Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, hψ, inv_one, mul_one]
  have h2 : coef T B v v' (x + d) = coef T B v v' x := by
    simp only [coef, uM_add, map_mul, Module.End.mul_apply, hd]
  rw [h1, h2]

end Rep

theorem exists_JJ_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → ∃ v', JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT hB v hv
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  haveI : (piHaar ν (n + 1)).IsAddHaarMeasure := by
    unfold piHaar
    infer_instance
  obtain ⟨r, hr⟩ := exists_cball_addChar_eq_one ψ hψ
  have hΩ₁ : {y : Fin (n + 1) → k | T (uM (n + 1) y) v = v} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    refine ((hT v).preimage (continuous_uM (n + 1))).mem_nhds ?_
    simp [uM]
  have hΩ₂ : {y : Fin (n + 1) → k | y (Fin.last n) ∈ cball r} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    have h0 : cball r ∈ 𝓝 ((0 : Fin (n + 1) → k) (Fin.last n)) := by simpa using cball_mem_nhds r
    exact (continuous_apply (Fin.last n)).continuousAt h0
  obtain ⟨t₀, ht₀⟩ := exists_box_subset (Filter.inter_mem hΩ₁ hΩ₂)
  refine ⟨t₀, fun t ht => ?_⟩
  have hDM : box (n + 1) t₀ ≤ box (n + 1) t := fun x hx j =>
    show valuation k (x j) ≤ valuation k (t : k) from
      le_trans (show valuation k (x j) ≤ valuation k (t₀ : k) from hx j) ht
  have hDo : IsOpen (box (n + 1) t₀ : Set (Fin (n + 1) → k)) :=
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (box_mem_nhds (n + 1) t₀)
  obtain ⟨S, hSM, hS⟩ := GlobalTheory.CompanionTheory.OpenSubgroupCosets.exists_finset_unique_coset_reps
    (box (n + 1) t₀) hDo (box (n + 1) t : Set (Fin (n + 1) → k)) (isCompact_box (n + 1) t)
  have hfin : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ ⊤ :=
    (isCompact_box (n + 1) t₀).measure_lt_top.ne
  have hpos : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ 0 :=
    hDo.measure_ne_zero _ ⟨0, (box (n + 1) t₀).zero_mem⟩
  have hvol : ((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) ≠ 0 :=
    (ENNReal.toReal_pos hpos hfin).ne'
  have hcard : (S.card : ℂ) ≠ 0 := by
    obtain ⟨s, ⟨hs, -⟩, -⟩ := hS 0 (box (n + 1) t).zero_mem
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hs)
  set v₁ : V := ∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v with hv₁
  have hv₁0 : v₁ ≠ 0 := by
    intro h0
    have h := avg_sub_mem_twKer ψ T S v
    rw [← hv₁, h0, zero_sub, neg_mem_iff] at h
    exact hv ((Submodule.smul_mem_iff _ hcard).1 h)
  obtain ⟨v', hv'⟩ := hB v₁ hv₁0
  refine ⟨v', ?_⟩
  have hJ : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' =
      (((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) : ℂ) * B v₁ v' := by
    rw [JJ, setIntegral_eq_sum_reps (piHaar ν (n + 1)) (box (n + 1) t₀) (box (n + 1) t) hDo.measurableSet hfin hDM S
      hSM hS _ fun x d hd => integrand_add ψ T B v v' x d (ht₀ hd).1 (hr _ (ht₀ hd).2)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hv₁, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, coef]
  rw [hJ]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 hvol) hv'

end GlobalTheory.CompanionTheory.MirPair.AvgBox

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLe
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

theorem relIndex_open_compact_and_twisted :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L : Subgroup H),
      IsOpen (L : Set H) → IsCompact (K : Set H) → L ≤ K → L.relIndex K ≠ 0 ∧
        ∀ (T C : Subgroup H) (x : H),
          (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 →
            (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 := by
  intro H _ _ _ K L hL hK hLK
  have hKL : L.relIndex K ≠ 0 := by
    haveI := isCompact_iff_compactSpace.mp hK
    haveI : Finite (K ⧸ L.subgroupOf K) :=
      Subgroup.quotient_finite_of_isOpen _ (hL.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  refine ⟨hKL, fun T C x hC => ?_⟩
  have hf : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have h1 : (L.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj x).toMonoidHom) ≠ 0 := by
    rwa [Subgroup.relIndex_map_map_of_injective L K hf]
  have h2 : (L.map (MulAut.conj x).toMonoidHom).relIndex (T ⊓ K.map (MulAut.conj x).toMonoidHom) ≠ 0 :=
    fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h)
  have h3 : T.relIndex (T ⊓ K.map (MulAut.conj x).toMonoidHom) ≠ 0 := by
    rw [Subgroup.relIndex_eq_one.mpr inf_le_left]
    exact one_ne_zero
  exact Subgroup.relIndex_ne_zero_trans (Subgroup.relIndex_inf_ne_zero h3 h2) hC

end GlobalTheory.CompanionTheory.OrbitalCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionBallIndicatorSpanStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_ball_indicator_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) (X E : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] (r : X →ₗ[ℂ] (Fin (N + 1) → k) → E), (∀ f, ∃ s : kˣ, ∀ (v a : Fin (N + 1) → k), Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → r f (v + a) = r f v) → (∀ f, ∃ S : kˣ, ∀ v : Fin (N + 1) → k, r f v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) → ∀ (tr : (Fin (N + 1) → k) → X → X), (∀ a f v, r (tr a f) v = r f (v + a)) → ∀ (lev : GL (Fin (N + 1)) k → X → X) (A : GL (Fin (N + 1)) k → E →ₗ[ℂ] E), (∀ m f v, r (lev m f) v = A m (r f (((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec v))) → ∃ T : X →ₗ[ℂ] E, (∀ a f, T (tr a f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f) ∧ (∀ m : GL (Fin (N + 1)) k, m ∈ Mir k N → ∀ f, T (lev m f) = ((nabs k (Matrix.GeneralLinearGroup.det m) : ℝ) : ℂ) • A m (T f)) ∧ (∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) → ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : X) (e : E), (∀ v, r b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s) (Classical.propDecidable _) e 0) → T b = c • e) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaInt.exists_twisted_integral | exact GlobalTheory.CompanionTheory.ThetaInt.exists_twisted_integral | (intros; apply GlobalTheory.CompanionTheory.ThetaInt.exists_twisted_integral <;> assumption)
end

