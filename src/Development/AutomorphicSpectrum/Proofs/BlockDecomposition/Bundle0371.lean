module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.RightWhit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0366
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0087
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairIrreducibleUnlinked
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem terms_eq_first (Γ : Segment k) {u v : IrrGL (k := k)} (hu : Γ.first = u)
    (hΓ : Γ.carrier ⊆ {u} ∪ {v}) (hv : v ≠ u.nu 1) :
    ∀ a : ℕ, a < Γ.len → Γ.first.nu a = u := by
  intro a
  induction a with
  | zero =>
    intro _
    rw [Nat.cast_zero, IrrGL.nu_zero, hu]
  | succ n ih =>
    intro hn
    have h1 : Γ.first.nu ((n + 1 : ℕ) : ℂ) = u.nu 1 := by
      rw [← ih (by omega), IrrGL.nu_nu, Nat.cast_succ]
    have hmem : Γ.first.nu ((n + 1 : ℕ) : ℂ) ∈ Γ.carrier := Segment.mem_carrier.2 ⟨n + 1, hn, rfl⟩
    rcases (Set.mem_union _ _ _).1 (hΓ hmem) with h | h
    · exact Set.mem_singleton_iff.1 h
    · exact absurd ((Set.mem_singleton_iff.1 h).symm.trans h1) hv

theorem not_linked_single {x y : IrrGL (k := k)} (hx : x.IsCusp) (hy : y.IsCusp) (h1 : y ≠ x.nu 1) (h2 : x ≠ y.nu 1) :
    ¬ (Segment.single x hx).Linked (Segment.single y hy) := by
  rintro ⟨⟨Γ, hΓ⟩, hxy, -⟩
  simp only [Segment.carrier_single] at hΓ hxy
  have hne : x ≠ y := fun h => hxy (by subst h; exact subset_rfl)
  have key : ∀ u v : IrrGL (k := k), Γ.first = u → Γ.carrier ⊆ {u} ∪ {v} → v ≠ u.nu 1 → v ∈ Γ.carrier → v = u := by
    intro u v hu hsub hv hvmem
    obtain ⟨a, ha, hav⟩ := Segment.mem_carrier.1 hvmem
    rw [← hav]
    exact terms_eq_first Γ hu hsub hv a ha
  have hfirst : Γ.first ∈ Γ.carrier :=
    Segment.mem_carrier.2 ⟨0, Γ.len_pos, by rw [Nat.cast_zero, IrrGL.nu_zero]⟩
  rw [hΓ] at hfirst
  rcases (Set.mem_union _ _ _).1 hfirst with h | h
  · refine hne (key x y (Set.mem_singleton_iff.1 h) hΓ.subset h1 ?_).symm
    rw [hΓ]
    exact Set.mem_union_right _ (Set.mem_singleton y)
  · refine hne (key y x (Set.mem_singleton_iff.1 h) ?_ h2 ?_)
    · intro z hz
      rw [hΓ] at hz
      rcases (Set.mem_union _ _ _).1 hz with hz | hz
      · exact Set.mem_union_right _ hz
      · exact Set.mem_union_left _ hz
    · rw [hΓ]
      exact Set.mem_union_left _ (Set.mem_singleton x)

end GlobalTheory.CompanionTheory.BZPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerCharEqOneOfMemUnipRad
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirJac

section Abstract

variable {M V X Y : Type} [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

theorem ker_comp_mkQ (K₁ K : Submodule ℂ V) (q : (V ⧸ K₁) →ₗ[ℂ] X) (e : LinearMap.ker q = K.map K₁.mkQ)
    (hle : K₁ ≤ K) : LinearMap.ker (q ∘ₗ K₁.mkQ) = K := by
  rw [LinearMap.ker_comp, e, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 hle]

end Abstract

section Iter

variable (k : Type) [Field k]

noncomputable def embedding₂ (n : ℕ) : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (embedding₂ n j)

end Iter

section IterRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iterPhi_quotient (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)),
    ∃ q : τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) ∧
      ∀ g v, q (τ.ρ (embedding₂ k n j g) v) = psiMinus k (iterPhi k ψ j τ).ρ g (q v) := by
  intro j
  induction j with
  | zero =>
    intro τ
    exact ⟨Submodule.mkQ _, Submodule.mkQ_surjective _,
      (Submodule.ker_mkQ _).trans (GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ n τ.V τ.ρ), fun _ _ => rfl⟩
  | succ j ih =>
    intro τ
    obtain ⟨q', hs, hk, hi⟩ := ih (MRep.phiM k ψ τ)
    have hnm : n ≤ n + j := Nat.le_add_right n j
    let N₁ := MirUin k (n + j + 1)
    let θ₁ := mirChar k ψ (n + j)
    let N₂ := derUnipM k (n + j) n
    let θ₂ := derCharM k ψ (n + j) n
    let N := derUnipM k (n + j + 1) n
    let θ := derCharM k ψ (n + j + 1) n
    let s := (levi k (n + j + 1)).comp (Mir k (n + j)).subtype
    let K₁ := twKer τ.ρ N₁ θ₁
    let K := twKer τ.ρ N θ
    let L : Submodule ℂ (τ.V ⧸ K₁) :=
      twKer (twAct τ.ρ N₁ θ₁ s (levi_stab ψ (n + j))) N₂ θ₂
    have hle : K₁ ≤ K := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨hu, hθ⟩ := GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm u
      exact Submodule.subset_span ⟨⟨u, hu⟩, v, by rw [hθ]⟩
    have e : L = K.map K₁.mkQ := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro w ⟨a, x, rfl⟩
        induction x using Submodule.Quotient.induction_on with
        | H v =>
          obtain ⟨ha, hθ⟩ := GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm a
          refine ⟨τ.ρ (s a) v - (θ ⟨s a, ha⟩ : ℂ) • v,
            Submodule.subset_span ⟨⟨s a, ha⟩, v, rfl⟩, ?_⟩
          change K₁.mkQ (τ.ρ (s a) v - (θ ⟨s a, ha⟩ : ℂ) • v) =
            K₁.mkQ (τ.ρ (s a) v) - (θ₂ a : ℂ) • K₁.mkQ v
          rw [map_sub, map_smul, hθ]
      · rw [Submodule.map_le_iff_le_comap]
        refine Submodule.span_le.2 ?_
        rintro w ⟨u, v, rfl⟩
        obtain ⟨u₁, a, hu⟩ := GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm u
        obtain ⟨hu₁, hθ₁⟩ := GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm u₁
        obtain ⟨ha, hθ₂⟩ := GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm a
        have hθ : θ u = θ₁ u₁ * θ₂ a := by
          have hu' : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
          rw [hu', map_mul, hθ₁, hθ₂]
        have hdec : τ.ρ (u : Mir k (n + j + 1)) v - (θ u : ℂ) • v =
            (τ.ρ u₁ (τ.ρ (s a) v) - (θ₁ u₁ : ℂ) • τ.ρ (s a) v) +
              (θ₁ u₁ : ℂ) • (τ.ρ (s a) v - (θ₂ a : ℂ) • v) := by
          rw [hθ, hu, map_mul, mul_apply_eq_comp, Units.val_mul, smul_sub, mul_smul]
          abel
        have hz : τ.ρ u₁ (τ.ρ (s a) v) - (θ₁ u₁ : ℂ) • τ.ρ (s a) v ∈ K₁ :=
          Submodule.subset_span ⟨u₁, _, rfl⟩
        have hzero : K₁.mkQ (τ.ρ u₁ (τ.ρ (s a) v) - (θ₁ u₁ : ℂ) • τ.ρ (s a) v) = 0 :=
          (Submodule.Quotient.mk_eq_zero K₁).2 hz
        change K₁.mkQ _ ∈ L
        rw [hdec, map_add, hzero, zero_add, map_smul]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, K₁.mkQ v, ?_⟩)
        change K₁.mkQ (τ.ρ (s a) v - (θ₂ a : ℂ) • v) =
          K₁.mkQ (τ.ρ (s a) v) - (θ₂ a : ℂ) • K₁.mkQ v
        rw [map_sub, map_smul]
    refine ⟨q' ∘ₗ K₁.mkQ, hs.comp K₁.mkQ_surjective, ?_, fun g v => ?_⟩
    · exact ker_comp_mkQ K₁ K q' (hk.trans e) hle
    · exact hi g (K₁.mkQ v)

end IterRep

section Concrete

variable {k : Type} [Field k]

theorem emb_inl_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) =
      (g.1 : Matrix (Fin n) (Fin n) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inl_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin n) (j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin t) (j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (g.2 : Matrix (Fin t) (Fin t) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem one_inr_inr {n t N : ℕ} (h : n + t = N) (i j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (1 : Matrix (Fin t) (Fin t) k) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  simp only [Equiv.apply_eq_iff_eq, Sum.inr.injEq]

theorem one_inl_inr {n t N : ℕ} (h : n + t = N) (i : Fin n) (j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  simp

theorem one_inr_inl {n t N : ℕ} (h : n + t = N) (i : Fin t) (j : Fin n) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  simp

end Concrete

section ConcreteChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end ConcreteChar

section Entries

variable {k : Type} [Field k]

theorem glEmbMat_block_apply {n m : ℕ} (hnm : n ≤ m) (g : Matrix (Fin n) (Fin n) k) (A : Matrix (Fin m) (Fin m) k)
    (hA : ∀ r s : Fin m, A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin m) (Fin m) k) r s) (r s : Fin (m + 1)) :
    glEmbMat k m A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r s := by
  induction r using Fin.lastCases with
  | last =>
    rw [dite_eq_right (fun h => by have := h.1; simp at this; omega)]
    induction s using Fin.lastCases with
    | last => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_last, one_apply_eq]
    | cast s => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_castSucc, one_apply_ne (Fin.castSucc_ne_last s).symm]
  | cast r =>
    induction s using Fin.lastCases with
    | last =>
      rw [dite_eq_right (fun h => by have := h.2; simp at this; omega), GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_last,
        one_apply_ne (Fin.castSucc_ne_last r)]
    | cast s =>
      rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_castSucc, hA r s]
      by_cases h : (r : ℕ) < n ∧ (s : ℕ) < n
      · rw [dite_eq_left h, dite_eq_left (by simpa using h)]
        rfl
      · rw [dite_eq_right h, dite_eq_right (by simpa using h)]
        rw [Matrix.one_apply, Matrix.one_apply]
        simp only [Fin.castSucc_inj]

theorem iotaM_apply (n : ℕ) (g : GL (Fin n) k) : ∀ (j : ℕ) (r s : Fin (n + j + 1)),
    (((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s =
      if h : (r : ℕ) < n ∧ (s : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s
  | 0, r, s => glEmbMat_block_apply le_rfl (g : Matrix (Fin n) (Fin n) k) (g : Matrix (Fin n) (Fin n) k)
      (fun r s => by rw [dite_eq_left ⟨r.2, s.2⟩]) r s
  | j + 1, r, s => glEmbMat_block_apply (by omega) (g : Matrix (Fin n) (Fin n) k) _ (iotaM_apply n g j) r s

theorem iotaM_eq_emb (n j : ℕ) (g : GL (Fin n) k) :
    ((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      emb₂ k (stdSum (rfl : n + (j + 1) = n + j + 1)) (g, 1) := by
  apply Units.ext
  ext r s
  rw [iotaM_apply]
  obtain ⟨x, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective r
  obtain ⟨y, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective s
  rcases x with x | x <;> rcases y with y | y
  · rw [emb_inl_inl, dite_eq_left (by simp)]
    congr 1
  · rw [emb_inl_inr, dite_eq_right (by simp), one_inl_inr]
  · rw [emb_inr_inl, dite_eq_right (by simp), one_inr_inl]
  · rw [emb_inr_inr, dite_eq_right (by simp), one_inr_inr]
    rfl

end Entries

end GlobalTheory.CompanionTheory.BZMirJac

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeUnitaryAction
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.IntegrateK

variable {n : ℕ}

theorem exp_smul_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

def onePar (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp ((s : ℂ) • X), exp_smul_mem_unitary X hX s⟩

theorem onePar_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) : onePar X hX 0 = 1 := by
  apply Subtype.ext
  simp [onePar]

theorem onePar_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (h s : ℝ) :
    onePar X hX (h + s) = onePar X hX h * onePar X hX s := by
  apply Subtype.ext
  have hc : Commute ((h : ℂ) • X) ((s : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  show NormedSpace.exp (((h + s : ℝ) : ℂ) • X) = _ * _
  simp only [onePar]
  rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]

theorem inner_sum_left {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Kf : Fin n → Fin n → Module.End ℂ V)
    (hs : ∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (x y : V) :
    ⟪∑ a, ∑ b, X a b • Kf a b x, y⟫_ℂ = -⟪x, ∑ a, ∑ b, X a b • Kf a b y⟫_ℂ := by
  have hent : ∀ a b, (starRingEnd ℂ) (X a b) = -X b a := by
    intro a b
    have := congrFun (congrFun hX b) a
    simpa [Matrix.conjTranspose_apply] using this
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hs, hent]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem intertwines_unitary : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → ∀ T : H →ₗ[ℂ] V, (∀ a b w, T (G a b w) = Kf a b (T w)) → ∀ k w, T (ρ k w) = σ k (T w) := by
  intro n H V _ _ _ _ _ ρ G hG σ Kf hK hskew T hT k w
  obtain ⟨X, hX, hk⟩ := GlobalTheory.CompanionTheory.UnitaryExp.exists_skew_exp_eq n k
  have hk1 : onePar X hX 1 = k := by
    apply Subtype.ext
    have hk_val : k.1 = (GLK.expG X 1).val := congrArg Units.val hk
    delta GLK.expG at hk_val
    exact (hk_val.trans (IsUnit.unit_spec _)).symm
  let Tc : H →L[ℝ] V :=
    (⟨T, T.continuous_of_finiteDimensional⟩ : H →L[ℂ] V).restrictScalars ℝ
  have hsub : ∀ u s : ℝ, onePar X hX (u - s) * onePar X hX s = onePar X hX u := by
    intro u s
    rw [← onePar_add, sub_add_cancel]
  have hY : ∀ s, HasDerivAt (fun s => T (ρ (onePar X hX s) w))
      (∑ a, ∑ b, X a b • Kf a b (T (ρ (onePar X hX s) w))) s := by
    intro s
    have h0 := hG X (onePar X hX) hX (fun _ => rfl) (ρ (onePar X hX s) w)
    have h1 : HasDerivAt (fun t => T (ρ (onePar X hX t) (ρ (onePar X hX s) w)))
        (T (∑ a, ∑ b, X a b • G a b (ρ (onePar X hX s) w))) 0 :=
      Tc.hasFDerivAt.comp_hasDerivAt 0 h0
    have h2 := HasDerivAt.comp_sub_const (f := fun t => T (ρ (onePar X hX t) (ρ (onePar X hX s) w)))
      s s (by simpa using h1)
    have e : (fun u => T (ρ (onePar X hX (u - s)) (ρ (onePar X hX s) w)))
        = fun u => T (ρ (onePar X hX u) w) := by
      funext u
      rw [← hsub u s, map_mul]
      rfl
    rw [e] at h2
    simpa only [map_sum, map_smul, hT] using h2
  have hU : ∀ (v : V) (s : ℝ), HasDerivAt (fun s => σ (onePar X hX s) v)
      (∑ a, ∑ b, X a b • Kf a b (σ (onePar X hX s) v)) s := by
    intro v s
    obtain ⟨S, _, hmem, _, _, hd⟩ := hK.2 (σ (onePar X hX s) v)
    have h0 := hd X (onePar X hX) (fun _ => rfl) _ hmem
    have h2 := HasDerivAt.comp_sub_const (f := fun t => σ (onePar X hX t) (σ (onePar X hX s) v))
      s s (by simpa using h0)
    have e : (fun u => σ (onePar X hX (u - s)) (σ (onePar X hX s) v))
        = fun u => σ (onePar X hX u) v := by
      funext u
      rw [← hsub u s, map_mul]
      rfl
    rw [e] at h2
    exact h2
  have hconst : ∀ v : V, ⟪T (ρ k w), σ k v⟫_ℂ = ⟪T w, v⟫_ℂ := by
    intro v
    have hf : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => ⟪T (ρ (onePar X hX s) w), σ (onePar X hX s) v⟫_ℂ) 0 s := by
      intro s
      have h := (hY s).inner ℂ (hU v s)
      rw [inner_sum_left Kf hskew X hX, add_neg_cancel] at h
      exact h
    have h := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
      (fun s => (hf s).deriv) 1 0
    simp only [hk1, onePar_zero, map_one] at h
    simpa using h
  have horth : ∀ v : V, ⟪T (ρ k w) - σ k (T w), σ k v⟫_ℂ = 0 := by
    intro v
    rw [inner_sub_left, hconst v, hK.1 k, sub_self]
  have hsurj : σ k (σ k⁻¹ (T (ρ k w) - σ k (T w))) = T (ρ k w) - σ k (T w) := by
    have : (σ k * σ k⁻¹) (T (ρ k w) - σ k (T w)) = T (ρ k w) - σ k (T w) := by
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    exact this
  have hz := horth (σ k⁻¹ (T (ρ k w) - σ k (T w)))
  rw [hsurj, inner_self_eq_zero] at hz
  exact sub_eq_zero.1 hz

end GlobalTheory.CompanionTheory.RealCount.IntegrateK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetRepsUnipotent
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_coset_reps_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G,
      (∀ i, x i ∈ D.J ⊓ D.N) ∧
        ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps G D.J
    (D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom) (D.J ⊓ D.N)
    D.isCompact_J (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen G D.J D.isOpen_J (t : G)) inf_le_left inf_le_left
    (exists_mem_inf_conj_of_isDom G D t ht)

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetReps
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_KN_coset_reps
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)) :
    IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) →
    HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∃ r : ℕ, 0 < r ∧
      ∃ x : Fin r → GL (Fin N) k, (∀ i, x i ∈ KN k N J d hd) ∧
        ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈
          J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  intro hJo hJc hIw hpos t hdom
  have hKN : KN k N J d hd ≤ J := inf_le_left
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps (GL (Fin N) k) J
    (J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom) (KN k N J d hd) hJc
    (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen _ J hJo _) inf_le_left hKN
    (exists_mem_KN_inv_mul_mem_inf_map_conj k N h d hd J hJo hJc hIw hpos t hdom)

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.DecGal

theorem exists_algHom_mulEquiv_dec : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∃ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (e : (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F)) ≃* Dec (F := F) A), Continuous e ∧ Continuous e.symm ∧ ∀ σ x, ι (((e σ : Dec (F := F) A) : G F Ω) x) = σ (ι x) := by
  intro F Ω _ _ _ _ _ A v h
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v h
  obtain ⟨θ, hθ, hθ', hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc F Ω A v h ι hι
  refine ⟨ι, θ.symm, hθ', hθ, fun σ x => ?_⟩
  have := hl (θ.symm σ) x
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.CompanionTheory.DecGal
end

