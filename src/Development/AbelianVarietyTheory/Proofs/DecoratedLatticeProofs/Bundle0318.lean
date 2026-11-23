module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexEquivalenceReduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

namespace GlobalTheory.FunObj.TieLev

theorem mem_iter_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {R t : Type} [Fintype R] [DecidableEq R] [Fintype t] [DecidableEq t]
    (P : TypeDatum k R) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : GL (Ix R t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔ g ∈ KO k (Ix R t j) ∧
      (∀ a b : Ix R t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧
      ∃ x ∈ P.J, x.val = g.val.submatrix Sum.inl Sum.inl := by
  induction j with
  | zero =>
    refine ⟨fun h => ⟨TypeDatum.le_KO _ h, fun a b hab => ?_, _, h, rfl⟩, fun ⟨_, _, x, hx, e⟩ => ?_⟩
    · have := Ix.blk_le a
      omega
    · change (reGL (ixZero R t)).symm g ∈ P.J
      rwa [show (reGL (ixZero R t)).symm g = x from Units.ext (by rw [reGL_symm_val, e]; rfl)]
  | succ j ih =>
    have e : g ∈ (P.iter t μ hμ (j + 1)).J ↔
        (reGL (ixSucc R t j)).symm g ∈ (P.iter t μ hμ j).stepJ t := Iff.rfl
    rw [e, TypeDatum.mem_stepJ_iff]
    constructor
    · rintro ⟨h0, ⟨u, hu, eu⟩, hC⟩
      obtain ⟨-, h1, x, hx, ex⟩ := (ih u).1 hu
      refine ⟨(reGL_symm_mem_KO _ _).1 h0, fun a b hab => ?_, x, hx, ?_⟩
      · obtain ⟨a, rfl⟩ := (ixSucc R t j).surjective a
        obtain ⟨b, rfl⟩ := (ixSucc R t j).surjective b
        rcases a with a | a <;> rcases b with b | b
        · rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          have := h1 a b hab
          rw [eu] at this
          exact this
        · rw [blk_ixSucc_inl, blk_ixSucc_inr] at hab
          have := Ix.blk_le a
          omega
        · exact hC a b
        · exact absurd hab (lt_irrefl _)
      · rw [ex, eu]; rfl
    · rintro ⟨h0, h1, x, hx, ex⟩
      have h0' := (reGL_symm_mem_KO (ixSucc R t j) g).2 h0
      have hC : MaxM ((reGL (ixSucc R t j)).symm g).val.toBlocks₂₁ := fun a b =>
        h1 (ixSucc R t j (.inr a)) (ixSucc R t j (.inl b)) (by
          rw [blk_ixSucc_inl, blk_ixSucc_inr]; exact Nat.lt_succ_of_le (Ix.blk_le b))
      obtain ⟨u, hu, eu⟩ := (exists_diag_blocks h0' hC).1
      refine ⟨h0', ⟨u, (ih u).2 ⟨hu, fun a b hab => ?_, x, hx, ?_⟩, eu⟩, hC⟩
      · rw [eu]
        exact h1 (ixSucc R t j (.inl a)) (ixSucc R t j (.inl b)) (by rwa [blk_ixSucc_inl, blk_ixSucc_inl])
      · rw [ex, eu]; rfl

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

section Num
variable {R : Type} {r t j a : ℕ}

def IsIxR (e₀ : R ≃ Fin r) (ea : Ix R (Fin t) j ≃ Fin a) : Prop :=
  a = r + j * t ∧ (∀ i, (ea (.inl i)).val = (e₀ i).val) ∧ ∀ c s, (ea (.inr (c, s))).val = r + (s.val + t * c.val)

theorem isIxR_of_isIx {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a}
    (h : GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin j × Fin t))).trans ea)) : IsIxR e₀ ea :=
  ⟨h.1, fun i => by simpa using h.2.1 (e₀ i), fun c s => by simpa using h.2.2 c s⟩

theorem IsIxR.blkOf {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} (h : IsIxR e₀ ea) (i : Ix R (Fin t) j) :
    Formalism.L2.DIV.blkOf r t (ea i) = i.blk := by
  rcases i with i | ⟨c, s⟩
  · rw [Formalism.L2.DIV.blkOf, if_pos (by rw [h.2.1]; exact (e₀ i).2)]; rfl
  · rw [Formalism.L2.DIV.blkOf, h.2.2, if_neg (by omega), Nat.add_sub_cancel_left, Nat.add_mul_div_left _ _ s.pos,
      Nat.div_eq_of_lt s.2, zero_add]; rfl

variable {b : ℕ} {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) (j + 1) ≃ Fin b}

theorem val_succ_inl (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (i : Ix R (Fin t) j) :
    (eb (ixSucc _ _ j (.inl i))).val = (ea i).val := by
  rcases i with i | ⟨c, s⟩
  · exact (hb.2.1 i).trans (ha.2.1 i).symm
  · exact (hb.2.2 c.castSucc s).trans (ha.2.2 c s).symm

theorem topL_a {κ : Type} [Zero κ] (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (y : Matrix (Fin b) (Fin a) κ)
    (i l : Ix R (Fin t) j) : topL a y (ea i) (ea l) = y (eb (ixSucc _ _ j (.inl i))) (ea l) := by
  have h : (ea i).val < b ∧ (ea l).val < a := ⟨val_succ_inl ha hb i ▸ (eb _).2, (ea l).2⟩
  rw [topL, dite_eq_left h]
  exact congrArg₂ y (Fin.ext (val_succ_inl ha hb i).symm) rfl

end Num

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

section Red
variable {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K}
variable {R : Type} {r t j a b : ℕ} {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) (j + 1) ≃ Fin b}


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem lowZero_a (h : GlobalTheory.FunObj.Comparison₂.IsRed φ ψ) (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (N : Matrix (Fin b) (Fin a) S) :
    LowZero a (N.map φ) ↔ MaxM (((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id).toRows₂ := by
  refine ⟨fun H i l => (h.ker _).1 (H _ _ ?_ (ea l).2), fun H i l hi _ => ?_⟩
  · have := hb.2.2 (Fin.last j) i
    rw [Fin.val_last, mul_comm] at this
    exact ha.1.le.trans (le_of_le_of_eq (by omega) this.symm)
  obtain ⟨i, rfl⟩ := eb.surjective i
  obtain ⟨l, rfl⟩ := ea.surjective l
  obtain ⟨i | i, rfl⟩ := (ixSucc _ _ j).surjective i
  · exact absurd (val_succ_inl ha hb i ▸ hi) (ea i).2.not_ge
  · exact (h.ker _).2 (H i l)


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem diagonalBlock_det_blockTriangular (ha : IsIxR e₀ ea) {g : GL (Fin a) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) (c : Fin j) :
    (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c.val + 1) g : κ) = (Ix.diagonalBlockOfMatrix (g.val.submatrix ea ea) c).det := by
  have hb : Function.Bijective fun s : Fin t =>
      (⟨ea (.inr (c, s)), ha.blkOf _⟩ : {i : Fin a // Formalism.L2.DIV.blkOf r t i = c.val + 1}) := by
    refine ⟨fun s s' h => by simpa using congrArg Subtype.val h, fun ⟨i, hi⟩ => ?_⟩
    obtain ⟨i | ⟨c', s⟩, rfl⟩ := ea.surjective i
    · exact absurd ((ha.blkOf _).symm.trans hi) (Nat.succ_ne_zero _).symm
    · obtain rfl : c' = c := Fin.ext (Nat.succ_injective ((ha.blkOf _).symm.trans hi))
      exact ⟨s, rfl⟩
  rw [Formalism.L2.DIV.diag_block_det_val _ hg, ← det_submatrix_equiv_self (Equiv.ofBijective _ hb)]
  rfl


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem firstBlock_topBlockMatrix_reduction_eq (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (hr : r ≤ a) (N : Matrix (Fin b) (Fin a) S) {g : GL (Fin a) κ}
    (hg : g.val = topL a (N.map φ)) (hbt : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) :
    (Formalism.L2.DIV.upperLeftBlock hr g).val.submatrix e₀ e₀ =
      ((N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea).submatrix Sum.inl Sum.inl).map φ := by
  ext i l
  rw [submatrix_apply, Formalism.L2.DIV.upper_block_val_submatrix hr (Formalism.L2.DIV.blockTri_blkOf_le r t hbt), submatrix_apply, hg,
    show Fin.castLE hr (e₀ i) = ea (.inl i) from Fin.ext (ha.2.1 i).symm,
    show Fin.castLE hr (e₀ l) = ea (.inl l) from Fin.ext (ha.2.1 l).symm, topL_a ha hb]
  rfl

end Red

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

theorem iterPhi_read : ∀ (S κ k : Type) [CommRing S] [CommRing κ] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : S →+* κ) (ψ : S →+* k), GlobalTheory.FunObj.Comparison₂.IsRed φ ψ → ∀ (R : Type) [Fintype R] [DecidableEq R] (r t j a b : ℕ) (e₀ : R ≃ Fin r) (ea : Ix R (Fin t) j ≃ Fin a) (eb : Ix R (Fin t) (j + 1) ≃ Fin b), GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin j × Fin t))).trans ea) → GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin (j + 1) × Fin t))).trans eb) → ∀ (hr : r ≤ a) (P : TypeDatum k R) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ c, IsTame (μ c)) (χ : ℕ → κˣ →* ℂˣ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat φ ψ (χ (c + 1)) (μ (c + 1))) → ∀ Rd : P.J → GL (Fin r) κ → Prop, (∀ (x : P.J) (g : GL (Fin r) κ) (M : Matrix R R S), g.val.submatrix e₀ e₀ = M.map φ → (Rd x g ↔ MaxM ((x : GL R k).val - M.map ψ))) → ∀ N : Matrix (Fin b) (Fin a) S, (P.iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) ≠ 0 → LowZero a (N.map φ) ∧ ∃ g : GL (Fin a) κ, g.val = topL a (N.map φ) ∧ g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ ∃ x, Rd x (Formalism.L2.DIV.upperLeftBlock hr g)) ∧ (LowZero a (N.map φ) → ∀ g : GL (Fin a) κ, g.val = topL a (N.map φ) → g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) → ∀ x, Rd x (Formalism.L2.DIV.upperLeftBlock hr g) → P.iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) = (P.lam x : ℂ) * (∏ c ∈ Finset.range j, (χ (c + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c + 1) g) : ℂ)) * (χ (j + 1) (Matrix.GeneralLinearGroup.det g) : ℂ)⁻¹) := by
  intro S κ k _ _ _ _ _ _ φ ψ h R _ _ r t j a b e₀ ea eb hA hB hr P μ hμ χ hχ Rd hRd N
  have ha := isIxR_of_isIx hA
  have hb := isIxR_of_isIx hB
  set M := N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea with hM
  have hy : (topL a (N.map φ)).submatrix ea ea = M.map φ := Matrix.ext (topL_a ha hb (N.map φ))
  have e1 : ∀ g : GL (Fin a) κ, g.val = topL a (N.map φ) → (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔
      ∀ i l : Ix R (Fin t) j, l.blk < i.blk → valuation k (ψ (M i l)) < 1) := fun g hg => by
    rw [Formalism.L2.DIV.mem_blockTri, hg, ea.surjective.forall₂]
    refine forall₂_congr fun i l => ?_
    rw [ha.blkOf, ha.blkOf, ← h.ker]
    exact imp_congr_right fun _ => iff_of_eq (congrArg (· = 0) (congrFun (congrFun hy i) l))
  have e3 : (topL a (N.map φ)).det = (M.map φ).det := by rw [← hy, det_submatrix_equiv_self]
  have hsub : ∀ g' : GL (Ix R (Fin t) j) k, g'.val = M.map ψ →
      g'.val.submatrix Sum.inl Sum.inl = (M.submatrix Sum.inl Sum.inl).map ψ := fun g' e => by rw [e]; rfl
  refine ⟨fun h0 => ?_, fun hlow g hg hbt x hx => ?_⟩
  · rw [TypeDatum.iterPhi, TypeDatum.Phi_ne_zero_iff] at h0
    obtain ⟨⟨g', hg', e'⟩, hlow⟩ := h0
    have e'' : g'.val = M.map ψ := e'
    obtain ⟨k1, k2, x, hx, ex⟩ := (mem_iter_gen P μ hμ j g').1 hg'
    obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 (e3 ▸ (h.isUnit_det_iff M).2 ⟨g', k1, e''⟩)
    have hbt : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := (e1 g hg).2 fun i l hil => by
      have := k2 i l hil
      rwa [e''] at this
    refine ⟨(lowZero_a h ha hb N).2 hlow, g, hg, hbt, ⟨x, hx⟩, (hRd ⟨x, hx⟩ _ _ (firstBlock_topBlockMatrix_reduction_eq ha hb hr N hg hbt)).2 ?_⟩
    change MaxM (x.val - _)
    rw [ex, hsub g' e'', sub_self]
    exact maxM_zero
  · have hmx := (hRd x _ _ (firstBlock_topBlockMatrix_reduction_eq ha hb hr N hg hbt)).1 hx
    obtain ⟨g', k1, e''⟩ := (h.isUnit_det_iff M).1 (e3 ▸ hg ▸ (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
    have hx' : MaxM (g'.val.submatrix Sum.inl Sum.inl - (x : GL R k).val) := fun i l => by
      rw [hsub g' e'', Matrix.sub_apply, ← neg_sub, Valuation.map_neg]
      exact hmx i l
    obtain ⟨x', hx'J, ex'⟩ := P.exists_of_congr x.2 hx'
    have hJ : g' ∈ (P.iter (Fin t) μ hμ j).J := (mem_iter_gen P μ hμ j g').2
      ⟨k1, fun i l hil => by rw [e'']; exact (e1 g hg).1 hbt i l hil, x', hx'J, ex'⟩
    obtain ⟨g₀, D, e0, hD, el⟩ := GlobalTheory.SymBridge.iter_lam_closed k R (Fin t) P μ hμ j ⟨g', hJ⟩
    have hl : P.lam g₀ = P.lam x := by
      have h5 : MaxM ((g₀ : GL R k).val - (x : GL R k).val) := by
        rw [e0]; exact hx'
      have := P.lam_eq_one (x⁻¹ * g₀) (inv_mul_mem_KOne (P.le_KO x.2) h5)
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    have hblk : ∀ c : Fin j, μ (c.val + 1) (Matrix.GeneralLinearGroup.det (D c)) =
        χ (c.val + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c.val + 1) g) := fun c =>
      ((hχ c c.2.le).det (Ix.diagonalBlockOfMatrix M c) (by rw [diagonalBlock_det_blockTriangular ha hbt c, hg, hy]; rfl)
        (by rw [Matrix.GeneralLinearGroup.val_det_apply, (hD c).2, e'']; rfl)).symm
    have hdet : μ (j + 1) (Matrix.GeneralLinearGroup.det g') = χ (j + 1) (Matrix.GeneralLinearGroup.det g) :=
      ((hχ j le_rfl).det M (by rw [← hy, det_submatrix_equiv_self, ← hg]; rfl)
        (by rw [Matrix.GeneralLinearGroup.val_det_apply, e''])).symm
    rw [TypeDatum.iterPhi, TypeDatum.Phi_of_mem (x := ((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id) _ _
      ⟨g', hJ⟩ e'' ((lowZero_a h ha hb N).1 hlow), el, hl, hdet, Units.val_mul, Units.coe_prod,
      Units.val_inv_eq_inv_val, Finset.prod_range]
    simp only [hblk]

end GlobalTheory.FunObj.TieLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexIntegralMatricesInSubstitutionImage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section

namespace GlobalTheory.LocOm.IntIndex

section Det

variable {K : Type} [Field K] {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def mulRight (Y : Type) (G : Matrix Y' Y' K) : Matrix Y Y' K →ₗ[K] Matrix Y Y' K :=
  LinearMap.pi fun i : Y => (Matrix.toLin' Gᵀ).comp (LinearMap.proj i)

theorem mulRight_apply (G : Matrix Y' Y' K) (w : Matrix Y Y' K) : mulRight Y G w = w * G := by
  ext i j
  change (Gᵀ.mulVec (w i)) j = _
  rw [Matrix.mulVec_transpose]
  rfl

theorem det_mulRight (G : Matrix Y' Y' K) : LinearMap.det (mulRight Y G) = G.det ^ Fintype.card Y := by
  have := LinearMap.det_pi (R := K) (ι := Y) fun _ => Matrix.toLin' Gᵀ
  rw [LinearMap.det_toLin', Matrix.det_transpose, Finset.prod_const, Finset.card_univ] at this
  exact this

theorem exists_mul_map (H : Matrix Y Y K) (G : Matrix Y' Y' K) :
    ∃ B : Matrix Y Y' K →ₗ[K] Matrix Y Y' K, (∀ w, B w = H * w * G) ∧
      LinearMap.det B = G.det ^ Fintype.card Y * H.det ^ Fintype.card Y' := by
  let τ := Matrix.transposeLinearEquiv Y' Y K K
  refine ⟨mulRight Y G ∘ₗ ((τ : _ →ₗ[K] _) ∘ₗ mulRight Y' Hᵀ ∘ₗ (τ.symm : _ →ₗ[K] _)), fun w => ?_, ?_⟩
  · change mulRight Y G (mulRight Y' Hᵀ wᵀ)ᵀ = _
    rw [mulRight_apply, mulRight_apply, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  · rw [LinearMap.det_comp, LinearMap.det_conj, det_mulRight, det_mulRight, Matrix.det_transpose]

end Det

theorem index_integral_image : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), Enl gk hk → ∃ R₀ : Finset (Matrix Y Y' k), (R₀.card : ℝ) = nabs k (Matrix.GeneralLinearGroup.det hk) ^ (Fintype.card Y' : ℝ) * nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card Y : ℝ)) ∧ (∀ v ∈ R₀, ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * v * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]) ∧ ∀ w : Matrix Y Y' k, (∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]) → ∃! v, v ∈ R₀ ∧ ∀ r q, (w - v) r q ∈ 𝒪[k] := by
  intro k _ _ _ _ Y Y' _ _ _ _ gk hk hE
  let M : Submodule 𝒪[k] (Matrix Y Y' k) :=
    { carrier := {x | ∀ r q, x r q ∈ 𝒪[k]}
      add_mem' := fun ha hb r q => add_mem (ha r q) (hb r q)
      zero_mem' := fun _ _ => zero_mem _
      smul_mem' := fun c x hx r q => by
        rw [Matrix.smul_apply, Algebra.smul_def]
        exact mul_mem c.2 (hx r q) }
  haveI : Submodule.IsLattice k M := by
    apply Submodule.IsLattice.of_fg k
    let φ : Matrix Y Y' 𝒪[k] →ₗ[𝒪[k]] Matrix Y Y' k := (Algebra.linearMap 𝒪[k] k).mapMatrix
    refine Submodule.FG.of_le (Submodule.fg_range φ) fun m hm => ⟨Matrix.of fun i j => ⟨m i j, hm i j⟩, ?_⟩
    ext i j
    rfl
  haveI : Submodule.IsFullLattice k M := by
    constructor
    apply top_unique
    rw [← (Matrix.stdBasis k Y Y').span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    apply Submodule.subset_span
    change ∀ r q, Matrix.stdBasis k Y Y' (i, j) r q ∈ 𝒪[k]
    rw [Matrix.stdBasis_eq_single]
    intro r q
    simp only [Matrix.single_apply]
    split <;> simp
  obtain ⟨Bl, hBl, hd⟩ := exists_mul_map (↑(hk⁻¹) : Matrix Y Y k) (↑gk : Matrix Y' Y' k)
  have hbij : Function.Bijective Bl := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun w => (↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k), fun w => ?_, fun w => ?_⟩
    · change (↑hk : Matrix Y Y k) * Bl w * (↑(gk⁻¹) : Matrix Y' Y' k) = w
      rw [hBl]
      calc (↑hk : Matrix Y Y k) * ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) * (↑(gk⁻¹) : Matrix Y' Y' k)
          = ((↑hk : Matrix Y Y k) * (↑(hk⁻¹) : Matrix Y Y k)) * w * ((↑gk : Matrix Y' Y' k) * (↑(gk⁻¹) : Matrix Y' Y' k)) := by
            simp only [Matrix.mul_assoc]
        _ = w := by rw [hk.mul_inv, gk.mul_inv, Matrix.one_mul, Matrix.mul_one]
    · change Bl ((↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k)) = w
      rw [hBl]
      calc (↑(hk⁻¹) : Matrix Y Y k) * ((↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k)) * (↑gk : Matrix Y' Y' k)
          = ((↑(hk⁻¹) : Matrix Y Y k) * (↑hk : Matrix Y Y k)) * w * ((↑(gk⁻¹) : Matrix Y' Y' k) * (↑gk : Matrix Y' Y' k)) := by
            simp only [Matrix.mul_assoc]
        _ = w := by rw [hk.inv_mul, gk.inv_mul, Matrix.one_mul, Matrix.mul_one]
  have hM : ∀ m ∈ M, Bl m ∈ M := fun m hm =>
    show ∀ r q, (Bl m) r q ∈ 𝒪[k] by rw [hBl]; exact hE m hm
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨m, u, e1, e2⟩ := GlobalTheory.SplitLinear.relIndex_comap_lattice M Bl hbij hM hp
  have hq : Nat.card (𝒪[k] ⧸ Ideal.span {p}) = resCard k := by
    rw [resCard, ← hp.maximalIdeal_eq]
    rfl
  have hq0 : 0 < resCard k := Nat.card_pos
  set A := M.toAddSubgroup with hA
  set Bs := AddSubgroup.comap Bl.toAddMonoidHom A with hBs
  have hne : A.relIndex Bs ≠ 0 := by rw [e2, hq]; exact pow_ne_zero _ hq0.ne'
  haveI : (A.addSubgroupOf Bs).FiniteIndex := ⟨hne⟩
  haveI : Finite (Bs ⧸ A.addSubgroupOf Bs) := AddSubgroup.finite_quotient_of_finiteIndex
  obtain ⟨R, hRc, hRB, hRu⟩ := GlobalTheory.SplitLinear.exists_reps A Bs
  have hmemB : ∀ w, w ∈ Bs ↔ ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k] := by
    intro w
    change (∀ r q, (Bl w) r q ∈ 𝒪[k]) ↔ _
    rw [hBl]
  refine ⟨R, ?_, fun v hv => (hmemB v).1 (hRB v hv), fun w hw => hRu w ((hmemB w).2 hw)⟩

  have hpow : ∀ (x : kˣ) (n : ℕ), nabs k (x ^ n) = nabs k x ^ n := by
    intro x n; simp [nabs, map_pow]
  have hinv : ∀ x : kˣ, nabs k x⁻¹ = (nabs k x)⁻¹ := by
    intro x; simp [nabs, map_inv]
  have hp0 : (p : k) ≠ 0 := fun h => hp.ne_zero (by exact_mod_cast h)
  let X : kˣ := Matrix.GeneralLinearGroup.det gk ^ Fintype.card Y * Matrix.GeneralLinearGroup.det hk⁻¹ ^ Fintype.card Y'
  let U : kˣ := Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) u
  let P : kˣ := Units.mk0 (p : k) hp0
  have hXU : X * U = P ^ m := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ← hd]
    exact e1
  have hU : nabs k U = 1 := by
    apply nabs_eq_one_of_valuation_eq_one
    exact (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.mp u.isUnit
  have hP : nabs k P = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp rfl
  have key := congrArg (nabs k) hXU
  rw [GlobalTheory.SplitWeil.nabs_mul, GlobalTheory.SplitWeil.nabs_mul, hpow, hpow, hpow, hU, hP, map_inv, hinv, mul_one] at key
  rw [hRc, e2, hq, Real.rpow_natCast, Real.rpow_neg (GlobalTheory.SplitWeil.nabs_pos k _).le, Real.rpow_natCast]
  push_cast
  have hq' : ((resCard k : ℝ)) ^ m = (((resCard k : ℝ))⁻¹ ^ m)⁻¹ := by rw [inv_pow, inv_inv]
  rw [hq', ← key, inv_pow (nabs k _), mul_inv, inv_inv, mul_comm]

end GlobalTheory.LocOm.IntIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTrivialNearOneOfLocalBadPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section
namespace GlobalTheory.ChiCont

theorem chi_eq_one_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F)))
    (S : StepLevel F E σ J T f bad) (u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (s : Finset (HeightOneSpectrum (𝓞 F)))
    (H : ∀ v ∈ s, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) →
      bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) :
    ∀ κ : S.U, (∀ v ∈ s, bc (prV (E := E) v) κ.1 = bc (prV (E := E) v) u) →
      (∀ v ∈ bad, v ∉ s → bc (prV (E := E) v) κ.1 = 1) → S.chi κ = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    intro κ _ hb
    exact S.chi_triv κ (fun v hv => hb v hv (Finset.notMem_empty v))
  | @insert v s hvs ih =>
    intro κ hu hb
    have hκ := (S.U_eq κ.1).1 κ.2
    set x0 := Formalism.UG.P.afsplitU v (bc (prV (E := E) v) κ.1) 1 with hx0
    have hx0v : bc (prV (E := E) v) x0 = bc (prV (E := E) v) κ.1 := Formalism.UG.P.afsplit_right1 _ _ _
    have hx0w : ∀ w, w ≠ v → bc (prV (E := E) w) x0 = 1 := by
      intro w hw
      apply Units.ext
      rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
      simp
    have hx0U : x0 ∈ S.U := by
      rw [S.U_eq]
      refine ⟨Formalism.UG.P.afsplitU_mem v _ _ _ _ (Formalism.UG.P.afsplit_bc_mem _ _ v κ.1 hκ.1) (one_mem _), fun w => ?_⟩
      by_cases hw : w = v
      · subst hw
        rw [hx0v]
        exact hκ.2 w
      · rw [hx0w w hw]
        exact one_mem _
    let x : S.U := ⟨x0, hx0U⟩
    have hchix : S.chi x = 1 :=
      H v (Finset.mem_insert_self v s) x hx0w (by rw [hx0v]; exact hu v (Finset.mem_insert_self v s))
    let κ' : S.U := x⁻¹ * κ
    have hκ'w : ∀ w, w ≠ v → bc (prV (E := E) w) κ'.1 = bc (prV (E := E) w) κ.1 := by
      intro w hw
      show bc (prV (E := E) w) (x0⁻¹ * κ.1) = _
      rw [map_mul, map_inv, hx0w w hw, inv_one, one_mul]
    have hκ'v : bc (prV (E := E) v) κ'.1 = 1 := by
      show bc (prV (E := E) v) (x0⁻¹ * κ.1) = _
      rw [map_mul, map_inv, hx0v, inv_mul_cancel]
    have hchi' : S.chi κ' = 1 := by
      refine ih (fun w hw => H w (Finset.mem_insert_of_mem hw)) κ' ?_ ?_
      · intro w hw
        have hwv : w ≠ v := fun h => hvs (h ▸ hw)
        rw [hκ'w w hwv]
        exact hu w (Finset.mem_insert_of_mem hw)
      · intro w hw hws
        by_cases hwv : w = v
        · subst hwv; exact hκ'v
        · rw [hκ'w w hwv]
          exact hb w hw (by simp [hwv, hws])
    have hk : κ = x * κ' := by rw [mul_inv_cancel_left]
    rw [hk, map_mul, hchix, hchi', one_mul]

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Vs : Set (HeightOneSpectrum (𝓞 F))), Vs.Finite → (∀ v ∈ bad, v ∈ Vs) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ v ∈ Vs, ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) → bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) := by
  intro F E _ _ _ _ _ σ n J T f bad S Vs hVs hbad hloc
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  have hall : ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ v ∈ Vs,
      ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) →
        bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1 :=
    (Filter.eventually_all_finite hVs).2 hloc
  filter_upwards [hall] with u hu κ hκu
  refine chi_eq_one_of_split σ J T f bad S u hVs.toFinset
    (fun v hv => hu v (hVs.mem_toFinset.1 hv)) κ (fun v _ => by rw [hκu]) ?_
  intro v hv hvs
  exact absurd (hVs.mem_toFinset.2 (hbad v hv)) hvs

end GlobalTheory.ChiCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearLawLocalModelInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section

namespace GlobalTheory.LocOm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_inv_of_unit (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by simp [nabs]

theorem nabs_pos_of_unit (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact NNReal.coe_pos.mpr distribHaarChar_pos

theorem linearFormula_inv_cancel {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (μS μT : kˣ →* ℂˣ)
    (gk : GL Y' k) (hk : GL Y k) (Φ : Matrix Y Y' k → ℂ) :
    (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk
      ((((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk⁻¹) : ℂˣ) : ℂ) • om μS⁻¹ gk⁻¹ hk⁻¹ Φ) = Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul]
  have hx : ((↑(hk⁻¹⁻¹) : Matrix Y Y k) * ((↑(hk⁻¹) : Matrix Y Y k) * x * (↑gk : Matrix Y' Y' k)) *
      (↑(gk⁻¹) : Matrix Y' Y' k)) = x := by
    simp only [inv_inv, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hx]
  simp only [map_inv, nabs_inv_of_unit, Units.val_inv_eq_inv_val, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
  have p1 := nabs_pos_of_unit (Matrix.GeneralLinearGroup.det gk)
  have p2 := nabs_pos_of_unit (Matrix.GeneralLinearGroup.det hk)
  rw [Real.inv_rpow p1.le, Real.inv_rpow p2.le]
  push_cast
  simp only [neg_div]
  have q1 : ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos p1 _).ne'
  have q2 : ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-((Fintype.card Y' : ℝ) / 2)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos p2 _).ne'
  have u1 := (μS (Matrix.GeneralLinearGroup.det gk)).ne_zero
  have u2 := (μS (Matrix.GeneralLinearGroup.det hk)).ne_zero
  have u3 := (μT (Matrix.GeneralLinearGroup.det gk)).ne_zero
  field_simp

theorem lawLoc_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k),
    LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g⁻¹ gk⁻¹ h⁻¹ hk⁻¹ := by
  intro D k _ _ _ _ S T ω μS μT Y Y' _ _ _ _ Tm g gk h hk hL Φ Φ' hΦ'
  have e : ω (g, h) (Tm Φ') = Tm Φ := hL Φ' Φ (by rw [hΦ', linearFormula_inv_cancel])
  rw [← e, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel]
  change ω 1 (Tm Φ') = Tm Φ'
  rw [map_one, Module.End.one_apply]

end GlobalTheory.LocOm

end
end

