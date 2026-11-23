module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0022

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrAIntReindex
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

theorem frA_int_reindex {F : Type} [Field F] (O : ValuationSubring F) {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix n n F) (w : m → F) :
    (∀ i, ((Matrix.reindex e.symm e.symm A) *ᵥ w) i ∈ O) ↔ ∀ i, (A *ᵥ (w ∘ e.symm)) i ∈ O := by
  have h : ∀ i, ((Matrix.reindex e.symm e.symm A) *ᵥ w) i = (A *ᵥ (w ∘ e.symm)) (e i) := by
    intro i
    simp only [mulVec, dotProduct, reindex_apply, submatrix_apply, Equiv.symm_symm, Function.comp_apply]
    exact Fintype.sum_equiv e _ _ (fun j => by simp)
  simp only [h]
  constructor
  · intro H j
    simpa using H (e.symm j)
  · intro H i
    exact H (e i)

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem latCrd_of (hL : LatBasis X p θ (reindex₂ X p Q)) (x : Fin X.B.I.n → TpX X p) :
    x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x) := by
  have hPi : (((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        (((Q⁻¹ : GL (IdxD D) (FpX X p))) : Matrix (IdxD D) (IdxD D) (FpX X p)) := rfl
  have hP : ((reindex₂ X p Q : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        ((Q : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) := rfl
  have hJ : J1 X p θ = jm1 X.B.I.J θ := rfl
  have hv : ∀ w : Fin X.B.I.n → FpX X p,
      (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ (w ∘ (idxEquiv X).symm) =
        ((jm1 X.B.I.J θ)ᵀ *ᵥ w) ∘ (idxEquiv X).symm := by
    intro w
    rw [Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    congr 2
    funext i
    simp
  rw [hL x]
  unfold IntVec crd1 crd2
  rw [hPi, frA_int_reindex, ← Matrix.mulVec_mulVec, hP, Matrix.transpose_reindex, frA_int_reindex, hJ, ← hv]
  rfl

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdapted
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Pos

variable {r k : ℕ}

theorem frA_condE (a : Fin r) (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.castSucc a → i ≠ pe a') ↔ i ∉ (Sum.inl '' {b : Fin r | b.1 < a.1}) := by
  constructor
  · rintro h ⟨b, hb, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_castSucc_iff.mpr hb) (by rw [pe_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    have ha2 : (a' : ℕ) < a.1 := ha'
    refine ⟨⟨a', by omega⟩, ha2, ?_⟩
    rw [hi, pe_inl_of_lt ha']

theorem frA_condZ (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.last r → i ≠ pe a') ↔ i ∉ (Sum.inl '' Set.univ) := by
  constructor
  · rintro h ⟨b, -, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_last b) (by rw [pe_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    refine ⟨⟨a', ha'⟩, trivial, ?_⟩
    rw [hi, pe_inl_of_lt ha']

theorem frA_condF (a : Fin r) (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.castSucc a → i ≠ pf a') ↔
      i ∉ ((fun b : Fin r => (Sum.inr (Sum.inr (Fin.rev b)) : Formalism.FourierDecayAlt.S3.Idx r k)) '' {b : Fin r | b.1 < a.1}) := by
  constructor
  · rintro h ⟨b, hb, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_castSucc_iff.mpr hb) (by rw [pf_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    have ha2 : (a' : ℕ) < a.1 := ha'
    refine ⟨⟨a', by omega⟩, ha2, ?_⟩
    rw [hi, pf_of_lt ha']

theorem frA_condFZ (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.last r → i ≠ pf a') ↔
      i ∉ ((fun b : Fin r => (Sum.inr (Sum.inr (Fin.rev b)) : Formalism.FourierDecayAlt.S3.Idx r k)) '' Set.univ) := by
  constructor
  · rintro h ⟨b, -, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_last b) (by rw [pf_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    refine ⟨⟨a', ha'⟩, trivial, ?_⟩
    rw [hi, pf_of_lt ha']

end Pos

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem ent_iff_nuG (π : Op X p →+* ZMod (gOf p)) (Y : GL (IdxD D) (Op X p)) :
    EntA X p π Y ↔ glRed π Y ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k := by
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  open Formalism.FourierDecayAlt.S3 Formalism.DoubleCosetMeasures in
  have colW_iff {K : Type} [Field K] {r k : ℕ} (m : Matrix (Idx r k) (Idx r k) K) :
      ColW m ↔ ∀ i : Fin k, ∀ j, j ∉ posW (r := r) i → m j (wI i) = if j = wI i then 1 else 0 := by
    unfold ColW
    refine forall_congr' fun i => ?_
    rw [mem_span_single]
    refine forall_congr' fun j => forall_congr' fun _ => ?_
    have e : (m *ᵥ Pi.single (wI i) (1 : K)) j = m j (wI i) := by rw [Matrix.mulVec_single_one]; rfl
    rw [Pi.sub_apply, sub_eq_zero, e, Pi.single_apply]

  have par_uni_iff_flags {K : Type} [Field K] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) K) (hxy : x * y = 1) (hyx : y * x = 1) :
      Par IsUpUni x ↔ ColC x ∧ ColW x ∧ RowC y := by
    constructor
    · intro hx
      have hu : Par (fun h => IsUnit h.det) x := by
        obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
        exact ⟨h11, h33, h21, h31, h32, h, uni_unit hh, h22⟩
      obtain ⟨hC, hR⟩ := (par_iff_flags x y hxy hyx).1 hu
      refine ⟨hC, ?_, hR⟩
      obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
      rw [colW_iff]
      intro i j hj
      rcases j with a | (j | u) | c
      · exact absurd (Or.inl ⟨a, rfl⟩) hj
      · have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
        simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
        have hji : ¬ j < i := fun hlt => hj (Or.inr ⟨j, hlt, rfl⟩)
        show x (wI j) (wI i) = _
        rw [show x (wI j) (wI i) = h j i from e]
        by_cases hij : j = i
        · subst hij; simp [hh.2 j, wI]
        · have hlt : i < j := lt_of_le_of_ne (not_lt.1 hji) (Ne.symm hij)
          rw [hh.1 hlt]
          have : (wI j : Idx r k) ≠ wI i := by
            intro e'; apply hij; simpa [wI] using e'
          simp [wI, hij]
      · have e := congrFun (congrFun h22 (Sum.inr u)) (Sum.inl i)
        simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at e
        have e' : x (Sum.inr (Sum.inl (Sum.inr u))) (wI i) = 0 := e
        rw [e']; simp [wI]
      · have e := congrFun (congrFun h32 c) (Sum.inl i)
        simp only [b32, Matrix.of_apply, Matrix.zero_apply] at e
        have e' : x (Sum.inr (Sum.inr c)) (wI i) = 0 := e
        rw [e']; simp [wI]
    · rintro ⟨hC, hW, hR⟩
      obtain ⟨h11, h33, h21, h31, h32, h, -, h22⟩ := (par_iff_flags x y hxy hyx).2 ⟨hC, hR⟩
      refine ⟨h11, h33, h21, h31, h32, h, ⟨fun j i hlt => ?_, fun i => ?_⟩, h22⟩
      ·
        have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
        simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
        rw [← e]
        have hnot : (wI j : Idx r k) ∉ posW (r := r) i := by
          rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
          · simp [wI] at ha
          · have : j' = j := by simpa [wI] using he
            subst this
            exact absurd hlt (not_lt.2 (le_of_lt hj'))
        have := (colW_iff x).1 hW i (wI j) hnot
        rw [show x (wI j) (wI i) = x (Sum.inr (Sum.inl (Sum.inl j))) (Sum.inr (Sum.inl (Sum.inl i))) from rfl] at this
        rw [this]
        have hne : (wI j : Idx r k) ≠ wI i := by
          intro e'; have : j = i := by simpa [wI] using e'
          exact absurd hlt (by rw [this]; exact lt_irrefl _)
        simp [hne]
      · have e := congrFun (congrFun h22 (Sum.inl i)) (Sum.inl i)
        simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
        rw [← e]
        have hnot : (wI i : Idx r k) ∉ posW (r := r) i := by
          rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
          · simp [wI] at ha
          · have : j' = i := by simpa [wI] using he
            subst this
            exact lt_irrefl j' hj'
        have := (colW_iff x).1 hW i (wI i) hnot
        have h1 : x (wI i) (wI i) = 1 := by simpa using this
        exact h1

  have mem_nuG_iff_flags {K : Type} [Field K] {r k : ℕ} (g : GL (Idx r k) K) :
      g ∈ nuG K r k ↔ ColFlag (g : Matrix (Idx r k) (Idx r k) K) ∧ ColW (g : Matrix (Idx r k) (Idx r k) K) ∧
        RowFlag ((g⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) := by
    rw [colFlag_iff, rowFlag_iff]
    exact par_uni_iff_flags _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
  rw [mem_nuG_iff_flags, colFlag_iff', colW_iff, rowFlag_iff', ← map_inv, Fin.forall_fin_succ',
    Fin.forall_fin_succ']
  simp only [pe_castSucc, pe_last, pf_castSucc, pf_last]
  simp only [frA_condE, frA_condZ, frA_condF, frA_condFZ]
  unfold EntA
  constructor
  · rintro ⟨hP, hR, hT, hQ, hS⟩
    exact ⟨⟨hP, hR⟩, hT, ⟨hQ, hS⟩⟩
  · rintro ⟨⟨hP, hR⟩, hT, ⟨hQ, hS⟩⟩
    exact ⟨hP, hR, hT, hQ, hS⟩

variable (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (IdxD D) (FpX X p))

theorem transA_of (hθ : IsSplitEquiv X p θ) (π : Op X p →+* ZMod (gOf p))
    (hker : RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}) (hS : SplitA X p θ Q) (hA : AdaptA X p θ Q) :
    TransA X p θ Q π := fun x _ Y hY =>
  (locCong_iff_ent X p θ Q hθ π hker hS hA x Y hY).trans (ent_iff_nuG X p π Y)

def StAdaptA : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ SplitA X p θ Q ∧ AdaptA X p θ Q

theorem stFrameA_of_adapt (hC : LatCoreX) (h : StAdaptA X p) : StFrameA X p := by
  obtain ⟨θ, hθ, Q, hL, hS, hA⟩ := h
  have hres : ResArith X p := by
    have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
    have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
      have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
        (D.host.g_prime 1).ne_zero p.1).1 p.2
      unfold gOf
      split_ifs with h
      · exact h
      · exact hty.resolve_left h
    have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
        ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
      unfold gOf
      split_ifs
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
    obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
    obtain ⟨hc, hn⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
    exact ⟨hc, hmem, hn⟩

  obtain ⟨π, hπ, hker⟩ := stResZ_of X p hres
  exact stFrameA_of_trans X hC p ⟨θ, hθ, Q, hL, π, hπ, hker, transA_of X p θ Q hθ π hker hS hA⟩

theorem reduction_image_of_adapted (hb : AdBridgeIso X.B.I) (hC : LatCoreX) (h : StAdaptA X p) : LevelReductionImage X hb p :=
  reduction_image_of_frame X hb p (stFrameA_of_adapt X p hC h)

end Loc

end MassDataIdxSteps
end
end

