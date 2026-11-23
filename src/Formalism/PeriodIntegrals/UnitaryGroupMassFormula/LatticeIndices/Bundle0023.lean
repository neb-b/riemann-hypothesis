module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0022

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllHolds
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem latBasisAll_holds {D : D7} (X : HidaSetting D) (p : TypX X) : LatBasisAll X p := by
  apply latBasisAll_of_parts
  · intro θ hθ
    exact denom_holds (X := X) (p := p) (θ := θ) hθ
  · intro θ hθ
    exact approx_of (X := X) (p := p) (θ := θ) hθ (denseF_holds X p) (epsLat_holds X p θ)

theorem stRed_of_embP {D : D7} (X : HidaSetting D) (p : TypX X) (hE : EmbP X p) : StRed X p :=
  stRed_of_emb X p hE (latBasisAll_holds X p)

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocCongIffEnt
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem locCong_iff_ent (hθ : IsSplitEquiv X p θ) (π : Op X p →+* ZMod (gOf p))
    (hker : RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}) (hS : SplitA X p θ Q) (hA : AdaptA X p θ Q)
    (x : HAp X p) (Y : GL (IdxD D) (Op X p))
    (hY : ((glRed (algebraMap (Op X p) (FpX X p)) Y : GL (IdxD D) (FpX X p)) :
        Matrix (IdxD D) (IdxD D) (FpX X p)) =
      ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) :
    LocCong X p x ↔ EntA X p π Y := by
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  obtain ⟨hE1, hZ1, hB1, hE2, hZ2, hB2⟩ := hA
  set O := OvA X p
  set M := ((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
    Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p))
  set Ym := (Y : Matrix (IdxD D) (IdxD D) (Op X p))
  set Yi := ((Y⁻¹ : GL (IdxD D) (Op X p)) : Matrix (IdxD D) (IdxD D) (Op X p))
  have hYm : ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *
      (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) = Ym.map ((↑) : O → FpX X p) := hY.symm
  have hZ : Yi.map ((↑) : O → FpX X p) * (((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
      (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) = 1 := by
    rw [← hY]
    have h1 : Yi * Ym = 1 := by
      simp only [Yi, Ym]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := congrArg (fun A => A.map (algebraMap (Op X p) (FpX X p))) h1
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  have c1 : ∀ u, crd1 X p θ Q ((M - 1) *ᵥ u) = (Ym.map ((↑) : O → FpX X p) - 1) *ᵥ crd1 X p θ Q u := by
    intro u
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, firstCoords_sub, firstCoords_mulVec, hYm, Matrix.sub_mulVec, Matrix.one_mulVec]
  have c2 : ∀ u, crd2 X p θ Q ((M - 1) *ᵥ u) = (Yiᵀ.map ((↑) : O → FpX X p) - 1) *ᵥ crd2 X p θ Q u := by
    intro u
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, secondCoords_sub, secondCoords_mulVec X p θ Q hθ x _ hZ, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.transpose_map]

  have hsplit : ∀ S y, InModP X p X.B.g S y ↔ CongSpan O (gA X p) (crd1 X p θ Q '' S) (crd1 X p θ Q y) ∧
      CongSpan O (gA X p) (crd2 X p θ Q '' S) (crd2 X p θ Q y) := fun S y => (imA_inModP_Bg X p S y).trans (hS S y)

  have ce : ∀ a : Fin D.R.rS, InModP X p X.B.g ((fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) '' {b | b.1 < a.1})
      ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.e0 a)) ↔
      (∀ i, i ∉ (Sum.inl '' {b : Fin D.R.rS | b.1 < a.1} : Set (IdxD D)) →
        π (Ym i (Sum.inl a)) = if i = Sum.inl a then 1 else 0) ∧
      (∀ i, i ∉ (fposA (D := D) '' {b : Fin D.R.rS | b.1 < a.1}) →
        π (Yi (fposA a) i) = if i = fposA a then 1 else 0) := by
    intro a
    rw [hsplit, Set.image_image, Set.image_image, c1, c2]
    refine and_congr ?_ ?_
    · exact clause_iff O π (gA X p) hker Ym _ (fun b => (Sum.inl b : IdxD D)) (fun b => hE1 b) _ _ _ (hE1 a)
    · have := clause_iff O π (gA X p) hker Yiᵀ _ (fposA (D := D)) (fun b => hE2 b) {b : Fin D.R.rS | b.1 < a.1}
        _ (fposA a) (hE2 a)
      simpa only [Matrix.transpose_apply] using this

  have cz : InModP X p X.B.g (Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b))
      ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 X.z0) ↔
      (∀ i, i ∉ (Sum.inl '' Set.univ : Set (IdxD D)) → π (Ym i zI) = if i = zI then 1 else 0) ∧
      (∀ i, i ∉ (fposA (D := D) '' Set.univ) → π (Yi zI i) = if i = zI then 1 else 0) := by
    rw [hsplit, ← Set.image_univ, Set.image_image, Set.image_image, c1, c2]
    refine and_congr ?_ ?_
    · exact clause_iff O π (gA X p) hker Ym _ (fun b => (Sum.inl b : IdxD D)) (fun b => hE1 b) _ _ _ hZ1
    · obtain ⟨z, hz, hz'⟩ := hZ2
      have hw : ∃ z', IntVec O z' ∧ -crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0) =
          Pi.single zI 1 + ((gA X p : O) : FpX X p) • z' :=
        ⟨-z, fun i => by simpa using neg_mem (hz i), by rw [hz', neg_add, neg_neg, smul_neg]⟩
      have hneg : (Yiᵀ.map ((↑) : O → FpX X p) - 1) *ᵥ crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0) =
          -((Yiᵀ.map ((↑) : O → FpX X p) - 1) *ᵥ -crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0)) := by
        rw [Matrix.mulVec_neg, neg_neg]
      rw [hneg, congSpan_neg]
      have := clause_iff O π (gA X p) hker Yiᵀ _ (fposA (D := D)) (fun b => hE2 b) Set.univ _ zI hw
      simpa only [Matrix.transpose_apply] using this

  have cw : ∀ j : Fin D.R.k, InModP X p X.B.g ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
      (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j' | j'.1 < j.1})
      ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw j)) ↔
      (∀ i, i ∉ (posW (r := D.R.rS) j : Set (IdxD D)) → π (Ym i (wI j)) = if i = wI j then 1 else 0) := by
    intro j
    have h0 : crd2 X p θ Q ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw j)) = 0 := by
      rw [c2]
      have : crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw j)) = 0 := by
        unfold crd2; rw [hB2 j]
        have : ((0 : Fin X.B.I.n → FpX X p) ∘ (idxEquiv X).symm) = 0 := rfl
        rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero]
      rw [this, Matrix.mulVec_zero]
    rw [hsplit, h0, c1]
    simp only [congSpan_zero, and_true]
    let u : Fin D.R.rS ⊕ Fin D.R.k → IdxD D → FpX X p :=
      Sum.elim (fun b => crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.e0 b)))
        (fun j' => crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw j')))
    let pos : Fin D.R.rS ⊕ Fin D.R.k → IdxD D := Sum.elim Sum.inl wI
    let s : Set (Fin D.R.rS ⊕ Fin D.R.k) := Set.range Sum.inl ∪ Sum.inr '' {j' | j'.1 < j.1}
    have hset : crd1 X p θ Q '' ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
        (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j' | j'.1 < j.1}) = u '' s := by
      ext v; simp only [u, s, Set.mem_image, Set.mem_union, Set.mem_range, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨x, (⟨y, rfl⟩ | ⟨b, hb, rfl⟩), rfl⟩
        · exact ⟨Sum.inl y, Or.inl ⟨y, rfl⟩, rfl⟩
        · exact ⟨Sum.inr b, Or.inr ⟨b, hb, rfl⟩, rfl⟩
      · rintro ⟨c, (⟨y, rfl⟩ | ⟨b, hb, rfl⟩), rfl⟩
        · exact ⟨_, Or.inl ⟨y, rfl⟩, rfl⟩
        · exact ⟨_, Or.inr ⟨b, hb, rfl⟩, rfl⟩
    have hpos : pos '' s = posW (r := D.R.rS) j := by
      ext v; simp [pos, s, posW]
    rw [hset]
    have hu : ∀ b, ∃ z, IntVec O z ∧ u b = Pi.single (pos b) 1 + ((gA X p : O) : FpX X p) • z := by
      rintro (b | j')
      · exact hE1 b
      · exact hB1 j'
    have := clause_iff O π (gA X p) hker Ym u pos hu s _ (wI j) (hB1 j)
    rw [hpos] at this
    exact this
  unfold LocCong EntA
  rw [forall_congr' ce, cz, forall_congr' cw, forall_and]
  constructor
  · rintro ⟨⟨hP, hQ⟩, ⟨hR, hS'⟩, hT⟩; exact ⟨hP, hR, hT, hQ, hS'⟩
  · rintro ⟨hP, hR, hT, hQ, hS'⟩; exact ⟨⟨hP, hQ⟩, ⟨hR, hS'⟩, hT⟩

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsSmulInteger
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct Pointwise

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem firstCoords_zero : crd1 X p θ Q 0 = 0 := by
  unfold crd1; rw [map_zero, Pi.zero_comp, Matrix.mulVec_zero]

theorem secondCoords_zero : crd2 X p θ Q 0 = 0 := by
  unfold crd2; rw [map_zero, Pi.zero_comp, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem firstCoords_smul_integer (c : OvA X p) (v : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q (c • v) = c • crd1 X p θ Q v := by
  rw [smulO_eq]
  show crd1 X p θ Q ((c : FpX X p) • v) = (c : FpX X p) • crd1 X p θ Q v
  unfold crd1
  rw [LinearMap.map_smul, show ((c : FpX X p) • pr1 θ v) ∘ (idxEquiv X).symm =
    (c : FpX X p) • (pr1 θ v ∘ (idxEquiv X).symm) from rfl, Matrix.mulVec_smul]

theorem secondCoords_smul_integer (c : OvA X p) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (c • v) = c • crd2 X p θ Q v := by
  rw [smulO_eq]
  show crd2 X p θ Q ((c : FpX X p) • v) = (c : FpX X p) • crd2 X p θ Q v
  unfold crd2
  rw [LinearMap.map_smul, show ((c : FpX X p) • pr2 θ v) ∘ (idxEquiv X).symm =
    (c : FpX X p) • (pr2 θ v ∘ (idxEquiv X).symm) from rfl, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem splitA_of (hO1 : ∀ t ∈ OEp X p, (θ t).1 ∈ OvA X p ∧ (θ t).2 ∈ OvA X p)
    (hO2 : θ.symm (1, 0) ∈ OEp X p) (hO3 : θ.symm (0, 1) ∈ OEp X p)
    (hLat : ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x))
    (hInj : ∀ x, crd1 X p θ Q x = 0 → crd2 X p θ Q x = 0 → x = 0)
    (hSurj : ∀ a b, ∃ x, crd1 X p θ Q x = a ∧ crd2 X p θ Q x = b) : SplitA X p θ Q := by
  intro S y
  unfold InModP
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_sup]
  constructor
  · rintro ⟨w, hw, l', hl', rfl⟩
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hl'
    have key : ∀ w ∈ Submodule.span (OvA X p) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s},
        crd1 X p θ Q w ∈ Submodule.span (OvA X p) (crd1 X p θ Q '' S) ∧
        crd2 X p θ Q w ∈ Submodule.span (OvA X p) (crd2 X p θ Q '' S) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t, ht, s, hs, rfl⟩ := hx
        rw [firstCoords_tensor_smul, secondCoords_tensor_smul]
        exact ⟨Submodule.smul_mem _ (⟨_, (hO1 t ht).1⟩ : OvA X p) (Submodule.subset_span ⟨s, hs, rfl⟩),
          Submodule.smul_mem _ (⟨_, (hO1 t ht).2⟩ : OvA X p) (Submodule.subset_span ⟨s, hs, rfl⟩)⟩
      | zero => rw [firstCoords_zero, secondCoords_zero]; exact ⟨zero_mem _, zero_mem _⟩
      | add x y _ _ hx hy =>
        rw [firstCoords_add, secondCoords_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
      | smul c x _ hx =>
        rw [firstCoords_smul_integer, secondCoords_smul_integer]
        exact ⟨Submodule.smul_mem _ c hx.1, Submodule.smul_mem _ c hx.2⟩
    have hl2 := (hLat l).1 hl
    refine ⟨⟨crd1 X p θ Q w, (key w hw).1, crd1 X p θ Q l, hl2.1, ?_⟩,
      ⟨crd2 X p θ Q w, (key w hw).2, crd2 X p θ Q l, hl2.2, ?_⟩⟩
    · rw [firstCoords_add, firstCoords_smul_integer]; rfl
    · rw [secondCoords_add, secondCoords_smul_integer]; rfl
  · rintro ⟨⟨w1, hw1, z1, hz1, e1⟩, ⟨w2, hw2, z2, hz2, e2⟩⟩
    have lift1 : ∀ w1 ∈ Submodule.span (OvA X p) (crd1 X p θ Q '' S),
        ∃ w ∈ Submodule.span (OvA X p) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s},
          crd1 X p θ Q w = w1 ∧ crd2 X p θ Q w = 0 := by
      intro w1 hw1
      induction hw1 using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, hs, rfl⟩ := hx
        refine ⟨θ.symm (1, 0) • s, Submodule.subset_span ⟨_, hO2, s, hs, rfl⟩, ?_, ?_⟩
        · rw [firstCoords_tensor_smul, AlgEquiv.apply_symm_apply, one_smul]
        · rw [secondCoords_tensor_smul, AlgEquiv.apply_symm_apply, zero_smul]
      | zero => exact ⟨0, zero_mem _, firstCoords_zero X p θ Q, secondCoords_zero X p θ Q⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, ha1, ha2⟩ := hx
        obtain ⟨b, hb, hb1, hb2⟩ := hy
        exact ⟨a + b, add_mem ha hb, by rw [firstCoords_add, ha1, hb1], by rw [secondCoords_add, ha2, hb2, add_zero]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, ha1, ha2⟩ := hx
        exact ⟨c • a, Submodule.smul_mem _ c ha, by rw [firstCoords_smul_integer, ha1], by rw [secondCoords_smul_integer, ha2, smul_zero]⟩
    have lift2 : ∀ w2 ∈ Submodule.span (OvA X p) (crd2 X p θ Q '' S),
        ∃ w ∈ Submodule.span (OvA X p) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s},
          crd1 X p θ Q w = 0 ∧ crd2 X p θ Q w = w2 := by
      intro w2 hw2
      induction hw2 using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, hs, rfl⟩ := hx
        refine ⟨θ.symm (0, 1) • s, Submodule.subset_span ⟨_, hO3, s, hs, rfl⟩, ?_, ?_⟩
        · rw [firstCoords_tensor_smul, AlgEquiv.apply_symm_apply, zero_smul]
        · rw [secondCoords_tensor_smul, AlgEquiv.apply_symm_apply, one_smul]
      | zero => exact ⟨0, zero_mem _, firstCoords_zero X p θ Q, secondCoords_zero X p θ Q⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, ha1, ha2⟩ := hx
        obtain ⟨b, hb, hb1, hb2⟩ := hy
        exact ⟨a + b, add_mem ha hb, by rw [firstCoords_add, ha1, hb1, add_zero], by rw [secondCoords_add, ha2, hb2]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, ha1, ha2⟩ := hx
        exact ⟨c • a, Submodule.smul_mem _ c ha, by rw [firstCoords_smul_integer, ha1, smul_zero], by rw [secondCoords_smul_integer, ha2]⟩
    obtain ⟨wa, hwa, ha1, ha2⟩ := lift1 w1 hw1
    obtain ⟨wb, hwb, hb1, hb2⟩ := lift2 w2 hw2
    obtain ⟨l, hl1, hl2⟩ := hSurj z1 z2
    have hl : l ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
      (hLat l).2 ⟨hl1 ▸ hz1, hl2 ▸ hz2⟩
    have hy : y = (wa + wb) + ((gOf p : ℕ) : OvA X p) • l := by
      have h0 := hInj (y - ((wa + wb) + ((gOf p : ℕ) : OvA X p) • l)) ?_ ?_
      · exact sub_eq_zero.mp h0
      · rw [firstCoords_sub, firstCoords_add, firstCoords_add, firstCoords_smul_integer, e1, ha1, hb1, hl1, add_zero]
        show w1 + ((gA X p : OvA X p) : FpX X p) • z1 - (w1 + ((gA X p : OvA X p) : FpX X p) • z1) = 0
        exact sub_self _
      · rw [secondCoords_sub, secondCoords_add, secondCoords_add, secondCoords_smul_integer, e2, ha2, hb2, hl2, zero_add]
        show w2 + ((gA X p : OvA X p) : FpX X p) • z2 - (w2 + ((gA X p : OvA X p) : FpX X p) • z2) = 0
        exact sub_self _
    exact ⟨wa + wb, add_mem hwa hwb, _, Submodule.smul_mem_pointwise_smul _ _ _ hl, hy.symm⟩

end Loc

end MassDataIdxSteps
end
end

