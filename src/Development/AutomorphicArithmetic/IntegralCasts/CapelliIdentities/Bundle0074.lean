module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovOfLocal
section
theorem UpperTheory.Reformulated.B.Qm13.cov_of_local :
    ∀ {O : Type} [inst : CommRing O] {X : AlgebraicGeometry.Scheme} (Q : X.Opens → Prop)
    (q : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of O)) [AlgebraicGeometry.IsSeparated q]
    [AlgebraicGeometry.QuasiCompact q],
    (∀ (x : ↥X), ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ Q V ∧ Nonempty (CrystallineSemistableComparison.Pb.Coord q V d)) →
      ∃ (U : CrystallineSemistableComparison.Pb.Cov q),
        ∀ (α : U.ι),
          Q
            (U.U
              α) := by
  intro O _ X Q q _ _ h
  choose V d hx hQ hc using h
  have : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace q
  have : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from q]; infer_instance⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨⟨s, fun a => V a, fun a => d a, fun a => (hc a).some, ?_, fun S hS => ?_⟩, fun a => hQ _⟩
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  · exact AlgebraicGeometry.IsAffineOpen.biInf (S : Set s) S.finite_toSet hS
      fun a _ => (hc a).some.affine
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulMem
section
theorem UpperTheory.Reformulated.B.ExistsNsmulMem.exists_nsmul_mem.{u_1, u_2} :
    ∀ {E : Type u_1} {W : Type u_2} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice (E := E) La →
      ∀ (w : W),
        ∃ (d : ℕ),
          (0 : ℕ) < d ∧
            d • w ∈ La := by
  intro E W _ _ _ _ La hL w
  induction (hL.span_eq_top ▸ Submodule.mem_top : w ∈ Submodule.span E (La : Set W))
    using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨⟨d, hd, hx⟩, ⟨e, he, hy⟩⟩ := And.intro hx hy
    refine ⟨d * e, mul_pos hd he, smul_add (d * e) x y ▸ La.add_mem ?_ ?_⟩
    exacts [mul_comm e d ▸ mul_smul e d x ▸ La.nsmul_mem hx e, mul_smul d e y ▸ La.nsmul_mem hy d]
  | smul a x _ hx =>
    obtain ⟨⟨d, hd, hx⟩, n, s, hn, hs⟩ := And.intro hx (((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (.of_finite ℚ a)).exists_nsmul_eq (NumberField.RingOfIntegers E))
    refine ⟨n * d, mul_pos (Nat.pos_of_ne_zero hn) hd, ?_⟩
    rw [mul_smul, smul_comm d a x, ← smul_assoc, hs]; exact hL.smul_mem s _ hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsZsmulMem
section
theorem UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem.{u_1, u_2} :
    ∀ {E : Type u_1} [inst : Field E] [NumberField E] {W : Type u_2} [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice (E := E) La →
      ∀ (x : W),
        ∃ (d : ℤ),
          d ≠ (0 : ℤ) ∧
            d • x ∈ La := by
  intro E _ _ W _ _ La h x
  refine Submodule.span_induction (p := fun x _ => ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La)
    (fun y hy => ⟨1, one_ne_zero, by simpa using hy⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_
    (h.span_eq_top ▸ Submodule.mem_top : x ∈ Submodule.span E (La : Set W))
  · rintro y z - - ⟨d, hd, hy⟩ ⟨e, he, hz⟩
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add, mul_smul d e z, mul_comm d e, mul_smul e d y]
    exact add_mem (La.zsmul_mem hy e) (La.zsmul_mem hz d)
  · rintro a y - ⟨d, hd, hy⟩
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
    refine ⟨m * d, mul_ne_zero hm hd, ?_⟩
    rw [mul_smul, smul_comm d a y, ← smul_assoc]
    exact h.smul_mem ⟨m • a, hi⟩ _ hy
end

