module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeStabilizerNormalisingSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentStabilizesSomeLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem volSt_conj_self {G : Type} [Group G] (H : Subgroup G) {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

theorem volSt_inf_stab_smul {G X : Type} [Group G] [MulAction G X] (H : Subgroup G) {h : G} (hh : h ∈ H)
    (x : X) : H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  rw [Subgroup.smul_inf, volSt_conj_self H hh]
  congr 1
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, MulAction.mem_stabilizer_iff, mul_smul,
    inv_smul_eq_iff]

theorem volSt {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
    (r k : ℕ) (S : Frames L r k) :
    (∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.K0 ≠ 0 ∧ ∀ h ∈ S.St, S.mu (h • Λ) = S.mu Λ) ∧
    ∀ C, S.IsCls C → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 ∧ 1 ≤ S.wC C ∧
      ∀ h ∈ S.St, S.wC (h • C) = S.wC C := by
  obtain ⟨Λ1, hΛ1, hK0, -⟩ := _root_.GlobalTheory.HL.FrameStabLat.main L r k S 1 S.N.one_mem 1 S.N'.one_mem
  have hK : S.K0 = S.St ⊓ stabL L Λ1 := hK0.symm
  have hc : ∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ stabL L Λ) ≠ 0 ∧
      (S.St ⊓ stabL L Λ).relIndex S.K0 ≠ 0 := by
    intro Λ hΛ
    rw [hK]
    exact ⟨(_root_.GlobalTheory.LatComm.stab_commensurable L Λ Λ1 hΛ hΛ1 S.St).1, (_root_.GlobalTheory.LatComm.stab_commensurable L Λ1 Λ hΛ1 hΛ S.St).1⟩
  have hconj : ∀ h ∈ S.St, S.K0.relIndex (MulAut.conj h • S.K0) ≠ 0 ∧
      (MulAut.conj h • S.K0).relIndex S.K0 ≠ 0 := by
    intro h hh
    have e : MulAut.conj h • S.K0 = S.St ⊓ stabL L (h • Λ1) := by
      rw [hK]; exact (volSt_inf_stab_smul S.St hh Λ1).symm
    rw [e]
    exact hc _ ((_root_.GlobalTheory.LatComm.stab_commensurable L Λ1 Λ1 hΛ1 hΛ1 S.St).2 h).1
  have hle : S.K0 ≤ S.St := by rw [hK]; exact inf_le_left
  have hmod := (_root_.GlobalTheory.HL.invVol_conj_modular S.St S.K0 hle hconj).2.2.2
  have hone : ∀ h ∈ S.St, invVol S.K0 (MulAut.conj h • S.K0) = 1 := by
    intro h hh
    obtain ⟨Λ, hΛ, hs⟩ := _root_.GlobalTheory.HL.exists_isLat_stabL_of_unipotent L h _ (_root_.GlobalTheory.FlagUnipotent.main L r k S h hh.1)
    exact (hmod _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh).2 (volSt_conj_self _ ⟨hh, hs⟩)
  have hinv : ∀ K' : Subgroup S.GLV, S.K0.relIndex K' ≠ 0 → K'.relIndex S.K0 ≠ 0 → ∀ h ∈ S.St,
      invVol S.K0 (MulAut.conj h • K') = invVol S.K0 K' := by
    intro K' h1 h2 h hh
    rw [(hmod K' h1 h2 h hh).1, hone h hh, one_mul]
  refine ⟨fun Λ hΛ => ⟨(hc Λ hΛ).1, (hc Λ hΛ).2, fun h hh => ?_⟩, ?_⟩
  · unfold Frames.mu
    rw [volSt_inf_stab_smul S.St hh Λ]
    exact hinv _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh
  rintro C ⟨n, hn, n', hn', hC⟩
  obtain ⟨Λ, hΛ, e1, e2, e3⟩ := _root_.GlobalTheory.HL.FrameStabLat.main L r k S n hn n' hn'
  rw [← hC] at e2 e3
  obtain ⟨⟨K, hKm, hKi, -⟩, -⟩ := _root_.GlobalTheory.HL.congruence_subgroup_facts L S.ϖ S.ϖ_irr Λ hΛ 1
  have a1 : S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 :=
    fun h0 => (hc Λ hΛ).1 (Subgroup.relIndex_eq_zero_of_le_right e2 h0)
  have b1 : K.relIndex (S.St ⊓ stabL L Λ) ≠ 0 :=
    fun h0 => hKi (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  have b2 : (K ⊓ (S.St ⊓ stabL L Λ)) ≤ S.St ⊓ MulAction.stabilizer S.GLV C :=
    fun g hg => ⟨hg.2.1, e3 g hg.2 ((hKm g).1 hg.1).2⟩
  have b3 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex (S.St ⊓ stabL L Λ) ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_eq_zero_of_le_left b2 h0
    rw [Subgroup.inf_relIndex_right] at this
    exact b1 this
  have a2 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans b3 (hc Λ hΛ).2
  refine ⟨a1, a2, ?_, fun h hh => ?_⟩
  · obtain ⟨h, hh, hw, -⟩ := GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup L r k S n hn
    have c1 : S.St ⊓ MulAction.stabilizer S.GLV C ≤ MulAut.conj h • S.K0 :=
      e2.trans (e1.le.trans (inf_le_left.trans hw))
    have c2 := (invVol_mul_pos_le_conj S.K0 (MulAut.conj h • S.K0) _ (hconj h hh).1 (hconj h hh).2
      a1 a2).2.2.1 c1
    have c3 := Subgroup.relIndex_ne_zero_trans a2 (hconj h hh).1
    unfold Frames.wC
    rw [c2, hone h hh, one_mul]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 c3
  · unfold Frames.wC
    rw [volSt_inf_stab_smul S.St hh C]
    exact hinv _ a1 a2 h hh

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCompleteDense
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.HilbTensorExists

theorem exists_pre_fin (n : ℕ) : ∀ (H : Fin n → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)],
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  induction n with
  | zero =>
    intro H _ _
    refine ⟨ℂ, inferInstance, inferInstance, fun _ => 1, fun x y => ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    simp
  | succ n ih =>
    intro H _ _
    obtain ⟨K, iK, iK', t, ht⟩ := ih (fun i => H i.castSucc)
    refine ⟨K ⊗[ℂ] H (Fin.last n), inferInstance, inferInstance,
      fun x => t (fun i => x i.castSucc) ⊗ₜ[ℂ] x (Fin.last n), fun x y => ?_⟩
    rw [TensorProduct.inner_tmul, ht, Fin.prod_univ_castSucc]

theorem exists_pre {ι : Type} [Fintype ι] (H : ι → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  let e := Fintype.equivFin ι
  obtain ⟨K, iK, iK', t, ht⟩ := exists_pre_fin (Fintype.card ι) (fun i => H (e.symm i))
  refine ⟨K, iK, iK', fun x => t (fun i => x (e.symm i)), fun x y => ?_⟩
  rw [ht]
  exact e.symm.prod_comp (fun v => ⟪x v, y v⟫_ℂ)

theorem exists_complete_dense {X K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (t : X → K) :
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : CompleteSpace L) (s : X → L),
      (∀ x y, ⟪s x, s y⟫_ℂ = ⟪t x, t y⟫_ℂ) ∧ Dense (Submodule.span ℂ (Set.range s) : Set L) := by
  let V := Submodule.span ℂ (Set.range t)
  let u : X → V := fun x => ⟨t x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hu : Submodule.span ℂ (Set.range u) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    rfl
  refine ⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance,
    fun x => ((u x : V) : UniformSpace.Completion V), fun x y => ?_, ?_⟩
  · rw [UniformSpace.Completion.inner_coe]
    rfl
  · refine UniformSpace.Completion.denseRange_coe.mono ?_
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span ℂ (Set.range u) := hu ▸ Submodule.mem_top
    have hm := Submodule.mem_map_of_mem
      (f := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := V)).toLinearMap) hv
    rw [Submodule.map_span, ← Set.range_comp] at hm
    exact hm

end GlobalTheory.HilbTensorExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd
section
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

namespace GlobalTheory

theorem eq_of_inner_eq_on_dense_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} (hs : Dense (Submodule.span ℂ s : Set E)) {a b : E}
    (h : ∀ y ∈ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ) : a = b := by
  have h1 : ∀ y ∈ Submodule.span ℂ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, inner_add_left, hy, hz]
    | smul c y _ hy => rw [inner_smul_left, inner_smul_left, hy]
  have h2 : (fun y : E => ⟪y, a⟫_ℂ) = fun y => ⟪y, b⟫_ℂ :=
    Continuous.ext_on hs (by fun_prop) (by fun_prop) h1
  exact ext_inner_left ℂ fun y => congrFun h2 y

theorem exists_continuousMultilinearMap_of_inner_prod {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (t : (∀ v, H v) → E)
    (hin : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range t) : Set E)) :
    ∃ m : ContinuousMultilinearMap ℂ H E, (∀ x, m x = t x) ∧ ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
  have hn : ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
    intro x
    have h := hin x x
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h' : ‖t x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
      rw [← Finset.prod_pow]
      exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _)
      two_ne_zero).1 h'
  have hu : ∀ [DecidableEq ι] (y x : ∀ v, H v) (i : ι) (a : H i),
      ⟪t y, t (Function.update x i a)⟫_ℂ =
        ⟪y i, a⟫_ℂ * ∏ j ∈ Finset.univ.erase i, ⟪y j, x j⟫_ℂ := by
    intro _ y x i a
    rw [hin, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  let m : MultilinearMap (RingHom.id ℂ) H E :=
    { toFun := t
      map_update_add' := by
        intro _ x i a b
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [inner_add_right, hu, hu, hu, inner_add_right, add_mul]
      map_update_smul' := by
        intro _ x i c a
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [RingHom.id_apply, inner_smul_right, hu, hu, inner_smul_right, mul_assoc] }
  refine ⟨m.mkContinuous 1 fun x => ?_, fun x => rfl, hn⟩
  rw [one_mul]
  exact (hn x).le

theorem rowsAut_tens_continuousMultilinear :
    ∀ B : RowsAut, ∃ m : ContinuousMultilinearMap ℂ B.H B.Hs,
      (∀ x, m x = B.tens x) ∧ ∀ x, ‖B.tens x‖ = ∏ v, ‖x v‖ := fun B =>
  exists_continuousMultilinearMap_of_inner_prod B.tens B.tens_spec.1 B.tens_spec.2.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormSqTensUpdate
section
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace GlobalTheory

theorem exists_gram_factor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {k : ℕ}
    (x : Fin k → E) : ∃ C : Fin k → Fin k → ℂ, ∀ l l',
      ⟪x l, x l'⟫_ℂ = ∑ r, (starRingEnd ℂ) (C r l) * C r l' := by
  have h := (Matrix.posSemidef_gram ℂ x).nonneg
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h
  refine ⟨fun r l => C r l, fun l l' => ?_⟩
  have := congrFun (congrFun hC l) l'
  simpa [Matrix.gram_apply, Matrix.mul_apply, Matrix.star_apply] using this

theorem exists_normSq_tens_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (tens : (∀ v, H v) → Hs)
    (ht : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (v₀ : ι) {k : ℕ}
    (u : Fin k → ∀ v, H v) :
    ∃ C : ({v // v ≠ v₀} → Fin k) → Fin k → ℂ, ∀ a : Fin k → H v₀,
      ‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 = ∑ r, ‖∑ l, C r l • a l‖ ^ 2 := by
  choose D hD using fun v : {v // v ≠ v₀} => exists_gram_factor (fun l => u l v.1)
  refine ⟨fun r l => ∏ v, D v (r v) l, fun a => ?_⟩
  have key : ∀ l l', ⟪tens (Function.update (u l) v₀ (a l)),
      tens (Function.update (u l') v₀ (a l'))⟫_ℂ =
      ∑ r : {v // v ≠ v₀} → Fin k,
        ⟪(∏ v, D v (r v) l) • a l, (∏ v, D v (r v) l') • a l'⟫_ℂ := by
    intro l l'
    rw [ht, Fintype.prod_eq_mul_prod_subtype_ne _ v₀]
    simp only [Function.update_self]
    have h1 : ∏ v : {v // v ≠ v₀}, ⟪Function.update (u l) v₀ (a l) v.1,
        Function.update (u l') v₀ (a l') v.1⟫_ℂ =
        ∏ v : {v // v ≠ v₀}, ∑ r, (starRingEnd ℂ) (D v r l) * D v r l' := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Function.update_of_ne v.2, Function.update_of_ne v.2, hD]
    rw [h1, Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [inner_smul_left, inner_smul_right, Finset.prod_mul_distrib, map_prod]
    ring
  have hc : ((‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 : ℝ) : ℂ) =
      ((∑ r : {v // v ≠ v₀} → Fin k, ‖∑ l, (∏ v, D v (r v) l) • a l‖ ^ 2 : ℝ) : ℂ) := by
    have hn : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E),
        ((‖z‖ ^ 2 : ℝ) : ℂ) = ⟪z, z⟫_ℂ := by
      intro E _ _ z
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [Complex.ofReal_sum, hn]
    simp only [hn, sum_inner, inner_sum, key]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
  exact_mod_cast hc

theorem sum_normSq_tens_update_le :
    ∀ (B : RowsAut) (v₀ : InfinitePlace B.I.F) (S : ∀ v, Submodule ℂ (B.H v)) (m : ℕ) (L : Fin m → (S v₀ →ₗ[ℂ] B.H v₀)) (β : ℝ), (∀ y : S v₀, ∑ i, ‖L i y‖ ^ 2 ≤ β * ‖y‖ ^ 2) → ∀ (k : ℕ) (u : Fin k → ∀ v, S v), open Classical in ∑ i, ‖∑ l, B.tens (Function.update (fun v => (u l v : B.H v)) v₀ (L i (u l v₀)))‖ ^ 2 ≤ β * ‖∑ l, B.tens (fun v => (u l v : B.H v))‖ ^ 2 := by
  classical
  intro B v₀ S m L β hL k u
  obtain ⟨C, hC⟩ := exists_normSq_tens_update B.tens B.tens_spec.1 v₀
    (fun l v => (u l v : B.H v))
  have h0 := hC (fun l => (u l v₀ : B.H v₀))
  have hu : ∀ l, Function.update (fun v => (u l v : B.H v)) v₀ (u l v₀ : B.H v₀) =
      fun v => (u l v : B.H v) := fun l => Function.update_eq_self v₀ _
  simp only [hu] at h0
  rw [h0, Finset.mul_sum]
  have h1 : ∀ i, _ := fun i => hC (fun l => L i (u l v₀))
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun r _ => ?_
  have := hL (∑ l, C r l • u l v₀)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul] at this
  refine this.trans_eq ?_
  rw [← Submodule.norm_coe]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalSameIntegralSpanUnimodular
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SelfDual

open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

theorem exists_orthonormal_same_span : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ b : Fin m → Fin n → E, (∀ i j, hf L Hm (b i) (b j) ∈ L.O) → (∃ P : Matrix (Fin m) (Fin m) E, IsIntM L P ∧ (Matrix.of fun i j => hf L Hm (b i) (b j)) * P = 1) → ∃ b' : Fin m → Fin n → E, (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) ∧ Submodule.span L.O (Set.range b') = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n m Hm hH b hint₀ hunim
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, hpir, -, -, -, hnorm⟩ := order_facts L ϖ hϖ
  obtain ⟨P₀, hP₀, hGP₀⟩ := hunim
  have hmem : ∀ i, b i ∈ Submodule.span L.O (Set.range b) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have hsm : ∀ (a : L.O) (v : Fin n → E), a • v = (a : E) • v := fun _ _ => rfl
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  let G : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨hf L Hm (b i) (b j), hint₀ i j⟩
  have hGv : ∀ i j, (G i j : E) = hf L Hm (b i) (b j) := fun _ _ => rfl
  have hG : ∀ i j, c (G i j) = G j i := fun i j => Subtype.ext (hf_cj L hH.1 _ _)
  let Q : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨P₀ i j, hP₀ i j⟩
  have hGQ : G * Q = 1 := by
    ext i j
    have h := congrFun (congrFun hGP₀ i) j
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))
  obtain ⟨P, hP, hGP⟩ := GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map (R₀ := 𝒪[F]) c hc hfix
    (by
      obtain ⟨w, hw, h⟩ := htr 1
      exact ⟨⟨w, hw⟩, Subtype.ext (by simpa [hcv] using h)⟩)
    (fun u hu hu' => by
      obtain ⟨v, hv⟩ := hu'.exists_right_inv
      have hv' := congrArg c hv
      rw [map_mul, hu, map_one] at hv'
      obtain ⟨s, rfl⟩ := hfix v (by linear_combination v * hv' - c v * hv)
      obtain ⟨r, rfl⟩ := hfix u hu
      have hr : IsUnit r := IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hv, map_one]))
      obtain ⟨x, hx, h⟩ := hnorm hr.unit
      exact ⟨⟨x, hx⟩, Subtype.ext h⟩)
    hG (Matrix.isUnit_det_of_right_inverse hGQ)
  have hQ : (P⁻¹)ᵀ * G * (P⁻¹).map c = 1 := by
    rw [hGP, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.transpose_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.map_one _ (map_zero c) (map_one c)]
  refine ⟨fun i => ∑ k, P⁻¹ k i • b k, fun i j => ?_, le_antisymm ?_ ?_⟩
  · have h := congrArg Subtype.val (congrFun (congrFun hQ i) j)
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero] at h
    rw [← h]
    simp only [hsm, hf_sum_l, hf_sum_r, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum,
      Subring.coe_mul, Matrix.transpose_apply, Matrix.map_apply, hcv, hGv]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmem l)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine (Submodule.mem_span_range_iff_exists_fun L.O).2 ⟨fun i => P i k, ?_⟩
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ i, P i k * P⁻¹ l i = if l = k then 1 else 0 := fun l => by
      rw [← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hP, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp [← Finset.sum_smul, h]

end GlobalTheory.HL.SelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWtEqMulNu
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordDatum

theorem exists_invVol_eq_mul {G : Type} [Group G] (K' K0 : Subgroup G) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ K : Subgroup G, K0.relIndex K ≠ 0 → K.relIndex K0 ≠ 0 →
      invVol K' K = κ * invVol K0 K := by
  by_cases hc : K'.relIndex K0 ≠ 0 ∧ K0.relIndex K' ≠ 0
  · refine ⟨invVol K' K0, ?_, fun K hK hK' => ?_⟩
    · unfold invVol
      positivity
    · exact (invVol_mul_pos_le_conj K' K0 K hc.1 hc.2
        (Subgroup.relIndex_ne_zero_trans hc.1 hK)
        (Subgroup.relIndex_ne_zero_trans hK' hc.2)).1
  · refine ⟨0, le_rfl, fun K hK hK' => ?_⟩
    rw [zero_mul]
    unfold invVol
    by_cases h1 : K.relIndex K' = 0
    · simp [h1]
    · have h2 : K'.relIndex K = 0 := by
        by_contra h2
        exact hc ⟨Subgroup.relIndex_ne_zero_trans h2 hK', Subgroup.relIndex_ne_zero_trans hK h1⟩
      simp [h2]

theorem exists_wt_eq_mul_nu : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ d0 : LocNG.Datum P, ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → LocNG.Datum.wt d0 d = κ * S.nu (c.dat d) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ, hK⟩ :=
    exists_invVol_eq_mul (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) S.complementReferenceCompactSubgroup
  refine ⟨κ, hκ, fun d Λ hT => ?_⟩
  obtain ⟨h1, h2⟩ := (Frames.stab_commensurable_invVol_smul M.L r k S).2 (c.dat d) Λ hT
  rw [(transport M hM H r k P S c).2.2.2.2 d0 d]
  exact hK _ h1 h2

end GlobalTheory.HL.CoordDatum
end

