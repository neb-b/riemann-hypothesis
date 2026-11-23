module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlueBackOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAInj
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Inj

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem hermSp_W0_eq_perp_span_range_MMfam {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.W0 f f' = H.perp (Submodule.span E (Set.range (Sum.elim f f'))) := by
  rw [Set.Sum.elim_range, Submodule.span_union]
  rfl

theorem span_frames_le_MM {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) :
    Submodule.span E (Set.range (Sum.elim t.f t.f')) ≤ Submodule.span E (Set.range (H.MMfam t)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  unfold HermSp.MMfam
  split
  · exact Submodule.subset_span ⟨i, rfl⟩
  · rename_i g _
    have hq : ((g.q : F)) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    set c : E := algebraMap F E ((g.q : F))⁻¹ with hc
    have hcu : IsUnit c := by
      rw [hc]
      exact (IsUnit.mk0 _ (inv_ne_zero hq)).map (algebraMap F E)
    rcases i with a | a
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · have h1 : t.f a ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b))) :=
        Submodule.subset_span ⟨Sum.inl a, rfl⟩
      have h2 : c • (t.f' a - t.f a) ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b))) :=
        Submodule.subset_span ⟨Sum.inr a, rfl⟩
      have h3 : t.f' a = t.f a + (((hcu.unit)⁻¹ : Eˣ) : E) • (c • (t.f' a - t.f a)) := by
        rw [smul_smul, IsUnit.val_inv_mul, one_smul]
        abel
      show t.f' a ∈ _
      rw [h3]
      exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

private theorem span_MMfam_eq_span_f_f' {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) :
    Submodule.span E (Set.range (H.MMfam t)) = Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  refine le_antisymm ?_ (span_frames_le_MM H t)
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h := MMfam_mem_sup H t i
  refine (sup_le ?_ ?_ : H.Xp t.f ⊔ H.Xp t.f' ≤ _) h
  · exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)
  · exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)

private theorem isCompl_span_perp_of_isGeneric {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) (ht : H.IsGeneric t) :
    IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f')))
      (H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f')))) := by
  have h := isCompl_span_frames_W0 H t.f t.f' t.T t.T' ⟨ht.1.2.1.2.1, ht.1.2.1.2.2.1⟩
    ⟨ht.1.2.2.1.2.1, ht.1.2.2.1.2.2.1⟩ ht.1.2.2.2.1 (isUnit_Gdet H _ _ _ _ ht.1.2.2.2.2.1)
  rwa [hermSp_W0_eq_perp_span_range_MMfam] at h

private theorem mem_MMsharp_of_integral_pairing {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) (abelian₂ : Submodule (↥M.L.O) V) (hmem : ∀ a, H.MMfam t a ∈ abelian₂) (u : V)
    (hu : u ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')))
    (hint : ∀ y ∈ abelian₂, y ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) → H.h u y ∈ M.L.O) :
    u ∈ MMsharp H t := by
  refine ⟨by rw [span_MMfam_eq_span_f_f']; exact hu, ?_⟩
  intro m hm
  apply hint m
  · exact (Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hmem a)) hm
  · rw [← span_MMfam_eq_span_f_f' H t]
    exact Submodule.span_le_restrictScalars (↥M.L.O) E _ hm

theorem glueInj_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) : GlueInj M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT Λ₂ Λ₂' hG hTh hG' hTh' hrel
  obtain ⟨ψ, hψh, hψ⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hG.1.2.2.2.1
  have hW₁ := hermSp_W0_eq_perp_span_range_MMfam H t₁.f t₁.f'
  have hW₂ := hermSp_W0_eq_perp_span_range_MMfam H f₂ f₂'
  have hU₁ := isCompl_span_perp_of_isGeneric H t₁ hT.1
  have key : ∀ A B : Submodule (↥M.L.O) V,
      H.IsGeneric { abelian₂ := A, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } →
      ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' →
      ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } B φ φ' →
      (∀ (m₁ : ↥(MMsharp H t₁))
          (m₂ : ↥(MMsharp H { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' })),
          GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' m₁ m₂ →
          GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } B φ φ' m₁ m₂) →
      A ≤ B := by
    intro A B hGA hThA hThB hAB x hx
    let U₂ : Submodule E V := Submodule.span E (Set.range (Sum.elim f₂ f₂'))
    let U₁ : Submodule E V := Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))
    have hU₂ : IsCompl U₂ (H.perp U₂) := isCompl_span_perp_of_isGeneric H _ hGA
    have gA := local_hermitian_glue F E M hM V H A hGA.1.1 U₂ hU₂
    have g₁ := local_hermitian_glue F E M hM V H t₁.abelian₂ hT.1.1.1 U₁ hU₁
    obtain ⟨p, hp, hpint, q, hq, hqint, hxpq⟩ : ∃ p ∈ U₂, (∀ y ∈ A, y ∈ U₂ → H.h p y ∈ M.L.O) ∧
        ∃ q ∈ H.perp U₂, (∀ y ∈ A, y ∈ H.perp U₂ → H.h q y ∈ M.L.O) ∧ p + q = x :=
      ⟨_, Submodule.coe_mem _, (gA.1 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩,
       _, Submodule.coe_mem _, (gA.2 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩,
       Submodule.projection_add_projection_eq_self hU₂ x⟩
    have hpS : p ∈ MMsharp H { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } :=
      mem_MMsharp_of_integral_pairing H _ A hGA.2.1 p hp hpint
    have hqW : q ∈ H.W0 f₂ f₂' := hW₂.ge hq
    obtain ⟨n₁, hψn₁⟩ : ∃ n₁ : ↥(H.W0 t₁.f t₁.f'), (ψ n₁ : V) = q := ⟨ψ.symm ⟨q, hqW⟩, by simp⟩
    have hcorr₁ : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' (n₁ : V) q :=
      (hψ _ _).mpr ⟨n₁.2, hψn₁⟩
    have hn₁int : ∀ y ∈ t₁.abelian₂, y ∈ H.perp U₁ → H.h (n₁ : V) y ∈ M.L.O := by
      intro y hy hyp
      have hyW : y ∈ H.W0 t₁.f t₁.f' := hW₁.ge hyp
      have hc : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' y
          (ψ ⟨y, hyW⟩ : V) := (hψ _ _).mpr ⟨hyW, rfl⟩
      have hyA : (ψ ⟨y, hyW⟩ : V) ∈ A := (hThA _ _ hc).mp hy
      have hyp2 : (ψ ⟨y, hyW⟩ : V) ∈ H.perp U₂ := hW₂.le (ψ ⟨y, hyW⟩).2
      have e : H.h (n₁ : V) y = H.h q (ψ ⟨y, hyW⟩ : V) := by
        rw [← hψn₁]
        exact (hψh n₁ ⟨y, hyW⟩).symm
      rw [e]
      exact hqint _ hyA hyp2
    have hn₁p : (n₁ : V) ∈ H.perp U₁ := hW₁.le n₁.2
    obtain ⟨z, hz, hzn⟩ := (g₁.2 _ hn₁p).mpr hn₁int
    have hmS : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) ∈ MMsharp H t₁ :=
      mem_MMsharp_of_integral_pairing H t₁ t₁.abelian₂ hT.1.2.1 _ (Submodule.coe_mem _)
        ((g₁.1 _ (Submodule.coe_mem _)).mp ⟨z, hz, rfl⟩)
    have hzsum : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) = z := by
      rw [← hzn]
      exact Submodule.projection_add_projection_eq_self hU₁ z
    have hz' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) ∈ t₁.abelian₂ := by
      rw [hzsum]; exact hz
    have hglA : GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ'
        ⟨_, hmS⟩ ⟨p, hpS⟩ :=
      ⟨n₁, q, hcorr₁, hz', by show p + q ∈ A; rw [hxpq]; exact hx⟩
    obtain ⟨n₁', n₂', hc', h1', h2'⟩ := hAB _ _ hglA
    obtain ⟨hn₁'W, hψ'⟩ := (hψ _ _).mp hc'
    have h1'' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + n₁' ∈ t₁.abelian₂ := h1'
    have hd : n₁' - (n₁ : V) ∈ t₁.abelian₂ := by
      have h0 := t₁.abelian₂.sub_mem h1'' hz'
      rwa [add_sub_add_left_eq_sub] at h0
    have hdW : n₁' - (n₁ : V) ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁'W n₁.2
    have hψd : (ψ ⟨n₁' - n₁, hdW⟩ : V) = n₂' - q := by
      have e : (⟨n₁' - n₁, hdW⟩ : ↥(H.W0 t₁.f t₁.f')) = ⟨n₁', hn₁'W⟩ - n₁ := rfl
      rw [e, map_sub, Submodule.coe_sub, hψ', hψn₁]
    have hcd : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ'
        (n₁' - n₁) (n₂' - q) := (hψ _ _).mpr ⟨hdW, hψd⟩
    have hB : n₂' - q ∈ B := (hThB _ _ hcd).mp hd
    have h2'' : p + n₂' ∈ B := h2'
    have h0 := B.sub_mem h2'' hB
    have e : p + n₂' - (n₂' - q) = x := by rw [← hxpq]; abel
    rwa [e] at h0
  exact le_antisymm (key Λ₂ Λ₂' hG hTh hTh' (fun m₁ m₂ => (hrel m₁ m₂).mp))
    (key Λ₂' Λ₂ hG' hTh' hTh (fun m₁ m₂ => (hrel m₁ m₂).mpr))

end Inj

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBAt
section
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minors

variable {K : Type*} [CommRing K]

theorem sum_castLE {N l : ℕ} (h : l ≤ N) (f : Fin N → K) (hf : ∀ k : Fin N, l ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k' : Fin l, f (Fin.castLE h k') := by
  have hsub : (Finset.univ : Finset (Fin l)).map (Fin.castLEEmb h) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub (fun k _ hk => ?_), Finset.sum_map]
  · rfl
  · apply hf
    by_contra hlt
    push_neg at hlt
    exact hk (Finset.mem_map.2 ⟨⟨k.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem submatrix_loUni_mul {N l : ℕ} (h : l ≤ N) (L A U : Matrix (Fin N) (Fin N) K) (hL : IsLoUni L)
    (hU : IsUpUni U) :
    (L * A * U).submatrix (Fin.castLE h) (Fin.castLE h) =
      L.submatrix (Fin.castLE h) (Fin.castLE h) * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        U.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hin : ∀ m : Fin N, ∑ k, L (Fin.castLE h i) k * A k m =
      ∑ k' : Fin l, L (Fin.castLE h i) (Fin.castLE h k') * A (Fin.castLE h k') m := fun m =>
    sum_castLE h _ fun k hk => by
      rw [(hL _ _).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le (by simpa using i.isLt) hk)), zero_mul]
  simp only [hin]
  exact sum_castLE h _ fun m hm => by
    rw [(hU _ _).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le (by simpa using j.isLt) hm)), mul_zero]

theorem det_sub_loUni {N l : ℕ} (h : l ≤ N) (L A U : Matrix (Fin N) (Fin N) K) (hL : IsLoUni L) (hU : IsUpUni U) :
    ((L * A * U).submatrix (Fin.castLE h) (Fin.castLE h)).det = (A.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  rw [submatrix_loUni_mul h L A U hL hU, Matrix.det_mul, Matrix.det_mul]
  have h1 : (L.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    have hb : (L.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular OrderDual.toDual := by
      intro i j hij
      exact (hL _ _).1 (Fin.lt_iff_val_lt_val.2 (by
        simpa using Fin.lt_iff_val_lt_val.1 (OrderDual.toDual_lt_toDual.1 hij)))
    rw [Matrix.det_of_lowerTriangular _ hb]
    exact Finset.prod_eq_one fun i _ => (hL _ _).2 rfl
  have h2 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    have hb : (U.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro i j hij
      exact (hU _ _).1 (Fin.lt_iff_val_lt_val.2 (by simpa using Fin.lt_iff_val_lt_val.1 hij))
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_eq_one fun i _ => (hU _ _).2 rfl
  rw [h1, h2, one_mul, mul_one]

theorem det_sub_ZhatOM {r l : ℕ} (h : l ≤ r + 1) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ((ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (∏ b : Fin l, ((-1 : K) ^ (r - b.val))) * (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  have e : (ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h) =
      Z.submatrix (Fin.castLE h) (Fin.castLE h) * Matrix.diagonal fun b : Fin l => (-1 : K) ^ (r - b.val) := by
    ext a b
    simp [ZhatOM, Matrix.mul_diagonal, mul_comm]
  rw [e, Matrix.det_mul, Matrix.det_diagonal, mul_comm]

end Minors

theorem conjF_eq_star {D : Formalism.BasicNotions.D7} (x : D.host.E) : D.conjF x = star x :=
  (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm

theorem atPtG_holds {D : Formalism.BasicNotions.D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : AtPtG u u' F0 what₂ := by
  intro γ w hat
  obtain ⟨F', -, hG, L, U, hL, hU, hZ⟩ := hat
  have N_eq : ∀ (l : ℕ) (h : l ≤ D.R.rS + 1),
      leadMinorE (ZhatL (lf D F0) F') l * star (leadMinorE (ZhatL (lf D F0) F') l) =
        Dmin w l * D.conjF (Dmin w l) := by
    intro l h
    have e1 : ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det =
        (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) *
          ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      rw [← det_sub_loUni h L (ptMat w) U hL hU, ← hZ]
      exact det_sub_ZhatOM h _
    have hss : (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) *
        (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun b _ => by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have hst : star (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) =
        ∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val)) := by
      rw [star_prod]
      exact Finset.prod_congr rfl fun b _ => by rw [star_pow, star_neg, star_one]
    have hD : Dmin w l = ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      unfold Dmin
      rw [dite_eq_left h]
    have hM : leadMinorE (ZhatL (lf D F0) F') l =
        ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      unfold leadMinorE
      rw [dite_eq_left h]
    rw [hD, hM, conjF_eq_star, e1, star_mul', hst]
    linear_combination (-(((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det *
      star ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det)) * hss
  have key : Gval (lf D F0) F' = Gpt (D.mem u).A.T (D.mem u').A.T w := by
    rw [CntLocal.gz_eq]
    unfold CntLocal.GZ Gpt
    rw [N_eq (D.R.rS + 1) le_rfl, N_eq D.R.rS (Nat.le_succ _)]
  rw [← key]
  exact hG

theorem dnInDens_of {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hN : NormRepElig u u' F0 what₂) (hrows : IsRowReps D F0 what₂) :
    DnInDens u u' F0 what₂ := by
  intro γ w hγ
  have hex := hN γ w hγ
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dite_eq_left hex]
  obtain ⟨⟨hPD, hmk⟩, hadm, -, -, -⟩ := hex.choose_spec
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam (hrows.1 γ.lam γ.mem)
  have hGt := TermDef.Gt_mk hTF.1 ⟨_, hPD⟩
  have hGen := TermDef.isGen_mk (gS D) hTF.2.2.2.1 ⟨_, hPD⟩
  rw [hmk] at hGt hGen
  refine ⟨γ.lam, γ.mem, hex.choose.2.1, ⟨hPD.1, hPD.2.1, ?_⟩, hadm, hGen.1 hγ.1.1, hPD.2.2, hz.symm⟩
  exact fun h => hγ.1.2 (hGt.trans h)

end Formalism.L2.SG.LsDatumB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBTup
section
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Tup

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {T T' : ℕ}

theorem fL_eq (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) :
    fL M δ T T' p w τ O = hL M δ T T' p w O * kL M δ T T' p w τ O := by
  by_cases h1 : IsLCls M δ T T' p w O <;> simp [fL, hL, kL, h1]

theorem gL_eq (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) :
    gL M δ T T' p w τ O = hL M δ T T' p w O * eL M δ T T' p w τ O := by
  by_cases h1 : IsLCls M δ T T' p w O <;>
    by_cases h2 : thL M δ T T' p w (repL M δ T T' p w O) = τ <;> simp [gL, hL, eL, h1, h2]

theorem eL_zero_or_one (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS))
    (O : Set (MatP D p)) : eL M δ T T' p w τ O = 0 ∨ eL M δ T T' p w τ O = 1 := by
  unfold eL
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem base_factors {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {θ : Option ((M p).Cls D.R.rS)}
    (hf : ∀ τ O, fL M δ T T' p w τ O = if O = x0L M δ T T' p w ∧ τ = θ then 1 else 0)
    (hg : ∀ τ O, gL M δ T T' p w τ O = if O = x0L M δ T T' p w ∧ τ = θ then 1 else 0) :
    hL M δ T T' p w (x0L M δ T T' p w) = 1 ∧ kL M δ T T' p w θ (x0L M δ T T' p w) = 1 ∧
      eL M δ T T' p w θ (x0L M δ T T' p w) = 1 := by
  have g1 := hg θ (x0L M δ T T' p w)
  rw [if_pos ⟨rfl, rfl⟩, gL_eq] at g1
  have he : eL M δ T T' p w θ (x0L M δ T T' p w) = 1 := by
    rcases eL_zero_or_one (M := M) (δ := δ) (T := T) (T' := T') p w θ (x0L M δ T T' p w) with h | h
    · rw [h, mul_zero] at g1
      exact absurd g1 zero_ne_one
    · exact h
  rw [he, mul_one] at g1
  have f1 := hf θ (x0L M δ T T' p w)
  rw [if_pos ⟨rfl, rfl⟩, fL_eq, g1, one_mul] at f1
  exact ⟨g1, f1, he⟩

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem partnerTupleSum_of {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hC : CoefProd M δ u u' F0 what₂) (hN : PartnerCount M δ u u' F0 what₂) : PartnerTupleSum M δ u u' F0 what₂ := by
  intro γ w hγ w' hG' hk
  obtain ⟨hres, hcnt⟩ := hN γ w hγ w' hG' hk
  refine ⟨hres, fun x => ?_⟩
  obtain ⟨S, hS⟩ := hU w' hG'
  have hRf := hR γ w hγ
  have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
      hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p) = 1 ∧
        kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p) = 1 := by
    intro p hp
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hth : thT M δ γ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
    have hx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' := by
      by_contra h
      exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
    rw [hx, hth]
    have hb := base_factors (fun τ O => ((hS p hpS).2 τ O).1) (fun τ O => ((hS p hpS).2 τ O).2)
    exact ⟨hb.1, hb.2.1⟩
  have hfunc : (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
        PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w') =
      fun γ' => (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p)) *
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) := by
    funext γ'
    rw [hC γ'.1 w' γ'.2.1.2, γ'.2.2]
  rw [hfunc]
  have hv : (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p)) =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p)) *
        ∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p) := by
    rw [← finprod_mul_distrib]
    · exact finprod_congr fun p => fL_eq p w' _ _
    · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
      by_contra h
      exact (Function.mem_mulSupport.1 hp) (hone p h).1
    · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
      by_contra h
      exact (Function.mem_mulSupport.1 hp) (hone p h).2
  rw [hv]
  exact (hcnt x).mul_left _

theorem fiberTupleSum_of {L : CntLocal.LocSp D M} {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hC : CoefProd M δ u u' F0 what₂) (hN : FiberCount M δ L u u' F0 what₂) : FiberTupleSum M δ L u u' F0 what₂ := by
  intro nc hnc ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  obtain ⟨hres, hcnt⟩ := hN nc hnc ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  refine ⟨hres, fun x => ?_⟩
  obtain ⟨S, hS⟩ := hU w hG
  have hRf := hR γ₀ w₀ hγ₀
  have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
      hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p) = 1 ∧
        eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p) = 1 := by
    intro p hp
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hth : thT M δ γ₀ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
    have hx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
      by_contra h
      exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
    rw [hx, hth]
    have hb := base_factors (fun τ O => ((hS p hpS).2 τ O).1) (fun τ O => ((hS p hpS).2 τ O).2)
    exact ⟨hb.1, hb.2.2⟩
  have hfunc : (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
      (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
        (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w) =
      fun γ => (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
        ((PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ)) := by
    funext γ
    rw [hC γ.1 w γ.2.1.1, γ.2.2]
    ring
  rw [hfunc]
  have hv : (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
      (∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) := by
    rw [show (∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) =
        (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p) from by
      rw [← finprod_mul_distrib]
      · exact finprod_congr fun p => gL_eq p w _ _
      · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
        by_contra h
        exact (Function.mem_mulSupport.1 hp) (hone p h).1
      · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
        by_contra h
        exact (Function.mem_mulSupport.1 hp) (hone p h).2]
    ring
  rw [hv]
  exact (hcnt x).mul_left _

end Tup

end Formalism.L2.SG.LsDatumB
end
end

