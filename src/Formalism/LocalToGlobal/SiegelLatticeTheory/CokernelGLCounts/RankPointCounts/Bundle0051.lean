module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GenericityConstantDoubleCosets
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGenLoc
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem starGenLoc_of_P (hP : CtxP u u' F0 what₂) : StarGenLoc Zd u u' F0 what₂ := by
  intro γ w hγ p
  have hR : IsRowLat D F0 γ.lam := hP.2.1.1 γ.lam γ.mem
  obtain ⟨hgen, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
  have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
    (h1e.trans h2e.symm)
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) :=
    (PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have hGv : Gval (lf D F0) (repF γ) ≠ 0 := by
    intro hz
    apply hG
    exact (Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2).symm.trans hz
  exact (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 γ.lam (repF γ) hR h2
    (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hGv).1 hgenR p

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGramPair
section
noncomputable section

open scoped Classical
open Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem lm_conjTranspose {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) :
    leadMinorE Aᴴ l = star (leadMinorE A l) := by
  unfold leadMinorE
  split_ifs with h
  · rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]
  · simp

theorem eq_of_mulVec_last {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : A.det ≠ 0) (x : Fin (r + 1) → E)
    (c : E) (h : A *ᵥ x = c • Pi.single (Fin.last r) 1) :
    x = (c / A.det) • fun b => A.adjugate b (Fin.last r) := by
  have hx : x = A⁻¹ *ᵥ (c • Pi.single (Fin.last r) 1) := by
    rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  rw [hx, Matrix.inv_def, Ring.inverse_eq_inv']
  ext b
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.single_apply, div_eq_inv_mul]
  ring

theorem gram_pair_det {r : ℕ} {T T' : E} (F : FlagG S r T) (f₁ : Fin (r + 1) → S.V)
    (h1 : ∀ a b, (a ≠ Fin.last r ∨ b ≠ Fin.last r) → S.hT (f₁ a) (f₁ b) = 0)
    (h2 : S.hT (f₁ (Fin.last r)) (f₁ (Fin.last r)) = -T')
    (hZ₁ : (gram S f₁ F.fvec).det ≠ 0)
    (hG : (gram S f₁ F.fvec).det * star (gram S f₁ F.fvec).det -
      T * T' * (leadMinorE (gram S f₁ F.fvec) r * star (leadMinorE (gram S f₁ F.fvec) r)) ≠ 0) :
    (gram S (Sum.elim F.fvec f₁) (Sum.elim F.fvec f₁)).det ≠ 0 := by
  set f := F.fvec with hf
  set Z₁ := gram S f₁ f with hZ₁d
  set l := Fin.last r with hl
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set α : Fin (r + 1) → E := fun a => v (Sum.inl a) with hα
  set β : Fin (r + 1) → E := fun b => v (Sum.inr b) with hβ
  have hrow : ∀ k, ∑ a, S.hT (Sum.elim f f₁ k) (f a) * α a + ∑ b, S.hT (Sum.elim f f₁ k) (f₁ b) * β b = 0 := by
    intro k
    have := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, gram, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply] at this
    exact this
  have hΓ : ∀ a' (x : Fin (r + 1) → E), ∑ a, S.hT (f a') (f a) * x a = if a' = l then -T * x l else 0 := by
    intro a' x
    rw [Finset.sum_eq_single l]
    · split_ifs with h
      · subst h; rw [show S.hT (f l) (f l) = -T from gram_fvec_last F]
      · rw [show S.hT (f a') (f l) = 0 from gram_fvec_zero F _ _ (Or.inl h), zero_mul]
    · intro a _ ha; rw [show S.hT (f a') (f a) = 0 from gram_fvec_zero F _ _ (Or.inr ha), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hΓ' : ∀ b' (x : Fin (r + 1) → E), ∑ b, S.hT (f₁ b') (f₁ b) * x b = if b' = l then -T' * x l else 0 := by
    intro b' x
    rw [Finset.sum_eq_single l]
    · split_ifs with h
      · subst h; rw [h2]
      · rw [h1 _ _ (Or.inl h), zero_mul]
    · intro b _ hb; rw [h1 _ _ (Or.inr hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hZβ : Z₁ *ᵥ β = (T * α l) • Pi.single l 1 := by
    ext a'
    have e := hrow (Sum.inl a')
    simp only [Sum.elim_inl, hΓ] at e
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul, hZ₁d, gram]
    split_ifs at e ⊢ with h
    · linear_combination e
    · linear_combination e
  have hZα : Z₁ᴴ *ᵥ α = (T' * β l) • Pi.single l 1 := by
    ext b'
    have e := hrow (Sum.inr b')
    simp only [Sum.elim_inr, hΓ'] at e
    have hc : ∀ a, S.hT (f₁ b') (f a) = Z₁ᴴ b' a := fun a => by
      rw [Matrix.conjTranspose_apply, hZ₁d, gram, ← (LinearMap.isSymm_def.1 S.herm) (f₁ b') (f a),
        starRingEnd_apply, star_star]
    simp only [hc] at e
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs at e ⊢ with h
    · linear_combination e
    · linear_combination e
  have hZ₁h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁
  have eβ := eq_of_mulVec_last Z₁ hZ₁ β _ hZβ
  have eα := eq_of_mulVec_last Z₁ᴴ hZ₁h α _ hZα
  have eβl : β l = T * α l / Z₁.det * leadMinorE Z₁ r := by
    have := congrFun eβ l
    rw [this, Pi.smul_apply, smul_eq_mul, adj_last]
  have eαl : α l = T' * β l / star Z₁.det * star (leadMinorE Z₁ r) := by
    have := congrFun eα l
    rw [this, Pi.smul_apply, smul_eq_mul, adj_last, lm_conjTranspose, Matrix.det_conjTranspose]
  have hsZ : star Z₁.det ≠ 0 := star_ne_zero.2 hZ₁
  have hαl : α l = 0 := by
    have key : α l * (Z₁.det * star Z₁.det - T * T' * (leadMinorE Z₁ r * star (leadMinorE Z₁ r))) = 0 := by
      rw [eβl] at eαl
      field_simp at eαl
      linear_combination eαl
    rcases mul_eq_zero.1 key with h | h
    · exact h
    · exact absurd h hG
  have hβ0 : β = 0 := by rw [eβ, hαl, mul_zero, zero_div, zero_smul]
  have hβl : β l = 0 := by rw [hβ0]; rfl
  have hα0 : α = 0 := by rw [eα, hβl, mul_zero, zero_div, zero_smul]
  apply hv0
  funext k
  rcases k with a | b
  · exact congrFun hα0 a
  · exact congrFun hβ0 b

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfA
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.LprU

open Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

def GramInvE {ι : Type} [Fintype ι] [DecidableEq ι] (H : HermSp M V) (v : ι → V) : Prop :=
  ∃ N : Matrix ι ι E, N * H.gram v = 1

theorem eqz {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInvE H v) {z : V}
    (hz : z ∈ Submodule.span E (Set.range v)) (h0 : ∀ i, H.h z (v i) = 0) : z = 0 := by
  obtain ⟨N, hN⟩ := hN
  have hz0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V),
      H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [hz0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hz
  have hg : H.gram v *ᵥ c = 0 := by
    funext i
    rw [Pi.zero_apply, ← h0 i, hsum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc : c = 0 := by
    have h2 := congrArg (fun u => N *ᵥ u) hg
    simp only [Matrix.mulVec_mulVec, hN, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  simp [hc]

theorem decompE {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInvE H v) (x : V) :
    ∃ c : ι → E, ∀ i, H.h (x - ∑ j, c j • v j) (v i) = 0 := by
  obtain ⟨N, hN⟩ := hN
  have hN' : H.gram v * N = 1 := mul_eq_one_comm.mp hN
  have h0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V),
      H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  let w : ι → E := fun i => H.h x (v i)
  refine ⟨N *ᵥ w, fun i => ?_⟩
  have hsub : ∀ y z : V, H.h (y - z) (v i) = H.h y (v i) - H.h z (v i) := fun y z => by
    rw [sub_eq_add_neg, H.h_add_left, ← neg_one_smul E z, H.h_smul_left]
    ring
  rw [hsub, hsum]
  have e : ∑ j, (N *ᵥ w) j * H.h (v j) (v i) = (H.gram v *ᵥ (N *ᵥ w)) i :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e, Matrix.mulVec_mulVec, hN', Matrix.one_mulVec, sub_self]

theorem y_eq_om {r : ℕ} (f f' : Fin (r + 1) → V) (α : Fin (r + 1) → E)
    (hy : ∀ b, b ≠ Fin.last r → H.h (∑ a, α a • f a) (f' b) = 0) :
    M.L.cj (H.Zhat f f').det • ∑ a, α a • f a = H.h (∑ a, α a • f a) (f' (Fin.last r)) • H.om f f' := by
  have h0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset (Fin (r + 1))) (c : (Fin (r + 1)) → E) (y : V),
      H.h (∑ a ∈ s, c a • f a) y = ∑ a ∈ s, c a * H.h (f a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  set Z := H.Zhat f f' with hZ
  set W := Z.map M.L.cj with hW
  set β : Fin (r + 1) → E := fun b => H.h (∑ a, α a • f a) (f' b) with hβdef

  have hβ : β = Wᵀ *ᵥ α := by
    funext b
    simp only [hβdef]
    rw [hsum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [H.h_herm (f' b) (f a)]
      exact mul_comm _ _

  have hcr : W.det • α = W.adjugateᵀ *ᵥ β := by
    rw [hβ, Matrix.mulVec_mulVec, Matrix.adjugate_transpose, Matrix.adjugate_mul, Matrix.det_transpose]
    first
      | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
      | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      | (ext a; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
  have hdet : W.det = M.L.cj Z.det := by
    first
      | exact (RingHom.map_det M.L.cj Z).symm
      | exact (RingHom.map_det (M.L.cj : E →+* E) Z).symm
  have hadj : W.adjugate = Z.adjugate.map M.L.cj := by
    first
      | (have h := RingHom.map_adjugate (M.L.cj : E →+* E) Z
         simp only [RingHom.mapMatrix_apply, RingHom.coe_coe] at h
         exact h.symm)
  have hcomp : ∀ a, M.L.cj Z.det * α a = β (Fin.last r) * M.L.cj (Z.adjugate (Fin.last r) a) := by
    intro a
    have h1 := congrFun hcr a
    rw [Pi.smul_apply, smul_eq_mul, hdet] at h1
    rw [h1, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.transpose_apply, hadj, Matrix.map_apply]
      ring
    · intro b _ hb
      have hb0 : β b = 0 := hy b hb
      rw [hb0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold Formalism.MainNotions.S.Loc.HermSp.om
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, smul_smul, hcomp a]

end Formalism.MainNotions.S.Loc.HermSp.LprU
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FibSumOf
section
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem fibSum_of (hD : TupFun M δ u u' F0 what₂) (hC : RepAtTup M δ u u' F0 what₂) (hB : OrbZT M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.FCount.FibSum M δ u u' F0 what₂ := by
  intro hA hT hP hN hR hE w hG Z hZ hfin
  have hpre : Pre M δ u u' F0 what₂ := ⟨hA, hT, hP, hN, hR, hE⟩
  let S : Set (TermDef.Term D u u' F0 what₂) := {γ | EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z}
  have hrep : ∀ γ ∈ S, RepIn u u' F0 what₂ γ Z := fun γ hγ => hC hpre γ w hG Z hZ hγ.1 hγ.2
  have hclsFin : ∀ Λ ∈ what₂, (clsSet F0 u' Λ Z).Finite := fun Λ hΛ =>
    Set.encard_ne_top_iff.1 (by rw [← cntE_eq]; exact hfin Λ hΛ)
  have hsub : ∀ γ : TermDef.Term D u u' F0 what₂,
      PairVal.orbT D u u' F0 what₂ γ Z ⊆ clsSet F0 u' γ.lam Z := by
    rintro γ O ⟨F', hF', -, rfl⟩
    exact ⟨F', hF', rfl⟩
  have horbFin : ∀ γ : TermDef.Term D u u' F0 what₂, (PairVal.orbT D u u' F0 what₂ γ Z).Finite := fun γ =>
    (hclsFin γ.lam γ.mem).subset (hsub γ)
  have hne : ∀ γ ∈ S, (PairVal.orbT D u u' F0 what₂ γ Z).Nonempty := by
    intro γ hγ
    obtain ⟨F', hF', hr⟩ := hrep γ hγ
    exact ⟨_, F', hF', hr, rfl⟩
  have hnc : ∀ γ ∈ S, (PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard = (PairVal.orbT D u u' F0 what₂ γ Z).ncard := by
    intro γ hγ
    rw [Set.ncard_def, Set.ncard_def, hB hpre γ w Z hγ.1 hZ (hrep γ hγ)]

  have hSfin : S.Finite := by
    have hU : S ⊆ ⋃ Λ ∈ (what₂ : Set (Submodule (𝓞 D.host.E) (VS D).V)), ⋃ O ∈ clsSet F0 u' Λ Z,
        {γ : TermDef.Term D u u' F0 what₂ | γ.lam = Λ ∧ O ∈ PairVal.orbT D u u' F0 what₂ γ Z} := by
      intro γ hγ
      obtain ⟨O, hO⟩ := hne γ hγ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨γ.lam, γ.mem, O, hsub γ hO, rfl, hO⟩
    refine Set.Finite.subset ?_ hU
    refine Set.Finite.biUnion what₂.finite_toSet (fun Λ hΛ => Set.Finite.biUnion (hclsFin Λ hΛ) (fun O _ => ?_))
    refine Set.Subsingleton.finite (fun γ₁ h₁ γ₂ h₂ => ?_)
    exact orbT_disj (h₁.1.trans h₂.1.symm) h₁.2 h₂.2

  have hrow : ∀ Λ ∈ what₂, ∑ γ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
      ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) = ((clsSet F0 u' Λ Z).ncard : ℝ) := by
    intro Λ hΛ
    have hbU : (hclsFin Λ hΛ).toFinset =
        (hSfin.toFinset.filter (fun γ => γ.lam = Λ)).biUnion (fun γ => (horbFin γ).toFinset) := by
      ext O
      simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨F', hF', rfl⟩
        refine ⟨termOf Λ hΛ F' (pd_of_ez hF'), ⟨⟨eligAt_termOf Λ hΛ hZ hF', ?_⟩, rfl⟩,
          mem_orbT_termOf Λ hΛ hF'⟩
        exact hD hpre _ w Z (eligAt_termOf Λ hΛ hZ hF') hZ (repIn_termOf Λ hΛ hF')
      · rintro ⟨γ, ⟨-, hγΛ⟩, hO⟩
        have := hsub γ hO
        rw [hγΛ] at this
        exact this
    have hdisj : ∀ γ₁ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ), ∀ γ₂ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
        γ₁ ≠ γ₂ → Disjoint (horbFin γ₁).toFinset (horbFin γ₂).toFinset := by
      intro γ₁ h₁ γ₂ h₂ hne12
      rw [Finset.disjoint_left]
      intro O hO₁ hO₂
      rw [Set.Finite.mem_toFinset] at hO₁ hO₂
      exact hne12 (orbT_disj ((Finset.mem_filter.1 h₁).2.trans (Finset.mem_filter.1 h₂).2.symm) hO₁ hO₂)
    rw [Set.ncard_eq_toFinset_card _ (hclsFin Λ hΛ), hbU, Finset.card_biUnion hdisj]
    push_cast
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Set.ncard_eq_toFinset_card _ (horbFin γ)]

  have hreal : ∑ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) =
      CntLocal.nu (CntLocal.Tn u') F0 what₂ Z := by
    have e1 : ∀ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) =
        PairVal.massRow D F0 what₂ γ.lam * ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) := by
      intro γ hγ
      rw [hnc γ ((Set.Finite.mem_toFinset hSfin).1 hγ)]
      rfl
    rw [Finset.sum_congr rfl e1]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun γ : TermDef.Term D u u' F0 what₂ => γ.lam) (t := what₂)
      (fun γ _ => γ.mem)]
    have e2 : ∀ Λ ∈ what₂, ∑ γ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
        PairVal.massRow D F0 what₂ γ.lam * ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) =
        PairVal.massRow D F0 what₂ Λ * ((clsSet F0 u' Λ Z).ncard : ℝ) := by
      intro Λ hΛ
      rw [← hrow Λ hΛ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun γ hγ => ?_)
      rw [(Finset.mem_filter.1 hγ).2]
    rw [Finset.sum_congr rfl e2]
    unfold CntLocal.nu PairVal.massRow
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun Λ _ => ?_)
    rw [Set.ncard_def, ← cntE_eq]
    unfold Formalism.MainNotions.S.Cnt.massRows
    ring
  haveI : Fintype {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} := hSfin.fintype
  have hs := hasSum_fintype (fun γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} =>
    (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
  have h1 : ∑ γ ∈ hSfin.toFinset, (PairVal.massTerm γ : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) =
      ∑ γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z},
        (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ) :=
    Finset.sum_subtype hSfin.toFinset (fun γ => Set.Finite.mem_toFinset hSfin) _
  have h2 : ((∑ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) : ℝ) : ℂ) =
      ∑ γ ∈ hSfin.toFinset, (PairVal.massTerm γ : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) := by
    push_cast
    rfl
  have key := h1.symm.trans (h2.symm.trans (congrArg (fun x : ℝ => (x : ℂ)) hreal))
  exact Eq.mpr (congrArg (HasSum _) key.symm) hs

end Count

end Formalism.L2.SG.Pf.FibPart
end
end

