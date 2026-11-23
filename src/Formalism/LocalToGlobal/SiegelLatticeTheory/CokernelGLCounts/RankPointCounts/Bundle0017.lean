module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioRetr
section
noncomputable section

namespace Formalism.L2.SG.Pf.ProdEP2Core

open Formalism.L2.SG.Pf.IndexCocycleOrbits

variable {G : Type} [Group G]

structure Retr (S N : Subgroup G) (π : G → G) : Prop where
  le : S ≤ N
  mul : ∀ x ∈ N, ∀ y ∈ N, π (x * y) = π x * π y
  mem : ∀ x ∈ N, π x ∈ S
  id : ∀ s ∈ S, π s = s

theorem Retr.one {S N : Subgroup G} {π : G → G} (h : Retr S N π) : π 1 = 1 := by
  have h1 := h.mul 1 N.one_mem 1 N.one_mem
  rw [mul_one] at h1
  simpa using h1

theorem Retr.inv {S N : Subgroup G} {π : G → G} (h : Retr S N π) {x : G} (hx : x ∈ N) : π x⁻¹ = (π x)⁻¹ := by
  have h1 := h.mul x⁻¹ (N.inv_mem hx) x hx
  rw [inv_mul_cancel, h.one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

def img {S N : Subgroup G} {π : G → G} (h : Retr S N π) (H : Subgroup G) (hH : H ≤ N) : Subgroup G where
  carrier := π '' H
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, H.mul_mem hx hy, h.mul x (hH hx) y (hH hy)⟩
  one_mem' := ⟨1, H.one_mem, h.one⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, H.inv_mem hx, h.inv (hH hx)⟩

theorem cj_eq_cj_img {S N : Subgroup G} {π : G → G} (h : Retr S N π) {H : Subgroup G} (hH : H ≤ N) {g₀ : G}
    (hg : g₀ ∈ N) (hC : cj g₀ H ≤ S) : cj g₀ H = cj (π g₀) (img h H hH) := by
  ext y
  rw [mem_cj, mem_cj]
  constructor
  · intro hy
    have hyS : y ∈ S := hC ((mem_cj).2 hy)
    have hyN : y ∈ N := h.le hyS
    refine (Set.mem_image π _ _).2 ⟨g₀ * y * g₀⁻¹, hy, ?_⟩
    rw [h.mul _ (N.mul_mem hg hyN) _ (N.inv_mem hg), h.mul _ hg _ hyN, h.inv hg, h.id y hyS]
  · intro hy
    obtain ⟨x, hx, hxe⟩ := (Set.mem_image π _ _).1 hy
    have hz : g₀⁻¹ * x * g₀ ∈ cj g₀ H := by
      rw [mem_cj]
      simpa [mul_assoc] using hx
    have hzS := hC hz
    have e1 : π (g₀⁻¹ * x * g₀) = g₀⁻¹ * x * g₀ := h.id _ hzS
    rw [h.mul _ (N.mul_mem (N.inv_mem hg) (hH hx)) _ hg, h.mul _ (N.inv_mem hg) _ (hH hx), h.inv hg,
      hxe] at e1
    have hyz : y = g₀⁻¹ * x * g₀ := by
      rw [← e1]
      group
    rw [hyz]
    simpa [mul_assoc] using hx

end Formalism.L2.SG.Pf.ProdEP2Core
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGlueCut
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GDefs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def ThL (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V :=
  t.abelian₂ ⊓ (H.W0 t.f t.f').restrictScalars M.L.O

def ThSharp (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) : Submodule M.L.O V where
  carrier := {w | w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O}
  add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun m hm => by
    rw [H.h_add_left]; exact M.L.O.add_mem (ha.2 m hm) (hb.2 m hm)⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun m _ => by rw [H.h_zero_left]; exact M.L.O.zero_mem⟩
  smul_mem' := fun c u hu => ⟨by rw [Subring.smul_def]; exact Submodule.smul_mem _ _ hu.1, fun m hm => by
    rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 (hu.2 m hm)⟩

abbrev DDW (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) : Type :=
  ↥(ThSharp H t N) ⧸ N.comap (ThSharp H t N).subtype

def dwMk (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) (w : ↥(ThSharp H t N)) : DDW H t N :=
  Submodule.Quotient.mk w

end GDefs

section GProps

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def CorrIso (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) →
    ∃ ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 f₂ f₂'), (∀ x y, H.h (ψ x) (ψ y) = H.h x y) ∧
      ∀ n₁ n₂ : V, Corr H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' n₁ n₂ ↔
        ∃ h₁ : n₁ ∈ H.W0 t₁.f t₁.f', (ψ ⟨n₁, h₁⟩ : V) = n₂

def GlueEta (M : Model F E) (r : ℕ) : Prop :=
  M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t →
    ∃ η : DDt H t ≃ₗ[M.L.O] DDW H t (ThL H t),
      (∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t (ThL H t))),
        η (ddMk H t m) = dwMk H t _ w ↔ (m : V) + w ∈ t.abelian₂) ∧
      (∀ (m m' : ↥(MMsharp H t)) (w w' : ↥(ThSharp H t (ThL H t))),
        η (ddMk H t m) = dwMk H t _ w → η (ddMk H t m') = dwMk H t _ w' →
          H.h m m' + H.h w w' ∈ M.L.O)

def GlueConv (M : Model F E) (r : ℕ) : Prop :=
  M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    IsUnit (H.gram (H.MMfam t)).det → MMInt H t →
    ∀ N : Submodule M.L.O V, N ≤ (H.W0 t.f t.f').restrictScalars M.L.O → N.FG →
      Submodule.span E (N : Set V) = H.W0 t.f t.f' → (∀ x ∈ N, ∀ y ∈ N, H.h x y ∈ M.L.O) →
    ∀ η : DDt H t ≃ₗ[M.L.O] DDW H t N,
      (∀ (m m' : ↥(MMsharp H t)) (w w' : ↥(ThSharp H t N)),
        η (ddMk H t m) = dwMk H t N w → η (ddMk H t m') = dwMk H t N w' → H.h m m' + H.h w w' ∈ M.L.O) →
      ∃! Λ : Submodule M.L.O V, H.IsSelfDual Λ ∧ H.Prim Λ (H.MMfam t) ∧
        Λ ⊓ (H.W0 t.f t.f').restrictScalars M.L.O = N ∧
        ∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t N)), η (ddMk H t m) = dwMk H t N w ↔ (m : V) + w ∈ Λ

def GenOfPrim (M : Model F E) (r n : ℕ) : Prop :=
  M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) →
    ∀ Λ₂ : Submodule M.L.O V, H.IsSelfDual Λ₂ → H.Prim Λ₂ (H.MMfam ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩) →
      H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩

end GProps

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob
section
noncomputable section

open scoped Classical

open NumberField ValuativeRel IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem lg_int_of_locF (t : D.host.F)
    (h : ∀ p : PlF D, (D.s.atP p).ιE (algebraMap D.host.F D.host.E t) ∈ (D.s.atP p).O) :
    t ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.F t fun p => ?_
  have h1 := h p
  rw [(D.s.atP p).O_def, (D.s.atP p).compat] at h1
  have : Nontrivial (D.s.atP p).Ep := by
    have := (D.s.atP p).free
    exact Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have h2 : IsIntegral 𝒪[(D.s.atP p).Fp] ((D.s.atP p).ιF t) :=
    (isIntegral_algebraMap_iff ).1 h1
  have h3 := (Valuation.integer.integers _).mem_of_integral h2
  have h4 : (D.s.atP p).ιF t ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [map_one]
    exact (valuation (D.s.atP p).Fp).vle_one_iff.2 h3
  simpa using ((D.s.atP p).val t 1).1 h4

theorem lg_cj_mem (p : PlF D) {y : (D.s.atP p).Ep} (hy : y ∈ (D.s.atP p).O) :
    (D.s.atP p).cj y ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hy ⊢
  exact hy.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])

theorem lg_iota_int (p : PlF D) (c : 𝓞 D.host.E) :
    (D.s.atP p).ιE (algebraMap (𝓞 D.host.E) D.host.E c) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h1 : IsIntegral ℤ ((D.s.atP p).ιE (c : D.host.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe c).map (D.s.atP p).ιE.toIntAlgHom
  exact h1.tower_top

theorem lg_int_of_loc (z : D.host.E) (h : ∀ p : PlF D, (D.s.atP p).ιE z ∈ (D.s.atP p).O) : IsIntegral ℤ z := by
  have hfix : ∀ y : D.host.E, D.conjF y = y → (∀ p : PlF D, (D.s.atP p).ιE y ∈ (D.s.atP p).O) →
      IsIntegral ℤ y := by
    intro y hy hl
    obtain ⟨a, rfl⟩ := Formalism.MainNotions.BridgeLemma.conjF_fix y hy
    obtain ⟨b, rfl⟩ := lg_int_of_locF a hl
    exact (NumberField.RingOfIntegers.isIntegral_coe b).algebraMap
  have hc : ∀ p : PlF D, (D.s.atP p).ιE (D.conjF z) ∈ (D.s.atP p).O := fun p => by
    rw [← (D.s.atP p).cj_ιE]
    exact lg_cj_mem p (h p)
  have ht := hfix (z + D.conjF z) (by rw [map_add (f := _), Formalism.MainNotions.BridgeLemma.conjF_inv, add_comm])
    fun p => by rw [map_add]; exact add_mem (h p) (hc p)
  have hn := hfix (z * D.conjF z) (by rw [map_mul, Formalism.MainNotions.BridgeLemma.conjF_inv, mul_comm])
    fun p => by rw [map_mul]; exact mul_mem (h p) (hc p)
  have hz : IsIntegral (integralClosure ℤ D.host.E) z := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨_, ht⟩ : integralClosure ℤ D.host.E) * Polynomial.X +
      Polynomial.C (⟨_, hn⟩ : integralClosure ℤ D.host.E), ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      show z ^ 2 - (z + D.conjF z) * z + z * D.conjF z = 0
      ring
  exact isIntegral_trans z hz

theorem locGlob : LocGlob D := by
  intro I hI x
  constructor
  · intro h
    have key : ∀ y ∈ (I⁻¹ : FI D), x * y ∈ (1 : FI D) := by
      intro y hy
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨⟨x * y, lg_int_of_loc _ fun p => ?_⟩, rfl⟩
      have hp := h p
      unfold LocMem at hp
      rw [map_mul]
      refine Submodule.span_induction
        (p := fun w _ => w * (D.s.atP p).ιE y ∈ (D.s.atP p).O) ?_ ?_ ?_ ?_ hp
      · rintro _ ⟨i, hi, rfl⟩
        rw [← map_mul]
        have hiy : i * y ∈ (1 : FI D) := by
          rw [← mul_inv_cancel₀ hI]
          exact FractionalIdeal.mul_mem_mul hi hy
        obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hiy
        rw [← hc]
        exact lg_iota_int p c
      · simp
      · intro a b _ _ ha hb
        rw [add_mul]
        exact add_mem ha hb
      · intro o a _ ha
        rw [smul_mul_assoc, Subring.smul_def]
        exact mul_mem o.2 ha
    have hle : FractionalIdeal.spanSingleton _ x * I⁻¹ ≤ 1 := by
      rw [FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c (key j hj)
    rw [← FractionalIdeal.spanSingleton_le_iff_mem]
    calc FractionalIdeal.spanSingleton _ x = FractionalIdeal.spanSingleton _ x * I⁻¹ * I := by
          rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
      _ ≤ I := FractionalIdeal.mul_le.2 fun a ha b hb => by
          obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 (hle ha)
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ c hb
  · intro hx p
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem lg_ddS_ne : ddS D ≠ 0 := by
  rw [ddS, Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem shapeNZ : ShapeNZ D := by
  have hd : ∀ k, ddPow D k ≠ 0 := fun k => zpow_ne_zero _ lg_ddS_ne
  refine ⟨hd, fun k => mul_ne_zero ?_ (hd k)⟩
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, qq]
  intro h0
  have hm : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {((Lat.gS D : ℕ) : 𝓞 D.host.E)} :=
    Ideal.mem_span_singleton_self _
  rw [h0, Ideal.mem_bot] at hm
  exact (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne' (by exact_mod_cast hm)

end Formalism.L2.SG.Pf.StabIntSh
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfStG
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.BlockPermutation

open Formalism.MainNotions.S Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj Matrix

variable {K : Type*} [Field K] {N : ℕ} (p : Point K N)

abbrev cv (a : Fin N) : K := pval p.1 a.val

theorem cv_ne (a : Fin N) : cv p a ≠ 0 :=
  pval_ne p.1 (fun b hb => (p.2.1 b hb).1) a.val (by rw [p.2.2]; exact a.isLt)

theorem cv_pinv (a : Fin N) : cv p (pinv p a) = cv p a := pval_pinv p a

theorem pinv_inj {a b : Fin N} (h : pinv p a = pinv p b) : a = b := by
  have := congrArg (pinv p) h
  rwa [pinv_pinv, pinv_pinv] at this

theorem ptMat_mul_mono : ptMat p * mono (pinv p) (fun a => (cv p a)⁻¹) = 1 := by
  rw [ptMat_eq_mono]
  funext a b
  rw [mul_mono_apply _ (pinv_pinv p)]
  by_cases h : a = b
  · subst h
    simp only [mono, if_true, Matrix.one_apply_eq]
    rw [cv_pinv]; exact mul_inv_cancel₀ (cv_ne p a)
  · have hne : pinv p b ≠ pinv p a := fun e => h (pinv_inj p e).symm
    simp only [mono, hne, if_false, zero_mul, Matrix.one_apply_ne h]

theorem ptMat_inv : (ptMat p)⁻¹ = mono (pinv p) (fun a => (cv p a)⁻¹) :=
  Matrix.inv_eq_right_inv (ptMat_mul_mono p)

theorem conj_apply (M : Matrix (Fin N) (Fin N) K) (a b : Fin N) :
    ((ptMat p)⁻¹ * M * ptMat p) a b = (cv p a)⁻¹ * M (pinv p a) (pinv p b) * cv p b := by
  rw [ptMat_inv]
  conv_lhs => rw [ptMat_eq_mono]
  rw [mul_mono_apply _ (pinv_pinv p), mono_mul_apply]
  simp only [cv, pval_pinv]

theorem conj'_apply (M : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    (ptMat p * M * (ptMat p)⁻¹) i j = cv p i * M (pinv p i) (pinv p j) * (cv p j)⁻¹ := by
  rw [ptMat_inv]
  conv_lhs => rw [ptMat_eq_mono]
  rw [mul_mono_apply _ (pinv_pinv p), mono_mul_apply]
  simp only [cv, pval_pinv]

theorem ptMat_isUnit : IsUnit (ptMat p).det := Matrix.isUnit_det_of_right_inverse (ptMat_mul_mono p)

def IsBlockDiagonalMatrix (X : Matrix (Fin N) (Fin N) K) : Prop := ∀ a b : Fin N, blkOf p.1 a.val ≠ blkOf p.1 b.val → X a b = 0

theorem blk_lt_of_lt {a b : Fin N} (hab : a < b) (hne : blkOf p.1 a.val ≠ blkOf p.1 b.val) :
    blkOf p.1 a.val < blkOf p.1 b.val :=
  lt_of_le_of_ne (blkOf_mono p.1 a.val b.val (le_of_lt hab)) hne

theorem X_of_st {β b : Matrix (Fin N) (Fin N) K} (hβ : IsLoUni β) (hb : IsUpUni b) (hW : β * ptMat p * b = ptMat p) :
    (ptMat p)⁻¹ * β * ptMat p = b⁻¹ ∧ UpU ((ptMat p)⁻¹ * β * ptMat p) ∧ IsBlockDiagonalMatrix p ((ptMat p)⁻¹ * β * ptMat p) := by
  have hu := ptMat_isUnit p
  have h1 : (ptMat p)⁻¹ * β * ptMat p * b = 1 := by
    rw [show (ptMat p)⁻¹ * β * ptMat p * b = (ptMat p)⁻¹ * (β * ptMat p * b) by simp only [Matrix.mul_assoc], hW,
      Matrix.nonsing_inv_mul _ hu]
  have hX : (ptMat p)⁻¹ * β * ptMat p = b⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  refine ⟨hX, ?_, ?_⟩
  · rw [hX]; exact upU_inv hb
  · intro a c hne
    rw [conj_apply]
    rcases lt_or_gt_of_ne (show a ≠ c from fun e => hne (by rw [e])) with h | h
    · have hb' := (lt_of_blk_lt p a c (blk_lt_of_lt p h hne)).2
      rw [(hβ _ _).1 hb', mul_zero, zero_mul]
    · have hup : UpU ((ptMat p)⁻¹ * β * ptMat p) := by rw [hX]; exact upU_inv hb
      have := (hup a c).1 h
      rwa [conj_apply] at this

theorem st_of_X {X : Matrix (Fin N) (Fin N) K} (hX : UpU X) (hB : IsBlockDiagonalMatrix p X) :
    IsLoUni (ptMat p * X * (ptMat p)⁻¹) ∧ IsUpUni X⁻¹ ∧
      ptMat p * X * (ptMat p)⁻¹ * ptMat p * X⁻¹ = ptMat p ∧ (ptMat p * X * (ptMat p)⁻¹).det = 1 := by
  have hu := ptMat_isUnit p
  have hXd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  refine ⟨fun i j => ⟨fun hij => ?_, fun hij => ?_⟩, upU_inv hX, ?_, ?_⟩
  · rw [conj'_apply]
    by_cases hs : blkOf p.1 i.val = blkOf p.1 j.val
    · have := (pinv_lt_iff p i j hs).1 hij
      rw [(hX _ _).1 this, mul_zero, zero_mul]
    · have h2 := (lt_of_blk_lt p i j (blk_lt_of_lt p hij hs)).2
      have hs' : blkOf p.1 (pinv p i).val ≠ blkOf p.1 (pinv p j).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact hs
      rw [hB _ _ hs', mul_zero, zero_mul]
  · subst hij
    rw [conj'_apply, (hX _ _).2 rfl, mul_one, mul_inv_cancel₀ (cv_ne p i)]
  · rw [Matrix.mul_assoc (ptMat p * X), Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hXd, Matrix.mul_one]
  · rw [Matrix.det_mul, Matrix.det_mul, upU_det hX, mul_one, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ hu,
      Matrix.det_one]

end Formalism.L2.SG.Pf.BlockPermutation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ToCellSurj
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]

section

variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

structure Data : Prop where
  stab : ∀ x : G, x • W = W ↔ x ∈ S
  mem : ∀ x, π x ∈ S
  id : ∀ s ∈ S, π s = s
  ker : ∀ x, x ∈ N' ↔ π x = 1
  kπ : ∀ k ∈ K, π k ∈ K

def cell (x : G) : G := x * (π x)⁻¹

theorem π_π (hD : Data W S N' K π) (x : G) : π (π x) = π x := hD.id _ (hD.mem x)

theorem cell_mem (hD : Data W S N' K π) (x : G) : cell π x ∈ N' := by
  rw [hD.ker, cell, map_mul, map_inv, π_π W S N' K π hD, mul_inv_cancel]

theorem cell_smul (hD : Data W S N' K π) (x : G) : cell π x • W = x • W := by
  rw [cell, mul_smul, (hD.stab _).mpr (S.inv_mem (hD.mem x))]

def Cells : Set G := {x | x ∈ N' ∧ ∃ k ∈ K, x • W = k • (g • W)}

def cellRel : Setoid (Cells W N' K g) where
  r x y := (y : G) * (x : G)⁻¹ ∈ K ⊓ N'
  iseqv := ⟨fun x => by simp [(K ⊓ N').one_mem], fun {x y} h => by
      have := (K ⊓ N').inv_mem h; simpa [mul_inv_rev] using this,
    fun {x y z} h1 h2 => by
      have := (K ⊓ N').mul_mem h2 h1; simpa [mul_assoc] using this⟩

def Hs : Subgroup G := K ⊓ MulAction.stabilizer G (g • W)

def toCell (hD : Data W S N' K π) (k : K) : Cells W N' K g :=
  ⟨cell π ((k : G) * g), cell_mem W S N' K π hD _, k, k.2, by rw [cell_smul W S N' K π hD, mul_smul]⟩

theorem toCell_surj (hD : Data W S N' K π) : Function.Surjective (toCell W S N' K π g hD) := by
  rintro ⟨c, hcN, k, hk, hc⟩
  refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
  show cell π (k * g) = c
  have hs : (k * g)⁻¹ * c ∈ S := by
    rw [← hD.stab, mul_smul, hc, ← mul_smul k g W, inv_smul_smul]
  obtain ⟨s, hsS, hc'⟩ : ∃ s ∈ S, c = k * g * s := ⟨_, hs, by group⟩
  have hπc : π c = 1 := (hD.ker c).mp hcN
  have hπ : π (k * g) = s⁻¹ := by
    rw [hc', map_mul, hD.id s hsS] at hπc
    exact eq_inv_of_mul_eq_one_left hπc
  rw [cell, hπ, inv_inv, ← hc']

end

end Formalism.L2.SG.Pf.CountAb
end
end

