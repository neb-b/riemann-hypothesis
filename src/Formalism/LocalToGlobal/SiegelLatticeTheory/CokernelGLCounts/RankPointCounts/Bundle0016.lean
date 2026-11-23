module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.IdxCocycle
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0014

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjSub
section
noncomputable section

namespace Formalism.L2.SG.Pf.ProdEP2Core

open Formalism.L2.SG.Pf.IndexCocycleOrbits

section Conj

variable {G : Type} [Group G]

def cj (s : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj s⁻¹).toMonoidHom

theorem mem_cj {s : G} {X : Subgroup G} {g : G} : g ∈ cj s X ↔ s * g * s⁻¹ ∈ X := by
  unfold cj
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨s * g * s⁻¹, h, by simp [mul_assoc]⟩

theorem cj_le {s : G} {X Y : Subgroup G} (h : X ≤ Y) : cj s X ≤ cj s Y := Subgroup.map_mono h

theorem cj_self {s : G} {X : Subgroup G} (hs : s ∈ X) : cj s X = X := by
  ext g
  rw [mem_cj]
  constructor
  · intro h
    have h2 : s⁻¹ * (s * g * s⁻¹) * s ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hs) h) hs
    simpa [mul_assoc] using h2
  · intro h
    exact X.mul_mem (X.mul_mem hs h) (X.inv_mem hs)

theorem relIndex_cj (s : G) (X Y : Subgroup G) : (cj s X).relIndex (cj s Y) = X.relIndex Y := Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj s⁻¹).injective

theorem idxRatio_self (A : Subgroup G) : IdxRatio A A = 1 := by
  simp [IdxRatio, Subgroup.relIndex_self]

end Conj

section Dc

variable {K : Type} [Group K] (A : Subgroup K) (π : K →* A) (H : Subgroup K)

def dcMap (k : K) : A ⧸ H.map π := QuotientGroup.mk (π k)

theorem dcMap_surjective (hπ : ∀ a : A, π a = a) : Function.Surjective (dcMap A π H) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨a, by simp [dcMap, hπ]⟩

theorem dcMap_eq_iff (k k' : K) :
    dcMap A π H k = dcMap A π H k' ↔ ∃ n ∈ π.ker, ∃ h ∈ H, k' = n * k * h := by
  unfold dcMap
  rw [QuotientGroup.eq, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hH, hh⟩
    refine ⟨k' * h⁻¹ * k⁻¹, ?_, h, hH, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, hh]
    group
  · rintro ⟨n, hn, h, hH, rfl⟩
    refine ⟨h, hH, ?_⟩
    rw [MonoidHom.mem_ker] at hn
    rw [map_mul, map_mul, hn, one_mul]
    group

theorem card_dc (hπ : ∀ a : A, π a = a) :
    Nat.card (Quotient (Setoid.ker (dcMap A π H))) = (H.map π).index := by
  rw [Subgroup.index, Nat.card_congr (Setoid.quotientKerEquivOfSurjective _ (dcMap_surjective A π H hπ))]

end Dc

end Formalism.L2.SG.Pf.ProdEP2Core
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGlue
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GlueDefs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def Corr (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') (n₁ n₂ : V) : Prop :=
  ∃ (h₁ : n₁ ∈ H.W0 t₁.f t₁.f') (h₂ : n₂ ∈ H.W0 t₂.f t₂.f'),
    φ (H.mkW t₁.f ⟨n₁, mem_perp_isotropicSpan_of_mem_framePerp H h₁⟩) = H.mkW t₂.f ⟨n₂, mem_perp_isotropicSpan_of_mem_framePerp H h₂⟩ ∧
    φ' (H.mkW t₁.f' ⟨n₁, mem_perp_isotropicSpan_of_mem_framePerp' H h₁⟩) = H.mkW t₂.f' ⟨n₂, mem_perp_isotropicSpan_of_mem_framePerp' H h₂⟩

def ThCond (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Prop :=
  ∀ n₁ n₂, Corr H t₁ t₂ φ φ' n₁ n₂ → (n₁ ∈ t₁.abelian₂ ↔ n₂ ∈ Λ₂)

def GlueRel (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (m₁ : ↥(MMsharp H t₁)) (m₂ : ↥(MMsharp H t₂)) : Prop :=
  ∃ n₁ n₂, Corr H t₁ t₂ φ φ' n₁ n₂ ∧ (m₁ : V) + n₁ ∈ t₁.abelian₂ ∧ (m₂ : V) + n₂ ∈ Λ₂

def GamCond (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) : Prop :=
  (M.split = none →
      (fun p => (θ p.1, φ p.2)) '' Gam H t₁ = Gam H t₂ ∧ (fun p => (θ p.1, φ' p.2)) '' Gam' H t₁ = Gam' H t₂) ∧
    (∀ g : SplitG M.L, M.split = some g →
      (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
        GamR H t₂ (algebraMap F E (g.q : F)))

end GlueDefs

section GlueProps

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def Glue (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∃ e : {Λ₂ : Submodule M.L.O V // H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
        ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ'} ≃
      {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ //
        IsUnit (H.Dl f₂ f₂' (r + 1)) ∧ MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ ∧ IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ},
      ∀ x m₁ m₂, (e x).1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
        GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ x.1 φ φ' m₁ m₂

def ClaimR (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' →
    ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩,
      (∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂) →
      (H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ↔
        GamCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' θ)

theorem latSide_of (M : Model F E) (r n : ℕ) (hG : Glue M r n) (hR : ClaimR M r n) : LatSide M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp
  obtain ⟨e, he⟩ := hG V H hn t₁ f₂ f₂' φ φ' hyp
  have hR' := hR V H hn t₁ f₂ f₂' φ φ' hyp
  have thc : ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' → ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' := by
    intro Λ₂ hg hr n₁ n₂ hc
    obtain ⟨h₁, h₂, c₁, c₂⟩ := hc
    exact thCorr_holds M r V H t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' hyp.1 hg hr n₁ h₁ n₂ h₂ c₁ c₂
  have heq : ∀ y, ∀ m₁ m₂, y.1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
      GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ (e.symm y).1 φ φ' m₁ m₂ := by
    intro y m₁ m₂
    have := he (e.symm y) m₁ m₂
    rwa [e.apply_symm_apply] at this
  refine Nat.card_congr
    { toFun := fun Λ => ⟨(e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).1,
        (e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).2.1, (e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).2.2.1,
        (e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).2.2.2,
        ((hR' Λ.1 Λ.2.1 (thc Λ.1 Λ.2.1 Λ.2.2) _ (he ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩)).1 Λ.2.2).1,
        ((hR' Λ.1 Λ.2.1 (thc Λ.1 Λ.2.1 Λ.2.2) _ (he ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩)).1 Λ.2.2).2⟩
      invFun := fun θ => ⟨(e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).1, (e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).2.1,
        (hR' _ (e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).2.1 (e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).2.2 θ.1
          (heq ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩)).2 θ.2.2.2.2⟩
      left_inv := fun Λ => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
      right_inv := fun θ => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply] }

end GlueProps

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LtOfBlkOfLt
section
noncomputable section

namespace Formalism.L2.SG.Pf.BlockPermutation

open Formalism.MainNotions.S Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj

variable {K : Type*} [Field K]

theorem pval_pperm : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    pval bs (pperm bs i) = pval bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · simp only [pperm, pval, hi, if_true]
      rw [if_pos (by omega)]
    · simp only [pperm, pval, hi, if_false]
      rw [if_neg (by omega), show s + pperm bs (i - s) - s = pperm bs (i - s) by omega]
      exact pval_pperm bs (i - s) (by omega)

theorem blkOf_pperm : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    blkOf bs (pperm bs i) = blkOf bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · simp only [pperm, blkOf, hi, if_true]
      rw [if_pos (by omega)]
    · simp only [pperm, blkOf, hi, if_false]
      rw [if_neg (by omega), show s + pperm bs (i - s) - s = pperm bs (i - s) by omega]
      rw [blkOf_pperm bs (i - s) (by omega)]

theorem pperm_lt_iff : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → (i < j ↔ pperm bs j < pperm bs i)
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pperm, h1, h2, if_true]; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_left_inj] at hb
      simp only [pperm, h1, h2, if_false]
      have := pperm_lt_iff bs (i - s) (j - s) (by omega) (by omega) hb
      omega

theorem lt_of_blkOf_lt : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i < blkOf bs j → i < j ∧ pperm bs i < pperm bs j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [blkOf, h1, h2, if_true] at hb; omega
    · simp only [pperm, h1, h2, if_true, if_false]; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_lt_add_iff_right] at hb
      simp only [pperm, h1, h2, if_false]
      have := lt_of_blkOf_lt bs (i - s) (j - s) (by omega) (by omega) hb
      omega

theorem pperm_add : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → pperm bs i + i = pperm bs j + j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pperm, h1, h2, if_true]; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_left_inj] at hb
      simp only [pperm, h1, h2, if_false]
      have := pperm_add bs (i - s) (j - s) (by omega) (by omega) hb
      omega

theorem blkOf_mono : ∀ (bs : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf bs i ≤ blkOf bs j
  | [], i, j, _ => by simp [blkOf]
  | (t, s) :: bs, i, j, hij => by
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp [blkOf, h1, h2]
    · simp [blkOf, h1, h2]
    · omega
    · simp only [blkOf, h1, h2, if_false, add_le_add_iff_right]
      exact blkOf_mono bs (i - s) (j - s) (by omega)

theorem pval_eq_of_blk : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → pval bs i = pval bs j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pval, h1, h2, if_true]
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_left_inj] at hb
      simp only [pval, h1, h2, if_false]
      exact pval_eq_of_blk bs (i - s) (j - s) (by omega) (by omega) hb

section Pt

variable {N : ℕ} (p : Point K N)

theorem pval_pinv (a : Fin N) : pval p.1 (pinv p a).val = pval p.1 a.val :=
  pval_pperm p.1 a.val (by rw [p.2.2]; exact a.isLt)

theorem blkOf_pinv (a : Fin N) : blkOf p.1 (pinv p a).val = blkOf p.1 a.val :=
  blkOf_pperm p.1 a.val (by rw [p.2.2]; exact a.isLt)

theorem pinv_lt_iff (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) : a < b ↔ pinv p b < pinv p a :=
  pperm_lt_iff p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem lt_of_blk_lt (a b : Fin N) (hb : blkOf p.1 a.val < blkOf p.1 b.val) : a < b ∧ pinv p a < pinv p b :=
  lt_of_blkOf_lt p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem pinv_add (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) :
    (pinv p a).val + a.val = (pinv p b).val + b.val :=
  pperm_add p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem pval_eq_blk (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) : pval p.1 a.val = pval p.1 b.val :=
  pval_eq_of_blk p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

end Pt

end Formalism.L2.SG.Pf.BlockPermutation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfSk
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev FI : Type := FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

def qq : Ideal (𝓞 D.host.E) := Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)}

def ddPow (k : ℕ) : FI D := ddS D ^ (-(k : ℤ))

def qdPow (k : ℕ) : FI D := (qq D : FI D) * ddPow D k

def bt (b : MatR D) (i j : Fin (D.R.rS + 1)) : D.host.E :=
  (-1) ^ (D.R.rS - i.val) * b i j * (-1) ^ (D.R.rS - j.val)

def EntryShape (a b : MatR D) : Prop :=
  ∀ i j : Fin (D.R.rS + 1), j < i →
    a i j ∈ ddPow D (i.val - j.val) ∧ bt D b j i ∈ ddPow D (i.val - j.val) ∧
      a i j - D.conjF (bt D b j i) ∈ qdPow D (i.val - j.val)

def LocMem (p : PlF D) (I : FI D) (x : D.host.E) : Prop :=
  (D.s.atP p).ιE x ∈ Submodule.span (D.s.atP p).O ((D.s.atP p).ιE '' (I : Set D.host.E))

def LocEntryShape (p : PlF D) (a b : MatR D) : Prop :=
  ∀ i j : Fin (D.R.rS + 1), j < i →
    LocMem D p (ddPow D (i.val - j.val)) (a i j) ∧ LocMem D p (ddPow D (i.val - j.val)) (bt D b j i) ∧
      LocMem D p (qdPow D (i.val - j.val)) (a i j - D.conjF (bt D b j i))

def LocShapeL : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D),
    (∀ q, Agree δ M q) → (M p).split = none → ∀ a b : MatR D, IsLoUni a → IsUpUni b →
      (Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
        LocEntryShape D p a b)

def LocShapeG : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D),
    (∀ q, Agree δ M q) → (M p).split.isSome → ∀ a b : MatR D, IsLoUni a → IsUpUni b →
      (Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
        LocEntryShape D p a b)

def LocGlob : Prop :=
  ∀ I : FI D, I ≠ 0 → ∀ x : D.host.E, (∀ p, LocMem D p I x) ↔ x ∈ I

def ShapeNZ : Prop := (∀ k, ddPow D k ≠ 0) ∧ ∀ k, qdPow D k ≠ 0

def StabIntShapeC : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (a : GLR D),
      a ∈ stabInt D u u' δ M w ↔ IsLoUni (a : MatR D) ∧ ∃ b : MatR D, IsUpUni b ∧
        (a : MatR D) * ptMat w * b = ptMat w ∧ EntryShape D a (b)

variable {D}

theorem loc_iff (hL : LocShapeL D) (hG : LocShapeG D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {p : PlF D} (hA : ∀ q, Agree δ M q) {a b : MatR D}
    (ha : IsLoUni a) (hb : IsUpUni b) :
    (Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
      LocEntryShape D p a b) := by
  cases h : (M p).split with
  | none => exact hL δ M p hA h a b ha hb
  | some g => exact hG δ M p hA (by simp [h]) a b ha hb

theorem glob_iff (hLG : LocGlob D) (hNZ : ShapeNZ D) (a b : MatR D) :
    (∀ p, LocEntryShape D p a b) ↔ EntryShape D a b := by
  constructor
  · intro h i j hij
    exact ⟨(hLG _ (hNZ.1 _) _).1 fun p => (h p i j hij).1, (hLG _ (hNZ.1 _) _).1 fun p => (h p i j hij).2.1,
      (hLG _ (hNZ.2 _) _).1 fun p => (h p i j hij).2.2⟩
  · intro h p i j hij
    exact ⟨(hLG _ (hNZ.1 _) _).2 (h i j hij).1 p, (hLG _ (hNZ.1 _) _).2 (h i j hij).2.1 p,
      (hLG _ (hNZ.2 _) _).2 (h i j hij).2.2 p⟩

theorem stabIntShape_of (hL : LocShapeL D) (hG : LocShapeG D) (hLG : LocGlob D) (hNZ : ShapeNZ D) :
    StabIntShapeC D := by
  intro δ M hA u u' w a
  rw [StabIntGrp.mem_stabInt_iff, StabShape.mem_stabIntSet_iff δ M u u' hA w a]
  constructor
  · rintro ⟨ha, b, hb, hW, hp⟩
    exact ⟨ha, b, hb, hW, (glob_iff hLG hNZ a b).1 fun p => (loc_iff hL hG (p := p) hA ha hb).1 (hp p)⟩
  · rintro ⟨ha, b, hb, hW, he⟩
    exact ⟨ha, b, hb, hW, fun p => (loc_iff hL hG (p := p) hA ha hb).2 ((glob_iff hLG hNZ a b).2 he p)⟩

end Formalism.L2.SG.Pf.StabIntSh
end
end

