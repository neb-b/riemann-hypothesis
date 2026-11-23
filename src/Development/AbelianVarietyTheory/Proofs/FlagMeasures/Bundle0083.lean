module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTerms
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ComplMove

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

lemma bbne_img (g : V ≃ₗ[E] V) (f f' : Fin (r + 1) → V) (hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b)
    (Λ : Submodule M.L.O V) (T T' : F) :
    LocNG.BBne (H := H) (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) ↔
      LocNG.BBne (H := H) (⟨Λ, f, f', T, T'⟩ : Term V M r) := by
  have hfam : ∀ i, g (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i := by
    intro i
    unfold HermSp.MMfam
    rcases hs : M.split with _ | gg <;> rcases i with i | i <;>
      simp [map_smul, map_sub, (hfix i).1, (hfix i).2]
  have hspan : ∀ v ∈ Submodule.span E (Set.range (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r))), g v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hfam i
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul s x _ hx => rw [map_smul, hx]
  have e : H.MMfam (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) := rfl
  unfold LocNG.BBne
  simp only [e]
  constructor
  · rintro ⟨v, hv, hs, hns⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    have ew : g w = w := g.injective (hspan _ hs)
    change g w ∈ _ at hs
    change g w ∉ _ at hns
    rw [ew] at hs hns
    exact ⟨w, hw, hs, hns⟩
  · rintro ⟨v, hv, hs, hns⟩
    exact ⟨v, Submodule.mem_map.2 ⟨v, hv, hspan v hs⟩, hs, hns⟩

lemma fwd (hM : M.OK) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : Coord P S) (g : V ≃ₗ[E] V)
    (hg : c.grp g ∈ S.H0) (d d' : LocNG.Datum P) (hmv : c.grp g • c.dat d = c.dat d')
    (f f' : Fin (r + 1) → V) (Λ : Submodule M.L.O V)
    (hT : LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) :
    LocNG.IsTermOver P d' (⟨LocNG.img g Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) := by
  letI := hM.loc
  haveI := hM.char0
  have hT0 := hT
  obtain ⟨-, -, ⟨n, hn, hf, hΛn⟩, ⟨n', hn', hf', hΛn'⟩, -⟩ := hT
  change f = _ at hf
  change f' = _ at hf'
  change Λ = _ at hΛn
  change Λ = _ at hΛn'
  subst hf hf'
  have hW := (_root_.GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d n n' Λ).1 ⟨hT0, hn, hn', hΛn, hΛn'⟩
  obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hg
  rw [hmv, ← GlobalTheory.HL.CoordTerm.lat_img c] at hW'
  have e1 : c.grp (c.grp.symm m) = m := c.grp.apply_symm_apply m
  have e2 : c.grp (c.grp.symm m') = m' := c.grp.apply_symm_apply m'
  rw [← e1, ← e2] at hW'
  have hR := ((_root_.GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d' (c.grp.symm m) (c.grp.symm m') (LocNG.img g Λ)).2 hW').1
  have k1 : (fun b => c.grp.symm m (P.A.f b)) = fun b => n (P.A.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq, e1, hm b]
  have k2 : (fun b => c.grp.symm m' (P.B.f b)) = fun b => n' (P.B.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq, e2, hm' b]
  rw [k1, k2] at hR
  exact hR

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ g ∈ P.UW0, ∀ d d' : LocNG.Datum P, LocNG.Datum.Moves g d d' → (∀ b, g (f b) = f b ∧ g (f' b) = f' b) ∧ LocNG.img g '' {Λ | LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} = {Λ | LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hP f f' ⟨n, hn, hf⟩ ⟨n', hn', hf'⟩ g hg d d' hmv
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hP
  obtain ⟨hU, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, hMv, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh := (hU g).1 hg
  have hmv' := (hMv g hg d d').1 hmv
  have fixv : ∀ x : V, c.e x ∈ S.ME → g x = x := by
    intro x hx
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh _ hx
  have hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b := by
    intro b
    subst hf hf'
    refine ⟨fixv _ ?_, fixv _ ?_⟩
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq]
      exact Submodule.mem_sup_left (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn)
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f b))
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq]
      exact Submodule.mem_sup_right (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn')
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f' b))
  have hginv : c.grp g⁻¹ ∈ S.H0 := by rw [map_inv]; exact S.H0.inv_mem hh
  have hmvinv : c.grp g⁻¹ • c.dat d' = c.dat d := by
    rw [← hmv', map_inv, inv_smul_smul]
  have hback : ∀ Λ : Submodule M.L.O V, LocNG.img g (LocNG.img g⁻¹ Λ) = Λ := by
    intro Λ
    rw [← GlobalTheory.HL.CoordTerm.lat_inj c, GlobalTheory.HL.CoordTerm.lat_img, GlobalTheory.HL.CoordTerm.lat_img, map_inv,
      smul_inv_smul]
  refine ⟨hfix, ?_⟩
  ext Λ
  constructor
  · rintro ⟨Λ0, ⟨hT, hB⟩, rfl⟩
    exact ⟨fwd hM P S c g hh d d' hmv' f f' Λ0 hT, by rwa [bbne_img g f f' hfix]⟩
  · rintro ⟨hT, hB⟩
    refine ⟨LocNG.img g⁻¹ Λ, ⟨fwd hM P S c g⁻¹ hginv d' d hmvinv f f' Λ hT, ?_⟩, hback Λ⟩
    rw [← bbne_img g f f' hfix, hback Λ]
    exact hB

end GlobalTheory.HL.ComplMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithData
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.LocalMove

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ h ∈ P.UW0, ∀ (d d' : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Moves h d d' → LocNG.IsTermOver P d' ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ∧ (LocNG.BBne (H := H) ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ↔ LocNG.BBne (H := H) τ) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP h hh d d' τ hτ hmv
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrk hP
  obtain ⟨hH0, -, -, hlat, -⟩ := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, hmov, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh0 : c.grp h ∈ S.H0 := (hH0 h).1 hh
  have ge : ∀ (g : V ≃ₗ[E] V) (x : V), c.grp g (c.e x) = c.e (g x) := GlobalTheory.HL.CoordTerm.grp_e c
  obtain ⟨Λ, f, f', T, T'⟩ := τ
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, hG⟩ := hτ
  dsimp only at hT hT' hf hΛ hf' hΛ' hG ⊢
  subst hT hT' hf hf'

  have fixA : ∀ b, h (n (P.A.f b)) = n (P.A.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_left
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn) (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  have fixB : ∀ b, h (n' (P.B.f b)) = n' (P.B.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f'_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_right
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn') (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  simp only [fixA, fixB]
  refine ⟨?_, ?_⟩
  · have hW := (GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d n n' Λ).1
      ⟨⟨rfl, rfl, ⟨n, hn, rfl, hΛ⟩, ⟨n', hn', rfl, hΛ'⟩, hG⟩, hn, hn', hΛ, hΛ'⟩
    obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hh0
    rw [(hmov h hh d d').1 hmv, ← hlat] at hW'
    obtain ⟨m0, rfl⟩ := c.grp.surjective m
    obtain ⟨m0', rfl⟩ := c.grp.surjective m'
    have e1 : (fun b => m0 (P.A.f b)) = fun b => n (P.A.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f_eq]; exact hm b
    have e2 : (fun b => m0' (P.B.f b)) = fun b => n' (P.B.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f'_eq]; exact hm' b
    have := ((GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d' m0 m0' (LocNG.img h Λ)).2 hW').1
    rw [e1, e2] at this
    exact this
  ·
    set t : Term V M r := ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ with ht
    have fam : ∀ i, h (H.MMfam t i) = H.MMfam t i := by
      intro i
      unfold HermSp.MMfam
      cases M.split with
      | none => rcases i with b | b <;> simp [ht, fixA, fixB]
      | some g => rcases i with b | b <;> simp [ht, fixA, fixB, map_sub]
    have fixS : ∀ x ∈ Submodule.span E (Set.range (H.MMfam t)), h x = x := by
      intro x hx
      have := LinearMap.eqOn_span' (f := (h : V →ₗ[E] V)) (g := LinearMap.id)
        (s := Set.range (H.MMfam t)) (by rintro _ ⟨i, rfl⟩; exact fam i) hx
      simpa using this
    change (∃ v ∈ LocNG.img h Λ, _) ↔ ∃ v ∈ Λ, _
    constructor
    · rintro ⟨v, hv, hE, hO⟩
      obtain ⟨w, hw, rfl⟩ := hv
      have hw' : h w = w := by
        have := fixS _ hE
        exact h.injective (by simpa using this)
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hE hO ⊢
      rw [hw'] at hE hO
      exact ⟨w, hw, hE, hO⟩
    · rintro ⟨v, hv, hE, hO⟩
      exact ⟨v, ⟨v, hv, fixS v hE⟩, hE, hO⟩

end GlobalTheory.HL.LocalMove
end
end

