module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumStabilizerPreservesTermLatticeGoodPlace
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StabLat

open Formalism.MainNotions.S.LocNG Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem perpX_of (Fr : FrameD H r) {k : V} (h : ∀ a : Fin r, H.h k (Fr.f a.castSucc) = 0) :
    k ∈ H.perp (H.X Fr.f) := by
  intro x hx
  unfold HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
  | zero => rw [H.h_herm 0 _, H.h_zero_left, map_zero]
  | add x y _ _ hx hy => rw [H.h_herm (x + y) _, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_herm (c • x) _, H.h_smul_left, map_mul, ← H.h_herm, hx, mul_zero]

theorem e_mem_X (Fr : FrameD H r) (a : Fin r) : Fr.e a ∈ H.X Fr.f :=
  Submodule.subset_span ⟨a, rfl⟩

theorem sub_prF_mem (Fr : FrameD H r) {y : V} (hy : y ∈ H.perp (H.X Fr.f)) : y - Fr.prF y ∈ H.X Fr.f := by
  have h0 : ∀ a, H.h y (Fr.e a) = 0 := fun a => hy _ (e_mem_X Fr a)
  have e : y - Fr.prF y = ∑ a, H.h y (Fr.es a) • Fr.e a := by
    unfold FrameD.prF
    simp only [h0, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel]
  rw [e]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (e_mem_X Fr a))

theorem prF_mem_perp (Fr : FrameD H r) (y : V) : Fr.prF y ∈ H.perp (H.X Fr.f) :=
  perpX_of Fr (fun a => ng_prF_e (Fr := Fr) y a)

theorem mkW_eq (Fr : FrameD H r) {x y : ↥(H.perp (H.X Fr.f))} (h : (x : V) - y ∈ H.X Fr.f) :
    H.mkW Fr.f x = H.mkW Fr.f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact h

theorem prF_mem_LamStd (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)} {y : V}
    (hy : y ∈ H.perp (H.X Fr.f)) (hyL : H.mkW Fr.f ⟨y, hy⟩ ∈ L) : Fr.prF y ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  refine ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩, rfl, ?_⟩
  · rw [ng_prF_es]; exact M.L.O.zero_mem
  · rw [ng_prF_e]; exact M.L.O.zero_mem
  · have e : H.mkW Fr.f ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ = H.mkW Fr.f ⟨y, hy⟩ := by
      apply mkW_eq
      have h1 := sub_prF_mem Fr hy
      have h2 := sub_prF_mem Fr (prF_mem_perp Fr y)
      have : Fr.prF (Fr.prF y) - y = -((y - Fr.prF y) + (Fr.prF y - Fr.prF (Fr.prF y))) := by abel
      rw [show ((⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) : V) = Fr.prF (Fr.prF y) from rfl,
        show ((⟨y, hy⟩ : ↥(H.perp (H.X Fr.f))) : V) = y from rfl, this]
      exact Submodule.neg_mem _ (Submodule.add_mem _ h1 h2)
    rw [e]; exact hyL

variable {P : FPair H r}

theorem h_add_right' (k u y : V) : H.h k (u + y) = H.h k u + H.h k y := by
  rw [H.h_herm (u + y) k, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem cls_mem {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {k : V} (hk : k ∈ t.abelian₂)
    (hkp : k ∈ H.perp (H.X P.A.f)) : H.mkW P.A.f ⟨k, hkp⟩ ∈ d.L := by
  have ht' := ht
  obtain ⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩ := ht'
  have hN := mem_NSet_of_mem_N P.A hn
  refine ((d.hL.2.1 ⟨k, hkp⟩).2) (fun y hyL => ?_)
  have hy := y.2
  have hyL' : H.mkW P.A.f ⟨(y : V), hy⟩ ∈ d.L := hyL
  have h0 := prF_mem_LamStd P.A hy hyL'
  have hny : n (P.A.prF y) ∈ t.abelian₂ := by rw [hL]; exact ⟨_, h0, rfl⟩
  have hint := ng_term_int ht hk hny
  have hu : n (P.A.prF y) - y ∈ H.X P.A.f := by
    have h1 := hN.2.2 _ (prF_mem_perp P.A (y : V))
    have h2 := sub_prF_mem P.A hy
    have : n (P.A.prF y) - y = (n (P.A.prF y) - P.A.prF y) - ((y : V) - P.A.prF y) := by abel
    rw [this]; exact Submodule.sub_mem _ h1 h2
  have e : n (P.A.prF y) = (n (P.A.prF y) - y) + y := by abel
  rw [e, h_add_right', hkp _ hu, zero_add] at hint
  exact hint

theorem mem_of_cls (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {k : V}
    (ho : NgOrth P k) (hkL : H.mkW P.A.f ⟨k, ng_orth_perp P.A ho.1⟩ ∈ d.L) : k ∈ t.abelian₂ := by
  have ht' := ht
  obtain ⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩ := ht'
  have hN := mem_NSet_of_mem_N P.A hn
  have hkp := ng_orth_perp P.A ho.1
  have h0 := prF_mem_LamStd P.A hkp hkL
  have hny : n (P.A.prF k) ∈ t.abelian₂ := by rw [hL]; exact ⟨_, h0, rfl⟩
  obtain ⟨m0, hm0, hk', hko⟩ := ng_term_split hP ht hny
  have hXle : H.X P.A.f ≤ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)) := by
    unfold HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl a.castSucc, rfl⟩
  have hx : n (P.A.prF k) - k ∈ H.X P.A.f := by
    have h1 := hN.2.2 _ (prF_mem_perp P.A k)
    have h2 := sub_prF_mem P.A hkp
    have : n (P.A.prF k) - k = (n (P.A.prF k) - P.A.prF k) - (k - P.A.prF k) := by abel
    rw [this]; exact Submodule.sub_mem _ h1 h2
  have hz : k - (n (P.A.prF k) - m0) = 0 := by
    refine ng_zero (H := H) (Sum.elim P.A.f P.B.f) ?_ ?_ ?_
    · rw [ng_gram_base]
      exact IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (ng_G_unit (by
        intro h0
        obtain ⟨_, y, _, hy⟩ := hP.2.1
        rw [h0, zero_mul] at hy
        have := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
        exact zero_ne_one hy))
    · have e : k - (n (P.A.prF k) - m0) = m0 - (n (P.A.prF k) - k) := by abel
      rw [e]
      exact Submodule.sub_mem _ (ng_span_base ht hm0) (hXle hx)
    · rintro (b | b)
      · rw [Sum.elim_inl, h_sub_left, ho.1, hko.1, sub_zero]
      · rw [Sum.elim_inr, h_sub_left, ho.2, hko.2, sub_zero]
  rw [sub_eq_zero.1 hz]; exact hk'

theorem complementUnitary_isUnitary_fixes_frames {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  unfold FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x (y u)) (x (y v)) = H.h u v
      rw [hx.1, hy.1]
    · show x (y (P.A.f b)) = P.A.f b
      rw [(hy.2 b).1, (hx.2 b).1]
    · show x (y (P.B.f b)) = P.B.f b
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    have e : ∀ u, x ((x⁻¹ : V ≃ₗ[E] V) u) = u := fun u => LinearEquiv.apply_symm_apply x u
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · rw [← hx.1, e, e]
    · conv_lhs => rw [← (hx.2 b).1]
      exact LinearEquiv.symm_apply_apply x _
    · conv_lhs => rw [← (hx.2 b).2]
      exact LinearEquiv.symm_apply_apply x _

theorem img_le (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {g : V ≃ₗ[E] V}
    (hU : IsUnitary H g) (hfix : ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b)
    (hmov : ∀ x y : ↥(H.perp (H.X P.A.f)), (y : V) = g x → H.mkW P.A.f x ∈ d.L → H.mkW P.A.f y ∈ d.L) :
    img g t.abelian₂ ≤ t.abelian₂ := by
  have hf := ng_term_f ht
  have hM : Submodule.span M.L.O (Set.range (Sum.elim t.f t.f')) ≤ t.abelian₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact (hf b).1
    · exact (hf b).2
  have hfixME : ∀ x ∈ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)), g x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rcases j with b | b
      · exact (hfix b).1
      · exact (hfix b).2
    | zero => exact map_zero g
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨m0, hm0, hk, hko⟩ := ng_term_split hP ht hv
  show g v ∈ t.abelian₂
  have e : g v = m0 + g (v - m0) := by
    rw [map_sub, hfixME m0 (ng_span_base ht hm0)]; abel
  rw [e]
  refine t.abelian₂.add_mem (hM hm0) ?_
  have hgo : NgOrth P (g (v - m0)) := by
    constructor
    · intro b; rw [← (hfix b).1, hU, hko.1]
    · intro b; rw [← (hfix b).2, hU, hko.2]
  apply mem_of_cls hP ht hgo
  exact hmov ⟨v - m0, ng_orth_perp P.A hko.1⟩ _ rfl (cls_mem ht hk _)

theorem stab_le_aut : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Stab d ≤ LocNG.Aut τ.abelian₂ := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P _ _ hP d τ ht
  unfold Datum.Stab
  rw [Subgroup.closure_le]
  rintro g ⟨hg, hmv⟩
  obtain ⟨hU, hfix⟩ := complementUnitary_isUnitary_fixes_frames hg
  rw [SetLike.mem_coe, ng_mem_Aut]
  have e : ∀ u, g ((g⁻¹ : V ≃ₗ[E] V) u) = u := fun u => LinearEquiv.apply_symm_apply g u
  have h1 := img_le hP ht hU hfix (fun x y hxy hx => (hmv.1 x y hxy).1 hx)
  have hU' : IsUnitary H g⁻¹ := fun u v => by rw [← hU, e, e]
  have hfix' : ∀ b, (g⁻¹ : V ≃ₗ[E] V) (P.A.f b) = P.A.f b ∧ (g⁻¹ : V ≃ₗ[E] V) (P.B.f b) = P.B.f b := fun b => by
    constructor
    · conv_lhs => rw [← (hfix b).1]
      exact LinearEquiv.symm_apply_apply g _
    · conv_lhs => rw [← (hfix b).2]
      exact LinearEquiv.symm_apply_apply g _
  have h2 := img_le hP ht hU' hfix' (fun x y hxy hx => by
    refine (hmv.1 y x ?_).2 hx
    rw [hxy]; exact (e x).symm)
  refine le_antisymm h1 ?_
  have h3 := ng_img_mono g h2
  rwa [← ng_img_mul, mul_inv_cancel, ng_img_one] at h3

end GlobalTheory.HL.StabLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientModelExists
section
noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm
open Formalism.HermitianLatticeCounting.S6

section EmbGen
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}

def frPerp (F : FlagD H r) : Submodule K V where
  carrier := {v | ∀ a, H.B (F.e a) v = 0}
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add (f := _), hx a, hy a, add_zero]
  zero_mem' := by
    intro a
    simp
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smulₛₗ, hx a, smul_zero]

theorem mem_frPerp (F : FlagD H r) (v : V) : v ∈ frPerp F ↔ ∀ a, H.B (F.e a) v = 0 := Iff.rfl

theorem B_right_nondeg (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (w : V) (h : ∀ v, H.B v w = 0) : w = 0 :=
  H.nondeg w (fun y => by rw [← H.herm y w, h y, star_zero])

theorem fr_indep (F : FlagD H r) : LinearIndependent K F.e := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hz : c (Fin.last r) = 0 := by
    have h : H.B (∑ a, c a • F.e a) (F.e (Fin.last r)) = 0 := by rw [hc, map_zero, LinearMap.zero_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [F.zperp, F.zz, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add] at h
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd (neg_eq_zero.1 h) F.hT
  have hc' : ∑ a : Fin r, c a.castSucc • F.e a.castSucc = 0 := by
    rw [Fin.sum_univ_castSucc, hz, zero_smul, add_zero] at hc
    exact hc
  have hcs := Fintype.linearIndependent_iff.1 F.indep (fun a => c a.castSucc) hc'
  intro i
  induction i using Fin.lastCases with
  | last => exact hz
  | cast a => exact hcs a

def frMap (F : FlagD H r) : V →ₗ[K] (Fin (r + 1) → K) :=
  LinearMap.pi fun a => H.B.flip (F.e a)

theorem frMap_apply (F : FlagD H r) (v : V) (a : Fin (r + 1)) : frMap F v a = H.B v (F.e a) := rfl

theorem ker_frMap (F : FlagD H r) : LinearMap.ker (frMap F) = frPerp F := by
  ext v
  rw [LinearMap.mem_ker, mem_frPerp, funext_iff]
  refine forall_congr' fun a => ?_
  rw [frMap_apply, Pi.zero_apply, ← H.herm (F.e a) v]
  exact ⟨fun h => by rw [← star_star (H.B (F.e a) v), h, star_zero], fun h => by rw [h, star_zero]⟩

theorem range_frMap (F : FlagD H r) : LinearMap.range (frMap F) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set c : Fin (r + 1) → K := fun a => f (fun j => if a = j then 1 else 0) with hcdef
  have hfx : ∀ x, f x = ∑ a, x a * c a := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, hcdef]
  have hv : ∀ v, H.B v (∑ a, star (c a) • F.e a) = 0 := by
    intro v
    have h1 : f (frMap F v) = 0 := by
      have : f (frMap F v) ∈ Submodule.map f (LinearMap.range (frMap F)) :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self _ v)
      rw [hf] at this
      exact (Submodule.mem_bot K).1 this
    rw [hfx] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [frMap_apply, mul_comm]
  have hw := B_right_nondeg H _ hv
  have hc := Fintype.linearIndependent_iff.1 (fr_indep F) _ hw
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [hfx]
  simp only [LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : c a = 0 := by simpa using hc a
  rw [this, mul_zero]

theorem finrank_frPerp [FiniteDimensional K V] (F : FlagD H r) :
    Module.finrank K (frPerp F) + (r + 1) = Module.finrank K V := by
  have h := LinearMap.finrank_range_add_finrank_ker (frMap F)
  rw [range_frMap, ker_frMap, finrank_top, Module.finrank_fin_fun] at h
  omega

theorem X_le_frPerp (F : FlagD H r) : F.X ≤ frPerp F := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, -, rfl⟩ a
  induction a using Fin.lastCases with
  | last => rw [← H.herm (F.e b.castSucc) (F.e (Fin.last r)), F.zperp b, star_zero]
  | cast a => exact F.iso a b

theorem finrank_X (F : FlagD H r) : Module.finrank K F.X = r := by
  have h : F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
    show Submodule.span K _ = _
    congr 1
    ext x
    simp
  rw [h, finrank_span_eq_card F.indep, Fintype.card_fin]

def resH (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (W : Submodule K V) (hnd : ∀ x : W, (∀ y : W, H.B x y = 0) → x = 0) :
    Formalism.HermitianLatticeCounting.S6.HermSpace K W where
  B := (H.B.comp W.subtype).compl₂ W.subtype
  herm x y := H.herm x y
  nondeg x h := hnd x h

theorem exists_emb [FiniteDimensional K V] (F : FlagD H r) (τ₀ : K →+* ℂ) (hP : ∀ σ : K →+* ℂ, F.PosDefAt σ) :
    ∃ (W : Submodule K V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W), GlobalTheory.DegAsm.IsEmb F HW W.subtype ∧
      Module.finrank K W + (2 * r + 1) = Module.finrank K V ∧ GlobalTheory.Mass.PD HW.B.flip := by
  obtain ⟨Y, hY⟩ := Submodule.exists_isCompl F.X
  set W := Y ⊓ frPerp F with hW
  have hsup : F.X ⊔ W = frPerp F := by
    rw [hW, ← sup_inf_assoc_of_le Y (X_le_frPerp F), hY.sup_eq_top, top_inf_eq]
  have hinf : F.X ⊓ W = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    exact hY.inf_eq_bot ▸ ⟨hx.1, hx.2.1⟩
  have hpos : ∀ (σ : K →+* ℂ) (x : W), x ≠ 0 → 0 < (σ (H.B x x)).re := by
    intro σ x hx
    refine hP σ x ((mem_frPerp F _).1 x.2.2) fun hxX => hx ?_
    have : (x : V) ∈ F.X ⊓ W := ⟨hxX, x.2⟩
    rw [hinf] at this
    exact Subtype.ext ((Submodule.mem_bot K).1 this)
  have hnd : ∀ x : W, (∀ y : W, H.B x y = 0) → x = 0 := by
    intro x h
    by_contra hx
    have := hpos τ₀ x hx
    rw [h x, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨W, resH H W hnd, ⟨fun x y => rfl, fun v => ?_⟩, ?_, fun σ x hx => hpos σ x hx⟩
  · rw [← mem_frPerp, Submodule.range_subtype, sup_comm, hsup]
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq F.X W
    rw [hsup, hinf, finrank_bot, finrank_X] at h1
    have h2 := finrank_frPerp F
    omega

end EmbGen

theorem embC : EmbC := by
  intro D large₂ X u _
  have hpos : ∀ σ : D.host.E →+* ℂ, (F0 X u).PosDefAt σ := fun σ =>
    Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (tu_ne D u)
      (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) σ
  let τ₀ : D.host.E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := D.host.E)).toRingHom
  obtain ⟨W, HW, h1, h2, h3⟩ := exists_emb (F0 X u) τ₀ hpos
  refine ⟨W, HW, h1, ?_, h3⟩
  have hV : Module.finrank D.host.E (VS D).V = D.R.rankY 0 := by
    rw [(VS D).rank_eq]
    exact D.sp.Y_rank 0 (Nat.zero_le _)
  have hR : D.R.rankY 0 = 2 * D.R.rS + D.R.k + 1 := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r, zero_mul, add_zero]
    omega
  rw [hV, hR] at h2
  omega

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFlagOfUnitriangularIsotropicShift
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MkFlag

variable {Ef : Type} [Field Ef] [NumberField Ef] [StarRing Ef] {H : HSpace Ef} {r : ℕ} {T : Ef}

theorem Xa_le_X (F : FlagG H r T) (a : ℕ) : F.Xa a ≤ F.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem orth_of_mem_X (F : FlagG H r T) {w : H.V} (hw : ∀ a, H.hT (F.e a) w = 0)
    {u : H.V} (hu : u ∈ F.X) : H.hT u w = 0 := by
  unfold FlagG.X at hu
  induction hu using Submodule.span_induction with
  | mem v hv => obtain ⟨a, rfl⟩ := hv; exact hw a
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem iso_X (F : FlagG H r T) {x y : H.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : H.hT x y = 0 := by
  refine orth_of_mem_X F (fun a => ?_) hx
  have hle : F.X ≤ LinearMap.ker (H.hT (F.e a)) := by
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact F.e_iso a b
  exact hle hy

theorem span_eq (F : FlagG H r T) (e' : Fin r → H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val) :
    Submodule.span Ef (Set.range e') = F.X := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hsplit : e' a = (e' a - F.e a) + F.e a := by abel
    rw [hsplit]
    exact Submodule.add_mem _ (Xa_le_X F a.val (h a)) (Submodule.subset_span ⟨a, rfl⟩)
  · have key : ∀ n : ℕ, ∀ a : Fin r, a.val < n → F.e a ∈ Submodule.span Ef (Set.range e') := by
      intro n
      induction n with
      | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
      | succ n ih =>
        intro a ha
        have hXa : F.Xa a.val ≤ Submodule.span Ef (Set.range e') := by
          rw [FlagG.Xa, Submodule.span_le]
          rintro _ ⟨b, hb, rfl⟩
          have hb' : b.val < a.val := hb
          exact ih b (by omega)
        have hsplit : F.e a = e' a - (e' a - F.e a) := by abel
        rw [hsplit]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, rfl⟩) (hXa (h a))
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact key (a.val + 1) a (Nat.lt_succ_self _)

theorem indep (F : FlagG H r T) (e' : Fin r → H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val) :
    LinearIndependent Ef e' := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_eq F e' h, FlagG.X,
    finrank_span_eq_card F.e_indep]

theorem herm_zero {u v : H.V} (h : H.hT u v = 0) : H.hT v u = 0 := by
  have h2 := H.herm.eq u v
  rw [← h2, h, map_zero]

def change (F : FlagG H r T) (e' : Fin r → H.V) (x : H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val)
    (hx : x ∈ F.X) : FlagG H r T where
  e := e'
  z := F.z + x
  e_indep := indep F e' h
  e_iso a b := by
    have hX : ∀ c, e' c ∈ F.X := fun c => span_eq F e' h ▸ Submodule.subset_span ⟨c, rfl⟩
    exact iso_X F (hX a) (hX b)
  z_orth a := by
    have hX : e' a ∈ F.X := span_eq F e' h ▸ Submodule.subset_span ⟨a, rfl⟩
    have h1 : H.hT (e' a) F.z = 0 := orth_of_mem_X F F.z_orth hX
    rw [map_add (f := _), h1, iso_X F hX hx, add_zero]
  z_norm := by
    have h1 : H.hT x F.z = 0 := orth_of_mem_X F F.z_orth hx
    have h2 : H.hT F.z x = 0 := herm_zero h1
    simp only [map_add (f := _), LinearMap.add_apply, h1, h2, iso_X F hx hx, F.z_norm]
    ring

theorem change_X (F : FlagG H r T) (e' : Fin r → H.V) (x : H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val)
    (hx : x ∈ F.X) : (change F e' x h hx).X = F.X :=
  span_eq F e' h

theorem mkflag : ∀ (D : D7) (T : D.host.E) (G : FlagG (VS D) D.R.rS T) (e' : Fin D.R.rS → (VS D).V) (x : (VS D).V), (∀ a, e' a - G.e a ∈ G.Xa a.val) → x ∈ G.X → ∃ G' : FlagG (VS D) D.R.rS T, G'.e = e' ∧ G'.z = G.z + x ∧ G'.X = G.X := by
  intro D T G e' x h hx
  exact ⟨change G e' x h hx, rfl, rfl, change_X G e' x h hx⟩

end GlobalTheory.MkFlag
end
end

