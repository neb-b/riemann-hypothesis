module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0010
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.OffPartLattice

open GlobalTheory.StdFrames

variable {D : D7}


open Classical in
theorem cpt_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  have h : ∀ PP ∈ P, cpt Q (toEAf D (es PP)) = if Q = PP then 1 else 0 := fun PP hP => by
    by_cases hq : Q = PP
    · subst hq; rw [if_pos rfl]; exact (cpt_of_isIdemAt (hes _ hP)).1
    · rw [if_neg hq]; exact (cpt_of_isIdemAt (hes PP hP)).2 Q hq
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]


open Classical in
theorem cpt_cA_idemSum (V : HSp D) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt Q (toEAf D (cA D e)) = if GlobalTheory.IdemSupport.cP Q ∈ P then 1 else 0 := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum]
  have hc := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.2
  have h : ∀ PP ∈ P, cpt Q (toEAf D (cA D (es PP))) = if GlobalTheory.IdemSupport.cP Q = PP then 1 else 0 := fun PP hP => by
    have hi := hc PP (GlobalTheory.IdemSupport.cP PP) (es PP) (hes PP hP) ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl)
    by_cases hq : GlobalTheory.IdemSupport.cP Q = PP
    · subst hq
      rw [if_pos rfl, cP_cP] at *
      exact (cpt_of_isIdemAt hi).1
    · rw [if_neg hq]
      exact (cpt_of_isIdemAt hi).2 Q fun h' => hq (by rw [h', cP_cP])
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

theorem cpt_pair_zero (V : HSp D) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E)
    (hQ : ∀ w ∈ P, Q.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) : cpt Q (toEAf D (e + cA D e)) = 0 := by
  rw [map_add (f := _), map_add (f := _), cpt_idemSum he, cpt_cA_idemSum V he, if_neg, if_neg, add_zero]
  · exact fun h => hQ _ h (GlobalTheory.IdemSupport.under_cP Q).symm
  · exact fun h => hQ Q h rfl

theorem cpt_pair_one (V : HSp D) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E)
    (hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)) : cpt Q (toEAf D (e + cA D e)) = 1 := by
  have h0 : cpt Q (toEAf D e) * cpt Q (toEAf D (cA D e)) = 0 := by
    rw [← map_mul, ← map_mul, he.2, map_zero, map_zero]
  rw [cpt_idemSum he, cpt_cA_idemSum V he] at h0
  rw [map_add (f := _), map_add (f := _), cpt_idemSum he, cpt_cA_idemSum V he]
  obtain ⟨w, hw, hu⟩ := hQ
  rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu with rfl | rfl
  · rw [if_pos hw, one_mul] at h0
    rw [if_pos hw, h0, add_zero]
  · rw [cP_cP, if_pos hw, mul_one] at h0
    rw [cP_cP, if_pos hw, h0, zero_add]

end GlobalTheory.OffPartLattice

namespace GlobalTheory.OffPartLattice

open GlobalTheory.StdFrames Matrix

variable {D : D7}

theorem mix_map' {A B : Type} [CommRing A] [CommRing B] {n : Type} [DecidableEq n] (ψ : A →+* B) (f : A)
    (a : Matrix n n A) :
    (f • a + (1 - f) • (1 : Matrix n n A)).map ψ = ψ f • a.map ψ + (1 - ψ f) • (1 : Matrix n n B) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mix_conj' {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (f : A) (β : GL n A)
    (y : Matrix n n A) :
    β.val * (f • y + (1 - f) • (1 : Matrix n n A)) * (β⁻¹).val =
      f • (β.val * y * (β⁻¹).val) + (1 - f) • (1 : Matrix n n A) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Units.mul_inv]

theorem finE_cutPart {a : AE D} (h : a * a = a) (hc : cA D a = a) (V : HSp D) (g : GA D V) :
    (Lev.finE V (cutPart a V g)).val = toEAf D a • (Lev.finE V g).val + (1 - toEAf D a) • (1 : Matrix _ _ (Lev.EAf D)) := by
  change (mt V (cutPart a V g)).map (toEAf D) = _
  rw [mt_cutPart h hc, mix_map']
  rfl

theorem inBasis_mix {n : ℕ} (β X Y : GL (Fin n) (Lev.EAf D)) (c : Lev.EAf D)
    (hX : X.val = c • Y.val + (1 - c) • (1 : Matrix (Fin n) (Fin n) (Lev.EAf D))) (Q : Pl D.host.E) :
    (cpt Q c = 0 → inBasis rfl β Q X = 1) ∧ (cpt Q c = 1 → inBasis rfl β Q X = inBasis rfl β Q Y) := by
  have hM : (β⁻¹ * X * β).val = c • (β⁻¹ * Y * β).val + (1 - c) • (1 : Matrix (Fin n) (Fin n) (Lev.EAf D)) := by
    have := mix_conj' c β⁻¹ Y.val
    rw [inv_inv] at this
    rw [Units.val_mul, Units.val_mul, hX, this, Units.val_mul, Units.val_mul]
  have h1 : (β⁻¹ * 1 * β : GL (Fin n) (Lev.EAf D)) = 1 := by group
  constructor
  · intro h0
    rw [← map_one (inBasis rfl β Q)]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [inBasis_apply, inBasis_apply, hM, h1]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, h0, zero_mul,
      zero_add, sub_zero, one_mul, Units.val_one]
  · intro h0
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [inBasis_apply, inBasis_apply, hM]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, h0, one_mul,
      sub_self, zero_mul, add_zero]

theorem mulVec_mem_hatL_of_St {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : IsFrame β Λ) {x : GL (Fin n) (Lev.EAf D)} (hx : x ∈ St β) (v : Fin n → Lev.EAf D)
    (hv : v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) : x.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨y, rfl⟩ := hx
  rw [hβ] at hv ⊢
  intro i
  have e0 : β⁻¹ * frGL β y = intGL D.host.F D.host.E n y * β⁻¹ := by
    simp only [frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e : ((β⁻¹ : GL (Fin n) (Lev.EAf D)) : Matrix (Fin n) (Fin n) (Lev.EAf D)) * (frGL β y).val =
      (intGL D.host.F D.host.E n y).val * (β⁻¹ : GL (Fin n) (Lev.EAf D)).val := by
    rw [← Units.val_mul, e0, Units.val_mul]
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (y.val i k).2 (hv k)

theorem actO_mem_latO_of (S T : HSp D) (g : GA D S) (h : GA D T)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hg : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS, (mt S g).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (hh : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT, (mt T h).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT)
    (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    exact GlobalTheory.AdelicLatMove.rankOne_mem_latO S T ΛS ΛT a ha _
      (hg _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (hh _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

end GlobalTheory.OffPartLattice

namespace GlobalTheory.OffPartLattice

open GlobalTheory.StdFrames Matrix

variable {D : D7}

theorem isFrame_moved {n : ℕ} (Λ₀ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β Uf : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hU : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ₀ ↔ Uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    IsFrame (Uf⁻¹ * β) Λ₀ := by
  intro x
  rw [hU, hβ]
  have e : ((Uf⁻¹ * β)⁻¹ : GL (Fin n) (Lev.EAf D)).val = (β⁻¹ : GL (Fin n) (Lev.EAf D)).val * Uf.val := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  rw [e, ← Matrix.mulVec_mulVec]

theorem finE_cut_mem_St (V : HSp D) (β Uf K : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (hg : Lev.finE V g = Uf⁻¹ * K * Uf)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hK : ∀ Q : Pl D.host.E, (∀ w ∈ P, Q.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) →
      inBasis rfl β Q K ∈ GlobalTheory.SplitWeil.KO (Kw Q) (Fin V.rank)) :
    Lev.finE V (cutPart (1 - (e + cA D e)) V g) ∈ St (Uf⁻¹ * β) := by
  have hf := idem_conj_sum (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2
  have h2 := idem_compl hf
  have hX := finE_cutPart h2.1 h2.2 V g
  refine StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO _ _ fun Q => ?_
  have hm := inBasis_mix (Uf⁻¹ * β) _ _ _ hX Q
  by_cases hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)
  · rw [hm.1 (by simp only [map_sub, map_one, cpt_pair_one V he Q hQ, sub_self])]
    exact one_mem _
  · push_neg at hQ
    rw [hm.2 (by simp only [map_sub, map_one, cpt_pair_zero V he Q hQ, sub_zero])]
    have e1 : (Uf⁻¹ * β)⁻¹ * (Uf⁻¹ * K * Uf) * (Uf⁻¹ * β) = β⁻¹ * K * β := by group
    have e2 : inBasis rfl (Uf⁻¹ * β) Q (Lev.finE V g) = inBasis rfl β Q K := by
      refine Units.ext (Matrix.ext fun a b => ?_)
      rw [inBasis_apply, inBasis_apply, hg, e1]
    rw [e2]
    exact hK Q hQ

end GlobalTheory.OffPartLattice


open GlobalTheory.OffPartLattice Matrix in
theorem GlobalTheory.OffPartLattice.offPart_keeps_stdLatO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ u : WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)),
      u ∈ stdLatO S (.top t (j + 1)) ↔ ∃ u₀ ∈ stdLatO S (.top t (j + 1)),
        u = actO _ _ (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
          ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))) 1 u₀ := by
  intro D T L sc G W U S t _ Φ β j hj k hk e he u
  have hdef : DefNode D.R.m (.top (j + 1)) := by show j + 1 ≤ D.R.m; omega
  have hfr := isFrame_moved (colLat (S.N.fr (.top (j + 1)))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hdef) (S.N.u_lat _ hdef)
  have hk2 : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) (fun w => topRank_eq G t w hj.le)
      (fun w => (S.term t Φ β w).pr _ j.succ_pos hj) := hk
  have hSt := finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1)) (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)
    (finG (G.V (.top (j + 1))) k) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D _)
    (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; rfl) he (fun Q hQ => by
      have h3 := (Subgroup.mem_inf.1 hk2).2
      rw [Subgroup.mem_iInf] at h3
      have h4 := h3 Q
      rw [Subgroup.mem_iInf] at h4
      exact Subgroup.mem_comap.1 (h4 hQ))
  have hpres : ∀ y : GA D (G.V (.top (j + 1))),
      Lev.finE (G.V (.top (j + 1))) y ∈ St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) →
      ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))),
        (mt (G.V (.top (j + 1))) y).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))) :=
    fun y hy x hx => mulVec_mem_hatL_of_St hfr hy x hx
  have h1 : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (S.N.latT (.top t (j + 1))),
      (mt (G.pT (.top t (j + 1) : Pair T)) 1).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (S.N.latT (.top t (j + 1))) := by
    intro x hx
    rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact hx
  have key : ∀ g₂ : GA D (G.V (.top (j + 1))),
      Lev.finE (G.V (.top (j + 1))) g₂ ∈ St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) →
      (u ∈ stdLatO S (.top t (j + 1)) ↔ ∃ u₀ ∈ stdLatO S (.top t (j + 1)),
        u = actO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂ 1 u₀) := by
    intro g₂ hg₂
    constructor
    · intro hu
      refine ⟨actO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂⁻¹ 1⁻¹ u, ?_,
        (GlobalTheory.AdelicLatMove.actO_actO_inv (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂ 1 u).symm⟩
      exact actO_mem_latO_of (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂⁻¹ 1⁻¹
        (colLat (S.N.fr (.top (j + 1)))) (S.N.latT (.top t (j + 1)))
        (hpres _ (by rw [map_inv]; exact inv_mem hg₂)) (by rw [inv_one]; exact h1) u hu
    · rintro ⟨u₀, hu₀, rfl⟩
      exact actO_mem_latO_of (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂ 1
        (colLat (S.N.fr (.top (j + 1)))) (S.N.latT (.top t (j + 1))) (hpres _ hg₂) h1 u₀ hu₀
  exact key _ hSt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedThetaEqFiniteHeisenbergTranslatesVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

open GlobalTheory.PlaceModel GlobalTheory.SeeSaw

variable {D : D7} {S T : HSp D}

theorem comb_eq_linearCombination (ψ : AddChar (AF D.host.F) ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u f) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem comb_sum_single {ι : Type} [Fintype ι] (ψ : AddChar (AF D.host.F) ℂ) (x : ι → WO S T) (a : ι → ℂ)
    (f : WO S T → ℂ) :
    comb ψ S T (∑ i, Finsupp.single (x i) (a i)) f = ∑ i, a i • heisO ψ S T (x i) f := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb_eq_linearCombination, map_sum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.linearCombination_single _ _ _

theorem isFinComb_sum_single {ι : Type} [Fintype ι] (x : ι → WO S T) (a : ι → ℂ)
    (hx : ∀ i, (x i).map (infPart D) = 0) : IsFinComb (∑ i, Finsupp.single (x i) (a i)) := by
  classical
  intro u hu
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hu)
  have hui : u = x i := Finset.mem_singleton.1 (Finsupp.support_single_subset hi)
  rw [hui]
  exact hx i

theorem map_infPart_add_neg {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + -y).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
  show infPart D (x i j + -y i j) = 0
  rw [map_add (f := _), map_neg, h1, h2, neg_zero, add_zero]

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  linear_combination -h

theorem symplO_self (x : WO S T) : symplO S T x x = 0 := by
  have h := symplO_skew S T x x
  have hh := half_mul_two D
  linear_combination (algebraMap D.host.F (AF D.host.F) (1 / 2)) * h - symplO S T x x * hh

theorem heisL_cancel (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (f : WO S T → ℂ) :
    heisL S T ψ x (heisL S T ψ (-x) f) = f := by
  rw [heisL_heisL, symplOH, symplO_neg_right, symplO_self, neg_zero, mul_zero, AddChar.map_zero_eq_one, one_smul,
    add_neg_cancel]
  funext w
  change ψ (symplOH S T w 0) * f (w + 0) = f w
  rw [symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem lamE_two_nsmul {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ)
    {u : WO S T} (hu : u ∈ Λ) : lamE ψ S T e (2 • u) = 1 := by
  have h := hΛ _ (he u hu) _ (hc _ (Λ.nsmul_mem hu 2))
  rw [← h]
  unfold lamE symplOH
  congr 1
  rw [two_nsmul u, smul_add e, symplO_add_left]
  have hh := half_mul_two D
  linear_combination (symplO S T (e • u) (cA D e • (u + u))) * hh

theorem lamE_half {ψ : AddChar (AF D.host.F) ℂ} (e : AE D) {e' : AE D} (he' : e' * cA D e' = 0) {u : WO S T}
    (hu : IsHalf e' u) : lamE ψ S T e u = 1 := by
  have h : e' • u = u := (isHalf_iff S T).1 hu
  have h1 : e • u = e' • (e • u) := by rw [smul_comm, h]
  have h2 : cA D e' • (cA D e • u) = 0 := by
    rw [smul_comm, ← h, smul_smul (cA D e'), mul_comm, he', zero_smul, smul_zero]
  unfold lamE symplOH
  rw [h1, symplO_smul, h2, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]

theorem finite_Qm {V : Type} [AddCommGroup V] {Λ : AddSubgroup V} {m : ℕ} {R : Set V} (hR : R.Finite)
    (h : ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + m • u) : Finite (Qm m Λ) := by
  classical
  haveI : Finite R := hR
  refine Finite.of_surjective
    (fun r : R => if hr : (r : V) ∈ Λ then (QuotientAddGroup.mk (⟨r, hr⟩ : Λ) : Qm m Λ) else 0) fun q => ?_
  obtain ⟨r, hr, u, hu, ht⟩ := h _ (repm_mem q)
  have hrΛ : r ∈ Λ := by
    have := Λ.sub_mem (repm_mem q) (Λ.nsmul_mem hu m)
    rwa [ht, add_sub_cancel_right] at this
  refine ⟨⟨r, hr⟩, ?_⟩
  simp only [dif_pos hrΛ]
  rw [← mk_repm q, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine mem_mLat.2 ⟨u, hu, ?_⟩
  change m • u = -r + repm q
  rw [ht]; abel

theorem decomp_of_lam (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    (lam : WO S T → ℂ) (hlam : ∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y))
    (hlm : ∀ l ∈ Λ, lam (m • l) = 1) [Fintype (Qm m Λ)] (f : WO S T → ℂ) (hf : ∀ l ∈ Λ, heisO ψ S T (m • l) f = f) :
    ∃ (u : Qm m Λ → WO S T) (c : Qm m Λ → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, IsFinComb (c i)) ∧
      (∀ i, ∀ b ∈ Λ, lam b • heisO ψ S T b (comb ψ S T (c i) f) = comb ψ S T (c i) f) ∧
      f = ∑ i, heisO ψ S T (u i) (comb ψ S T (c i) f) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Qm m Λ → WO S T, ∀ a, s a = incA D ((m : D.host.E)⁻¹) • repm a := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ, N = (Fintype.card (Qm m Λ) : ℂ) := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast Fintype.card_ne_zero
  have hsinf : ∀ a, (s a).map (infPart D) = 0 := fun a => by
    rw [hs]; exact map_infPart_smul _ (hinf _ (repm_mem a))
  have hcomb : ∀ a, comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) (N⁻¹ • heisL S T ψ (-s a) f) := by
    intro a
    rw [comb_sum_single]
    refine Finset.sum_congr rfl fun q _ => ?_
    change _ = lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)
    rw [map_smul, heisL_heisL, smul_smul, smul_smul]
    rfl
  refine ⟨s, fun a => ∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a))), hsinf,
    fun a => isFinComb_sum_single _ _ fun q => map_infPart_add_neg (hinf _ (repm_mem q)) (hsinf a), fun a b hb => ?_, ?_⟩
  · rw [hcomb]
    refine heisAvg_invariant D ψ S T Λ m lam hlam _ (fun l hl => ?_) b hb
    change lam (m • l) • heisL S T ψ (m • l) (N⁻¹ • heisL S T ψ (-s a) f) = _
    have h1 : ψ (symplO S T (m • l) (-s a)) = 1 := by
      rw [symplO_neg_right, ← symplO_skew, hs, symplO_inv_smul_nsmul hm]
      exact hΛ _ (repm_mem a) _ hl
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [hlm l hl, one_smul, map_smul, heisL_comm, h1, one_smul, h2]
  · have h3 : ∀ a, heisO ψ S T (s a) (comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
        (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f) =
        ∑ q : Qm m Λ, ψ (symplO S T (s a) (repm q)) • ((lam (repm q) * N⁻¹) • heisL S T ψ (repm q) f) := by
      intro a
      rw [hcomb]
      change heisL S T ψ (s a) (∑ q : Qm m Λ, lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, map_smul, map_smul, heisL_comm, heisL_cancel, smul_smul, smul_smul, smul_smul]
      congr 1
      ring
    simp only [h3]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hs, charSum_selfAnn D ψ S T Λ m hm hinf hΛ hmax, ← hN, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 (repm_zero_mem (m := m) (Λ := Λ))
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [← hl', hlm l hl, h2, one_mul, smul_smul, mul_inv_cancel₀ hN0, one_smul]

theorem theta_eq_sum_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) := by
  intro D ψ θ S T sS sT LS LT f₀ hS hT hv f hf
  have hψ := hv.1
  obtain ⟨k, hk, hfk⟩ := Formalism.IndefR.Fin.latLevel_of (Formalism.IndefR.Fin.latSelfDual D) ψ hψ S T LS LT hS hT f hf
  obtain ⟨-, -, hmod, hdual⟩ := Formalism.IndefR.Fin.latSelfDual D ψ hψ S T LS LT hS hT
  have hinf := fun u (hu : u ∈ latO S T LS LT fun _ => True) => Formalism.IndefR.Fin.latAll_inf S T LS LT hu
  obtain ⟨R, hR, hRc⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg (fun _ => True) (2 * k) (by omega)
  change ∀ u ∈ latO S T LS LT fun _ => True, _ at hfk
  generalize latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at hfk hmod hdual hinf hRc ⊢
  haveI : Finite (Qm (2 * k) Λ) := finite_Qm hR hRc
  letI : Fintype (Qm (2 * k) Λ) := Fintype.ofFinite _
  obtain ⟨e, h1, h2, hi, hi', h, hh, h3⟩ := GlobalTheory.TwoPlaceIdem.exists_idem_half D
  have hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1 := fun x hx => (hdual x (hinf x hx)).1 hx
  have hr : ∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z := fun u hu =>
    ⟨h • u, hmod h hh u hu, by rw [← h3, two_mul, add_smul, two_nsmul]⟩
  have hl2 : ∀ u ∈ Λ, lamE ψ S T e (2 • u) = 1 := fun u hu => lamE_two_nsmul hΛ (hmod e hi) (hmod _ hi') hu
  obtain ⟨u, c, hu, hc, hfix, hsum⟩ := decomp_of_lam ψ Λ (2 * k) (by omega) hinf hΛ (fun x hx h => (hdual x hx).2 h)
    (lamE ψ S T e) (lamE_add_of_lattice D ψ S T Λ e h1 h2 hΛ (hmod e hi) (hmod _ hi') hr)
    (fun l hl => by rw [mul_nsmul']; exact hl2 _ (Λ.nsmul_mem hl k)) f
    (fun l hl => by rw [mul_nsmul]; exact hfk _ (Λ.nsmul_mem hl 2))
  let ι := (Fintype.equivFin (Qm (2 * k) Λ)).symm
  refine ⟨_, fun i => u (ι i), fun i => c (ι i), fun i => hu _, fun i => hc _, fun i => ⟨fun b hb => ?_, fun e' he' b hb hb' => ?_⟩, ?_⟩
  · have := hfix (ι i) _ (Λ.nsmul_mem hb 2)
    rwa [hl2 b hb, one_smul] at this
  · have := hfix (ι i) b hb
    rwa [lamE_half e he'.2.1 hb', one_smul] at this
  · exact hsum.trans (Equiv.sum_comp ι fun q => heisO ψ S T (u q) (comb ψ S T (c q) f)).symm

end GlobalTheory.FinDecomp

end

theorem _root_.GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) :=
  GlobalTheory.FinDecomp.theta_eq_sum_latVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRowGridBottomSelfDualLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomGrid

theorem bottom : All fun {D} _ {L} _ {G} _ _ => IsSelfDualC (Yc D 0) (L.ΛY 0) ∧ IsSelfDualC (G.V (.core 0)) (G.Λ (.core 0)) ∧ G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) ∧ zv G.sp.dec0 ∈ G.Λ (.core 0) ∧ (∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈ G.levCong (.core 0) → k ∈ levRow L) ∧ (Yc D 0).rank = D.R.r ∧ (G.V (.core 0)).rank = D.R.r + 1 ∧ ∀ (A : Fr (Yc D 0)) τ, (Finset.univ.filter fun a => A.ε τ a = false).card ≤ D.R.m := by
  intro D _ T L μ0 hL sc G W M _
  have hY : (⟨Yc D 0, L.ΛY 0⟩ : LSp D).IsV (Node.rank D (.grid 0 0)) (Node.neg D.R.m (.grid 0 0)) :=
    node_isV G hL (X := .grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hP := G.sp.P_is 0 (Nat.zero_le _)
  refine ⟨hY.sd, hP.sd, G.sp.lat0, ?_, ?_, ?_, ?_, ?_⟩
  · show zv G.sp.dec0 ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, Submodule.zero_mem _, fun _ => 1, fun p => ?_, ?_⟩
    · exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    · funext i
      simp [zv, Matrix.mulVec, dotProduct]
  · intro k hk hfin
    have h1 : Lev.finE (Yc D 0) k ∈ congLev D.sp.cm (Yc D 0).gram (L.ΛY 0) G.modul := by
      refine GlobalTheory.T.congruence_level_of_embedding G.sp.dec0 (L.ΛY 0) (fun _ => 1) G.modul k ?_
      have e : G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) := G.sp.lat0
      have := hfin
      unfold GridData.levCong at this
      rw [e] at this
      exact this
    have h2 := GlobalTheory.T.unitaryLatticeCongruence_mem_conjugateIdeal_inf (Yc D 0) (L.ΛY 0) hY.sd _ _ h1
    exact Subgroup.mem_inf.2 ⟨hk, congLev_mono (_root_.GlobalTheory.ModulConj.modul_inf_conj_le G) h2⟩
  · simpa [Node.rank, rankV] using hY.rank
  · simpa [Node.rank, rankP, nRk] using hP.rank
  · intro A τ
    rw [_root_.GlobalTheory.FrameSylvester.neg_card_eq_sig _ hY.sigOK A τ, hY.sig]
    simp only [Node.neg, Nat.sub_zero]
    exact Nat.div_le_self _ _
end GlobalTheory.BottomGrid
end

