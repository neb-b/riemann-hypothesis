module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHeckeAtZeroOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

theorem isDC_one' {G : Type} [Group G] (J : Subgroup G) : Formalism.IndefR.Bridge.IsDC J 1 {1} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k, k', rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using J.mul_mem k.2 k'.2⟩, fun a ha => Finset.mem_singleton.1 ha.1⟩

theorem isHeckeAt_zero_one' {D : D7} (V : HSp D) {P : PlE D.host} (hP : Formalism.BasicNotions.IsSplitPl D.host P) :
    IsHeckeAt V P 0 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hP)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  exact ⟨e, ϖ, he, h1, h2, GlobalTheory.HeckeParts.isHeckeElt_one V he.1 ϖ⟩

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem heckeScalar_eq (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (P : PlE D.host) (k : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R.toRealDat i P k = hkNorm R i k P := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar, hkNorm, zpow_neg, zpow_natCast, inv_pow]
end

theorem heckeOn_one {D : D7} {V : HSp D} {S} (M : DSModel V S) (F : MMap M) : heckeOn M {1} F = F := by
  ext v g
  simp [heckeOn, postOn, heckeLin]

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def famOf (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ) (k : ℕ)
    (Pl : PlE D.host) : Module.End D.what₂.LL (Fin (R.nW (idxOf D j)) → D.what₂.LL) :=
  if h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r then
    Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2)
  else 1

theorem famOf_zero (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ)
    (Pl : PlE D.host) : famOf R hq j 0 Pl = 1 := by
  unfold famOf
  rw [dite_eq_right (fun h => h.1 rfl)]

theorem exists_heckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i)
    (hg : ∀ v : PlE D.host, IsSplitPl D.host v → v ∉ Sb → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat v) :
    ∃ hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j),
      StabC (ratDatR R cG kKs hk) hL' ∧ (∀ j Pl, hL' j 0 Pl = 1) ∧ HeckeRd R cG kKs hk Sb hL' := by
  refine ⟨famOf R hq, ?_, fun j Pl => famOf_zero R hq j Pl, ?_⟩
  · intro j _ _ k Pl y hy
    change famOf R hq j k Pl y ∈ (R.FW (idxOf D j)).WK
    unfold famOf
    split_ifs with h
    · exact (Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).2 y hy
    · exact hy
  · intro j k Pl α Rr _ _ hd y
    have hg' : GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl := hg Pl hd.split hd.offS
    by_cases hk0 : k = 0
    · subst hk0
      have hr := (Classical.choose_spec (hq (idxOf D j) Pl hg' 0 (Nat.zero_le _))).1
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1 (hr Rr ⟨α, hd.elt, hd.reps⟩) y
      have e2 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        (hr {1} ⟨1, isHeckeAt_zero_one' _ hd.split, isDC_one' _⟩) y
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar_zero, one_smul] at e1 e2
      have e4 := (e2.trans (heckeOn_one _ _)).symm.trans e1
      have hn : hkNorm R (idxOf D j) 0 Pl = 1 := by simp [hkNorm]
      rw [famOf_zero, hn, one_smul]
      exact e4
    · have h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r := ⟨hk0, hg', hd.le⟩
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        ((Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).1 Rr ⟨α, hd.elt, hd.reps⟩) y
      have h1 : famOf R hq j k Pl = Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2) := by
        unfold famOf
        rw [dite_eq_left h]
      rw [h1, ← heckeScalar_eq]
      exact e1
end Gen

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepsMatHeqRefl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def KeepsMat {D : D7} (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) : Prop :=
  ∃ hF : D.host.F = maximalRealSubfield D.host.E, ∀ i : Fin D.R.m, ∃ hn : (Vc D i).rank = D.R.nV, ∀ κ a b,
    finMat D.sp.cm.sig (Vc D i).gram (p i κ) a b = (GlobalTheory.Mem.R3.swapCast hF).symm
      ((κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))

theorem keepsMat_heq_refl (D : D7) : ∀ (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) (p' : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)),
    KeepsMat p → KeepsMat p' → ∀ (j : Fin D.R.m) (j' : Fin D.R.m), (j : ℕ) = j' →
    HEq (fun g => (finHom (Vc D j)).rangeRestrict (p j g)) fun g => (finHom (Vc D j')).rangeRestrict (p' j' g) := by
  rintro p p' ⟨hF, hp⟩ ⟨hF', hp'⟩ j j' hj
  cases Fin.ext hj
  obtain ⟨hn, hp⟩ := hp j
  obtain ⟨hn', hp'⟩ := hp' j
  exact heq_of_eq (funext fun g => Subtype.ext (Units.ext (Matrix.ext fun a b => (hp g a b).trans (hp' g a b).symm)))

theorem keepsMat_heq (h : CopyTw D D' ι e) : ∀ (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) (p' : ∀ i : Fin D'.R.m, GAf D'.host.E D'.R.nV → GA D' (Vc D' i)),
    KeepsMat p → KeepsMat p' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    HEq (fun g => (finHom (Vc D j)).rangeRestrict (p j g)) fun g => (finHom (Vc D' j')).rangeRestrict (p' j' g) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((keepsMat_heq_refl D) :))

theorem low_copy_refl (D : D7) : (LowIn D → LowIn D) ∧
    (∀ (bad : D.ntw.Tw → ℕ) (bad' : D.ntw.Tw → ℕ), HEq bad bad' → (∀ i, bad i = normProd (D.ntw.S0 i)) →
      ∀ i, bad' i = normProd (D.ntw.S0 i)) ∧
    ((∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) →
      ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) := by
  refine ⟨id, fun _ _ hb H => ?_, id⟩
  subst hb; exact H

theorem low_copy (h : CopyTw D D' ι e) : (LowIn D → LowIn D') ∧
    (∀ (bad : D.ntw.Tw → ℕ) (bad' : D'.ntw.Tw → ℕ), HEq bad bad' → (∀ i, bad i = normProd (D.ntw.S0 i)) →
      ∀ i, bad' i = normProd (D'.ntw.S0 i)) ∧
    ((∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) →
      ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D'.R.m) → Subsingleton (D'.nexp.Fm i j b)) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((low_copy_refl D) :))

theorem pq_copy_refl (D : D7) : ∀ (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
      (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), HEq Pq Pq' →
      (∀ (ch : D.ntw.Tw → Set (Pl D.host.E)) (ch' : D.ntw.Tw → Set (Pl D.host.E)), HEq ch ch' →
        (∀ i P, IsSplitPl D.host P → (P ∈ ch i ↔ P ∈ Set.range Pq)) → ∀ i P, IsSplitPl D.host P → (P ∈ ch' i ↔ P ∈ Set.range Pq')) ∧
      ∀ (i' : D.ntw.Tw) (k : ℕ) (Q' : Finset (PlE D.host)) (ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i' k)ˣ),
        ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
          HEq (NX.qpOf D Pq Q) (NX.qpOf D Pq' Q') ∧ HEq (NX.qpOf D Pq (D.ntw.pD i)) (NX.qpOf D Pq' (D.ntw.pD i')) := by
  refine fun Pq Pq' hPq => ⟨fun _ _ hc H => ?_, fun i k Q ψ => ?_⟩
  · subst hPq; subst hc; exact H
  · subst hPq; exact ⟨i, Q, ψ, .rfl, .rfl, .rfl, .rfl, .rfl⟩

theorem pq_copy (h : CopyTw D D' ι e) : ∀ (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
      (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D'.host.E)) → PlE D'.host), HEq Pq Pq' →
      (∀ (ch : D.ntw.Tw → Set (Pl D.host.E)) (ch' : D'.ntw.Tw → Set (Pl D'.host.E)), HEq ch ch' →
        (∀ i P, IsSplitPl D.host P → (P ∈ ch i ↔ P ∈ Set.range Pq)) → ∀ i P, IsSplitPl D'.host P → (P ∈ ch' i ↔ P ∈ Set.range Pq')) ∧
      ∀ (i' : D'.ntw.Tw) (k : ℕ) (Q' : Finset (PlE D'.host)) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ),
        ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
          HEq (NX.qpOf D Pq Q) (NX.qpOf D' Pq' Q') ∧ HEq (NX.qpOf D Pq (D.ntw.pD i)) (NX.qpOf D' Pq' (D'.ntw.pD i')) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((pq_copy_refl D) :))

theorem join_copy_refl (D : D7) : ∀ (i' : D.ntw.Tw) (j : Fin D.R.m) (j' : Fin D.R.m), (j : ℕ) = j' → ∀ (b : Bool) (k : ℕ)
    (Q' : Finset (PlE D.host)) (ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i' k)ˣ), TwOK i' k Q' ψ' →
    ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
      TwOK i k Q ψ ∧ PolF D (Wc D j).rank (Vc D j).rank = PolF D (Wc D j').rank (Vc D j').rank ∧
      HEq (inferInstance : AddCommGroup (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : AddCommGroup (PolF D (Wc D j').rank (Vc D j').rank)) ∧
      HEq (inferInstance : Module ℂ (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : Module ℂ (PolF D (Wc D j').rank (Vc D j').rank)) ∧
      ∀ (ek : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ) (ek' : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ),
        HEq ek ek' → HEq (ek i b k) (ek' i' b k) ∧
        ∀ (r : ∀ k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))
          (r' : ∀ k Q ψ, D.nexp.MtV i' ((j' : ℕ) + 1) b k Q ψ →ₛₗ[ek' i' b k]
            (Bridge.Gf (Vc D j') → PolF D (Wc D j').rank (Vc D j').rank)), HEq r r' →
          ∀ (p : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j)) (p' : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j')), HEq p p' →
            HEq (fun f g => r k Q ψ f (p g)) fun f g => r' k Q' ψ' f (p' g) := by
  intro i j j' hj b k Q ψ hT
  cases Fin.ext hj
  refine ⟨i, Q, ψ, .rfl, .rfl, .rfl, hT, rfl, .rfl, .rfl, fun _ _ hek => ?_⟩
  subst hek
  refine ⟨.rfl, fun _ _ hr _ _ hp => ?_⟩
  subst hr; subst hp
  rfl

theorem join_copy (h : CopyTw D D' ι e) : ∀ (i' : D'.ntw.Tw) (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ (b : Bool) (k : ℕ)
    (Q' : Finset (PlE D'.host)) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), TwOK i' k Q' ψ' →
    ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
      TwOK i k Q ψ ∧ PolF D (Wc D j).rank (Vc D j).rank = PolF D' (Wc D' j').rank (Vc D' j').rank ∧
      HEq (inferInstance : AddCommGroup (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : AddCommGroup (PolF D' (Wc D' j').rank (Vc D' j').rank)) ∧
      HEq (inferInstance : Module ℂ (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : Module ℂ (PolF D' (Wc D' j').rank (Vc D' j').rank)) ∧
      ∀ (ek : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ) (ek' : ∀ i, Bool → ∀ k, FractionRing (D'.ntw.Ok i k) →+* ℂ),
        HEq ek ek' → HEq (ek i b k) (ek' i' b k) ∧
        ∀ (r : ∀ k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))
          (r' : ∀ k Q ψ, D'.nexp.MtV i' ((j' : ℕ) + 1) b k Q ψ →ₛₗ[ek' i' b k]
            (Bridge.Gf (Vc D' j') → PolF D' (Wc D' j').rank (Vc D' j').rank)), HEq r r' →
          ∀ (p : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j)) (p' : GAf D'.host.E D'.R.nV → Bridge.Gf (Vc D' j')), HEq p p' →
            HEq (fun f g => r k Q ψ f (p g)) fun f g => r' k Q' ψ' f (p' g) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((join_copy_refl D) :))

def ExpMove (X : NExpTied D) (X' : NExpTied D') : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)),
    HEq Q Q' → ∀ (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), HEq ψ ψ' →
    ∀ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h2' : j ≤ D'.R.m) (hA' : Formalism.L2.NX.AdmTw D' i' k Q' ψ'), ∃ hA : Formalism.L2.NX.AdmTw D i k Q ψ,
      HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV i' j b k Q' ψ' h1 h2' hA').QP ∧
      HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV i' j b k Q' ψ' h1 h2' hA').DP ∧
      ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (ε' : FractionRing (D'.ntw.Ok i' k) →+* ℂ), HEq ε ε' →
        ∀ (V V' : Type) [aV : AddCommGroup V] [mV : Module ℂ V] [aV' : AddCommGroup V'] [mV' : Module ℂ V'], V = V' → HEq aV aV' →
          HEq mV mV' → ∀ (r : D.nexp.MtV i j b k Q ψ → GAf D.host.E D.R.nV → V) (r' : D'.nexp.MtV i' j b k Q' ψ' → GAf D'.host.E D'.R.nV → V'),
            HEq r r' → GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V r → GlobalTheory.HeightCounting.Reads X' i' j b k Q' ψ' h1 h2' hA' ε' V' r'

def PqLaw (X : NExpTied D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Prop :=
  ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : Formalism.L2.NX.AdmTw D i k Q ψ),
    (X.mtV i j b k Q ψ h1 h2 hadm).QP = NX.qpOf D Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = NX.qpOf D Pq (D.ntw.pD i)

theorem pqLaw_move (h : CopyTw D D' ι e) {X : NExpTied D} {X' : NExpTied D'} (hX : ExpMove X X') {Pq Pq'} (hPq : HEq Pq Pq')
    (L : PqLaw X Pq) : PqLaw X' Pq' := by
  intro i' j b k Q' ψ' h1 h2' hA'
  have h2 : j ≤ D.R.m := by rw [h.gal.R]; exact h2'
  obtain ⟨i, Q, ψ, hi, hQ, hψ, e1, e2⟩ := (pq_copy h Pq Pq' hPq).2 i' k Q' ψ'
  obtain ⟨hA, q1, q2, -⟩ := hX i i' hi j b k Q Q' hQ ψ ψ' hψ h1 h2 h2' hA'
  obtain ⟨l1, l2⟩ := L i j b k Q ψ h1 h2 hA
  exact ⟨eq_of_heq (q1.symm.trans ((heq_of_eq l1).trans e1)), eq_of_heq (q2.symm.trans ((heq_of_eq l2).trans e2))⟩

end GlobalTheory.HeightCounting.SerCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceHodgeGramLocalHolomorphicModel
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.LocalModel

theorem differentiableAt_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} {u : V} (hA : ∀ a b, DifferentiableAt ℂ (fun v => A v a b) u) :
    DifferentiableAt ℂ (fun v => (A v).det) u := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  have key : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, A v (σ i) i) u := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).mul ih
  exact key _

theorem differentiableAt_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} {u : V} (hA : ∀ a b, DifferentiableAt ℂ (fun v => A v a b) u)
    (hd : (A u).det ≠ 0) (i k : Fin d) : DifferentiableAt ℂ (fun v => (A v)⁻¹ i k) u := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((differentiableAt_det hA).inv hd).mul (differentiableAt_det fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact hA _ _

theorem differentiableAt_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b d : ℕ}
    {A : V → Matrix (Fin a) (Fin b) ℂ} {B : V → Matrix (Fin b) (Fin d) ℂ} {u : V}
    (hA : ∀ i k, DifferentiableAt ℂ (fun v => A v i k) u) (hB : ∀ i k, DifferentiableAt ℂ (fun v => B v i k) u)
    (i k : Fin _) : DifferentiableAt ℂ (fun v => (A v * B v) i k) u := by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun c _ => (hA i c).mul (hB c k)

theorem gram_cast {n m q q' : ℕ} (h : n = m) (h' : q' = q) (κ : ℂ) (Gm Mu : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin q) ℂ)
    (hG : Gm.submatrix (Fin.cast h.symm) (Fin.cast h.symm) = κ • (Cᴴ * (Formalism.DegreeFormula.hP z)⁻¹ * C)) :
    (Muᴴ * Gm * Mu)ᵀ = κ • ((C.submatrix (Fin.cast h) (Fin.cast h) * Mu)ᵀ *
      GlobalTheory.PointFormSign.domGram n q' (fun a b => z (Fin.cast h a) (Fin.cast h' b)) *
        (C.submatrix (Fin.cast h) (Fin.cast h) * Mu)ᴴᵀ) := by
  subst h h'
  have hG' : Gm = κ • (Cᴴ * (Formalism.DegreeFormula.hP z)⁻¹ * C) := by simpa using hG
  subst hG'
  simp only [GlobalTheory.PointFormSign.domGram, Formalism.DegreeFormula.hP, Fin.cast_eq_self, Matrix.submatrix_id_id, Matrix.of_apply]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  rfl

theorem posDef_cast {n m q q' : ℕ} (h : n = m) (h' : q' = q) (z : Matrix (Fin m) (Fin q) ℂ)
    (hz : (1 - z * zᴴ).PosDef) :
    (1 - Matrix.of (fun a b => z (Fin.cast h a) (Fin.cast h' b)) *
      (Matrix.of (fun a b => z (Fin.cast h a) (Fin.cast h' b)))ᴴ).PosDef := by
  subst h h'
  simp only [Fin.cast_eq_self]
  exact hz

theorem lieGram_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ (κ : ℝ) (W : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ) (Z : V X.dim → (Fin (Dw.mult τ.1) → Fin (Dw.p + Dw.q - Dw.mult τ.1) → ℂ)), 0 < κ ∧ (∀ᶠ u in 𝓝 (c'.e y), lieGram e U hj f₀ A₀ A (c'.e.symm u) τ.1 = (κ : ℂ) • ((W u)ᵀ * domGram _ _ (Z u) * (W u)ᴴᵀ)) ∧ (∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ Z u) ∧ (∀ i j, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => W u i j) u) ∧ IsUnit (W (c'.e y)).det ∧ (1 - Matrix.of (Z (c'.e y)) * (Matrix.of (Z (c'.e y)))ᴴ).PosDef := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hLie y hy c' hyc A hA τ
  obtain ⟨kU, G, hG⟩ := GlobalTheory.LieBase.HoloFrame.exists_holo_frame_chart E H Dw l Xo c O β Y T F e σ U hσ hU X j hLie.1
    hj y hy c' hyc
  have hF : ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom,
      cxPt T.Z (U.un kU ⟨G u, h⟩) = cxOf e σ hj (c'.e.symm u) := hG.mono fun u ⟨h, h1, _⟩ => ⟨h, h1⟩
  have hGd : ∀ τ' a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u :=
    fun τ' a b => hG.mono fun u ⟨_, _, h2⟩ => h2 τ' a b
  obtain ⟨M, hMd, hMu, hMc⟩ := GlobalTheory.LieBase.exists_holo_coord_frameAt E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀
    Eb A₀ hj hLie y hy c' hyc A hA τ kU G hF hGd
  have hle : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X kU).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 kU).1]; omega
  have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.HodgeGenUnf.mult_psi τ
  have hq : Dw.p + Dw.q - Dw.mult τ.1 = Dw.p + Dw.q - Dw.p := by rw [hm]
  set τ' := GlobalTheory.HodgeGenUnf.letter hσ hU kU τ with hτ'

  have hco : ∀ u, (∀ τ'' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ'' a b) u) →
      ∀ a b, DifferentiableAt ℂ (fun v => GlobalTheory.TrueCx.frameCo (U.X kU) hle (G v) τ' a b) u := by
    intro u hd a b
    simp only [GlobalTheory.TrueCx.frameCo, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun c _ => (hd _ _ _).const_mul _
  have hmo : ∀ u, (∀ τ'' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ'' a b) u) →
      G u ∈ (U.X kU).dom → ∀ a b,
      DifferentiableAt ℂ (fun v => Formalism.MJ.moeb (GlobalTheory.TrueCx.frameCo (U.X kU) hle (G v) τ') 0 a b) u := by
    intro u hd hdom a b
    simp only [GlobalTheory.TrueCx.moeb_zero]
    refine differentiableAt_mul (fun i k => hco u hd _ _) (differentiableAt_inv (fun i k => hco u hd _ _) ?_) a b
    exact (GlobalTheory.TrueCx.frameCo_isUnit₂₂ (U.X kU) hle hp hdom τ').ne_zero
  refine ⟨2 * Real.pi,
    fun u => (GlobalTheory.ShFam.coW (U.X kU) hle (G u) τ').submatrix (Fin.cast hm) (Fin.cast hm) * M u,
    fun u a b => Formalism.MJ.moeb (GlobalTheory.TrueCx.frameCo (U.X kU) hle (G u) τ') 0 (Fin.cast hm a) (Fin.cast hq b),
    Real.two_pi_pos, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hMc, hF] with u hu1 hu2
    obtain ⟨h, ⟨g, hg⟩, hc⟩ := hu1
    obtain ⟨h', hx⟩ := hu2
    have hex : ∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm u)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm u) g :=
      ⟨g, hg⟩
    rw [lieGram, dite_eq_left hex]
    show ((hodgeMet T.Z U).gram _ hex.choose τ.1)ᵀ = _
    rw [GlobalTheory.HodgeOnDomain.eigGram_transport (hodgeMet T.Z U) hx.symm hex.choose (cxFrame T.Z (U.un kU ⟨G u, h⟩)) τ.1
      (M u) (hc _ _ hex.choose_spec)]
    exact gram_cast hm hq _ _ _ _ _ (GlobalTheory.HodgeGenUnf.hodgeMet_gram_frame T.Z hσ hU kU ⟨G u, h⟩ τ τ' rfl hle)
  · filter_upwards [hG] with u hu
    obtain ⟨h, -, hd⟩ := hu
    exact differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => hmo u hd h _ _
  · intro a b
    filter_upwards [hG, Filter.eventually_all.2 fun c => Filter.eventually_all.2 fun d => hMd c d] with u hu hM
    obtain ⟨h, -, hd⟩ := hu
    refine differentiableAt_mul (fun i k => ?_) (fun i k => hM i k) a b
    simp only [Matrix.submatrix_apply, GlobalTheory.ShFam.coW, Matrix.sub_apply]
    exact (hco u hd _ _).sub (differentiableAt_mul (fun i k => hmo u hd h _ _) (fun i k => hco u hd _ _) _ _)
  · obtain ⟨h, -, -⟩ := hG.self_of_nhds
    rw [Matrix.det_mul]
    refine IsUnit.mul ?_ hMu
    have e1 : ((GlobalTheory.ShFam.coW (U.X kU) hle (G (c'.e y)) τ').submatrix (Fin.cast hm) (Fin.cast hm)).det =
        (GlobalTheory.ShFam.coW (U.X kU) hle (G (c'.e y)) τ').det := Matrix.det_submatrix_equiv_self (finCongr hm) _
    rw [e1]
    exact GlobalTheory.ShFam.isUnit_coW (U.X kU) hle hp h τ'
  · obtain ⟨h, -, -⟩ := hG.self_of_nhds
    have hz := GlobalTheory.TrueCx.domPt_mem (U.X kU) hle id hp h τ'
    exact posDef_cast hm hq _ (GlobalTheory.HodgeDomain.hP_posDef hz)

end GlobalTheory.LieBase.LocalModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodChartRescaleBallToUnitPolydisc
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.HodgeChart


open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in
theorem periodChart_rescale_ball : ∀ (n a g rk : ℕ) (ha : a ≤ n) (ρ : ℝ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ → ρ ≤ 1 → rk ≤ g → (∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (τ₀ z).IsSymm) → (∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0) → (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ z : Fin n → ℂ, (∀ i : Fin a, z (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B (ρ⁻¹ • z) = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z := by
  intro n a g rk ha ρ τ₀ B hr hr1 hrk hholo hsymm hpsd hsupp htoric habel
  set cst : ℂ := (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) with hcst
  have him : cst.im = -Real.log ρ / (2 * Real.pi) := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e : cst = ((-Real.log ρ / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hcst]; push_cast; field_simp; rw [Complex.I_sq]; ring
    rw [e, Complex.im_ofReal_mul, Complex.I_im, _root_.mul_one]
  have hBs : ∀ i (j k : Fin g), B i k j = B i j k := fun i j k => by
    have := (hpsd i).isHermitian.apply j k
    simp at this
    exact_mod_cast this
  have hmaps : ∀ z ∈ polydisc n 1, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    intro u hu
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]
    have : ‖u‖ < 1 := (pi_norm_lt_iff one_pos).2 hu
    calc ρ * ‖u‖ < ρ * 1 := by gcongr
      _ = ρ := _root_.mul_one ρ
  have hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => ρ • z) (polydisc n 1) :=
    ((differentiable_id.const_smul (ρ : ℂ)).differentiableOn).congr fun u _ => by
      funext k; simp [Complex.real_smul]
  refine ⟨⟨hrk, fun j k => ?_, fun z hz => ?_, hpsd, hsupp, htoric, fun z hz => ?_⟩, fun u hu => ?_⟩
  · have h1 := (hholo j k).comp hdiff hmaps
    refine (h1.add (differentiableOn_const (∑ i, cst * (B i j k : ℂ)))).congr fun z _ => ?_
    simp [Matrix.add_apply, Matrix.sum_apply, Function.comp]
  · refine Matrix.IsSymm.ext fun j k => ?_
    have := (hsymm _ (hmaps z hz)).apply j k
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, hBs, this]
  · have h1 := habel _ (hmaps z hz)
    convert h1 using 1
    ext ⟨j, hj⟩ ⟨k, hk⟩
    simp [Matrix.sum_apply, hsupp _ j k (Or.inl hj)]
  · have hρu : ρ • (ρ⁻¹ • u) = u := smul_inv_smul₀ hr.ne' u
    ext j k
    have hu' : ∀ i : Fin a, tlog ((ρ⁻¹ • u) (Fin.castLE ha i)) = Real.log ρ / (2 * Real.pi) + tlog (u (Fin.castLE ha i)) := by
      intro i
      rw [Pi.smul_apply, tlog, tlog, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le,
        Real.log_mul (inv_pos.2 hr).ne' (norm_ne_zero_iff.2 (hu i)), Real.log_inv]
      ring
    simp only [hodgeGram, imPeriod, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      hu', hρu, Complex.add_im, Complex.im_sum, smul_eq_mul]
    push_cast
    simp only [Complex.smul_im, Complex.intCast_im, Complex.intCast_re, smul_eq_mul, him, add_mul, Finset.sum_add_distrib]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, him]
    push_cast
    simp only [zero_add]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

end GlobalTheory.LieBase.HodgeChart
end
end

