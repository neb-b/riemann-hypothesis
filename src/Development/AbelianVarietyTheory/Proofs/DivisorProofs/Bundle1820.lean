module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

section Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure TwLev (R : RealDat D A Ks) (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E))
    (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop where
  xi : ChrEq xi χ
  xi_fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  xi_triv : χ.TrivOn D.host.F
  xi_tame : ∀ v, χ.TameAt v
  Q_pl : IsTwistPlaces D.host.g Q
  Q_off : ∀ PP ∈ Q, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
    ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  Q_de : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
    (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
      ∀ PP ∈ Q, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭
  Q_ram : ∀ PP, ¬ χ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP
  xiR : ∀ PP ∈ Q, IsRes χ PP (xiR PP)
  roots : ∀ PP ∈ Q, ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))
  muVal : ∀ (i : Fin D.R.m) (P : Pl0), Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (Q : Set (Pl D.host.E))) →
    ∃ a : D.what₂.LLˣ, D.what₂.embLL (a : D.what₂.LL) = (((R.C.mu0 i * χ).val (R.pl P) : ℂˣ) : ℂ)
  half : ∀ PP ∈ Q, ∀ PP' ∈ Q, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))
  guard : ∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

theorem twLev_of_core {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hG : QGuard R) (t : T0) :
    TwLev R (R.xiH t) (R.xi t) (R.Q t) (R.xiR t) :=
  { xi := hC.lev.xi t
    xi_fin := hC.lev.xi_fin t
    xi_triv := hC.lev.xi_triv t
    xi_tame := hC.lev.xi_tame t
    Q_pl := hC.lev.Q_pl t
    Q_off := hC.lev.Q_off t
    Q_de := fun p hp => by
      obtain ⟨𝔭, h𝔭⟩ := hC.lev.Q_de p hp
      exact ⟨𝔭, h𝔭, h𝔭 t⟩
    Q_ram := hC.lev.Q_ram t
    xiR := hC.lev.xiR t
    roots := fun PP hPP => hC.fam.roots t PP (Or.inr hPP)
    muVal := fun i P hP => by
      obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
      exact ⟨A.muVal i t P, hC.fam.muVal i t P ((ht.ok t P).2 hP)⟩
    half := hG.1 t
    guard := hG.2 t }

end Lev

section Laws

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def Laws (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)) : Prop :=
  GlobalTheory.Hk3.Core R F ∧ Finite T0 ∧ Nonempty (FWTie T R κ v₀) ∧ IoExt R ∧ QGuard R ∧ OMPins T R κ v₀ O j ∧ PhaseTie T R κ v₀ O ph j ∧
    BaseOf R j B

def Ext (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (j : Fin D.R.m)
    {T0' : Type} {A' : FamIn D.what₂.LL G Pl0 T0' D.R.m} (R' : RealDat D A' T.Q.c.F)
    (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)) : Prop :=
  (∀ τ, FixBase T R j τ → FixBase T R' j τ) ∧
    (∀ τ ζ Φ Φ', ConjFun (O' j) (κ j) τ ζ Φ Φ' → ConjFun (O j) (κ j) τ ζ Φ Φ') ∧
    (∀ (c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W) (u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ), ExtC R j (inC (O j).c') (O j).c0' c →
      (∀ ρ, (u ρ : (R.MW j (sg0 D A)).sm ρ) = v₀ j (sg0 D A) ρ) →
      ∃ (c' : VsV D j ℂ →ₗ[ℂ] (R'.cV j).W) (u' : ∀ ρ, lowT (R'.MW j (sg0 D A')) ρ), ExtC R' j (inC (O' j).c') (O' j).c0' c' ∧
        (∀ ρ, (u' ρ : (R'.MW j (sg0 D A')).sm ρ) = v₀' j (sg0 D A') ρ) ∧
        ∀ x, R'.ioP j (PiTensorProduct.tprod ℂ u') (c' x) = R.ioP j (PiTensorProduct.tprod ℂ u) (c x))

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} {j : Fin D.R.m}

theorem Ext.refl : Ext T R κ v₀ O j R v₀ O :=
  ⟨fun _ h => h, fun _ _ _ _ h => h, fun c u hc hu => ⟨c, u, hc, hu, fun _ => rfl⟩⟩

theorem Ext.trans {T1 T2 : Type} {A1 : FamIn D.what₂.LL G Pl0 T1 D.R.m} {A2 : FamIn D.what₂.LL G Pl0 T2 D.R.m}
    {R1 : RealDat D A1 T.Q.c.F} {R2 : RealDat D A2 T.Q.c.F} {v1 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R1.MW i σ).Vec}
    {v2 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R2.MW i σ).Vec} {O1 : ∀ i, OMDat T.toCore R1 i Unit (fun _ => A1.μ0)}
    {O2 : ∀ i, OMDat T.toCore R2 i Unit (fun _ => A2.μ0)} (h1 : Ext T R κ v₀ O j R1 v1 O1) (h2 : Ext T R1 κ v1 O1 j R2 v2 O2) :
    Ext T R κ v₀ O j R2 v2 O2 := by
  refine ⟨fun τ h => h2.1 τ (h1.1 τ h), fun τ ζ Φ Φ' h => h1.2.1 τ ζ Φ Φ' (h2.2.1 τ ζ Φ Φ' h), fun c u hc hu => ?_⟩
  obtain ⟨c1, u1, hc1, hu1, e1⟩ := h1.2.2 c u hc hu
  obtain ⟨c2, u2, hc2, hu2, e2⟩ := h2.2.2 c1 u1 hc1 hu1
  exact ⟨c2, u2, hc2, hu2, fun x => (e2 x).trans (e1 x)⟩

theorem hasTuples_of_laws {ph : Fin D.R.m → ℂ} {B : Base (Vc D j) (Wc D j)} {ψ ψ' : Twist D Circle} {T0' : Type}
    {A' : FamIn D.what₂.LL G Pl0 T0' D.R.m} {R' : RealDat D A' T.Q.c.F} {F' : Face D A'}
    {v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec} {O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)}
    (hL : Laws T R' F' κ v₀' O' ph j B) (hE : Ext T R κ v₀ O j R' v₀' O') {t t' : T0'} (ht : IsTupOf R' B ψ t)
    (ht' : IsTupOf R' B ψ' t') : HasTuples T R κ v₀ O ph j B ψ ψ' :=
  ⟨T0', A', R', F', v₀', O', hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1, hL.2.2.2.2.1, hL.2.2.2.2.2.1, hL.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2,
    hE.1, hE.2.1, hE.2.2, t, t', ht, ht'⟩

end Laws

section Point


end Point

end GlobalTheory.BigOn.Exp.TwConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCosetProductsCommuteSplitPlace
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckePairCount

theorem card_pairs_eq {G : Type} [Group G] (J L : Subgroup G) (x y : G) (A B : Finset G)
    (hθ : ∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧
      (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b)
    (hAL : ∀ a ∈ A, a ∈ L) (hBL : ∀ a ∈ B, a ∈ L) (hA : Bridge.IsDC J x A) (hB : Bridge.IsDC J y B) (c : G ⧸ J) :
    ((A ×ˢ B).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card =
      ((B ×ˢ A).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card := by
  obtain ⟨θ, hL, hm, hi, hK, hdc⟩ := hθ
  by_cases hc : ∃ z ∈ L, (z : G ⧸ J) = c
  · obtain ⟨z, hz, rfl⟩ := hc
    have key : ∀ C E : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ E, a ∈ L) →
        (C ×ˢ E).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = (z : G ⧸ J)) =
          (C ×ˢ E).filter (fun p => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) := by
      intro C E hC hE
      refine Finset.filter_congr fun p hp => ?_
      rw [Finset.mem_product] at hp
      rw [eq_comm, QuotientGroup.eq, QuotientGroup.eq]
      exact ⟨fun h => ⟨h, L.mul_mem (L.inv_mem hz) (L.mul_mem (hC _ hp.1) (hE _ hp.2))⟩, fun h => h.1⟩
    rw [key A B hAL hBL, key B A hBL hAL]
    have e1 := GlobalTheory.DoubleCosetComm.card_pairs (A := A) hB hAL hBL hz
    have e2 := GlobalTheory.DoubleCosetComm.card_pairs (A := B) hA hBL hAL hz
    have e3 := le_antisymm (GlobalTheory.DoubleCosetComm.card_conv_le hm hi hK hL hdc hA hB hAL hz)
      (GlobalTheory.DoubleCosetComm.card_conv_le hm hi hK hL hdc hB hA hBL hz)
    exact e1.trans (e3.trans e2.symm)
  · have key : ∀ C E : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ E, a ∈ L) →
        (C ×ˢ E).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c) = ∅ := by
      intro C E hC hE
      refine Finset.filter_eq_empty_iff.2 fun p hp h => hc ?_
      rw [Finset.mem_product] at hp
      exact ⟨_, L.mul_mem (hC _ hp.1) (hE _ hp.2), h⟩
    rw [key A B hAL hBL, key B A hBL hAL]


set_option maxHeartbeats 1600000 in
theorem side_count {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hβ : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) {Pl0 : Type}
    (pl : Pl0 → Formalism.L2.DIV.Pl D.host.E) (ok : Set Pl0) (Sp : Set (Formalism.L2.DIV.Pl D.host.E))
    (hok : ∀ P, P ∈ ok ↔ Bridge.SplitOff (pl P) Sp) (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ∈ Sp) (i i' : ok × ℕ)
    (hv : (pl i.1).under (𝓞 D.host.F) = (pl i'.1).under (𝓞 D.host.F)) (hi : i.2 ≤ V.rank)
    (x y : Bridge.Gf V) (A B : Finset (Bridge.Gf V)) (hx : isTEnv V pl ok i x)
    (hA : ∀ a ∈ A, isLocEnv V pl ok i a) (hB : ∀ a ∈ B, isLocEnv V pl ok i' a)
    (dA : Bridge.IsDC (levEnv V β L).J x A) (dB : Bridge.IsDC (levEnv V β L).J y B)
    (c : Bridge.Gf V ⧸ (levEnv V β L).J) :
    ((A ×ˢ B).filter (fun p => ((p.1 * p.2 : Bridge.Gf V) : Bridge.Gf V ⧸ (levEnv V β L).J) = c)).card =
      ((B ×ˢ A).filter (fun p => ((p.1 * p.2 : Bridge.Gf V) : Bridge.Gf V ⧸ (levEnv V β L).J) = c)).card := by
  refine (hx hi).elim fun α h0 => h0.1.elim fun e h1 => h1.elim fun ϖ h2 => ?_
  have he := h2.1
  have hsp := (hok _).1 i.1.2
  have hl := GlobalTheory.SplitHeckeAdj.local_group V β Λ L hβ (pl i.1) e he
    fun PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff hsp PP (hS PP h)
  refine hl.elim fun Lc hl => ?_
  have l1 := hl.1
  have l4 := hl.2.2.2.1
  have hm : ∀ x, isLocEnv V pl ok i x → x ∈ Lc := fun x hx => by
    refine (GlobalTheory.SplitHeckeAdj.loc_supp V hx he).elim fun g hg => ?_
    rw [← hg.2]
    exact l1 g hg.1
  have hm' : ∀ x, isLocEnv V pl ok i' x → x ∈ Lc := fun x hx => by
    refine hm x (GlobalTheory.FrameProdLoc.isLocEnv_of_mem V pl ok i x e he ?_)
    rw [hv]
    exact GlobalTheory.FrameProdLoc.mem_locGrp_of_isLocEnv V pl ok i' x hx
  exact card_pairs_eq (levEnv V β L).J Lc x y A B l4 (fun a ha => hm a (hA a ha)) (fun a ha => hm' a (hB a ha)) dA dB c


set_option maxHeartbeats 1600000 in
theorem card_pairs_comm : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i i' : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → 1 ≤ i'.2 → i'.2 ≤ (Vc D j).rank → (plOf p j t i.1).under (𝓞 D.host.F) = (plOf p j t i'.1).under (𝓞 D.host.F) → ∀ c : Bridge.Gf (Vc D j) ⧸ levJ p j t, ((hkA p j t i ×ˢ hkA p j t i').filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card = ((hkA p j t i' ×ˢ hkA p j t i).filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t i i' h1 h2 h1' h2' hv c
  have hb := p.charW.base
  refine hb.fam.tie.elim fun gramR h3 => h3.elim fun c0R h4 => h4.elim fun c0L tie => ?_
  refine (hb.lev.βV j).elim fun c' hc => ?_
  rw [one_pow] at hc
  have main := side_count (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) hc p.R.pl (p.P.A3.A.ok t) _ (tie.ok t)
    (fun PP hP => hP.elim (fun h1 => Or.inl (hb.fam.Sb h1)) Or.inr) i i' hv h2
    ((p.R.B.L j t).hecke.hx i) ((p.R.B.L j t).hecke.hx i') (hkA p j t i) (hkA p j t i')
    ((p.R.B.L j t).hecke.hx_ok i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hA_loc i' ⟨h1', h2'⟩)
    ((p.R.B.L j t).hecke.hDC i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hDC i' ⟨h1', h2'⟩) c
  exact main

end GlobalTheory.HeckePairCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalGeneratorZpowMulCuspFormMemSpan
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.MulSpan

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem zero_mem_SS' (X : Data E r) (la : Wt X.Ψ r) : (0 : Frame X.Ψ r → ℂ) ∈ X.SS la := by
  refine ⟨⟨⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩, 0, fun x _ => by
    simp [Data.pnorm]⟩, fun ξ _ x _ => ?_⟩
  unfold Data.fj
  split_ifs <;> simp


open Classical in
def mulAt {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) : FDSec X →ₗ[ℂ] FDSec X :=
  (LinearMap.single ℂ (fun k => Frame (X k).Ψ r → ℂ) k0) ∘ₗ (LinearMap.mulLeft ℂ h) ∘ₗ
    (LinearMap.proj (R := ℂ) (φ := fun k => Frame (X k).Ψ r → ℂ) k0)

theorem mulAt_same {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) (P : FDSec X) :
    mulAt X k0 h P k0 = fun y => h y * P k0 y := by
  simp only [mulAt, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_same, LinearMap.mulLeft_apply,
    LinearMap.proj_apply]
  rfl

open Classical in
theorem mulAt_ne {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) (P : FDSec X) {k : Comp}
    (hk : k ≠ k0) : mulAt X k0 h P k = 0 := by
  simp only [mulAt, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_of_ne hk]

theorem mulAt_mem_holSub {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ)
    (la la' : ∀ k, Wt (X k).Ψ r) (hh : ∀ Q ∈ (X k0).SS (la k0), (fun y => h y * Q y) ∈ (X k0).SS (la' k0))
    {P : FDSec X} (hP : P ∈ holSub X la) : mulAt X k0 h P ∈ holSub X la' := by
  have hle : holSub X la ≤ (holSub X la').comap (mulAt X k0 h) := by
    refine Submodule.span_le.2 fun Q hQ => ?_
    refine Submodule.subset_span (s := {P | IsHolCusp X la' P}) fun k => ?_
    by_cases hk : k = k0
    · subst hk
      rw [mulAt_same]
      exact hh _ (hQ k)
    · rw [mulAt_ne X k0 h Q hk]
      exact zero_mem_SS' _ _
  exact hle hP

theorem horizGen_zpow_mul_rdU_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (k0 : (U σ).Comp), framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} → ∀ (τ' : ((U σ).X k0).Ψ) (m : ℤ) (b b' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom b n → Dom b' n → (∀ ρ i, i < Dw.mult ρ → 1 ≤ b' (ρ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → modelWt (U σ) (wtZ b' n) k0 = modelWt (U σ) (wtZ b n) k0 + m • modelFlat r τ' → ∀ f ∈ cuspOn U Z (wtZ b n), (fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1) ∈ Submodule.span ℂ ((fun g : Rul Xo c => fun y : ↥((U σ).X k0).dom => rdU (U σ) g k0 y.1) '' (cuspOn U Z (wtZ b' n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z σ hσ k0 hk τ' m b b' n hb hb' hpos hn hw f hf
  have hP : rdU (U σ) f ∈ holSub (U σ).X (modelWt (U σ) (wtZ b n)) := (mem_cuspW.1 (cuspOn_le U Z _ hf)).2 σ hσ
  have hLP : mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) ∈
      holSub (U σ).X (modelWt (U σ) (wtZ b' n)) := by
    refine mulAt_mem_holSub _ k0 _ _ _ (fun Q hQ => ?_) hP
    rw [hw]
    refine HorizMul.horizGen_zpow_mul_mem_SS E r _ τ' _ m (hL.det σ hσ k0) (fun γ hγ => ?_) Q hQ
    rw [← hw, modelWt_wtZ, modelWt_wtZ, hL.chi σ hσ b n hb k0 γ hγ, hL.chi σ hσ b' n hb' k0 γ hγ]
  have hoff : ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k y = 0 := by
    intro k y hy
    by_cases hkk : k = k0
    · subst hkk
      have hd : y ∉ ((U σ).X k).dom := fun hd => hy (by rw [hk]; exact ⟨rfl, hd⟩)
      have h0 : rdU (U σ) f k y = 0 := by
        simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_neg, not_false_eq_true]
      rw [mulAt_same]
      simp only [h0, mul_zero]
    · rw [mulAt_ne _ _ _ _ hkk]
      rfl
  have hsp : mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) ∈
      Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtZ b' n) : Set (Rul Xo c))) := by
    let P := mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f)
    have hpts : HasPts U Z := GlobalTheory.FlatLine.hasPts U hL.pos hL.good hL.unf Z
    have e : goodOf c σ = σ := if_pos hσ
    have htest := (hpts.1 σ).2
    rw [e] at htest
    have hoff' : P ∈ offZero (U σ).X := fun k y hy => hoff k y fun hz => hy hz.1
    have hP0 : P ∈ holSub0 (U σ).X (laU (U σ) b' n) := ⟨by rwa [← modelWt_wtZ], hoff'⟩
    have hsp' := hL.onto σ hσ b' n hb' hpos hn hP0
    have hfix : rdU (U σ) (idem Z) * P = P := by
      funext k y
      show rdU (U σ) (idem Z) k y * P k y = P k y
      by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨hd, hl⟩ := hz
        have h1 : rdU (U σ) (idem Z) k y = 1 := by
          simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_pos]
          rw [evR_idem hl (htest _ ⟨hd, hl⟩ hd)]
          rfl
        rw [h1, one_mul]
      · have hzero : P k y = 0 := hoff k y hz
        rw [hzero, mul_zero]
    let g : FDSec (U σ).X →ₗ[ℂ] FDSec (U σ).X := LinearMap.mulLeft ℂ (rdU (U σ) (idem Z))
    have hmap := Submodule.mem_map_of_mem (f := g) hsp'
    rw [Submodule.map_span] at hmap
    have hg : g P = P := hfix
    rw [hg] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨idem Z * f, ⟨?_, ?_⟩, ?_⟩
    · rw [← cuspW_wtZ] at hf
      exact GlobalTheory.CompRestr.idem_mul_mem_cuspW hL.unf Z hf
    · rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
    · exact AllWt.rdU_mul (U σ) _ _
  let R : FDSec (U σ).X →ₗ[ℂ] (↥((U σ).X k0).dom → ℂ) :=
    { toFun := fun Q y => Q k0 y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmap := Submodule.mem_map_of_mem (f := R) hsp
  rw [Submodule.map_span, Set.image_image] at hmap
  have e : R (mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f)) =
      fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1 := by
    funext y
    show mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k0 y.1 = _
    rw [mulAt_same]
  rw [e] at hmap
  exact hmap

end GlobalTheory.FlatCore.MulSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntermediateFieldPadicIntegersEqNormLeOne
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameOf

theorem intEmb_range_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] Lf],
    Function.Injective (intEmb Lf) ∧ ∀ x, x ∈ Set.range (intEmb Lf) ↔ x ∈ Lf ∧ ‖x‖ ≤ 1 := by
  intro l _ Lf _
  refine ⟨fun a b h => Subtype.ext (Subtype.ext h), fun x => ?_⟩
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a : Lf).2, ?_⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le]
    have ha : IsIntegral ℤ_[l] (a : Lf) := a.2
    exact ha.map (Lf.val.restrictScalars ℤ_[l])
  · rintro ⟨hx, hn⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le] at hn
    have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : Lf) :=
      (isIntegral_algHom_iff (Lf.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 hn
    exact ⟨⟨⟨x, hx⟩, hi⟩, rfl⟩

end GlobalTheory.FrameOf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelComponentTransportComp
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isTransp_comp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a a' : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ' k k₁ a' → IsTransp p r i v ψ γ k₁ k₂ a → IsTransp p r i v ψ (γ' * γ) k k₂ (a * a') := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v ψ γ γ' k k₁ k₂ a a' h₁ h₂
  obtain ⟨m₁, f₁, l₁⟩ := h₁
  obtain ⟨m₂, f₂, l₂⟩ := h₂
  have hP := (h.laws v).p
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left 1 _, i.isLt⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1)
    (GlobalTheory.Proof.ModelAtPrimeToLevel.one_le_rank hP hj) hP.pins.2.1.2
  have hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k₂) (a * a') :=
    { psi := m₁.psi.trans m₂.psi
      p0 := m₁.p0.trans m₂.p0
      xi := m₁.xi.trans m₂.xi
      iso := fun u w => by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, m₂.iso, m₁.iso]
      lat := fun w => by
        rw [m₁.lat, m₂.lat, Units.val_mul, Matrix.mulVec_mulVec] }
  refine ⟨hm, fun x hx => ?_, fun w => ?_⟩
  · obtain ⟨hy₁, t₁, b₁⟩ := f₁ x hx
    obtain ⟨hy₂, t₂, b₂⟩ := f₂ _ hy₁
    have ef : castFrame hm.psi (lact (a * a') x) =
        castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) := by
      funext τ
      simp only [castFrame, lact, mat, Units.val_mul, Matrix.map_mul, Matrix.of_apply]
      rw [mul_assoc]
      rfl
    set Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)
    set c := (r.used v).full.Q.c
    set y₀ := (uAt r v i).un k ⟨x, hx⟩
    set y₁ := (uAt r v i).un k₁ ⟨castFrame m₁.psi (lact a' x), hy₁⟩
    have e1 := hL.mul γ' γ _ y₀ _ _ (mvPt_spec hL.total γ' y₀) (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e2 := hL.func (γ' * γ) _ y₀ _ _ (mvPt_spec hL.total (γ' * γ) y₀) e1
    have e3 : mvLev Xo c γ (mvLev Xo c γ' y₀) = mvLev Xo c (γ' * γ) y₀ :=
      ((GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).1 _ _ e2
        (GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).2.1)
    have e4 := hL.bor γ _ t₁ y₁ _ (mvLev Xo c γ' y₀) _ b₁ (mvPt_spec hL.total γ y₁)
      (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e5 := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ _ _ _ _ _ _).2.1 t₂ t₁ _ _ _ b₂ e4
    have key : ∀ (z : Frame ((uAt r v i).X k₂).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k₂).dom),
        z = castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) →
        FrBor (t₂ * t₁) ((uAt r v i).un k₂ ⟨z, hz⟩) (mvLev Xo c (γ' * γ) y₀) := by
      rintro z hz rfl
      rw [← e3]
      exact e5
    exact ⟨ef ▸ hy₂, t₂ * t₁, key _ _ ef⟩
  · obtain ⟨hw₁, q₁⟩ := l₁ w
    obtain ⟨hw₂, q₂⟩ := l₂ ⟨_, hw₁⟩
    have e : ((a * a' : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E) =
        (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec
          ((a' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E)) := by
      rw [Units.val_mul, Matrix.mulVec_mulVec]
    have hs : ∀ z, (γ' * γ).symm z = γ.symm (γ'.symm z) := fun z =>
      (γ' * γ).injective (by
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply])
    rw [e]
    refine ⟨hw₂, q₂.trans ?_⟩
    refine congrArg (ψ k₂) ?_
    refine (congrArg γ.symm ((congrArg (ψ k₁).symm q₁).trans ((ψ k₁).symm_apply_apply _))).trans ?_
    exact (hs _).symm

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoThickPlaceCentreWindowStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_thickPlace_centre_window : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → τ ∈ (GlobalTheory.ExpTie.Lift.wts L j).T2 → (GlobalTheory.ExpTie.parOf L j).Thick ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).h := by
  first | exact @GlobalTheory.ExpTie.Lift.thick_of_mem | exact GlobalTheory.ExpTie.Lift.thick_of_mem | (intros; apply GlobalTheory.ExpTie.Lift.thick_of_mem <;> assumption)
end

