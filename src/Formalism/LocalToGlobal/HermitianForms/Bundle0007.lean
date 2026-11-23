module

public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Formalism.LocalToGlobal.HermitianColumns.FullSym
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSame

@[expose] public section

-- bundled from Formalism.LocalToGlobal.HermitianForms.ExtraSym
section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Forms

def ColsFullS {D : D7} (C : ColsTiedSym D) :=
  { full : Formalism.L2.Herm.FullTiedS D // full.cols = C.herm }

def ColsExtraTiedS {D : D7} {C : ColsTiedSym D} (Fu : ColsFullS C) {L : SizeData₂ D} {hT : GatTies D}
    {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    (ex : Extra D L hT Gi Gl K Y cX) : Prop :=
  Formalism.L2.Herm.SymmetricExtraCompatibility Fu.1 ex

end Formalism.L2.Forms

end
end

-- bundled from Formalism.LocalToGlobal.HermitianForms.TiedTwPGen
section
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7}

section Gen

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def sgTG : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => shW (M.sg τ) ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)


set_option maxHeartbeats 1000000 in
structure ClassesAtPrimes (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) where
  lev : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad

  y : M.clsP → UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  lat : M.clsP → Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)
  y_lat : ∀ c (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb
  lat_fin : ∀ c, Module.Finite (𝓞 D.host.E) (lat c)

  stabI : ∀ c, M.stabilizer₂ c →* UJ (sigD D : D.host.E →+* D.host.E) (gramP D)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

variable {M}


set_option maxHeartbeats 1000000 in
structure ValuationAtPrimes {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (K : ClassesAtPrimes M bad) (okW : D.what₂.places.Pl → Prop) where

  sg : ∀ τ (i : Fin (D.R.N D.R.m - 1)),
    ((M.sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i

  eW : P.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ)

  ptC : ∀ z, z ∈ M.ptC ↔ eW z ∈ FiC K.lev (embT D) (sgTG M) K.y

  ipP : ∀ (o : FrP D), o.IsON → ∀ (z z' : P.Wrow)
    (Pc Qc : M.clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ),
    (∀ c, Pc c ∈ CSpan M.sg) → (∀ c, Qc c ∈ CSpan M.sg) →
    (∀ c, eW z c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) (Pc c)) →
    (∀ c, eW z' c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) (Qc c)) →
    M.ipP z z' = ∑ c, ((Nat.card (M.stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll M.sg (Qc c) (Pc c)

  rat : ∀ z, (∃ x, M.ptEmb x = z) ↔
    z ∈ M.ptC ∧ ∀ c, ∃ Pc ∈ RatSpan D M.sg, eW z c = fnOf _ (shiftOf (sgTG M)) 1 Pc

  lat : ∀ w, okW w → ∀ x : M.ptLat.V, x ∈ M.SP w ↔
    ∀ (c : M.clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w) (K.lat c : Set _) B →
      ∃ Pc ∈ IntSpan D w M.sg, eW (M.ptEmb x) c =
        fnOf _ (shiftOf (sgTG M)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N D.R.m - 1)) D.host.E).1) Pc

def NormPTieG {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}
    (W : ValuationAtPrimes K okW) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : M.ptLat.V)
    (Pc : M.clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
    (∀ c, W.eW (M.ptEmb x) c =
      fnOf _ (shiftOf (sgTG M)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))) →
    ∀ o : Frames (gramC (gramP D) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt M.ptLat.b M.ptLat.X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card (M.stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (sgTG M) τ)) *
          (nfAll M.sg (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

end Gen

def ClsPTied.toG {u : D.what₂.Word} (K : ClsPTied u) : ClassesAtPrimes (D.fm u) (badG D) where
  lev := K.lev
  y := K.y
  y_bij := K.y_bij
  lat := K.lat
  y_lat := K.y_lat
  lat_fin := K.lat_fin
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

end Formalism.L2.Forms

end
end

-- bundled from Formalism.LocalToGlobal.HermitianForms.TiedTwSym
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwChJointS {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ)
    (H : HermColsCh D) where

  gOf : ∀ u μ i, T.Ch u μ i → H.Ch u i

  Uloc_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    (i + 1 ≠ D.R.m ∨ v ∉ Formalism.L2.Forms.badG D) →
    (T.lev u μ i h1 hm β).Uloc v = (H.lev u i h1 hm (gOf u μ i β)).Uloc v
  Lb_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    locL v (T.lev u μ i h1 hm β).Lb = locL v (H.lev u i h1 hm (gOf u μ i β)).Lb
  Q_off : ∀ u μ, ∀ v ∈ T.Q μ, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ∧ ∀ a, (D.host.g a : 𝓞 D.host.F) ∉ v.asIdeal

end Formalism.L2.Herm

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def eYS {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf) (i : ℕ)
    (hi : i ≤ D.R.m) : (D.mem u).C.Y i ≃ Fr D i hi :=
  if h : i = 0 ∨ i = D.R.m then (F.val i hi h).eY else F.eYC i (by omega) (by omega)

theorem eYS_end {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf) (i : ℕ)
    (hi : i ≤ D.R.m) (h : i = 0 ∨ i = D.R.m) : eYS F i hi = (F.val i hi h).eY := by
  rw [eYS, dite_eq_left h]

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def twYS (T : Formalism.L2.Herm.TwChTied D inQ) {Ch : D.what₂.Word → ℕ → Type} {chOf : ∀ u i, (D.mem u).C.cls i → Ch u i}
    (F : ∀ u, FormsTiedSym D u (Ch u) (chOf u)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i ≤ D.R.m) :
    (D.chTw u μ).Y i ≃ Fr D i hi :=
  (T.eY u μ i hi).symm.trans (eYS (F u) i hi)


set_option maxHeartbeats 4000000 in
structure TwFormsTiedS (D : D7) (Tw : TwForms D) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (T : Formalism.L2.Herm.TwChTied D inQ) {H : Formalism.L2.Herm.HermColsCh D} (J : Formalism.L2.Herm.TwChJointS T H)
    (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) where

  atT : ∀ u μ, TwAtT Tw u μ

  ch : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), μ ≠ D.what₂.mu0 → ∀ (i : ℕ), 1 ≤ i → ∀ (hm : i ≤ D.R.m) (β : T.Ch u μ i),
    LevelChart D (D.mem u).A.T (badQ D (T.Q μ)) i hm
      (fun c : {c // T.chOf u μ i c = β} => (D.chTw u μ).stab i c.1) (fun c => latCrd D i hm (T.lat u μ i c.1))

  car : ∀ u μ (hμ : μ ≠ D.what₂.mu0) i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i),
    SameCar (rankN D i hm) (T.lev u μ i h1 hm β).Lb (ch u μ hμ i h1 hm β).lev.Lb
      (T.lev u μ i h1 hm β).Uloc (ch u μ hμ i h1 hm β).lev.Uloc (T.lev u μ i h1 hm β).U (ch u μ hμ i h1 hm β).lev.U
      (fun c => ((T.cls u μ hμ i h1 hm β).y c).1) (fun c => ((ch u μ hμ i h1 hm β).y c).1)
      (fun c s => ((T.cls u μ hμ i h1 hm β).stabI c s).1) (fun c s => ((ch u μ hμ i h1 hm β).stabI c s).1)

  chi_fin : ∀ u μ hμ i h1 hm β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (ch u μ hμ i h1 hm β).lev.chi κ ^ n = 1

  chi_offC : ∀ u μ hμ i h1 (h2 : i + 1 ≤ D.R.m) β (κ : (ch u μ hμ i h1 (le_of_succ_m h2) β).lev.U)
    (κ' : ((F u).ch i h1 h2 (J.gOf u μ i β)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) →
    (ch u μ hμ i h1 (le_of_succ_m h2) β).lev.chi κ = ((F u).ch i h1 h2 (J.gOf u μ i β)).lev.chi κ'

  chi_offM : ∀ u μ hμ (h1 : 1 ≤ D.R.m) β (κ : (ch u μ hμ D.R.m h1 le_rfl β).lev.U)
    (κ' : ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) →
    (ch u μ hμ D.R.m h1 le_rfl β).lev.chi κ = ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.chi κ'

  chiJ : ∀ u μ (h : 1 ≤ D.R.m - 1), (T.levJ u μ h).U →* ℂˣ
  chiJ_eq : ∀ u μ hμ (h : 1 ≤ D.R.m - 1) β (κ : (T.levJ u μ h).U)
    (κ' : (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.U), κ'.1 = reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.chi κ' = chiJ u μ h κ

  chiJ_off : ∀ u μ (h : 1 ≤ D.R.m - 1) (κ : (T.levJ u μ h).U) (κ' : (F u).levJ.U),
    κ'.1 = reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → chiJ u μ h κ = (F u).levJ.chi κ'

  val : ∀ u μ hμ i h1 hm, ValuationCompatibleChart (Tw.fm u μ) (twYS T F u μ i hm) (okQ D (T.Q μ)) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  dil : ∀ u μ hμ i h1 hm, DilationCompatibleChart (Tw.fm u μ) (twYS T F u μ i hm) ((atT u μ).eV (F u).atT) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  ipV : ∀ u μ i hi, IpVTieG (Tw.fm u μ) (twYS T F u μ i hi)

  norm : ∀ u μ i hi, NormTieG (Tw.fm u μ) (twYS T F u μ i hi)

  twisted_e0_at_mu0_eq_eMu0 : ∀ u x, Tw.e0 u D.what₂.mu0 x = Tw.eMu0 u 0 (Nat.zero_le _) x


set_option maxHeartbeats 4000000 in
structure SymmetricTwistedLevelData {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} (W : TwFormsTiedS D Tw T J F) where
  lv : ∀ u μ, μ ≠ D.what₂.mu0 → ∀ i, 1 ≤ i → ∀ hm : i ≤ D.R.m,
    LevelCompatibleLattices (Tw.fm u μ) (D.mem u).A.T ((W.atT u μ).res (F u).atT) i hm (fun c => latCrd D i hm (T.lat u μ i c))
  fMe : ∀ u μ hμ i h1 hm β v, (W.ch u μ hμ i h1 hm β).lev.fM (((W.atT u μ).eV (F u).atT) v).1 (((W.atT u μ).eV (F u).atT) v).2 ≃+
    (Tw.A u μ).Fv v
  fv : ∀ u μ hμ i h1 hm, FvTieG (lv u μ hμ i h1 hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm) (fMe u μ hμ i h1 hm)
  upN : ∀ u μ hμ i h1 hm, UpNatTieG (lv u μ hμ i h1 hm) (twYS T F u μ i hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm)
  dnN : ∀ u μ hμ i h1 hm, DnNatTieG (lv u μ hμ i h1 hm) (twYS T F u μ i hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm)
  bw : ∀ u μ, μ ≠ D.what₂.mu0 → ∀ i, 1 ≤ i → ∀ hm : i ≤ D.R.m,
    BwTieG (Tw.fm u μ) (D.mem u).A.T ((W.atT u μ).res (F u).atT) (twYS T F u μ i hm) (fun c => latCrd D i hm (T.lat u μ i c))

structure TwLvSameS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} (W : TwFormsTiedS D Tw T J F) where
  step0 : ∀ u μ, LvSame (W.atT u μ) 0 (T.eCls0 u μ) (T.eY u μ 0 (Nat.zero_le _)) (Tw.e0 u μ)
  mu0 : ∀ u i (hi : i ≤ D.R.m), LvSame (W.atT u D.what₂.mu0) i (Formalism.L2.Herm.clsCast D u i) (Formalism.L2.Herm.yCast D u i) (Tw.eMu0 u i hi)

end Formalism.L2.Forms

end
end

