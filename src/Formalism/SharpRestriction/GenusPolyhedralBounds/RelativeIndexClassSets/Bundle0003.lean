module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0001
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0003
public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LargeConstantLeParamCube
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface

@[expose] public section

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Geo NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.FamilyHypotheses

def SupBoundPageRows (D : D7) (large₂ : SizeData₂ D) {j : ℕ} (ka : WeightFamilies.Wt D j) : Prop :=
  (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧
  lrd D ≤ 2 * large₂.sc.L ∧
  Real.log D.host.d ≤ 2 * large₂.sc.L ∧
  Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * large₂.sc.L ∧
  Real.log D.R.f ≤ 2 * large₂.sc.L ∧
  Real.log D.host.pde ≤ large₂.sc.L ∧
  Real.log D.host.pde' ≤ large₂.sc.L ∧
  Real.log (1 + DF ka) ≤ 2 * large₂.sc.L ∧
  Real.log ka.n ≤ large₂.sc.L

def OwnPr (D : D7) (p : ℕ) : Prop := p = Formalism.MainNotions.DIV.Cons.po D ∨ p = Formalism.MainNotions.DIV.Cons.po2 D

theorem ownPr_iff (D : D7) (p : ℕ) : OwnPr D p ↔ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ) := Iff.rfl

section Split

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def FourthHypothesisSizes (large₂ : SizeData₂ D) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  large₂.sc.b ≤ ka.size ∧ (T : ℝ) * wL.size ≤ 2 * ka.size ∧
  wF.size ≤ ((WeightFamilies.dimY D j : ℝ) + 2) * wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T ∧
  WeightFamilies.PPv D large₂ C2 A2 ^ 3 * (T : ℝ) ^ 2 ≤ large₂.sc.b ∧
  WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ≤ large₂.sc.b ∧
  (∀ i, 2 * DF ka + 2 < D.host.g i)

def I4 (large₂ : SizeData₂ D) (X : PJ D B P j) (wL wF : WeightFamilies.Wt D j) (nW : ℕ) : Prop :=
  ∃ PLam lNc : ℝ, PLam ≤ 1009 * Zb D large₂ ∧ lNc ≤ 81 * Zb D large₂ ^ 2 ∧
  (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th ∈ B.Mlat j w1, X.NonZeroComp w1 th ∧
    ∀ σ, Real.log (B.supN j w1 σ th) ≤ 2 * PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size) ∧
  ∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 ∧ ∃ th ∈ B.Mlat j w2, X.NonZeroComp w2 th ∧
    ∀ σ, Real.log (B.supN j w2 σ th) ≤ PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size

theorem fourthHypothesis_iff_sizes_and_index (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nW : ℕ) :
    H4 large₂ X H C2 A2 CR ka wL wF T nW ↔ FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, e, f⟩, g⟩, fun ⟨⟨a, b, c, d, e, f⟩, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

def HypPage (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ)
    (h0 : ℝ) : Prop :=
  ParA large₂ H.CA ∧ SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0 ∧ H3 large₂ H C2 A2 CR 0 wL T ∧
    FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ (T : ℝ) ≤ large₂.sc.x ^ CT

theorem hypC_iff (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ↔
      HypPage large₂ X H C2 A2 CR CT ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧
        Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ X wL nus ∧ H2 X S ka wL wF ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨⟨a, b, f, ((fourthHypothesis_iff_sizes_and_index ..).1 g).1, h⟩, c, d, e, ((fourthHypothesis_iff_sizes_and_index ..).1 g).2⟩,
    fun ⟨⟨a, b, f, g, h⟩, c, d, e, i⟩ => ⟨a, b, c, d, e, f, (fourthHypothesis_iff_sizes_and_index ..).2 ⟨g, i⟩, h⟩⟩

def refill {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G₀ : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF)
    (del : ℕ) (th' : Fin del → B.Cusp j wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF)) (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G₀.N) →₀ ℕ) →₀ B.Cusp j ka)
    (rq : ℕ) (th : Fin rq → B.Mlat j ka) (iet : ℕ) (et : B.Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j iet)) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF :=
  ⟨G₀.N, G₀.w, del, th', rz, alz, th0, zc, rq, th, iet, et, G₀.mx⟩

end Split

section Views

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

variable (F : ShimFam D G Lev) (I : Type) (dat : I → Dat D Lev) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I)
  (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j)

end Views

end Formalism.MainNotions.Gaps.FamilyHypotheses
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def ShareRhoT (T rz rq d : ℕ) : Prop := (rz : ℝ) ≤ rq + 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def flipOneThree (D : D7) (nW : ℕ) : ℝ :=
  max (16200 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4)
    (max ((2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 * (nW : ℝ) + 2 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3)
      ((D.R.r : ℝ) * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3))

def PageSupp (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) {j : ℕ} (C2 A2 : ℝ) (nW : ℕ) (S : Scal B) (wL : WeightFamilies.Wt D j) :
    Prop :=
  flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  (∀ σ : B.KO →+* ℂ, (DF wL : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (S.sW : B.KO)‖) ∧
  (D.R.f : ℝ) ^ 2 ≤ D.host.rdE ∧ 8 ≤ D.R.r ∧ 3 ≤ DF wL

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def CombBound4 (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Prop :=
  ∀ la (ζ : PtsG G la),
    0 ≤ X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ∧ (X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ≠ ⊤ →
      X.depth S.sW wL la ((Qf la).y ζ) ≤
        (((nus la : ℝ) + c / (2 * (G.iet : ℝ)) * (X.vAt la ((Qf la).y ζ) (X.inc _ G.et)).toReal : ℝ) : EReal))

theorem combBound4_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : j < D.R.m) (h : CombBound G S c nus) (Qf : ∀ la, LocalPointData G la) : CombBound4 G Qf S c nus :=
  fun la ζ => (h la ((Qf la).y ζ)).1 hj

def DepthAtM (X : PJ D B P j) (S : Scal B) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ∀ la (y : X.Pt la), X.depth S.sW wL la y ≤ ((nus la : ℝ) : EReal)

theorem depthAtM_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : D.R.m ≤ j) (h : CombBound G S c nus) : DepthAtM X S wL nus :=
  fun la y => (h la y).2 hj

def ConclAtM (large₂ : SizeData₂ D) (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  D.R.m ≤ j → DepthAtM X S wL nus →
    Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

def PageGd4 (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) : Prop :=
  WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd

theorem pageGd4_iff {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {large₂ : SizeData₂ D} {CG AG Pd : ℝ} :
    PageGd4 X ka large₂ CG AG Pd ↔ PageGd X ka large₂ CG AG Pd := Iff.rfl

def PolyDom4 (D : D7) {j : ℕ} (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (C2 A2 CR Ch Ah Cq Aq : ℝ)
    (Gc PH Prw Pet Pd : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  2 ≤ K.CRm ∧ 0 ≤ CR ∧ 0 ≤ Gc ∧ 0 ≤ Prw ∧ 0 ≤ WeightFamilies.PP0v D large₂ K.CL K.AL ∧ WeightFamilies.Obound B large₂ Ch Ah ∧
  WeightFamilies.RRv D H.CRc * WeightFamilies.PPv D large₂ H.Cc H.Ac ≤ WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ∧
  WeightFamilies.RRv D K.CRm * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D CR ^ 2 ∧
  2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 ∧ 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f ∧
  (2 * Gc + 6 * PH + Prw) * 25 ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  Pet ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂) ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  60 * Gc + 180 * PH + 44 * (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) +
      22 * (2 * WeightFamilies.PPv D large₂ Cq Aq) ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * (WeightFamilies.dimY D j : ℝ) ∧
  1 / 2 ≤ Prw ∧ Prw ≤ PH ∧ 0 ≤ Pet ∧
  Prw ≤ WeightFamilies.PPv D large₂ C2 A2

theorem polyDom4_iff {B : WeightFamilies.Prov D} {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ}
    {ka : WeightFamilies.Wt D j} :
    PolyDom4 D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ↔ PolyDom D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka :=
  Iff.rfl

def Conclusion1OfComb4 : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd4 (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoT (D := D) (j := j) T G.rz G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    (∀ la, InContainZ G la S T) → (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) →
    (j < D.R.m → ∃ Qf : ∀ la, LocalPointData G la,
      (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
      CombBound4 G Qf S (cc D large₂ C2 A2 CR wL) nus ∧ Heights Qf Gc PH Prw Pet) →
    (D.R.m ≤ j → DepthAtM (X j h1 h2) S wL nus) →
    ConclAtM large₂ (X j h1 h2) S ka wL wF T nus →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.DiscriminantPowEightLeSqrt
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

def q0N (T : ParamsT D L P) : ℕ := ⌈L.sc.b / (T.TO : ℝ)⌉₊

theorem f_ge (D : D7) : 8 ≤ D.R.f := by
  have he : 2 ≤ D.R.toFrame.e := D.host.two_le_e
  have hU : Nat.card (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ = 2 ^ (D.R.toFrame.e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      show D.R.toFrame.e + 2 = (D.R.toFrame.e + 1) + 1 by ring, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  have hH : Nat.card (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by simp)
  have hmul := Subgroup.card_mul_index (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ))
  rw [hU] at hmul
  have hidx : 2 ^ D.R.toFrame.e ≤ (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index := by
    have h2 : 2 ^ (D.R.toFrame.e + 1) = 2 * 2 ^ D.R.toFrame.e := by ring
    nlinarith
  have hsurj := Nat.card_le_card_of_surjective _ D.R.toFrame.projection_surjective_field
  have hcard : Nat.card (Additive (Formalism.FrobeniusOrbits.HGrp D.R.toFrame.e)) =
      (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index := rfl
  have hfin : Nat.card (Formalism.HC.Idx D.R.toFrame.ord) = D.R.toFrame.ord := by
    unfold Formalism.HC.Idx
    simp
  rw [hcard, hfin] at hsurj
  have h4 : 4 ≤ 2 ^ D.R.toFrame.e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ D.R.toFrame.e := Nat.pow_le_pow_right (by norm_num) he
  unfold Ranks.f Ranks.n
  omega

theorem r_ge (D : D7) : 6 ≤ D.R.r := by
  unfold Ranks.r
  have := D.R.two_le_m
  have := D.R.m_add_three_le_k
  omega

theorem r_le_2k (D : D7) : D.R.r ≤ 2 * D.R.k := by
  unfold Ranks.r
  have := D.R.m_add_three_le_k
  omega

theorem f_le_k (D : D7) : D.R.f ≤ D.R.k := by
  unfold Ranks.f Ranks.n
  exact D.R.f_le_k

theorem one_le_L (L : SizeData₂ D) : 1 ≤ L.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem b_pos (L : SizeData₂ D) : 0 < L.sc.b := by
  unfold Scale.b
  exact Real.exp_pos _

theorem A_le_Z (L : SizeData₂ D) : (D.R.f : ℝ) * D.R.r ≤ zBase L := by
  unfold zBase
  exact le_mul_of_one_le_right (by positivity) (one_le_L L)

theorem zBase_pow_twelve_le (T : ParamsT D L P) (hZ : 1 ≤ zBase L) : zBase L ^ 12 ≤ T.PP := by
  rw [T.PP_eq]
  have h1 : zBase L ^ (12 : ℕ) = zBase L ^ (12 : ℝ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 : zBase L ^ (12 : ℝ) ≤ zBase L ^ T.eP := Real.rpow_le_rpow_of_exponent_le hZ T.eP_ge
  have h3 : 0 ≤ zBase L ^ T.eP := Real.rpow_nonneg (by linarith) _
  have h4 : 1 * zBase L ^ T.eP ≤ T.CP * zBase L ^ T.eP := mul_le_mul_of_nonneg_right T.one_le_CP h3
  rw [h1]
  linarith

theorem discriminant_pow_eight_le_sqrt (P : ParameterChoice' D L) (S : SizesAt L) : D.host.rdE ^ 8 ≤ L.sc.b ^ ((1 : ℝ) / 2) := by
  obtain ⟨-, -, -, -, ⟨ht1, -⟩, -, hQD, -⟩ := S
  obtain ⟨-, -, -, -, -, -, hrd1, hrd2⟩ := hQD
  have hc := P.condE_le
  simp only [Formalism.BasicNotions.LevelStarExponents.condE] at hc
  push_cast at hc
  have hq : (1 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 1 ≤ D.host.q)
  have hd : (1 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 1 ≤ D.host.d)
  have hQS : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs0 : 0 ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hC1 : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by nlinarith
  have hrdC : D.host.rdE ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
    have h1 : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) := by nlinarith
    have h2 : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hsq (by linarith)
    nlinarith
  have h8 : D.host.rdE ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 :=
    pow_le_pow_left₀ (by linarith) hrdC 8
  have h36 : ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 :=
    pow_le_pow_right₀ hC1 (by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
  have hpos : 0 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 := by positivity
  nlinarith

theorem rn_of (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) :
    Rn ((D.R.f : ℝ) * D.R.r) D.R.k L.sc.b (L.sc.b ^ ((1 : ℝ) / 2)) T.PP T.TO D.host.rdE D.R.r ((T.Dp : ℝ) + 2) T.nWn T.nP
      (q0N T) := by
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
  have hr6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast r_ge D
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast r_le_2k D
  have hz1 : (1 : ℝ) ≤ zBase L := le_trans (by norm_num) hZ
  have hz12 := zBase_pow_twelve_le T hz1
  have hAZ := A_le_Z L
  have hzz2 : zBase L ^ 2 ≤ zBase L ^ 12 := by
    first
    | exact pow_le_pow_right₀ hz1 (by norm_num)
    | exact pow_le_pow_right hz1 (by norm_num)
  have hPPA : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ T.PP := by
    have h1 : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ zBase L * zBase L :=
      mul_le_mul hZ hAZ (by positivity) (by linarith)
    nlinarith
  have hTO40 := T.TO_40
  have hTOpos : (0 : ℝ) < T.TO := by exact_mod_cast (by omega : 0 < T.TO)
  have hb := b_pos L
  have hrd1 : (1 : ℝ) ≤ D.host.rdE := by
    have hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
      have h := NumberField.discr_ne_zero D.host.E
      have h' : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h
      exact_mod_cast h'
    unfold Host.rdE
    exact Real.one_le_rpow hd (by positivity)
  have hnW : 40 ≤ T.nWn := by
    have h1 := T.nW_lo.1
    have h2 := f_ge D
    have h3 := r_ge D
    have h4 : 8 * 6 ≤ D.R.f * D.R.r := Nat.mul_le_mul h2 h3
    have h5 : D.R.f * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := by
      first
      | exact Nat.le_mul_of_pos_right _ (by omega)
      | exact Nat.le_mul_of_pos_right (by omega)
    generalize D.R.f * D.R.r * (D.R.r + 1) = X at *
    generalize D.R.f * D.R.r = Y at *
    omega
  have hq0lo : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℕ) := by
    unfold q0N
    have h := Nat.le_ceil (L.sc.b / T.TO)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO) = L.sc.b := by
      field_simp
    calc L.sc.b = (T.TO : ℝ) * (L.sc.b / T.TO) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h hTOpos.le
  have hq0hi : (T.TO : ℝ) * (q0N T : ℕ) ≤ L.sc.b + T.TO := by
    unfold q0N
    have h := Nat.ceil_lt_add_one (div_nonneg hb.le hTOpos.le)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO + 1) = L.sc.b + T.TO := by
      field_simp
      try ring
    have := mul_le_mul_of_nonneg_left h.le hTOpos.le
    linarith
  exact
    { forty_eight_le_constant := by nlinarith
      k8 := by linarith
      Ak := by nlinarith [mul_le_mul hfk hr2k (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      sb_sq := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.mul_self_sqrt hb.le
      PPA := hPPA
      h32 := T.precision_cube_order_sq_le_sqrt
      hTP := T.TO_PP'
      one_le_order_alt := by exact_mod_cast (by omega : 1 ≤ T.TO)
      rd1 := hrd1
      rd8 := discriminant_pow_eight_le_sqrt P S
      r6 := hr6
      rA := by nlinarith
      two_le_degree_alt := by have : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _; linarith
      W := by exact_mod_cast T.TO_nW
      forty_mul_degree_le_order := by exact_mod_cast T.TO_40
      forty_le_weight_count := by exact_mod_cast hnW
      projectivePointSizes := Nat.cast_nonneg _
      nPW := by exact_mod_cast T.nW_lo.2.2
      q0lo := hq0lo
      q0hi := hq0hi }

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IsLatticeOfAdmissible
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.T0

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem qlen_of_idx (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (la : HeightOneSpectrum (𝓞 B.KO))
    (hLat : InLat X ka la S wL wF T) (hΘM : X.Theta S ka wL wF T ≤ X.Msup ka) (e r : ℝ)
    (h : ∀ U : Submodule (X.Kl la) ↥(WL X ka la),
      (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(WL X ka la) (MW X ka la ⊓ U.restrictScalars (X.Ol la))
        (ThW X S ka wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤ e * (finrank (X.Kl la) U : ℝ) + r)
    (V' : Submodule (X.Kl la) (X.Vl la)) (hV' : V' ≤ X.locK la (X.Msup ka)) :
    X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤ e * (finrank (X.Kl la) V' : ℝ) + r := by
  have hb := h (V'.comap (WL X ka la).subtype)
  have hrk : finrank (X.Kl la) ↥(V'.comap (WL X ka la).subtype) = finrank (X.Kl la) V' :=
    (Submodule.comapSubtypeEquivOfLe hV').finrank_eq
  have hq := qlen_eq_inW X ka la (X.loc la (X.Msup ka)) (X.loc la (X.Theta S ka wL wF T)) V' hV'
  have hle : ThW X S ka wL wF T la ≤ MW X ka la :=
    Submodule.comap_mono (Submodule.span_mono (Set.image_mono hΘM))
  have h0 := qlen_eq_zero_of_le
    (MW X ka la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (ThW X S ka wL wF T la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (inf_le_inf_right _ hle)
  have hfin := qlen_inf_ne_top (X.Ol la) (X.Kl la) ↥(WL X ka la) (MW X ka la) (ThW X S ka wL wF T la)
    hLat.1 hLat.2 ((V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
  rw [← hq]
  refine ⟨hfin, ?_⟩
  rw [hrk] at hb
  unfold Formalism.LatticeIndexTer.idx at hb
  rw [h0] at hb
  have hb' := hb
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero, Int.cast_natCast] at hb'
  exact hb'

theorem span_eq_top_of_shortG {X : PJ D B P j} {w : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {β : ℝ}
    (h : ShortG X w N β) : Submodule.span B.KO (N : Set (B.Cusp j w)) = ⊤ := by
  obtain ⟨Sh, h1, h2, -⟩ := h
  exact top_le_iff.1 (h2 ▸ Submodule.span_mono h1)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfLocalAndSum
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

theorem concl_of_nat {j : ℕ} (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) (r : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hnu : ∀ la, 0 ≤ nus la) (hr0 : ∀ la, 0 ≤ r la) (hrs : Summable (fun la => r la * X.lN la))
    (hrb : (∑' la, r la * X.lN la) ≤ β)
    (hloc : ∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
        X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
        ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
            (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
          (e : ℝ) * (Module.finrank (X.Kl la) V' : ℝ) + r la) :
    Concl X S ka wL wF T nus β := by
  unfold Concl
  refine ⟨r, hr0, hrs, hrb, ?_⟩
  intro la e he V' hV'
  have hT : (0 : ℝ) ≤ (T : ℝ) * nus la := mul_nonneg (Nat.cast_nonneg _) (hnu la)
  have he0 : (0 : ℤ) ≤ e := by
    have h := hT.trans he
    exact_mod_cast h
  lift e to ℕ using he0 with n
  have h := hloc la n (by exact_mod_cast he) V' hV'
  simpa only [Int.cast_natCast] using h

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

