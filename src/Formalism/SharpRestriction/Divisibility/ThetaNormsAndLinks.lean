module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ThetaNormsAndLinks

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

structure MetX {D : D7} {r j p : ℕ} {Lc : ModuliIntegralCharts.Loc D r j p} (G : LiftErrorLocal.GeoX Lc) where

  Pts : Lc.Pt Lc.Xm → Lc.Unim → Type

  nAt : ∀ y La n, Lc.Sn y La n → Pts y La → ℝ

  nrm_def : ∀ y La n s, IsLUB (Set.range (nAt y La n s)) (G.nrm y La n s)

  mulP : ∀ y La, Pts y La → Pts y La
  mulP_surjective : ∀ y La, Function.Surjective (mulP y La)

  trP : ∀ y La n, Lc.Th y La n → Equiv.Perm (Pts y La)

  Fo : ∀ y La, Set (Pts y La)

namespace MetX

variable {D : D7} {r j p : ℕ} {Lc : ModuliIntegralCharts.Loc D r j p} {G : LiftErrorLocal.GeoX Lc} (M : MetX G)

def I1 : Prop := ∀ y La x, M.nAt y La 1 (Lc.vth y La 1) x ≤ 1

def I2 : Prop := ∀ y La n (s : Lc.Sn y La n) x,
  M.nAt y La (p * n) (G.pull y La n s) x = M.nAt y La n s (M.mulP y La x)

def I3 : Prop := ∀ y La n, ∃ c : Lc.Th y La n →* ℝ, (∀ γ, 0 < c γ) ∧
  ∀ γ (s : Lc.Sn y La n) x, M.nAt y La n (Lc.act y La n γ s) x = c γ * M.nAt y La n s (M.trP y La n γ x)

def I4 : Prop := ∀ y La n (s : Lc.Sn y La n), (∀ x ∈ M.Fo y La, M.nAt y La n s x ≤ 1) →
  ∀ DF, Lc.jet y La n DF s ∈ Lc.intJet y La n DF

def All : Prop := M.I1 ∧ M.I2 ∧ M.I3 ∧ M.I4

end MetX

structure QPack {D : D7} {r j p : ℕ} (Lc : ModuliIntegralCharts.Loc D r j p) (y : Lc.Pt Lc.Xm) where
  A : Type
  [rA : CommRing A]
  th : A →+* (Lc.fld y).C
  th_range : ∀ c : (Lc.fld y).C, ‖c‖ ≤ 1 ↔ c ∈ th.range
  xi : A
  nu : A
  th_nu : ‖th nu‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1))
  TA : Type
  [aT : AddCommGroup TA]
  [mT : Module A TA]
  M : Type
  [aM : AddCommGroup M]
  [mM : Module A M]
  iT : Lc.Tp y →+ TA
  iT_span : Submodule.span A (Set.range iT) = ⊤
  i : TA →ₗ[A] M
  k : M →ₗ[A] TA
  ik : ∀ m, i (k m) = (xi * nu) • m
  ki : ∀ t, k (i t) = (xi * nu) • t
  tf : ∀ m : M, xi • m = 0 → m = 0
  FilM : Submodule A M
  red : FilM →+ Lc.OmV y
  red_smul : ∀ (a : A) (m : FilM), red (a • m) = th a • red m
  red_range : ∀ v, v ∈ Lc.om y ↔ ∃ m, red m = v
  i_mem : ∀ t, i t ∈ FilM
  ht_eq : ∀ t, Lc.ht y t = red ⟨i (iT t), i_mem (iT t)⟩
  k_Fil : ∀ m ∈ FilM, ∃ t, k m = xi • t

attribute [instance] QPack.rA QPack.aT QPack.mT QPack.aM QPack.mM

structure Loc8 {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) where

  mg : ∀ d i, MetX (X.gx d i)
  mc : ∀ N i, MetX (X.cmx N i)

  DatK : ∀ i j b, Set (D.nexp.Dat i j b)

def Loc8.ThK {D : D7} {nch : NChoice D} {X : LiftErrorLocal.Loc D nch} (Z : Loc8 X) (w : LiftErrorLocal.Pl D) (j : ℕ) (b : Bool) :
    Submodule (D.ntw.O (nch.twI w)) (D.nexp.Fm (nch.twI w) j b) :=
  IntegralHeckeForms.Th D.nexp (nch.twI w) j b (Z.DatK (nch.twI w) j b)

def dK (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : ℝ := (LiftErrorLocal.rkK (D.nexp.Bsup i j b) : ℝ)

def d0 (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : ℝ :=
  (Module.finrank (FractionRing (D.ntw.O i)) (IntegralHeckeForms.Fm0 D.nexp i j b) : ℝ)

def dG (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : ℕ :=
  Module.finrank (FractionRing (D.ntw.O i)) (IntegralHeckeForms.V0 D.nexp i j b)

def eSh (D : D7) : ℝ := (((D.R.f : ℝ) * D.R.k) ^ 3)⁻¹ / 4

section Int

variable {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

def IntAt (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (la : HeightOneSpectrum (𝓞 X.B.KO)) (wt : WeightFamilies.Wt D j)
    (N : Submodule (𝓞 X.B.KO) (X.B.Cusp j wt)) : Prop :=
  ∀ F ∈ N, ∀ y : (X.W j h1 h2).Pt la, 0 ≤ (X.W j h1 h2).vAt la y ((X.W j h1 h2).inc wt F)

def Int4 (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (la : HeightOneSpectrum (𝓞 X.B.KO)) : Prop :=
  IntAt X j h1 h2 la (X.run j).wL ((X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL) ∧
  IntAt X j h1 h2 la (X.run j).wF ((X.W j h1 h2).Thc (X.run j).S.sF (X.run j).wF) ∧
  IntAt X j h1 h2 la ((X.W j h1 h2).wF0 (X.run j).wL (X.run j).wF)
    ((X.W j h1 h2).Thc (X.run j).S.s0 ((X.W j h1 h2).wF0 (X.run j).wL (X.run j).wF)) ∧
  IntAt X j h1 h2 la (X.run j).ka ((X.W j h1 h2).Thc (X.run j).S.sK (X.run j).ka)

def laDiv (n : ℕ) (la : HeightOneSpectrum (𝓞 X.B.KO)) : Prop := ((n : ℕ) : 𝓞 X.B.KO) ∈ la.asIdeal

end Int

section admitted

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X)

def admissible_unitary_of_inputs : Prop := (∀ d i, (Z.mg d i).All) ∧ ∀ N i, (Z.mc N i).All

def SandwichExists : Prop := (∀ d (i : Fin 2) (y : (X.P6.loc d (D.host.g i)).Pt (X.P6.loc d (D.host.g i)).Xm),
    Nonempty (QPack (X.P6.loc d (D.host.g i)) y)) ∧
  ∀ N i (y : (X.cm N i).Pt (X.cm N i).Xm), Nonempty (QPack (X.cm N i) y)

def TransferenceTheoremCond : Prop := WeightFamilies.TransferenceTheoremCond

def CharacterRankDiscriminant (CRd : ℝ) : Prop := ∀ d (i : Fin 2) (Z : (X.P6.loc d (D.host.g i)).Mdl) (y : (X.P6.loc d (D.host.g i)).Pt Z),
  (((X.P6.loc d (D.host.g i)).dP y : ℕ) : ℝ) ^ 2 ≤ WeightFamilies.RRv D (CRd - 2)

def MirabolicIndexCond : Prop := ∃ tableDegreeThreeBase : Subgroup (G0g D.nd), D.nexp.U ≤ tableDegreeThreeBase ∧
  (Nat.card tableDegreeThreeBase : ℝ) = LiftErrorLocal.delq D * (Nat.card D.nexp.U : ℝ) ∧
  ∀ (i : D.ntw.Tw) (b : Bool) (h : G0g D.nd), h ∈ tableDegreeThreeBase → h ∉ D.nexp.U →
    ∃ (u : D.nexp.U) (hu : h⁻¹ * (u : G0g D.nd) * h ∈ D.nexp.U),
      D.nexp.psiU i b u ≠ D.nexp.psiU i b ⟨h⁻¹ * (u : G0g D.nd) * h, hu⟩

def admR (C : NChoice D) : Prop := ∀ w : LiftErrorLocal.Pl D, ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  (1 - eSh D) * dK D (C.twI w) j b ≤ (Nat.card D.nexp.U : ℝ) * d0 D (C.twI w) j b

def admG2 : Prop := (1 - eSh D) * (Nat.card D.nexp.U : ℝ) ≤ LiftErrorLocal.delq D

def BadRowShareBound (C : NChoice D) : Prop := ∀ w : LiftErrorLocal.Pl D, ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  d0 D (C.twI w) j b - (dG D (C.twI w) j b : ℝ) ≤
    Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * d0 D (C.twI w) j b

def EqualGoodMultiplicities (C : NChoice D) : Prop := ∀ w : LiftErrorLocal.Pl D, ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  dG D (C.twI w) j b = D.what₂.D0

def admA : Prop := PDVN.ConjugationNormInvariance D

def SupLatticeGroupStable : Prop := ∀ (i : D.ntw.Tw), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (g : G0g D.nd),
  (D.nexp.Bsup i j b).map ((D.nexp.actG i j b g).toLinearMap.restrictScalars (D.ntw.O i)) ≤ D.nexp.Bsup i j b

def SupSpansPsiPart : Prop := ∀ (i : D.ntw.Tw), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
  Submodule.span (FractionRing (D.ntw.O i)) (IntegralHeckeForms.Mall D.nexp i j b : Set (D.nexp.Fm i j b)) = IntegralHeckeForms.Fm0 D.nexp i j b

def AdditiveCharacterIntegrality : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la → Int4 X j h1 h2 la

def ScalingIntegrality : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) la,
  laDiv X (2 * (NumberField.discr D.host.E).natAbs) la → Int4 X j h1 h2 la

def CrudeIntegrality : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) la,
  laDiv X (D.host.pde * D.host.pde') la → Int4 X j h1 h2 la

def ThetaLevelPrimeIntegrality : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) la,
  ¬ laDiv X (2 * (NumberField.discr D.host.E).natAbs * D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') la →
    Int4 X j h1 h2 la

def MLatticeCond : Prop := WeightFamilies.adm1 X.B

def admT4 : Prop := (∀ i0 w, LiftErrorLocal.Over D i0 w → D.ntw.NonzeroIndexPlace (nch.twI w)) ∧ IntegralHeckeForms.adm7 D X.I.E

def NormDecompositionCond : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  ∃ c : Bool → D.ntw.O (nch.twI w), (∀ b, c b ≠ 0) ∧
    (∑ b : Bool, LiftErrorLocal.vDv (D.ntw.O (nch.twI w)) (D.ntw.l (nch.twI w)) (c b)) = (LiftErrorLocal.Dpm D j : ℝ) ∧
    ∀ b, ∀ x ∈ X.ThN w j h1 h2 b, ∃ z ∈ Z.ThK w j b, x = c b • z

def ThetaKGroupStable : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool, LiftErrorLocal.GStab (Z.ThK w j b)

def ThetaKEquivariantData : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  ∀ x ∈ LiftErrorLocal.psiPart (Z.ThK w j b), ((Nat.card D.nexp.U : ℕ) : D.ntw.O (nch.twI w)) • x ∈ X.Th0 w j b

def WeightGeneratorsInLattice : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la →
  ∀ F ∈ X.WWB j la (X.run j).wL (X.run j).n1 (X.run j).n2, ∃ s : 𝓞 X.B.KO, s ∉ la.asIdeal ∧
    s • F ∈ (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL

def RunColumnChoices : Prop := ∀ j, 1 ≤ j → j ≤ D.R.m →
  (X.run j).nW = (X.run j).n1 + (X.run j).n2 ∧
  ∀ i0 la, X.laOver i0 la →
    (X.run j).nus la = (eWL X.B.KO la : ℝ) * (WeightAlgebra.DF (X.run j).wL : ℝ) / ((D.host.g i0 : ℝ) - 1)

def ScalarSizeConditions (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  WeightAlgebra.ParA L H.CA ∧
  WeightAlgebra.SetC L (X.W j h1 h2) H.CK H.C1 H.A1 (X.run j).ka (X.run j).wL (X.run j).wF X.TO (X.run j).nP (X.run j).nW
    (X.run j).h0 ∧
  WeightAlgebra.H3 L H C2 A2 CR 0 (X.run j).wL X.TO ∧ (X.TO : ℝ) ≤ L.sc.x ^ CT ∧
  ∀ i0, X.RangeB CRd i0 (X.run j).wL (X.run j).n1 (X.run j).n2 ∧ 2 * WeightAlgebra.DF (X.run j).ka + 2 < D.host.g i0 ∧
    X.cB CRd i0 j (WeightAlgebra.DF (X.run j).wL) (X.run j).nW ≤ WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL

def FurtherSizeConditions (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  WeightAlgebra.H4 L (X.W j h1 h2) H C2 A2 CR (X.run j).ka (X.run j).wL (X.run j).wF X.TO (X.run j).nW

def GlobalScalarBounds (H : WeightAlgebra.KHyp) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  WeightAlgebra.ScalB L (X.W j h1 h2) H.C1 H.A1 (X.run j).S (X.run j).ka (X.run j).wL (X.run j).wF X.TO

def RegularityOffTypePrimes (H : WeightAlgebra.KHyp) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  (∀ la, 0 ≤ (X.run j).nus la) ∧ (Function.support (X.run j).nus).Finite ∧
  (∑ᶠ la, |(X.run j).nus la| * (X.W j h1 h2).lN la) ≤ WeightAlgebra.PN D L * (X.run j).wL.size ∧
  ∀ la, (∀ i0, ¬ X.laOver i0 la) → ∀ y : (X.W j h1 h2).Pt la,
    (X.W j h1 h2).depth (X.run j).S.sW (X.run j).wL la y ≤
      (((X.run j).nus la + WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL * (X.W j h1 h2).phiC la y : ℝ) : EReal)

end admitted

section Conclusion₂

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

def Conclusion1 : Prop := (∀ d i, (X.gx d i).INT) ∧ ∀ N i, (X.cmx N i).INT

def Conclusion2 : Prop := (∀ d (i : Fin 2), LiftErrorLocal.HTb (X.P6.loc d (D.host.g i))) ∧ ∀ N i, LiftErrorLocal.HTb (X.cm N i)

def CoveringRadiusFunction (CRd : ℝ) : Prop := ∀ d (i : Fin 2), LiftErrorLocal.PhiB (X.P6.loc d (D.host.g i)) CRd

def Conclusion5 (C : NChoice D) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  ∀ B1 B2 : Submodule (D.ntw.O (C.twI w)) (D.nexp.Fm (C.twI w) j b),
    B1.FG → B2 ≤ B1 → LiftErrorLocal.spK B2 = LiftErrorLocal.spK B1 → LiftErrorLocal.GStab B1 → LiftErrorLocal.GStab B2 →
    LiftErrorLocal.delq D * LiftErrorLocal.lenQ (D.ntw.l (C.twI w)) (LiftErrorLocal.psiPart B1) (LiftErrorLocal.psiPart B2) ≤
      LiftErrorLocal.lenQ (D.ntw.l (C.twI w)) B1 B2 + (LiftErrorLocal.rkK B1 : ℝ) * LiftErrorLocal.vU D (C.twI w)

def Conclusion6 (C : NChoice D) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  (LiftErrorLocal.rkK (D.nexp.Bsup (C.twI w) j b) : ℝ) / LiftErrorLocal.delq D ≤
                 2 * (Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.Fm0 D.nexp (C.twI w) j b) : ℝ) ∧
    Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.V0 D.nexp (C.twI w) j b) = D.what₂.D0 ∧
    (Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.Fm0 D.nexp (C.twI w) j b) : ℝ) ≤ 2 * D.what₂.D0 ∧
    (D.nexp.Bsup (C.twI w) j b).map (IntegralHeckeForms.AO D.nexp (C.twI w) j b) ≤ D.nexp.Bsup (C.twI w) j b

def ShareLatticeRanks (C : NChoice D) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  LiftErrorLocal.rkK (IntegralHeckeForms.Mall D.nexp (C.twI w) j b) =
                 Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.Fm0 D.nexp (C.twI w) j b) ∧
    LiftErrorLocal.rkK (LiftErrorLocal.Mj D (C.twI w) j b) = D.what₂.D0

def GGEveryPlace (C : NChoice D) : Prop := ∀ w, PDVN.GGAt D C w

def ShareEveryPlace (C : NChoice D) : Prop := ∀ w, PDVN.SHAt D C w

def ShareRankEveryPlace (C : NChoice D) : Prop := ∀ w, PDVN.SHbAt D C w

def ScaledGeneratorsInSup : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL ≤ X.B.Mlat j (X.run j).wL ∧
  (X.W j h1 h2).Thc (X.run j).S.sF (X.run j).wF ≤ X.B.Mlat j (X.run j).wF ∧
  (X.W j h1 h2).Thc (X.run j).S.s0 ((X.W j h1 h2).wF0 (X.run j).wL (X.run j).wF) ≤
    X.B.Mlat j ((X.W j h1 h2).wF0 (X.run j).wL (X.run j).wF) ∧
  (X.W j h1 h2).Thc (X.run j).S.sK (X.run j).ka ≤ X.B.Mlat j (X.run j).ka

def LinkLatticesEveryPlace : Prop := ∀ w, PDVN.LKAt X w

def LinkConditions : Prop :=
  (∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    (∀ b : Bool, (D.nexp.Bsup (nch.twI w) j b).FG ∧ LiftErrorLocal.GStab (D.nexp.Bsup (nch.twI w) j b) ∧
      X.ThN w j h1 h2 b ≤ D.nexp.Bsup (nch.twI w) j b ∧
      IntegralHeckeForms.InclAt D.nexp (nch.twI w) j b (X.I.E.Dat0 (nch.twI w) j b) (nch.k' w) ∅ 1) ∧
    ∃ c : Bool → D.ntw.O (nch.twI w), (∀ b, c b ≠ 0) ∧
      (∑ b : Bool, LiftErrorLocal.vDv (D.ntw.O (nch.twI w)) (D.ntw.l (nch.twI w)) (c b)) = (LiftErrorLocal.Dpm D j : ℝ) ∧
      ∀ b, ∀ x ∈ LiftErrorLocal.psiPart (LiftErrorLocal.GSpan (X.ThN w j h1 h2 b)), ∃ z ∈ X.Th0 w j b,
        ((Nat.card D.nexp.U : ℕ) : D.ntw.O (nch.twI w)) • x = c b • z) ∧
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la →
    ∀ F ∈ X.WWB j la (X.run j).wL (X.run j).n1 (X.run j).n2, ∃ s : 𝓞 X.B.KO, s ∉ la.asIdeal ∧
      s • F ∈ (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL

def RunConditions (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  (X.run j).nW = (X.run j).n1 + (X.run j).n2 ∧
  (∀ i0, X.RangeB CRd i0 (X.run j).wL (X.run j).n1 (X.run j).n2 ∧ 2 * WeightAlgebra.DF (X.run j).ka + 2 < D.host.g i0 ∧
    X.cB CRd i0 j (WeightAlgebra.DF (X.run j).wL) (X.run j).nW ≤ WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL ∧
    ∀ la, X.laOver i0 la →
      (X.run j).nus la = (eWL X.B.KO la : ℝ) * (WeightAlgebra.DF (X.run j).wL : ℝ) / ((D.host.g i0 : ℝ) - 1)) ∧
  ((∀ i0 la, X.laOver i0 la → ∀ y : (X.W j h1 h2).Pt la,
      (X.W j h1 h2).depth (X.run j).S.sW (X.run j).wL la y ≤
        (((X.run j).nus la + WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL * (X.W j h1 h2).phiC la y : ℝ) : EReal)) →
    WeightAlgebra.Hyp L (X.W j h1 h2) H C2 A2 CR 0 CT (X.run j).S (X.run j).ka (X.run j).wL (X.run j).wF X.TO
      (X.run j).nP (X.run j).nW (X.run j).h0 (X.run j).nus)

end Conclusion₂

section Joint

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

end Joint

section Stmt

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X)

def admitted (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  admissible_unitary_of_inputs D X Z ∧ SandwichExists D X ∧ TransferenceTheoremCond ∧ CharacterRankDiscriminant D X CRd ∧ MirabolicIndexCond D ∧
    (admR D nch ∧ admG2 D ∧ BadRowShareBound D L nch ∧ EqualGoodMultiplicities D nch ∧ admA D ∧ SupLatticeGroupStable D) ∧ SupSpansPsiPart D ∧
    (AdditiveCharacterIntegrality D X ∧ ScalingIntegrality D X ∧ CrudeIntegrality D X ∧ ThetaLevelPrimeIntegrality D X) ∧
    (MLatticeCond D X ∧ admT4 D X ∧ NormDecompositionCond D X Z ∧ ThetaKGroupStable D X Z ∧ ThetaKEquivariantData D X Z ∧ WeightGeneratorsInLattice D X) ∧
    (RunColumnChoices D X ∧ ScalarSizeConditions D L X H C2 A2 CR CT CRd ∧ FurtherSizeConditions D L X H C2 A2 CR ∧ GlobalScalarBounds D L X H ∧ RegularityOffTypePrimes D L X H)

def AtEveryPlace : Prop := GGEveryPlace D nch ∧ ShareEveryPlace D nch ∧ ShareRankEveryPlace D nch ∧ LinkLatticesEveryPlace D X

def Conclusion₂ (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  Conclusion1 D X ∧ Conclusion2 D X ∧ CoveringRadiusFunction D X CRd ∧ Conclusion5 D nch ∧ Conclusion6 D nch ∧ ShareLatticeRanks D nch ∧ ScaledGeneratorsInSup D X ∧ LinkConditions D X ∧
    RunConditions D L X H C2 A2 CR CT CRd ∧ AtEveryPlace D X

def Stmt (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  2 ≤ CRd → admitted D L X Z H C2 A2 CR CT CRd → Conclusion₂ D L X H C2 A2 CR CT CRd

end Stmt

theorem vAdd_nonneg_int {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    0 ≤ vAdd la (a : K) := by
  unfold vAdd
  have h := la.valuation_le_one (K := K) a
  by_cases h0 : la.valuation K (a : K) = 0
  · rw [h0]; simp
  · have := (WithZero.log_le_log h0 one_ne_zero).2 h
    simp at this
    omega

section Forms

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (W : WeightAlgebra.PJ D B P j)

end Forms

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
  (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc8 (XF x hx i))

end Fam

end Formalism.MainNotions.ThetaNormsAndLinks

end
