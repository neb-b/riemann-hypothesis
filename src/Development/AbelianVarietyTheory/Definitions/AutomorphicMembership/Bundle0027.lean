module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.Divisibility.Bundle0006
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DefiniteSideNonzeroIndexPlacesAnyColumnsScale
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cx_zs_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) (κ lam e) : (reErr (reScal Y κ lam) e).zs = Y.zs := rfl

theorem cx_liftMat_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) : (reErr (reScal Y κ lam) e).liftMat cr b j t = Y.liftMat cr b j t := by
  have h : (reErr (reScal Y κ lam) e).liftMatC cr b j t = Y.liftMatC cr b j t := by
    unfold CxData.liftMatC
    rfl
  exact congrArg (kMat Bs.v0.embedding) h

theorem cx_Iw_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) :
    ((reErr (reScal Y κ lam) e).data cr b).Iw j t w = (Y.data cr b).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M b j) (Formalism.DivisionValues.matLat M ((lv (fc Y.zs) b).Tl j t))) (cx_liftMat_scal Y cr κ lam e b j t)

theorem definiteComplexNonzeroIndexPlaces_rescale_errors {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) : (reErr (reScal Y κ lam) e).W1 cr N w ↔ Y.W1 cr N w :=
  exists_congr fun j => or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _)))
    (or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _))) Iff.rfl)

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} (Y : CxData A3.fam3.amb3) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
  (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc Dc' : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
  (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Sp' : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc' Zs))
  (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)

theorem cx_tC_face (j : Fin m) (t : T) :
    Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t := rfl

theorem cx_liftMat_face (j : Fin m) (t : T) :
    Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t :=
  congrArg (fun g => kMat A3.fam3.base3.v0.embedding (relMat (Y.w0C false j) g)) (cx_tC_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem cx_Iw_face (j : Fin m) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false).Iw j t w = (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M false j) (Formalism.DivisionValues.matLat M ((A3.side3 P0 ψ0 Y.zs).Tl j t)))
    (cx_liftMat_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem definiteSide_nonzeroIndexPlaces_any_columns_scale (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 K)) :
    Y.W1 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') N w ↔ ∃ j : Fin m,
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 w ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) w ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨ N.F0 w j ≠ 0) ∨
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 (Formalism.DivisionValues.conjPl w) ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) (Formalism.DivisionValues.conjPl w) ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨
          N.F0 (Formalism.DivisionValues.conjPl w) j ≠ 0) := by
  refine exists_congr fun j => ?_
  rw [← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j, ← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j]
  have key : ∀ a b c d e f : Prop, (a ∨ b ∨ c ∨ d ∨ e ∨ f) ↔ (a ∨ c ∨ e) ∨ (b ∨ d ∨ f) := fun _ _ _ _ _ _ => by tauto
  exact key _ _ _ _ _ _

end Cx

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def NzAt (R : RealDat3 D A3 Ks) (F : Face3 D A3) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  (s0Of R F).Iw j A3.A.μ0 w ≠ 0 ∨
    Formalism.DivisionValues.jw ((A3.side3 F.P0 F.ψ0 (zsOf R F)).HT j A3.A.μ0) w ((A3.side3 F.P0 F.ψ0 (zsOf R F)).Tl j A3.A.μ0) ≠ 0 ∨ F0 w j ≠ 0


set_option maxHeartbeats 1000000 in
theorem toCx3_upd_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc) = reErr (reScal (R.toCx3 F) (fun _ => kap) lam) err := rfl


set_option maxHeartbeats 1000000 in
theorem complexSide_nonzeroIndexPlaces_iff (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (N : IndefNum A3.fam3.base3)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).W1 (reFace F Dc Sp Zsc).cr N w ↔
      ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  rw [e]
  exact (definiteComplexNonzeroIndexPlaces_rescale_errors (R.toCx3 F) _ _ _ _ N w).trans (definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc Dc F.Sp Sp F.Zsc Zsc N w)


set_option maxHeartbeats 1000000 in
theorem complexSide_nonzeroIndexPlaces_iff_self (R : RealDat3 D A3 Ks) (F : Face3 D A3) (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (R.toCx3 F).W1 F.cr N w ↔ ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) :=
  definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Dc F.Sp F.Sp F.Zsc F.Zsc N w


set_option maxHeartbeats 1000000 in
theorem nzAt_res {f : T' → T} {μ : T'} (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    NzAt (Res.dat3 f μ R mu tw) (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w ↔ NzAt R (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w := Iff.rfl


set_option maxHeartbeats 1000000 in
theorem complexSide_numberContents_eq_scaleAtSubspaces (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (C CH : ℝ) :
    (((R.updS kap lam).withErr err).num (reFace F Dc Sp Zsc) C CH).F0 = (Zsc (zsOf R F)).F0 := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  have e2 : (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).zs = (R.toCx3 F).zs :=
    (congrArg CxData.zs e).trans (cx_zs_scal (R.toCx3 F) _ _ _)
  have e3 : ∀ (F' : Face3 D A3) (s : DefSub A3.fam3.amb3), ((F'.fc s).Z.num C CH).F0 = (F'.Zsc s).F0 := fun _ _ => rfl
  exact (e3 (reFace F Dc Sp Zsc) _).trans (congrArg (fun s => (Zsc s).F0) e2)

end Generic

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

theorem _root_.GlobalTheory.Mem.R3.columnChoiceReferenceFace_eq_bareFaceTwoLevels (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) :
    face0 X I hX U Xg tr = Res.bare3 (famR X I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) := rfl


set_option maxHeartbeats 2000000 in
def resGeo (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.GeoHalf z.core (z.resR h).toRealDat fun _ => 1 :=
  Res.geoHalf (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') z.geo




set_option maxHeartbeats 2000000 in
theorem levOf_resR (h : Wt' ⊆ Wt) : LevOf X I (usedOf I T Wt') (z.resR h).toLevCh :=
  ⟨Res.levCh_is (L := z.R.toLevCh) (inclU_injective (usedOf_mono I T h)) z.lev.is,
    z.lev.C,
    fun t => z.lev.xiH (inclU I (usedOf_mono I T h) t),
    z.lev.Pg,
    fun t => z.lev.Q (inclU I (usedOf_mono I T h) t),
    z.lev.beta⟩

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsWtOfParUnique
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.StdModel

section Gen

variable {X : Fields} {n : ℕ} (σ : X.K →+* ℂ)

variable [NeZero n]

variable {σ} {a : ℕ} {H Γ W : Type} [AddCommGroup W] [Module ℂ W]
  {mat : H → GL (Fin a) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)} {rat : Γ → GL (Fin a) X.E → Prop} {ρ : Γ → W → W}
  {ι : Type} {lam : X.Tau → DomWeight n} {rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam)}

end Gen

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_V (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) (i : Fin X.toD7.R.m) : (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := hI.spaces
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.B.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.B.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)



end Rec

end GlobalTheory.Mem.R3.StdModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
section
noncomputable section

namespace GlobalTheory.Mem.Top.GroupRetwisting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

abbrev BaseP : Type 1 := ∀ B : Base, Fr B.toPre → Prop

structure BaseCond (KP : BaseP) : Prop where
  ex : EvG fun K => ∃ (P : Pre) (f₀ : Fr P), K.Over P ∧ ∀ (S₁ : IntermediateField ℚ ℂ → Finset ℂ)
    (S₂ : IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℂ), (∀ F, ∀ z ∈ S₁ F, IsAlgebraic ℚ z) →
    (∀ F F₀, ∀ z ∈ S₂ F F₀, IsAlgebraic ℚ z) →
    ∃ (B : Base) (f : Fr B.toPre), B.toPre = P ∧ HEq f f₀ ∧ KP B f ∧ Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex)
  enl : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre), Enl B B' → HEq f' f → KP B f → KP B' f'

def RetwistG (Q Q' : V4.Slot) : Prop :=
  EvG fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c → ExportAt X.toD7 c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ B : Pre, Fr B → Set (HChar B.host.E) → Finset ℂ), (∀ B f Ξ, ∀ z ∈ S₂ B f Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl X.B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧
        ∀ (C : Cols B') (W : RowsRest B' C) (V : DivStage B' C W) (S : SStage B' C W) (N : NStage B' C W) (G : GJStage B' C)
          (c' : V4.Core K ⟨B', C, W, V, S, N, G⟩ f' T'), Q K ⟨B', C, W, V, S, N, G⟩ f' T' c' →
          DQ.TwAllAt (assemble B' C W V S N G) c'.O.nch c'.O.xd ∧ Q' K ⟨B', C, W, V, S, N, G⟩ f' T' c'

def FromCoreAt (Q : V4.Slot) (K : Ctx) (D : D7) (Y : Lay D) : Prop :=
  ∃ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c ∧
    (⟨D, layObj Y⟩ : Σ D : D7, Obj2 D) = ⟨X.toD7, c.O⟩

def Forced (K : Ctx) (B : Base) (T : TwDat B) : Prop :=
  ∀ p : ℕ, p.Prime → ((∃ i, p = B.host.g i) ∨ p = B.host.d ∨ (p : ℝ) ≤ K.s.X'' B.R.n) → p ∈ T.pl

abbrev AtP : Type 1 := ∀ (_ : Ctx) (B : Base), Fr B.toPre → TwDat B → Prop

def Step (KP : BaseP) (p q : AtP) : Prop := EvLgG fun K B f T => KP B f → Forced K B T → p K B f T → q K B f T

def HasCore (Q : V4.Slot) : AtP := fun K B f T =>
  ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c

def FirstG (KP : BaseP) (Q : V4.Slot) : Prop := Step KP (fun _ B _ T => T = TwDat.untw B T.pl) (HasCore Q)

def ExportF (KP : BaseP) (Q : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd

def Pass (KP : BaseP) (Q : V4.Slot) (r : AtP) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ), (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ r K B' f' T'

def SecondG (KP : BaseP) (Q Q' : V4.Slot) : Prop :=
  Pass KP Q (HasCore fun K X f T c => Q K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧ Q' K X f T c)

def LargeBaseConditionG (KP : BaseP) (Q R : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

theorem evG_all {p : Ctx → Prop} (h : ∀ K, p K) : EvG p := evG_good.imp fun K _ _ _ _ _ => h K

theorem baseCond_of {KP : BaseP} (h : V4.KsCond KP) {PP : ∀ P : Pre, Fr P → Prop}
    (hP : EvG fun K => ∃ (P : Pre) (f : Fr P), K.Over P ∧ PP P f) : BaseCond fun B f => KP B f ∧ PP B.toPre f := by
  refine ⟨((evG_of_ev h.ex).inter hP).imp ?_, fun B B' f f' e hf hk => ⟨h.enl B B' f f' e hf hk.1, ?_⟩⟩
  · rintro K _ _ _ _ ⟨hk, P, f₀, hO, hp⟩
    obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
    refine ⟨_, f₀, hO, fun S₁ S₂ a₁ a₂ => ?_⟩
    obtain ⟨B, f, e, hf, k, H⟩ := hk B₀ f₀ S₁ S₂ hO a₁ a₂
    refine ⟨B, f, e, hf, ⟨k, ?_⟩, H⟩
    generalize B₀.toPre = P₀ at *
    subst e
    cases hf
    exact hp
  · have e1 := e.1
    have h2 := hk.2
    clear hk e
    generalize B.toPre = P at *
    generalize B'.toPre = P' at *
    subst e1
    cases hf
    exact h2

theorem lg_forced (K : Ctx) : large₂ K fun B _ T => Forced K B T := by
  have h : ∀ P : Pre, ∃ S : Finset ℕ,
      ∀ p : ℕ, p.Prime → ((∃ i, p = P.host.g i) ∨ p = P.host.d ∨ (p : ℝ) ≤ K.s.X'' P.R.n) → p ∈ S := fun P => by
    refine ⟨{P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1), ?_⟩
    rintro p - (⟨i, rfl⟩ | rfl | h)
    · fin_cases i <;> simp
    · simp
    · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h)))
  choose S hS using h
  exact ⟨fun _ _ _ => ∅, fun P _ _ _ => S P, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B _ _ _ _ h _ p hp h' => h (hS _ p hp h')⟩

theorem lg_all (K : Ctx) {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, K.Over B.toPre → p B f T) : large₂ K p :=
  (lg_forced K).imp fun B f T hO _ => h B f T hO

section Steps
variable {KP : BaseP} {p q r : AtP}

theorem Step.of_evG (h : EvG fun K => ∀ B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  EvG.imp h fun K _ _ _ _ H => lg_all K H

theorem Step.of_all (h : ∀ K B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  Step.of_evG (evG_all h)

theorem Step.trans (h : Step KP p q) (h' : Step KP q r) : Step KP p r :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => G.2 a b (G.1 a b c)

theorem Step.and (h : Step KP p q) (h' : Step KP p r) : Step KP p fun K B f T => q K B f T ∧ r K B f T :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => ⟨G.1 a b c, G.2 a b c⟩

theorem Step.of_evLgG (h : EvLgG q) : Step KP p q := EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G _ _ _ => G

end Steps

section Tests
variable (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM)
include hH hLP h2b

end Tests

end GlobalTheory.Mem.Top.GroupRetwisting

end
end

