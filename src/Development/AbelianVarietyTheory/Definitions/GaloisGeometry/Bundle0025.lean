module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
public import Formalism.LocalToGlobal.Columns.Bundle0046
public import Formalism.LocalToGlobal.Columns.Bundle0044
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
section
noncomputable section

namespace GlobalTheory.Svd

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2

def ModelsAt (D : D7) (O : Obj D) : Prop :=
  G.LatTied O.gatT O.Gx O.Gy → 2 * G.rG O.L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D O.Gy O.ex.cmp O.X O.ex.tw

structure StdAt {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l))
    (O : Obj (I.rec7 l Z)) (t : KerEntTied O.ex) : Prop where
  ok : I.Ok
  pins : TC.Pins B X
  isTw : I.IsTw
  jets : ColIn.JetsIn I
  tw : O.ex.tw = I.tw l l0 Z
  ker : I.StdKer l Z t
  entC : GlobalTheory.Pdv.IsEntC t
  adapted : t.Adapted
  top : t.TopPinned

def StdTie (D : D7) (O : Obj D) (t : KerEntTied O.ex) : Prop :=
  ∃ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l))
    (O' : Obj (I.rec7 l Z)) (t' : KerEntTied O'.ex), StdAt I l l0 Z O' t' ∧
    (⟨D, O, t⟩ : Σ (D : D7) (O : Obj D), KerEntTied O.ex) = ⟨I.rec7 l Z, O', t'⟩

theorem StdTie.intro {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {l0 : I.Law0 l} {Z : TC.Later B (I.cols l)}
    {O : Obj (I.rec7 l Z)} {t : KerEntTied O.ex} (h : StdAt I l l0 Z O t) : StdTie (I.rec7 l Z) O t :=
  ⟨B, X, I, l, l0, Z, O, t, h, rfl⟩

theorem StdTie.ind {R : ∀ (D : D7) (O : Obj D), KerEntTied O.ex → Prop}
    (h : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l))
      (O : Obj (I.rec7 l Z)) (t : KerEntTied O.ex), StdAt I l l0 Z O t → R (I.rec7 l Z) O t)
    {D : D7} {O : Obj D} {t : KerEntTied O.ex} (hD : StdTie D O t) : R D O t := by
  obtain ⟨B, X, I, l, l0, Z, O', t', hs, e⟩ := hD
  cases e
  exact h B X I l l0 Z _ _ hs

def ServH {Bd : GlobalTheory.Fc.BdT} (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex) (𝒜 : FamClass) (σ : GlobalTheory.Fc.RawSel Bd 𝒜) : Prop :=
  (Closed 𝒜 fun Fm _ => GlobalTheory.TwU.RowTwU Fm) ∧ GlobalTheory.Fc.AtAll (fun D O c b => GlobalTheory.Pdv.At O.ex (ker D O c b).ent) 𝒜 σ

section Part

open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

variable {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B}

structure Part (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) : Type 1 where
  pin : ColPin w
  col : ColT w Z
  errX : O.errX = Formalism.L2.Herm.toErrXS col.full.1
  tp : Formalism.L2.Host.TupTied (w.D Z) (TC.cf w.I w.l Z) O.nch
  xi : tp.xi = w.I.xi
  qp : TC.QpIs w.I O.X.Qp
  ker0 : KerFam (w.D Z) col.Gt col.cmp (w.tw Z) O.Gy
  ker_eq : (⟨O.gatT, O.cmp, O.tw, O.ker⟩ : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)),
    KerFam (w.D Z) Gt cmp tw O.Gy) = ⟨col.Gt, col.cmp, w.tw Z, ker0⟩
  ker : KerT col O.X O.Gy ker0

def HasPart : CP := fun _ _ _ _ w Z c => Nonempty (Part w Z c.O)

def HasPartAnd (P : ZP) : CP := fun K B f T w Z c => HasPart K B f T w Z c ∧ P K B f T w Z

end Part

end GlobalTheory.Svd

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
section
noncomputable section

namespace GlobalTheory.TwU.WildChar

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker _root_.Formalism.UG _root_.Formalism.L2.Forms
open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

section Idele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)

end Idele

section Central

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) {u : D.what₂.Word} (μ : D.what₂.Tup)

variable {t μ} {St : ChainCharts D u μ} {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}


end Central

section Twist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

end Twist

section Charts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
  {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}


end Charts

section True

open GlobalTheory.TwU.AtTrue

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



end True

end GlobalTheory.TwU.WildChar

end

noncomputable section

namespace GlobalTheory.TwU.Rigid

open _root_.Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.MainNotions.G.KAat _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV
open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}


end GlobalTheory.TwU.Rigid

end

noncomputable section

namespace GlobalTheory.TwU.Model

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.UG
open scoped TensorProduct

section CongBasic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

theorem intAtA_sum {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) :
    IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end CongBasic

theorem sameCoset_equiv {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (P : rowSG Pr sel mu) :
    Equivalence (fun y y' : Sp X.E n => SameCoset sel mu cst P y y') := by
  constructor
  · intro y l
    rw [sub_self, Pi.zero_apply, mul_zero]
    exact ciIntAt_zero
  · intro y y' h l
    have h1 := ciIntAt_neg (h l)
    rwa [← mul_neg, ← Pi.neg_apply, neg_sub] at h1
  · intro x y z h h' l
    have h1 := (h l).add (h' l)
    rwa [← mul_add, ← Pi.add_apply, sub_add_sub_cancel] at h1

end GlobalTheory.TwU.Model

end
end

