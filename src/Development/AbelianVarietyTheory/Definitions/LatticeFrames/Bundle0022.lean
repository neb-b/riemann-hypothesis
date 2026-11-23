module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CxTiesOf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Formalism.LocalRingCardinality.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.CornerCoordinateAutomatic
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mi

namespace GlobalTheory.MiS.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem used_base (P : RowSideFamily ex) : Formalism.IndefR.RecTie.Used0 D (P.I.tup P.A3.A.μ0) := Or.inl P.tied.div.tup.mu0

theorem mu_eq_of_heq (P : RowSideFamily ex) {Zs : DefSub P.A3.fam3.amb3} (h : Zs = P.Zs)
    (S : IndefData (P.A3.side3 P.P0 P.ψ0 Zs)) (hS : HEq S P.S0) : S.μ = P.S0.μ := by
  subst h
  rw [eq_of_heq hS]

end GlobalTheory.MiS.Check

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def intVec (D : D7) (n : ℕ) : Set (Fin n → D.host.E) := {x | ∀ k, IsIntegral ℤ (x k)}

def IsFinComb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO S T), (∀ k, (x k).map (infPart D) = 0) ∧ f = ∑ k, c k • heisO ψ S T (x k) f₀

abbrev stdHom {D : D7} (S T : HSp D) : AddSubgroup (WO S T) := latO S T (intVec D S.rank) (intVec D T.rank) fun _ => True

def IsRatDatum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ Φ : WO S T → ℂ, IsSBHalf e (stdHom S T) Φ ∧ (∀ γ, Φ (γ.map fun a => e * incA D a) = Ξ γ) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ Φ f

section Dat
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

structure ColDat (Ch : ℕ → Type) where

  ch : ∀ i, Ch i

  chr : ℕ → ((AE (I.rec7 l Z))ˣ →* Circle)

  om : ∀ i, Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))

  vac : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  w : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  μ : ∀ i, Measure (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))
  fd : ∀ i, Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))

  e : AE (I.rec7 l Z)

  kb : ∀ i, TC.GA B (B.R.N i)
  b0 : ∀ i, Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i
  p0 : ∀ i, PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i

variable {I l Z u} {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}

namespace ColDat
variable (A : ColDat I l Z u Ch) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
  (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))

def xi (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (γ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (xiAt I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) (I.idx I.mu0) u i (A.b0 i) (A.b0 (i + 1)) (A.p0 i) (A.p0 (i + 1))
    (Matrix.toLin' (γ.reindex (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))))))

abbrev Q (i : ℕ) (hi : i ≤ B.R.m) : Chart (I.rec7 l Z) u i hi := chart F i hi (A.ch i)

structure Is : Prop where
  std : IsStdChar (I.rec7 l Z) ψ (-1)
  inf : IsInfFam θ
  chr : ∀ j : Fin B.R.m, ChrEq (A.chr ((j : ℕ) + 1)) (I.C.mu0 j)
  om : ∀ i, i < B.R.m → IsWeilDatumO ψ _ _ (A.chr (i + 1)) (A.chr (i + 1)) (A.om i)
  vac : ∀ i, i < B.R.m → IsVacO ψ θ _ _ (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) (A.vac i)
  idem : IsIdemSum A.e (Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup I.mu0) u)
  datum : ∀ i (hi : i + 1 ≤ B.R.m), IsRatDatum ψ _ _ A.e (A.xi i hi) (A.vac i) (A.w i)
  comb : ∀ i, i < B.R.m → IsFinComb ψ _ _ (A.vac i) (A.w i)
  haar : ∀ i, i ≤ B.R.m → (A.μ i).IsHaarMeasure ∧ IsFundamentalDomain (GQ ((I.rec7 l Z).sp.X i)) (A.fd i) (A.μ i)

  base : ∀ i, i ≤ B.R.m → TC.PtOf (A.kb i) (A.p0 i).1.1 ∧ (A.p0 i).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)

  chart_ne : ∀ i hi, Nonempty (A.Q F i hi).cl
  rep : ∀ i hi (c : (A.Q F i hi).cl),
    TC.PtOf ((show TC.GA B (B.R.N i) from ((A.Q F i hi).K.y c).1) * A.kb i) ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)).1.1 ∧
      (show (I.stp u I.mu0 i).Cl from (A.Q F i hi).inc c).1 = A.b0 i ∧
      cosetIn ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)) = cosetIn (A.p0 i)

def IsForm (i : ℕ) (hi : i ≤ B.R.m) (φ : ((I.rec7 l Z).mem u).C.cls i → ((I.rec7 l Z).mem u).C.Y i → ℂ) : Prop :=
  φ ∈ ((I.rec7 l Z).fm u).Fi i ∧ OnChart F i hi (A.ch i) φ

def Keeps : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m) φ, A.IsForm F i (Nat.le_of_succ_le hi) φ → A.IsForm F (i + 1) hi (((I.rec7 l Z).mem u).C.K i φ)

abbrev rd (i : ℕ) (hi : i ≤ B.R.m) := (A.Q F i hi).rd θ

end ColDat
end Dat

def RamAt {D : D7} (u : D.what₂.Word) (i : ℕ) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) : Prop :=
  ∀ v c, ∑ a : ((D.mem u).A.Fv v)ˣ, (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) = 0

def IsEmbTop {D : D7} (z0 : Fin (D.R.N D.R.m) → D.host.E) (emb : GA D D.sp.X' →* GA D (D.sp.X D.R.m)) : Prop :=
  ∀ h, IsExt D z0 (incA D) ((mt _ h).reindex (finCongr (rankP D)) (finCongr (rankP D)))
    ((mt _ (emb h)).reindex (finCongr (rankN D _ le_rfl)) (finCongr (rankN D _ le_rfl)))

def TopForm {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    {par} (M : Formalism.IndefR.Mult.DSModel D.sp.X' par) (eT : (D.mem u).P.Mt → SmT M → GA D D.sp.X' → ℂ) : Prop :=
  ∃ J : SmT M →ₗ[ℂ] (FrP D → ℂ), Function.Injective J ∧ (∀ v, J v ∈ ValC (gramC (gramP D) (embT D)) (sgT u)) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      ∀ y y' : FrP D, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr (rankP D)) (finCongr (rankP D)))) y' y →
        J (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = J (PiTensorProduct.tprod ℂ v) y') ∧
    ∀ (G : (D.mem u).P.Mt) (c : (D.fm u).clsP) (v : SmT M) (h : GA D D.sp.X'), h ∈ GfC D.sp.X' →
      finM _ (rankP D) h = (F.clsP.y c).1.1 →
      eT G v h = (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) * (D.mem u).P.period (F.valP.eW.symm (Pi.single c (J v))) G

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk



def BigGap (D : D7) : Prop := D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)

def IsScaleWithBoundedGamma (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C' ∧ 1 ≤ large₂.CGam

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

section Alg

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}

def Anchored (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ)
    (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  ∀ u, ∃ p b : ℂ, p ≠ 0 ∧ b ≠ 0 ∧ ∀ t (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K),
    c u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) * b =
      p * ⟪sEE (V (X.Θ t (X.jR t (eV t F)))), (fc X.zs).Sp.Pu u ((U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def UnitAt (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  (∀ u t, c u t ≠ 0) ∧ ∀ u w (k : K), Bs.v0.embedding k = c u (X.μ w) / c u Bs.μ0 → vw w k = 0

end Alg

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

abbrev rJ : Set (GA D (D.sp.Y 0)) :=
  levS (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

abbrev rChi : GA D (D.sp.Y 0) → ℂ :=
  Formalism.IndefR.Lev.levChi (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

def rowOf (e : W.Q.Rl.HE.H) : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := PiTensorProduct.lift (W.Q.Rl.HE.e e)

def rowAt (t : W.P.T) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  rowOf W (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (cxW W).zs t F)))

abbrev F0 (u : D.what₂.Word) : Formalism.L2.Forms.Forms0 D u := (W.R.T.cols.forms u).to0

structure BotDat (u : D.what₂.Word) where
  B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)
  b : GA D (D.sp.Y 0)
  a₀ : GA D (D.sp.X 0)
  a : GA D (D.sp.X 0)
  k : GA D (D.sp.Y 0)

variable {W}

variable (W)

structure BotHyp : Prop where
  hyp : HypAt W
  pins : RealPins W.Q
  see : SeeEx W.Q
  used : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t)
  idE : GlobalTheory.Core.Mi.IdE W.S.X
  gap : GlobalTheory.Count.GapGe W.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  fin : Formalism.L2.SG.PackageTie2.FinX W.S.Y

end GlobalTheory.MiTop

namespace GlobalTheory.MiTop

def PuNZ (D : D7) : Prop :=
  ∀ u, ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0

end GlobalTheory.MiTop

end
end

