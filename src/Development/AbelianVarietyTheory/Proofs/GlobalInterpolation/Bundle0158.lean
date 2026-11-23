module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0136
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTrueColsRowInt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace GlobalTheory.PerQ.RowIntModel

theorem mem_mtildeL_iff {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (z : MtildeV W Ch sel mu P) :
  z ∈ MtildeL W Ch sel mu P ↔ ∀ d : RowPt Pr R sel mu, z.1 d ∈ nabAt X.emb W.sgTrue d.1.N := Iff.rfl

theorem mtildeL_rep_mem {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (z : MtildeV W Ch sel mu P) (hz : z ∈ MtildeL W Ch sel mu P) (c : (stepX Ch sel mu P).Cl) :
  ∃ y ∈ nabAt X.emb W.sgTrue ((stepX Ch sel mu P).rep c).1.1.deco.1.N, y = z.1 (toRow sel mu ((stepX Ch sel mu P).rep c).1.1) :=
  ⟨z.1 (toRow sel mu ((stepX Ch sel mu P).rep c).1.1), toRow_N sel mu ((stepX Ch sel mu P).rep c).1.1 ▸ (mem_mtildeL_iff W Ch sel mu P z).1 hz (toRow sel mu ((stepX Ch sel mu P).rep c).1.1), rfl⟩

open GlobalTheory.PerQ
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)



section G
open GlobalTheory.PeriodOnStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

theorem span_mtildeL (hX : X.Ok) : Submodule.span X.K (MtildeL W Ch sel mu P : Set (MtildeV W Ch sel mu P)) = ⊤ := (MtildeH_good W Ch hX sel mu P).2.2

theorem span_toMtP (hX : X.Ok) : Submodule.span ℂ (Set.range fun z : MtildeL W Ch sel mu P => toMtP W Ch sel mu P σ z.1) = ⊤ :=
    toCForm_span_of_span σ W.sgTrue _ _ hX (φ := fun z : MtildeL W Ch sel mu P => z.1) (eq_top_iff.2 ((span_mtildeL W Ch sel mu P hX).ge.trans (Submodule.span_mono fun z hz => ⟨⟨z, hz⟩, rfl⟩)))

include hd in
theorem exists_form_of_mt (F : (perOn W Ch sel mu P b0 til ext tz (fun _ => ⊤)).Mt X.emb σ) : ∃ G : MtP W Ch sel mu P σ, ∀ b d, F.1 b d = G.1 (toRow sel mu d.1.1) := by
  have hl : FrLaw σ W.sgTrue (rowTyG Ch P) (levQX R sel mu) ⊤ fun p : XPt Pr R sel mu => F.1 () (trivPt X _ _ _ _ p) := by
    intro p
    refine ⟨(F.2 () _).1, fun g hg => ?_⟩
    show F.1 () (trivPt X _ _ _ _ (g • p)) = _
    rw [← stepX_smul_trivPt]
    exact (F.2 () (trivPt X _ _ _ _ p)).2 g hg
  obtain ⟨G, hG, e⟩ := hl.exists_form σ W.sgTrue (isSubLev_top _ _) hd
  exact ⟨⟨G, hG⟩, fun b p => ((e p.1.1).trans (congrArg (F.1 ()) ((trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).apply_symm_apply p))).symm⟩

theorem exists_mem_of_form (hX : X.Ok) (T : Submodule ℂ ((perOn W Ch sel mu P b0 til ext tz (fun _ => ⊤)).Mt X.emb σ))
  (hT : ∀ z ∈ MtildeL W Ch sel mu P, rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ z ∈ T) (G' : MtP W Ch sel mu P σ) : ∃ F' ∈ T, ∀ b d, F'.1 b d = G'.1 (toRow sel mu d.1.1) := by
    have hG' : G' ∈ Submodule.span ℂ (Set.range fun z : MtildeL W Ch sel mu P => toMtP W Ch sel mu P σ z.1) := by
      rw [span_toMtP W Ch sel mu P σ hX]; exact Submodule.mem_top
    induction hG' using Submodule.span_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact ⟨_, hT z.1 z.2, fun _ _ => rfl⟩
    | zero => exact ⟨0, zero_mem _, fun _ _ => rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ea⟩ := hx; obtain ⟨b, hb, eb⟩ := hy
      exact ⟨a + b, add_mem ha hb, fun c d => congrArg₂ (· + ·) (ea c d) (eb c d)⟩
    | smul r x _ hx =>
      obtain ⟨a, ha, ea⟩ := hx
      exact ⟨r • a, Submodule.smul_mem _ _ ha, fun c d => congrArg (r • ·) (ea c d)⟩

theorem eq_top_of_rowEmb_mem (hX : X.Ok) (T : Submodule ℂ ((perOn W Ch sel mu P b0 til ext tz (fun _ => ⊤)).Mt X.emb σ))
  (hT : ∀ z ∈ MtildeL W Ch sel mu P, rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ z ∈ T) : T = ⊤ :=
  Submodule.eq_top_iff'.2 fun F => (exists_form_of_mt W Ch sel mu P b0 til ext tz hd σ F).elim fun G e =>
    (exists_mem_of_form W Ch sel mu P b0 til ext tz hd σ hX T hT G).elim fun F' h =>
      (congrArg (· ∈ T) (Subtype.ext (funext fun b => funext fun p => (h.2 b p).trans (e b p).symm) : F' = F)).mp h.1
end G

end GlobalTheory.PerQ.RowIntModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FivePointLawsTrueChainsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fivePointLaws_trueChains :
    ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn →
    ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι),
      ∃ Bd : Built.Dat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u,
        Bd.ch = tw (I.tw l l0 Z) u a ∧
        (∀ i, i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m →
          letI : NumberField Bd.E := Bd.nE
          Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧
        (∀ i, i < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m →
          ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧
        Bd = dat I l Z u a := by
  exact GlobalTheory.LvT.Built.TrueLaws.laws_true_fam
end

