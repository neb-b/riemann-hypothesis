module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProductLevelDefiniteFormsRealisationAtTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevProd

open GlobalTheory.MtInProd
open Formalism.L2.NX (locM InLevG InParah inParah_one)
open Classical

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eA (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    s.proj (eA L v) = if s.v = v then 1 else 0 := by
  show s.i 1 * (idemF (L := L) v) s.v = _
  rw [map_one, one_mul, idemF_apply]

theorem locM_cut (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n) :
    locM s (cutGA (eA_mul v) (conj_eA v) κ) = if s.v = v then locM s κ else 1 := by
  show ((cutGA (eA_mul v) (conj_eA v) κ).1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj = _
  rw [cutGA_val, map_cutMat, proj_eA]
  split_ifs
  · rw [cutMat_one_left]; rfl
  · rw [cutMat_zero_left]

theorem inLevG_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) :
    InLevG v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) := by
  refine ⟨inParah_one v r, fun a b _ _ => ⟨fun hba => ?_, fun hab => ?_⟩⟩
  · have h : a ≠ b := fun e => by subst e; exact lt_irrefl _ hba
    rw [Matrix.one_apply_ne h, map_zero]
    exact WithZero.zero_lt_coe _
  · subst hab
    rw [Matrix.one_apply_eq, sub_self, map_zero]
    exact WithZero.zero_lt_coe _

end Gen

theorem main : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  intro D X i b k Q ψ hA j κ hκ v
  obtain ⟨hU, hG, hQ, hD⟩ := ((cell X b hA j).J_mem κ).1 hκ
  refine ⟨cutGA (eA_mul v) (conj_eA v) κ, ((cell X b hA j).J_mem _).2 ⟨cutGA_mem_Umax _ _ (eA_mem v) hU, fun kv => ?_,
    fun P hP => ?_, fun P hP => ?_⟩, triv_cut_eA v κ, cut_eA_at v κ⟩
  · rw [locM_cut]; split_ifs
    · exact hG kv
    · exact inLevG_one _ _
  · rw [locM_cut]; split_ifs
    · exact hQ P hP
    · exact inParah_one _ _
  · rw [locM_cut]; split_ifs
    · exact hD P hP
    · exact inParah_one _ _

end GlobalTheory.LevProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyFinitenessGlobal
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open IsDedekindDomain NumberField

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem heckeFin : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite :=
  GlobalTheory.LevelChars.heckeFin_of _root_.GlobalTheory.LevelChars.LevTriv.levSub_triv _root_.GlobalTheory.LevelChars.rayClass_finite

namespace KeyFiniteness

theorem levelLe_one_two {L : Type} [Field L] [NumberField L] {χ : Formalism.L2.Host.HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (h : χ.LevelLe v 1) : χ.LevelLe v 2 := fun x hx hle =>
  h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))

def Sv (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {PP | (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v ∨ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ GlobalTheory.ChiGrid.S1 D}

def CS (D : D7) (c : ℝ) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Fin D.R.m) : Set (Formalism.L2.Host.HChar D.host.E) :=
  {χ | χ.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * GlobalTheory.ChiGrid.cen D c τ (a.1 + 1)) ∧
      (∀ PP, PP ∉ Sv D v → χ.UnrAt PP) ∧ ∀ PP ∈ Sv D v, χ.LevelLe PP 2}

def Q0 (D : D7) : Set (HeightOneSpectrum (𝓞 D.host.F)) := {v | ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

def KS (D : D7) (c : ℝ) : Set (HeightOneSpectrum (𝓞 D.host.F) × HeightOneSpectrum (𝓞 D.host.E) × (Fin D.R.m → Formalism.L2.Host.HChar D.host.E)) :=
  ⋃ v ∈ Q0 D, {v} ×ˢ ({w | w.under (𝓞 D.host.F) = v} ×ˢ Set.pi Set.univ (CS D c v))

theorem KS_finite (D : D7) (c : ℝ) : (KS D c).Finite := by
  classical
  have hQ0 : (Q0 D).Finite := by
    refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F)).finite_toSet.subset fun v hv => ?_
    exact Formalism.L2.DIV.mem_primesOf.2 ⟨Nat.cast_ne_zero.2 (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero, hv⟩
  have hSv : ∀ v, (Sv D v).Finite := fun v => by
    refine ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).union
      ((GlobalTheory.ChiGrid.S1 D).finite_toSet.biUnion fun u _ => Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F u)).subset ?_
    rintro PP (h | h)
    · exact Or.inl h
    · exact Or.inr (Set.mem_biUnion (Finset.mem_coe.2 h) rfl)
  exact hQ0.biUnion fun v _ => (Set.finite_singleton v).prod
    ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).prod
      (Set.Finite.pi fun a => heckeFin _ _ _ _ _ 2 (hSv v)))

theorem mem_KS {X : Stages} {T : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {sc : GlobalTheory.ChiGrid.Consts}
    (G : GlobalTheory.ChiGrid.GridData L sc) : gkeyOf G ∈ KS X.toD7 sc.cGap := by
  refine Set.mem_biUnion (x := G.pl.v0) G.pl.basePlace_over_qZero ⟨rfl, G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), fun a _ => ?_⟩
  have h1 : 1 ≤ a.1 + 1 := by omega
  have h2 : a.1 + 1 ≤ X.toD7.R.m := a.2
  refine ⟨G.ch.inf _ h1 h2, fun PP hPP => G.ch.unr _ h1 h2 PP fun h => hPP ?_, fun PP hPP => ?_⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases hPP with h | h
    · exact levelLe_one_two (G.ch.lev0 _ h1 h2 PP h).1
    · exact (G.ch.lev1 _ h1 h2 PP h).1

theorem KS_transfer (X X₀ : Stages) (h : X.B.toPre = X₀.B.toPre) (c : ℝ) :
    ∀ κ ∈ KS X.toD7 c, ∃ κ' ∈ KS X₀.toD7 c, HEq κ κ' := by
  obtain ⟨⟨P1⟩, C1, W1, V1, S1', N1, G1⟩ := X
  obtain ⟨⟨P0⟩, C0, W0, V0, S0, N0, G0⟩ := X₀
  change P1 = P0 at h
  subst h
  exact fun κ hκ => ⟨κ, hκ, HEq.rfl⟩

end KeyFiniteness

open KeyFiniteness in
theorem gKeyFin : GKeyFin := by
  intro P c
  by_cases hP : ∃ X : Stages, X.B.toPre = P
  swap
  · exact ⟨∅, Set.finite_empty, fun X _ _ _ _ h _ => (hP ⟨X, h⟩).elim⟩
  obtain ⟨X₀, rfl⟩ := hP
  refine ⟨KS X₀.toD7 c, KS_finite _ _, ?_⟩
  rintro X T L sc G hX rfl
  exact KS_transfer X X₀ hX _ _ (mem_KS G)

end GlobalTheory.Mem.LiteralAutomorphy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimeLtScaleBound
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.AtSize

theorem leastSplitAuxiliaryPrime_lt_scaleBound {K : Ctx} {X : Stages} (hO : K.Over X.B.toPre) {C5 c6 Cb : ℝ} (hG : K.Good C5 c6 Cb) :
    ((GlobalTheory.ChiGrid.q0 X.toD7 : ℕ) : ℝ) < K.s.X' := by
  have hOk := hG.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  have hmem := hOk.small.1
  rcases hOk.lev _ hmem with ⟨i, hi⟩ | hlt
  · exact absurd hi (hOk.small.2.2.2.1 i)
  · exact hlt


end GlobalTheory.Mem.AtSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelByPlacesParahoricAtConductorPlaceTameCharac
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevParaLoc

theorem locM_eq_one_of_ne {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s s' : SplitPlace L)
    {κ : GAf L n} (hκ : TrivOutside {s.v} κ) (h : s'.v ≠ s.v) : NX.locM s' κ = 1 :=
  GlobalTheory.LevGChar.locM_triv s' (B := {s.v}ᶜ) (by rwa [compl_compl]) (by simpa using h)

theorem intLift_one {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 1 = 1 := by
  unfold NX.intLift
  rw [dite_eq_left (v.adicCompletionIntegers (maximalRealSubfield L)).one_mem]
  rfl

theorem intLift_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 0 = 0 := by
  unfold NX.intLift
  rw [dite_eq_left (v.adicCompletionIntegers (maximalRealSubfield L)).zero_mem]
  rfl

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem redMat_one {L : Type} [Field L] [NumberField L] [IsCMField L] {r : ℕ}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {R : Type} [CommRing R]
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) :
    NX.redMat v red (1 : Matrix (Fin r) (Fin r) (v.adicCompletion (maximalRealSubfield L))) = 1 := by
  refine Matrix.ext fun a b => ?_
  show red (NX.intLift v ((1 : Matrix (Fin r) (Fin r) _) a b)) = (1 : Matrix (Fin r) (Fin r) R) a b
  by_cases hab : a = b
  · subst hab; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, intLift_one, map_one]
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, intLift_zero, map_zero]

open Classical in
theorem gVal_one (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) :
    NX.gVal D i k b kv s red τ 1 = 1 := by
  have htop : NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV)
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) = 1 :=
    Matrix.submatrix_one _ (Fin.castLE_injective _)
  have hgl : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.ext (NX.glOf_val _ (by simp))
  have hpsi : NX.psiUTot D i b 1 = 1 := by
    unfold NX.psiUTot
    rw [dite_eq_left (one_mem _)]
    have e : (⟨1, one_mem _⟩ : D.nexp.U) = 1 := rfl
    rw [e, map_one, Units.val_one]
  have hd : red (NX.intLift s.v (NX.detT D.R.r
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))))) = 1 := by
    rw [GlobalTheory.LevGChar.detT_one', intLift_one, map_one]
  unfold NX.gVal
  rw [htop, redMat_one, hgl, Pi.mulSingle_one, hpsi, map_one, one_mul]
  split_ifs with h
  · have hu : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)
    rw [hu, map_one, Units.val_one, map_one]
  · exact absurd (hd ▸ isUnit_one) h

theorem resRep_one {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    NX.resRep s s.w 1 - 1 ∈ s.w.asIdeal := by
  have hu := GlobalTheory.LevGChar.i_resRep s 1 (map_one _)
  show Valued.v (s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L)) < 1
  have e : s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L) = s.i ((NX.resRep s s.w 1 : 𝓞 L) : L) - 1 := by
    push_cast; rw [map_sub, map_one]
  rw [e]
  exact hu

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem mem_iff (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (P : PlE D.host)
    (hP : P ∈ M.QP ∨ P ∈ M.DP) (hG : ∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v)
    (hQ : ∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (hD : ∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (κ : GAf D.host.E D.R.nV) (hκ : TrivOutside {(M.sp P).v} κ) :
    κ ∈ M.J ↔ NG.ParaRT (M.sp P) D.R.r ((M.sp P).loc _ κ) := by
  have hpar : ((∀ P'' ∈ M.QP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ)) ∧
      (∀ P'' ∈ M.DP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ))) ↔
      NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) := by
    constructor
    · rintro ⟨h1, h2⟩
      rcases hP with h | h
      exacts [h1 P h, h2 P h]
    · intro h
      refine ⟨fun P'' hP'' => ?_, fun P'' hP'' => ?_⟩
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hQ P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hD P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
  have hg : ∀ kv, NX.InLevG (M.sp (NX.pG D kv)).v D.R.r (NX.locM (M.sp (NX.pG D kv)) κ) := fun kv => by
    rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact NX.inLevG_one _ _
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, -, h1, h2⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, (hpar.1 ⟨h1, h2⟩).2⟩
  · rintro ⟨hGL, hll⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, hg,
      hpar.2 ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩⟩

theorem levelPara_loc : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (ek : NX.Kk D i k →+* ℂ) (P : PlE D.host) (ξ : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (P ∈ M.QP ∨ P ∈ M.DP) → ¬ (P ∈ M.QP ∧ P ∈ M.DP) → (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v) → (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.QP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' e₀ u = 1) → (∀ P'' ∈ M.DP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀) u = 1) → (P ∈ M.QP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ P e₀ a).1)) → (P ∈ M.DP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e₀ else -e₀) a).1)) → NG.LevelPara M.J (cx ek M.χ) (M.sp P) D.R.r ξ := by
  intro D i j b k Q ψ e₀ W₀ _ _ ρ₀ τ M ek P ξ hP hPn hG hQ hD hψ hδ hξQ hξD
  refine ⟨fun κ hκ => mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ, ?_⟩
  intro κ h hκ u hu
  have hpara := (mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ).1 h
  have hUm : κ ∈ Umax D.host.E D.R.nV := ((M.J_mem κ).1 h).1
  have hx : NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) :=
    ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hpara.1).1 a b, hpara.2⟩
  have hv1 : Valued.v (NX.detT D.R.r (NX.locM (M.sp P) κ)) = 1 :=
    GlobalTheory.LevGChar.i_detT_one _ D.R.r _ (NX.locM (M.sp P) κ⁻¹)
      (by rw [← GlobalTheory.LevGChar.locM_mul, mul_inv_cancel, GlobalTheory.LevGChar.locM_one])
      (fun a b => GlobalTheory.LevGChar.locM_int _ (inv_mem hUm) a b) hx
  have hu' : (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) =
      NX.detT D.R.r (NX.locM (M.sp P) κ) := hu
  have hw : (M.sp P).w = P := M.sp_w P (by rcases hP with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  have hclose : Valued.v ((u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) -
      (M.sp P).i ((NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)) : 𝓞 D.host.E) : D.host.E)) < 1 := by
    have := GlobalTheory.LevGChar.i_resRep (M.sp P) _ hv1
    rw [hw] at this
    rw [hu', ← Valuation.map_neg, neg_sub]
    exact this
  have hnm := GlobalTheory.LevGChar.resRep_not_mem (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ))
  have hvu : Valued.v (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by rw [hu']; exact hv1
  have hGp : ∏ kv, NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (NX.locM (M.sp (NX.pG D kv)) κ) = 1 :=
    Finset.prod_eq_one fun kv _ => by rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact gVal_one _ _ _ _ _ _ _ _
  have offQ : ∀ P'' ∈ M.QP, P'' ≠ P → NX.ofOk D i k (NX.tameVal ψ P'' e₀
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hQ P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inl hP'')
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hψ P'' hP'' _ h1, Units.val_one, map_one]
  have offD : ∀ P'' ∈ M.DP, P'' ≠ P → NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀)
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hD P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inr (Or.inl hP''))
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hδ P'' hP'' _ h1, Units.val_one, map_one]
  apply Units.ext
  rw [cx_apply, M.chi_eq κ h, hGp, one_mul]
  rcases hP with hPQ | hPD
  · have hPD : P ∉ M.DP := fun h' => hPn ⟨hPQ, h'⟩
    rw [Finset.prod_eq_single_of_mem P hPQ offQ,
      Finset.prod_eq_one (fun P'' hP'' => offD P'' hP'' (fun e => hPD (e ▸ hP''))), mul_one]
    exact (hξQ hPQ u _ hnm hvu hclose).symm
  · have hPQ : P ∉ M.QP := fun h' => hPn ⟨h', hPD⟩
    rw [Finset.prod_eq_single_of_mem P hPD offD,
      Finset.prod_eq_one (fun P'' hP'' => offQ P'' hP'' (fun e => hPQ (e ▸ hP''))), one_mul]
    exact (hξD hPD u _ hnm hvu hclose).symm

end GlobalTheory.LevParaLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDatumCharactersNeOneAtFixedElementResidu
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.HeightCounting

theorem theta_xiRed_ne_one : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ), SideB D cf Rw low Pq S hL eig θ →
    2 ≤ D.R.r → D.ntw.Tw → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) ≠ 1 := by
  classical
  intro D cf Rw low Pq S hL eig θ Bs hr i kv h1
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨θ', hθ', hψ⟩ := Bs.exp.psiU_gen i true
  have hu : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ D.nexp.U := by
    rw [Bs.exp.U_eq]; exact Formalism.L2.NX.tvAt_mem hr _
  have hu' : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ Formalism.IndefR.NX.U D.nd :=
    Formalism.L2.NX.tvAt_mem hr _
  have e := Bs.psiU i true _ hu hu'
  have e2 : psiUOf D.nd (NX.xiRed D) θ ⟨_, hu'⟩ = θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) :=
    psiXi_tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) (NX.xiRed D) (fun kv => θ kv.1) hr kv
  have e3 : D.nexp.psiU i true ⟨_, hu⟩ = θ' kv (Multiplicative.ofAdd 1) :=
    (hψ ⟨_, hu⟩).trans (Formalism.L2.NX.stdVal_tvAt θ' hr kv)
  rw [e2, h1, e3] at e
  refine Formalism.L2.NX.char_one_ne (θ' kv) (hθ' hr kv) (Units.ext (e.trans ?_))
  exact map_one (readLL0 S i true)

end GlobalTheory.HeightCounting
end

