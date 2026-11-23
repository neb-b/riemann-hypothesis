module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceM
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.Bundle0036
public import Formalism.LocalToGlobal.Columns.Bundle0037
public import Formalism.LocalToGlobal.Columns.ChainTopLawB
public import Formalism.LocalToGlobal.Columns.Bundle0039
public import Formalism.LocalToGlobal.Columns.ChainTopLawTw
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
public import GroundTheory.LocalFields.MainTheorem
public import GroundTheory.GlobalFields.CompletionAtPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsDescend
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JumpsDescend

theorem jumps_descend : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime], ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (O' : Type) [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → Bw'.j = Bw.j → ∀ (τ : K →+* Qbar l) (τL : L →+* Qbar l), τL.comp (algebraMap K L) = τ → ∀ J : Multiset ℤ, IsJumpsAt P Bw' ((resTo L r).comp (Dec (F := L) A).subtype) τL J → IsJumpsAt P Bw (r.comp (Dec (F := K) A).subtype) τ J := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' _ _ l _ P AI hT a r hr O _ _ _ Bw O' _ _ _ Bw' hj hj' hjj τ τL hτL J hJ
  obtain ⟨T⟩ := hT

  have hle : Bw.Kw.1 ≤ Bw'.Kw.1 := by
    rw [BridgeInd.kw_eq_adjoin Bw, BridgeInd.kw_eq_adjoin Bw', IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨algebraMap K L x, ?_⟩
    show Bw'.j (algebraMap L Ω (algebraMap K L x)) = Bw.j (algebraMap K Ω x)
    rw [hjj, ← IsScalarTower.algebraMap_apply]
  have hJ0 := hJ
  obtain ⟨LL', r', hmod', hdR', τ₁, hi₁, -⟩ := hJ
  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  obtain ⟨L₁, hL₁, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G K Ω) a r hcont (supExt Bw.LL LL')
  have hBL : Bw.LL.1 ≤ L₁.1 := (le_sup_left : Bw.LL.1 ≤ (supExt Bw.LL LL').1).trans hL₁
  have hLL : LL'.1 ≤ L₁.1 := (le_sup_right : LL'.1 ≤ (supExt Bw.LL LL').1).trans hL₁
  obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont L₁ hmem
  set rE : ↥(Dec (F := K) A) →* GL (Fin a) ↥L₁.1 := r₁.comp (Dec (F := K) A).subtype with hrE
  have hmodE : IsModel Bw (r.comp (Dec (F := K) A).subtype) L₁ rE := by
    refine ⟨hBL, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) => ((f (g : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmodM : IsModel Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) L₁ (rE.comp (GlobalTheory.AboveLRes.decRes A)) := by
    refine ⟨hmod'.1.trans hLL, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) => ((f ((GlobalTheory.AboveLRes.decRes (K := K) A g : ↥(Dec (F := K) A)) : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hrep := GlobalTheory.AboveLRes.repE_decRes Bw Bw' hjj hle L₁ rE
  have hdM : Bw'.IsdRE P L₁ (rE.comp (GlobalTheory.AboveLRes.decRes A)) := (hmodM.isdRAt_iff P).1 ⟨LL', r', hmod', hdR'⟩
  have hdR2 : IsDR (P.PD Bw'.Kw) (GlobalTheory.Pst.resTo (Bw.repE L₁ rE) hle) := by
    unfold IsDR
    rw [← hrep, Module.finrank_fin_fun]
    exact hdM
  have hdR : IsDR (P.PD Bw.Kw) (Bw.repE L₁ rE) := (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hle (Bw.repE L₁ rE) T).2 hdR2
  have hdE : Bw.IsdRE P L₁ rE := by
    have := hdR
    unfold IsDR at this
    rw [Module.finrank_fin_fun] at this
    exact this

  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1 := (IntermediateField.inclusion hLL).comp τ₁
  have hiM : IsInduced Bw' τL τ'' := fun x => hi₁ x
  let τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1 := τ''.comp (IntermediateField.inclusion hle)
  have hτ₂ : IsInduced Bw τ τ₂ := by
    intro x
    have e1 : (IntermediateField.inclusion hle ⟨Bw.j (algebraMap K Ω x), Bw.j_E x⟩ : ↥Bw'.Kw.1) =
        ⟨Bw'.j (algebraMap L Ω (algebraMap K L x)), Bw'.j_E (algebraMap K L x)⟩ := by
      apply Subtype.ext
      show Bw.j (algebraMap K Ω x) = Bw'.j (algebraMap L Ω (algebraMap K L x))
      rw [hjj, ← IsScalarTower.algebraMap_apply]
    show τ x = ((τ'' (IntermediateField.inclusion hle ⟨Bw.j (algebraMap K Ω x), Bw.j_E x⟩) : ↥L₁.1) : Om l)
    rw [e1, ← hτL]
    exact hiM (algebraMap K L x)
  refine ⟨L₁, rE, hmodE, hdE, τ₂, hτ₂, fun n => ?_⟩
  rw [IsJumpsAt.count_eq P hmodM hiM hJ0 n]
  unfold LocBridge.multE
  rw [hrep]
  exact GlobalTheory.JumpRestrict.multV_restrict l P AI T Bw.Kw Bw'.Kw L₁ hle (Fin a → ↥L₁.1) (Bw.repE L₁ rE) hdR τ'' n

end GlobalTheory.JumpsDescend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastColumnStepDatumEqTwistTopDatum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem xiOver_eq_XiTopG {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))
    (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u j) :
    xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTopG Ch sel mu cst (n + 1) j (R.N j) p Y p' := by
  subst h
  rfl

theorem xiOver_eq_XiTop : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (n : ℕ) (h : n + 1 + 1 = R.m) (p : ChPt (R := R) sel mu u (n + 1)) (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u (n + 1 + 1)), xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTop Ch sel mu cst (n + 1) p Y p' := by
  intro X Pr R Ch sel S mu cst u n h p Y p'
  exact xiOver_eq_XiTopG Ch sel mu cst n h p Y p'

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceMStatement
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twTt_k1Depth_twice_m : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ} (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)) (hc' : κ'⁻¹ ∈ (twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H) (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ : Sp X.E (R.N (m2 + 1))), R.m = m2 + 2 → cst.Ok → ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → 2 * cst.M ≤ cst.D w → 2 * cst.M ≤ twTopDepth R → ((qOf w.1 : X.E) ^ cst.M) • y₁ ∈ stdAt X.E (R.N (m2 + 1)) w.1 → rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) * topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y) y₁ = (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam ⟨κ'⁻¹, hc'⟩ : X.Kˣ) : X.K) * topDat Ch sel mu cst (m2 + 1) w y y₁ := by
  first | exact @GlobalTheory.lastStepDatumLaw_K1Depth_twiceM | exact GlobalTheory.lastStepDatumLaw_K1Depth_twiceM | (intros; apply GlobalTheory.lastStepDatumLaw_K1Depth_twiceM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.TopInt

open GlobalTheory.PhiRootVal (RootOrZero phiGS_root phiG_root phiQ_root)
open GlobalTheory.CplTwoInt (intOff_prod ftY_intOff smul_symm_mem repY_mem)

theorem phiTopG_root {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (sharp : Bool) (i j n : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiTopG (R := R) Ch mu sharp i j n P x) := by
  unfold PhiTopG
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

theorem xiTop_intOff (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts)
    (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (u) (μ)
    (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (Yb : Set (Sp t.X.E (D.R.N i)))
    (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1)) (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1)))
    (hY : Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N) :
    IntOff (t.O u μ).S (t.seam.σ₀ (XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p Yb p' x)) := by
  have hok := t.idx_ok μ
  unfold XiTop XiTopG
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul ((phiTopG_root _ _ _ _ _ _ _ _).intOff _ _) ?_
    exact ftY_intOff t.sel (t.tup μ) (t.cst μ) hok.cst_ok P (hok.depthG P) (hok.depthQ P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _
      (smul_symm_mem (GlobalTheory.ColPeriod.isFrames_frsF p P) _ (repY_mem t.sel (t.tup μ) (t.cst μ) hY P))

theorem topInt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt := by
  intro D L hT Gi Gl K Y cX ex t hTop u μ c c' _ x
  obtain ⟨-, -, pt, ix, yb, pT, -, hyb, -, -, hpin, -, -⟩ := hTop u μ
  rw [hpin.2 c c' x]
  exact xiTop_intOff D L hT Gi Gl K Y cX ex t u μ _ _ _ _ _ (hyb c)

end GlobalTheory.TopInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompat
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.Global.AdicLiesOver

namespace GlobalTheory.ArtinNormU

theorem localArtin_normU : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') [v'.asIdeal.LiesOver v.asIdeal] (a : Weil h →* (v.adicCompletion K)ˣ) (a' : Weil h' →* (v'.adicCompletion L)ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ (g : Weil h) (g' : Weil h'), (∀ z : Ω, (g : G K Ω) z = (g' : G L Ω) z) → a g = GlobalTheory.BCChar.normU v v' (a' g') := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' _ a a' ha ha' g g' hgg
  classical
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero (v'.adicCompletion L) :=
    charZero_of_injective_algebraMap (algebraMap L (v'.adicCompletion L)).injective
  haveI : IsSepClosure (v'.adicCompletion L) (Kbar v') := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.IsSeparable (v.adicCompletion K) (v'.adicCompletion L) := inferInstance
  haveI : IsSepClosure (v.adicCompletion K) (Kbar v') :=
    isSepClosure_of_isSeparable (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (v'.adicCompletion L) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (Kbar v') :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : IsAlgClosure (v.adicCompletion K) (Kbar v') := ⟨inferInstance, inferInstance⟩
  obtain ⟨ι', hι'⟩ := GlobalTheory.LocDict.exists_isLocEmb L Ω A v' h'
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc L Ω A v' h' ι' hι'
  let gL : GalLoc v' := θ ⟨g', Weil_le_Dec h' g'.2⟩
  have hgL : Lifts ι' gL (g' : G L Ω) := hθ _
  let gK : Kbar v' ≃ₐ[v.adicCompletion K] Kbar v' := gL.restrictScalars (v.adicCompletion K)
  have hgK : ∀ z : Ω, gK (ι'.toRingHom z) = ι'.toRingHom ((g : G K Ω) z) := fun z => by
    change gL (ι' z) = ι' _
    rw [hgL z, hgg z]
  have hj : ∀ x : K, ι'.toRingHom (algebraMap K Ω x) =
      algebraMap (v.adicCompletion K) (Kbar v') (algebraMap K (v.adicCompletion K) x) := fun x => by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    change ι' (algebraMap L Ω _) = _
    rw [ι'.commutes, IsScalarTower.algebraMap_apply (v.adicCompletion K) (v'.adicCompletion L) (Kbar v'),
      GroundTheory.Global.AdicLiesOver.algebraMap_eq, GroundTheory.Global.adicCompletionMap_algebraMap,
      ← IsScalarTower.algebraMap_apply L (v'.adicCompletion L) (Kbar v')]
  let b : Kbar v ≃ₐ[v.adicCompletion K] Kbar v' := IsAlgClosure.equiv (v.adicCompletion K) (Kbar v) (Kbar v')
  have hb : ∀ x, (b : Kbar v ≃+* Kbar v') (algebraMap _ (Kbar v) x) =
      algebraMap (v'.adicCompletion L) (Kbar v') (GroundTheory.Global.adicCompletionMap v v' x) := fun x => by
    change b _ = _
    rw [b.commutes, IsScalarTower.algebraMap_apply (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')]
    rfl
  have hc : (algebraMap (v.adicCompletion K) (Kbar v')).comp
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      (b : Kbar v →+* Kbar v').comp (algebraMap (v.adicCompletionIntegers K) (Kbar v)) := RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v)]
    exact (b.commutes _).symm
  have hA : ∀ z : Ω, z ∈ A ↔ ((algebraMap (v.adicCompletion K) (Kbar v')).comp
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).IsIntegralElem (ι'.toRingHom z) := fun z => by
    have e := GlobalTheory.ClosureIso.isIntegral_map_iff (GroundTheory.Global.adicCompletionMap v v')
      (GroundTheory.Global.continuous_adicCompletionMap v v') (b : Kbar v ≃+* Kbar v') hb (b.symm (ι' z))
    have e2 : (b : Kbar v ≃+* Kbar v') (b.symm (ι' z)) = ι' z := b.apply_symm_apply _
    rw [e2] at e
    rw [hι' z, e, hc]
    change _ ↔ ((b : Kbar v →+* Kbar v').comp (algebraMap (v.adicCompletionIntegers K) (Kbar v))).IsIntegralElem (ι' z)
    constructor
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, ?_⟩
      have := congrArg (b : Kbar v →+* Kbar v') hp'
      rw [Polynomial.hom_eval₂, map_zero] at this
      rwa [show (b : Kbar v →+* Kbar v') (b.symm (ι' z)) = ι' z from b.apply_symm_apply _] at this
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, (b : Kbar v →+* Kbar v').injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, show (b : Kbar v →+* Kbar v') (b.symm (ι' z)) = ι' z from b.apply_symm_apply _]
      exact hp'
  have restrict_local : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
      [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
      (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
      ∀ [IsSepClosure (w.adicCompletion E) (Kbar w)] (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
        AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w)) g =
          (localArtinMap (w.adicCompletion E) (Kbar w) (a σ))⁻¹ := by
    intro E Ω _ _ _ _ _ A w h ι hι a ha _ σ g hg
    have hN := GlobalTheory.LocNormGrp.hasNormGroups_of_isLocalArtin GlobalTheory.globalArtinReciprocity_holds
      GlobalTheory.Published.chevalleyUnits' E Ω A w h ι a hι ha
    obtain ⟨θ, -, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
    let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
    have hψ : ∀ τ : Weil h, Lifts ι (ψ τ) τ := fun τ => hl ⟨τ, Weil_le_Dec h τ.2⟩
    have e2 : ψ σ = g := by
      have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) σ := by
        have := hl (θ.symm g)
        rw [θ.apply_symm_apply] at this
        exact Subtype.ext (this.eq hg)
      show θ _ = g
      rw [← e, θ.apply_symm_apply]
    let r := (AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w))).comp ψ
    have hr : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w)) [Normal (w.adicCompletion E) L]
        (hL : L ≤ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
        restrictAb L hL (r τ) = AlgEquiv.restrictNormalHom L (ψ τ) := fun τ L _ hL =>
      restrictAb_topologicalAbelianizationEquiv L hL (ψ τ)
    have hnorm : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w))
        [FiniteDimensional (w.adicCompletion E) L] [IsAbelianGalois (w.adicCompletion E) L],
        a τ ∈ (normUnits (w.adicCompletion E) L).range →
          restrictAb L (le_maximalAbelianExtension L) (r τ) = 1 := fun τ L _ hL hx => by
      have := (hN L ⟨inferInstance, inferInstance, hL.is_comm.comm⟩ τ _ (hψ τ)).2 hx
      rw [hr, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
      exact this
    let a' : Weil h →* (w.adicCompletion E)ˣ := invMonoidHom.comp a
    have ha' : Function.Surjective a' := inv_surjective.comp ha.surj
    have hker : a'.ker ≤ r.ker := fun τ hτ => by
      have h1 : a τ = 1 := inv_eq_one.1 (MonoidHom.mem_ker.1 hτ)
      refine MonoidHom.mem_ker.2 (ext_restrictAb fun L _ _ => ?_)
      rw [map_one]
      exact hnorm τ L (h1 ▸ Subgroup.one_mem _)
    let b := a'.liftOfSurjective ha' ⟨r, hker⟩
    have hb : ∀ τ, b (a τ)⁻¹ = r τ := fun τ =>
      MonoidHom.liftOfRightInverse_comp_apply a' _ (Function.rightInverse_surjInv ha') ⟨r, hker⟩ τ
    have hbφ : b = localArtinMap (w.adicCompletion E) (Kbar w) := by
      refine eq_localArtinMap_of (fun π hπ => ?_) (fun L _ _ x hx => ?_)
      · obtain ⟨τ, rfl⟩ := ha' π
        have h1 : GlobalTheory.SmGL.ord (w.adicCompletion E) (a τ⁻¹) = 1 := by rw [map_inv]; exact hπ
        rw [ha.ord_eq, deg_inv, neg_neg] at h1
        have hF := (GlobalTheory.WeilDict.isFrob_iff_of_lifts h (Weil_le_Dec h τ.2) (hψ τ)).1 (deg_eq_one_iff.1 h1)
        change restrictAb _ _ (b (a τ)⁻¹) = _
        rw [hb, hr]
        refine (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (ψ τ)).2 ?_
        rw [unramifiedDegree_eq_ofAdd_one_iff]
        rintro ξ ⟨n, hn, hξ⟩
        have hq : Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation (w.adicCompletion E)).integer) = normV w := resCard_eq_normV w
        rw [hq] at hξ ⊢
        refine hF ξ n (Nat.pos_of_ne_zero hn) ?_
        have h2 : normV w ^ n = normV w ^ n - 1 + 1 :=
          (Nat.sub_add_cancel (Nat.one_le_pow _ _ (zero_lt_one.trans (one_lt_normV w)))).symm
        rw [h2, pow_succ, hξ, one_mul]
      · obtain ⟨τ, rfl⟩ := ha' x
        change restrictAb _ _ (b (a τ)⁻¹) = _
        rw [hb]
        exact hnorm τ L (Subgroup.inv_mem_iff _ |>.1 hx)
    rw [← map_inv, ← hbφ, hb, ← e2]
    rfl
  
  have HK : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK =
      (localArtinMap (v.adicCompletion K) (Kbar v') (a g))⁻¹ := by
    have : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    have : IsSepClosure (v.adicCompletion K) (Kbar v) := ⟨inferInstance, inferInstance⟩
    let ε : (Kbar v') ≃ₐ[v.adicCompletion K] Kbar v := IsSepClosure.equiv (v.adicCompletion K) (Kbar v') (Kbar v)
    let ι : Ω →ₐ[K] Kbar v :=
      { (ε : (Kbar v') →+* Kbar v).comp ι'.toRingHom with
        commutes' := fun x => by
          change ε (ι'.toRingHom (algebraMap K Ω x)) = _
          rw [hj, ε.commutes, IsScalarTower.algebraMap_apply K (v.adicCompletion K) (Kbar v)] }
    have hιz : ∀ z, ι z = ε (ι'.toRingHom z) := fun _ => rfl
    have hc : (ε : (Kbar v') →+* Kbar v).comp ((algebraMap (v.adicCompletion K) (Kbar v')).comp
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))) =
        algebraMap (v.adicCompletionIntegers K) (Kbar v) := RingHom.ext fun x => by
      rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v)]
      exact ε.commutes _
    have hι : IsLocEmb A v ι := fun z => by
      rw [hA, hιz]
      constructor
      · rintro ⟨p, hp, hp'⟩
        refine ⟨p, hp, ?_⟩
        rw [← hc]
        have := congrArg (ε : (Kbar v') →+* Kbar v) hp'
        rwa [Polynomial.hom_eval₂, map_zero] at this
      · rintro ⟨p, hp, hp'⟩
        refine ⟨p, hp, (ε : (Kbar v') →+* Kbar v).injective ?_⟩
        rw [Polynomial.hom_eval₂, map_zero, hc]
        exact hp'
    let gK' : GalLoc v := ε.symm.trans (gK.trans ε)
    have hg' : Lifts ι gK' g := fun z => by
      change ε (gK (ε.symm (ε (ι'.toRingHom z)))) = ε (ι'.toRingHom _)
      rw [ε.symm_apply_apply, hgK]
    have H := restrict_local K Ω A v h ι hι a ha g gK' hg'
    have H1 : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK =
        (localArtinMap (v.adicCompletion K) (Kbar v') (a g))⁻¹ := by
      rw [← map_inv] at H ⊢
      ext y
      have h1 := localArtinMap_transport (RingEquiv.refl (v.adicCompletion K)) (fun _ _ => Iff.rfl)
        (ε : (Kbar v') ≃+* Kbar v) (fun x => ε.commutes x) (a g)⁻¹ y.2
      have h2 : Units.map (RingEquiv.refl (v.adicCompletion K)).toRingHom.toMonoidHom (a g)⁻¹ = (a g)⁻¹ :=
        Units.ext rfl
      rw [h2, ← H, AlgEquiv.restrictNormalHom_apply] at h1
      rw [AlgEquiv.restrictNormalHom_apply]
      apply ε.injective
      refine Eq.trans ?_ h1.symm
      change _ = ε (gK (ε.symm (ε y)))
      rw [ε.symm_apply_apply]
    exact H1
  have HL : ∀ (z : Kbar v') (hz : z ∈ maximalAbelianExtension (v'.adicCompletion L) (Kbar v')),
      gL ((localArtinMap (v'.adicCompletion L) (Kbar v') (a' g') ⟨z, hz⟩ :
        maximalAbelianExtension (v'.adicCompletion L) (Kbar v')) : Kbar v') = z := by
    intro z hz
    have H := restrict_local L Ω A v' h' ι' hι' a' ha' g' gL hgL
    have e : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v'.adicCompletion L) (Kbar v')) gL
        (localArtinMap (v'.adicCompletion L) (Kbar v') (a' g') ⟨z, hz⟩) = ⟨z, hz⟩ := by
      rw [H, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have e2 := congrArg (fun y : maximalAbelianExtension (v'.adicCompletion L) (Kbar v') => (y : Kbar v')) e
    simpa only [AlgEquiv.restrictNormalHom_apply] using e2
  have kK : ∀ (y : Kbar v') (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (Kbar v')),
      gK ((localArtinMap (v.adicCompletion K) (Kbar v') (a g) ⟨y, hy⟩ :
        maximalAbelianExtension (v.adicCompletion K) (Kbar v')) : Kbar v') = y := fun y hy => by
    have e : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK
        (localArtinMap (v.adicCompletion K) (Kbar v') (a g) ⟨y, hy⟩) = ⟨y, hy⟩ := by
      rw [HK, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have e2 := congrArg (fun y : maximalAbelianExtension (v.adicCompletion K) (Kbar v') => (y : Kbar v')) e
    simp only [AlgEquiv.restrictNormalHom_apply] at e2
    exact e2
  have key : localArtinMap (v.adicCompletion K) (Kbar v') (a g) =
      localArtinMap (v.adicCompletion K) (Kbar v') (normUnits (v.adicCompletion K) (v'.adicCompletion L) (a' g')) := by
    refine AlgEquiv.ext fun y => Subtype.ext ?_
    have hN := localArtinMap_norm (K := v.adicCompletion K) (K' := v'.adicCompletion L) (Ω := Kbar v') (a' g') y.2
    apply gK.injective
    rw [kK y y.2]
    change (y : Kbar v') = gL _
    rw [← hN, HL]
  exact injective_localArtinMap key

end GlobalTheory.ArtinNormU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.PlainChars

theorem exists_fin_enum {S : Type*} (t : Multiset S) {n : ℕ} (hn : Multiset.card t = n) :
    ∃ ξ : Fin n → S, Finset.univ.val.map ξ = t := by
  subst hn
  refine ⟨fun j => t.toList.get (Fin.cast (by simp) j), ?_⟩
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList t]
  congr 1
  apply List.ext_get (by simp)
  intro i h1 h2
  simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_ofChar (x : IrrGL (k := k)) (hx : x.1 = 1) : ∃ θ hθ, x = IrrGL.ofChar θ hθ := by
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.RoadU.PlainChars

theorem GlobalTheory.RoadU.plainTor_exists_chars : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), PlainTor x → ∃ (ξ : Fin x.1 → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) ∧ Unlinked (chars ξ hξ) := by
  intro k _ _ _ _ _ x ⟨s, hs, h1, hu⟩
  let S := {χ : kˣ →* ℂˣ // IsSmoothChar χ}
  let F : S → IrrGL (k := k) := fun χ => IrrGL.ofChar χ.1 χ.2
  obtain ⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s :=
    haveI : CanLift (IrrGL (k := k)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩
    (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by
      obtain ⟨χ, hχ, e⟩ := PlainChars.exists_eq_ofChar y (h1 y hy)
      exact ⟨⟨χ, hχ⟩, e.symm⟩
  have hcard : Multiset.card t = x.1 := by
    have h2 := hs.sum_fst
    rw [Multiset.map_map] at h2
    have h3 : t.map (Sigma.fst ∘ F) = Multiset.replicate (Multiset.card t) 1 :=
      Multiset.eq_replicate.2 ⟨by simp, fun b hb => by
        obtain ⟨χ, -, rfl⟩ := Multiset.mem_map.1 hb
        rfl⟩
    rw [h3, Multiset.sum_replicate, smul_eq_mul, mul_one, Fintype.card_fin] at h2
    exact h2
  obtain ⟨ξ, hξ⟩ := PlainChars.exists_fin_enum t hcard
  have hc : chars (fun j => (ξ j).1) (fun j => (ξ j).2) = t.map F := by
    rw [← hξ, Multiset.map_map]
    rfl
  exact ⟨fun j => (ξ j).1, fun j => (ξ j).2, hc ▸ hs, hc ▸ hu⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeLevelLastStepSymmetricRowsEqTwistLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory

theorem levGTop_rPsymF_eq_twLt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok → Ch.Ok →
    levGTop Ch (rPsymF Ch) = twLt Ch R.m := by
  intro X Pr R Ch _ _ _
  funext w
  rw [levGTop_PsymF]
  show _ = colLevSym Ch R.m w
  unfold colLevSym
  rw [if_neg (by have := R.two_le_m; omega), dite_eq_right (by omega), dite_eq_right (by omega)]
  rfl

end GlobalTheory
end

