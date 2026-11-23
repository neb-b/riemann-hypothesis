module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
public import Formalism.LocalToGlobal.Columns.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetPowerProductMulMemDelWShiftIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralSpanIffPadicWeylDualLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerNormOneFiniteAdeleDetClassStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_ker_normOneFiniteAdeleDetClass : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))), LevOk H SG SQ → letI := Formalism.BasicNotions.tensTopL (F := H.F) (E := H.E) (Formalism.L2.Herm.Af H.F); IsOpen {x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) | u1Dt H SQ x = 1} := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt | exact GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt | (intros; apply GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem k_pins_of_fields {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hOk : I.Ok) (hP : TC.Pins B X)
    (hX : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hSS : t.S = I.S) (hword : HEq t.word fun u : B.Word => u)
    (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst) (hglob : HEq t.glob I.glob) (hO : I.StdO l Z Y.Qp t.O)
    (hpi : ex.errX.piT = X.piT) : t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  have hU : t.MemSideU := by
    intro u
    refine ⟨?_, ?_, ?_⟩
    · show (t.O u I.mu0).mt = _
      rw [hO.mt u I.mu0, hOk.trueColumnChoices_heckeChar_reference_eq_one, tildeQ_one]
      funext j
      split_ifs
      · exact mul_one _
      · rfl
    · intro i c
      show (t.O u I.mu0).dt i c = _
      rw [hO.dt u I.mu0 i c]
      rfl
    · rw [hpi]
      exact memLatAt_std I hOk hP l Z u (t.memObj u) fun i c => hO.lat u I.mu0 i c
  have hPi : t.PiSide := by
    clear hU hO hglob hcst htup hSS hsel hCh
    cases t
    dsimp only at *
    subst hX
    cases hseam
    cases hPr
    cases hword
    intro u
    rw [hpi]
    rfl
  have hC : t.Ch.Ok ∧ MuValTie t.Ch t.glob ∧ ∀ a, (t.cst a).sharp = true := by
    clear hU hPi
    cases t
    dsimp only at *
    subst hX
    cases hPr
    cases hCh
    cases hsel
    subst hSS
    cases htup
    cases hcst
    cases hglob
    exact ⟨hOk.ch_ok, fun j v h => hOk.ch_tied.muVal j v h, fun a => hOk.sharp a⟩
  have hM : t.MtTwTie := by
    clear hU hPi hC
    cases t
    dsimp only at *
    subst hX
    cases hseam
    subst hSS
    cases htup
    refine ⟨(QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)), ⟨fun y => ?_, fun k z hz => ?_⟩,
      fun μ _ _ => ⟨tildeQ B.host I.SQ (I.xi μ), fun x => ?_, fun u => ?_⟩⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (show DtQ B.host I.SQ from y)
      refine ⟨finAf B.host.F B.host.E a, ?_⟩
      exact mk_eq_of_snd_eq B.host I.SQ (afIso_finAf B.host.F B.host.E a)
    · have hz' : (show B.host.E from z.1) * B.host.conj (k : B.host.E) = k := hz
      show (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) (ratId B.host.F B.host.E k)) : DtQ B.host I.SQ) = e1Q B.host I.SQ z
      rw [← isUnitaryPointsMap_unitaryRationalPointsFiner B.host I.SQ k z hz']
      refine mk_eq_of_snd_eq B.host I.SQ ?_
      show afIso B.host.F B.host.E ((k : B.host.E) ⊗ₜ[B.host.F] 1) = _
      rw [afIso_tmul_one]
      rfl
    · have hk : KDq B.host I.SQ ≤ ((I.xi μ).1.comp (finPartI B.host.E)).ker :=
        (KDq_anti B.host (I.Q_subset_SQ μ)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).2.2 μ).1
      show tildeQ B.host I.SQ (I.xi μ) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      rw [tildeQ_mk B.host I.SQ hk, finPartI_eq_self fun _ => rfl]
      exact Units.ext ((hOk.xi_reads μ).apply _ x rfl)
    · rw [hO.mt u μ]
      rfl
  exact ⟨⟨hC.1, hC.2.1, hPi, fun u _ => hU u⟩, hU, hM, hC.2.2⟩

theorem k_pins_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKerTie l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS hpi
  exact k_pins_of_fields I l Z t hOk hP hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.word hS.tup hS.cst hS.glob hS.O hpi

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open Formalism.HermitianLatticesTheory

theorem topChain : TopChain := by
  classical
  intro D X u C r Pr Ch sel S mu cst L σ v m2 hX hPr hc hm hpi h
  obtain ⟨hSS, hlev, pt, ix, yb, pT, hN, hyb, hE, hC, ⟨hTN, hTX⟩, hpin, hpin'⟩ := h
  have key : ∀ (c' : C.cls (m2 + 1 + 1)) d, OverRow sel mu v d (pT c') →
      HEq (r.N (m2 + 1 + 1) c') (tilQ sel mu v d).1.N ∧ ∀ c, HEq (r.Xi (m2 + 1) c c') fun x => σ (XiCpl2 Ch sel mu cst m2 (pt (m2 + 1) le_rfl c) (yb c) d x) := by
    intro c' d hd
    obtain ⟨p', hp, hrow⟩ := hd
    have gen : ∀ (j : ℕ) (hj : j = m2 + 1 + 1) (q : DecoF X.E (D.R.N j) (Pr.vT v) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))), HEq (pT c') q →
        HEq (pT c').deco.1.N q.deco.1.N ∧ ∀ c, HEq (fun x => σ (XiTop Ch sel mu cst (m2 + 1) (pt (m2 + 1) le_rfl c) (yb c) (pT c') x))
          (fun x => σ (XiTopG Ch sel mu cst (m2 + 1) j (D.R.N j) (pt (m2 + 1) le_rfl c) (yb c) q x)) := by
      intro j hj q hq
      subst hj
      obtain rfl := eq_of_heq hq
      exact ⟨HEq.rfl, fun _ => HEq.rfl⟩
    obtain ⟨g1, g2⟩ := gen D.R.m (by omega) p' hp
    refine ⟨?_, fun c => ?_⟩
    · rw [hTN c']
      refine g1.trans (heq_of_eq ?_)
      rw [hrow.1]
      rfl
    · have e : r.Xi (m2 + 1) c c' = fun x => σ (XiTop Ch sel mu cst (m2 + 1) (pt (m2 + 1) le_rfl c) (yb c) (pT c') x) := funext (hTX c c')
      rw [e]
      refine (g2 c).trans (heq_of_eq ?_)
      rw [xiTopTilQ_holds Ch sel mu cst hX hPr hc hm v hpi _ _ d p' hrow.1 hrow.2 (hyb c)]
  refine ⟨hSS, hlev, pt, ix, yb, fun c' => if h : ∃ d, OverRow sel mu v d (pT c') then some h.choose else none,
    hN, hyb, hE, hC, fun c' d hd => ?_, fun c c' d hd => ?_, hpin, fun c' => ?_⟩
  · dsimp only at hd
    split_ifs at hd with h
    obtain rfl := Option.some_inj.1 hd
    exact (key c' _ h.choose_spec).1
  · dsimp only at hd
    split_ifs at hd with h
    obtain rfl := Option.some_inj.1 hd
    exact (key c' _ h.choose_spec).2 c
  · rw [hpin' c']
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨_, dif_pos ⟨d, hd⟩⟩
    · rintro ⟨d, hd⟩
      dsimp only at hd
      split_ifs at hd with h
      exact h

section Gen
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xiOver_eq_topG {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))
    (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u j) :
    xiOver Ch sel mu cst n h p Y p' = XiTopG Ch sel mu cst (n + 1) j (R.N j) p Y p' := by
  subst h
  rfl
end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def kerRd (u : B.Word) (a : I.ι) : KerRead ((I.rec7 l Z).chTw u a) B.fields where
  SS := Sall (Pr := B.primes X) I.sel (I.tup a) u
  lev := levC (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u
  N i c := ((I.stp u a i).rep c).1.1.deco.1.N
  Xi i c c' x := B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') x)
  pin i c := i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1

theorem kerRd_top {m2 : ℕ} (hm : B.R.m = m2 + 2) (u : B.Word) (a : I.ι) :
    (I.kerRd l Z u a).IsChainTop I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) B.embLL u m2 := by
  have hm' : (I.rec7 l Z).R.m = m2 + 2 := hm
  refine ⟨rfl, rfl, fun i _ c => ((I.stp u a i).rep c).1.1, fun i hi c => Idx.get c.1 (by omega),
    fun c => ((I.stp u a (m2 + 1)).rep c).1.2, fun c => ((I.stp u a (m2 + 1 + 1)).rep c).1.1, fun _ _ _ => rfl,
    fun c => PtAt.mem_ybSet _ (by omega), fun i hi c c' x => ?_, fun c c' x => ?_, ⟨fun _ => rfl, fun c c' x => ?_⟩, fun i hi c => show i + 1 ≤ B.R.m ∨ _ from Or.inl (by omega), fun c' => ?_⟩
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 _ _ x) = _
    rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm (Idx.some_get _ (by omega)).symm]
    rfl
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u m2 c.1 c'.1 _ _ x) = _
    rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm]
    rfl
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (m2 + 1) c.1 c'.1 _ _ x) = _
    rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega : m2 + 1 + 1 = B.R.m), xiOver_eq_topG]
    rfl
  · exact or_iff_right (by show ¬ m2 + 1 + 1 + 1 ≤ B.R.m; omega)

theorem mem_stdL_iff {R : Ranks} (H : Host R) (n : ℕ) (x : Fin n → H.E) : x ∈ Th.stdL H n ↔ ∀ k, IsIntegral ℤ (x k) := by
  refine ⟨fun h k => ?_, fun h k _ => Submodule.mem_one.2 ⟨⟨x k, h k⟩, rfl⟩⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h k trivial)
  rw [← hr]
  exact NumberField.RingOfIntegers.isIntegral_coe r

theorem chiRec_lat (hok : I.Ok) {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : B.Word) (a : I.ι) (i : ℕ)
    (c : (I.stp u a i).Cl) :
    TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) =
      I.chi (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) := by
  have h1 := (O u a).dt_lat i c
  have h2 := hidl.2.2.2.2 _ ((O u a).L0 i) ((O u a).lat i c)
  rw [← h1] at h2
  have e0 : ((O u a).L0 i).1 = Th.stdL B.host (B.R.N i) := by
    ext x
    rw [(O u a).lattice_integral_coordinates]
    exact (mem_stdL_iff B.host _ x).symm
  have e1 : ((O u a).lat i c).1 = ((I.stp u a i).rep c).1.1.deco.1.N := hO.lat u a i c
  rw [e0, e1] at h2
  have h3 : Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N = idl (QuotientGroup.mk ((O u a).dt i c)) := h2.symm
  rw [h3, TaylorLogMetric.chiRec_idl _ _ hidl.1, ← h3]
  have h4 : ((TaylorLogMetric.chiQ (I.rec7 l Z) (QuotientGroup.mk ((O u a).dt i c)) : ℂˣ) : ℂ) = ((tildeQ B.host I.SQ I.C.chiPsi (detPt B.host I.SQ ((I.stp u a i).rep c).1.1) : ℂˣ) : ℂ) := by
    rw [hO.dt u a i c]
    rfl
  rw [h4]
  exact GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).1

theorem kerRd_Th (hok : I.Ok) {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : B.Word) (a : I.ι) (i : ℕ)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    (I.kerRd l Z u a).Th (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (TaylorLogMetric.chiRec (I.rec7 l Z) idl) I.J.cD) i c c' =
      I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') := by
  refine (congrArg (fun A => (I.kerRd l Z u a).Th (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) A i c c')
    (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).symm).trans ?_
  have he : (I.J.amb B (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N =
      I.A.e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N := by
    funext z
    show Th.chiFac B.host _ _ _ _ _ * _ = Th.chiFac B.host _ _ _ _ _ * _
    unfold Th.chiFac
    rw [I.chiRec_lat l Z hok hidl hO u a i c, I.chiRec_lat l Z hok hidl hO u a (i + 1) c']
  show thC _ _ _ _ _ _ _ _ _ _ ((I.J.amb B (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N) = thC _ _ _ _ _ _ _ _ _ _ (I.A.e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N)
  rw [he]
  rfl

theorem kerEntTied_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.Adapted ∧ t.TopPinned := by
  intro B X I hok hp l Z L hT Gi Gl K Y cX ex O E hQ hO hU hE hS
  obtain ⟨idl, hidl⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  obtain ⟨⟨kf, hkf⟩, hAd⟩ := hE
  have hm := hok.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hok.sel_ok u ⟨hok.T_mem u, hok.g_mem⟩).2.1
  let t : KerEntTied ex :=
    { cc := ⊤
      cc_rec := B.toPre.ccK_top.symm
      cc_ok := ⟨top_ne_bot, by simp⟩
      δ := I.J.δ
      δ_ok := hok.amb_ok.delta
      B := I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      χ := TaylorLogMetric.chiRec (I.rec7 l Z) idl
      χ_ok := TaylorLogMetric.isChi_chiRec _ _ hidl
      idl := idl
      idl_ok := hidl
      χ_rec := rfl
      cD := I.J.cD
      X := B.fields
      seam := seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      seam_ok := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      Pr := B.primes X
      pr_ok := l.pr
      g_rec := fun i => rfl
      Ch := I.Ch
      sel := I.sel
      S := I.S
      word := fun u => u
      T_rec := fun u => rfl
      tup := I.tup
      Q_rec := hQ
      cst := I.cst
      idx := I.idx
      m2 := B.R.m - 2
      glob := I.glob
      glob_σ := rfl
      glob_xi := rfl
      idx_ok := hok.idx_ok
      O := O
      rd := I.kerRd l Z
      rd_chain := fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hok.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a)
      O_dgen := hO.dgen
      O_S := hO.S
      O_lat := fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
      O_Th := fun u a i c c' => (hO.Th u a i c c').trans (I.kerRd_Th l Z hok hidl hO u a i c c').symm
      unf := fun u a i hi => (hU u a i hi).unfIs _
      ent := E
      ent_lam := fun u w h => (hS u w h).1
      kf := kf
      kf_un := hkf
      served := hS }
  exact ⟨t, ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl,
    heq_of_eq (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J _).symm, rfl, hO⟩, rfl, hAd, fun u a => I.kerRd_top l Z hm u a⟩

end GlobalTheory.Mem.Col2.TC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaChainStepExponentsAndNonzeroVacuum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastStepVac

theorem last_step : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωX → R.chain_vX → ∀ t (k : Fin D.R.m), (k : ℕ) = D.R.m - 1 → IsStepWeil k R.ψ (Yc D (D.R.m - 1)) D.sp.X' (R.ωX t) ∧ IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL _ hω hv t k hk
  have hm := D.R.two_le_m
  have hk' : (k : ℕ) + 1 = D.R.m := by omega
  have he := GlobalTheory.InnerSteps.exp_chrStep R.toLevCh hL t k
  rw [hk'] at he
  refine ⟨⟨_, _, hω t, he⟩, ?_⟩
  have hr : (Yc D (D.R.m - 1)).rank ≤ D.sp.X'.rank := by
    rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.X'_rank]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_right _ _)) _
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.InnerSteps.stepVec_vac
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (D.R.m - 1) (by omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX) hr (hv t)
  exact ⟨h1, h2, h3⟩

end GlobalTheory.LastStepVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIffIntegralWeylCoordinates
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.IntegralityCompare

theorem lift_ratSpan (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → ∃ R0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL,
      MvPolynomial.map D.what₂.embLL R0 = P0 := by
  intro h
  have hle : Formalism.L2.Forms.RatSpan D lam ≤ (MvPolynomial.map D.what₂.embLL).toAddMonoidHom.range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro p ⟨r, f, -, rfl⟩
    refine ⟨MvPolynomial.C r * Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    have hc : (D.what₂.embLL).comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    simp [Formalism.L2.Forms.ten, map_prod, MvPolynomial.map_map, MvPolynomial.smul_eq_C_mul, MvPolynomial.map_rename, hc]
  obtain ⟨R0, hR0⟩ := hle h
  exact ⟨R0, hR0⟩

theorem lattice_iff_weyl : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm →  ∀ v : ValQ O u μ i, evC O u μ i v = f → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ srcFun Pl Bs u μ w i c (secC O u μ i v) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) (nuT (I.rec7 l Z) u i)) := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f hRat Bm hBm v hv
  obtain ⟨P0, hP0, hf⟩ := hRat
  have hL : ∀ τ, GL3Columns.BasR (I.rec7 l Z) (Pl.lam w) τ (((I.stp u μ i).rep c).1.1.deco.1.N) (Bs u μ w i c τ) := by
    intro τ
    have h := hBas u μ w i hi.le c τ
    have e := hStd.lat u μ i c
    exact (congrArg (fun L => GL3Columns.BasR (I.rec7 l Z) (Pl.lam w) τ L (Bs u μ w i c τ)) e).mp h
  choose g hg1 hg2 hg3 using fun τ => _root_.GlobalTheory.LocBasisChange.basis_change _ (Pl.lam w) τ _ Bm _ (hL τ) hBm
  obtain ⟨k, hk1, hk⟩ := _root_.GlobalTheory.IntegralityCompare.weight_arith_step I hOk hPins l Z u μ i hi
  obtain ⟨R0, hR0⟩ := lift_ratSpan _ _ P0 hP0
  have hsrc := _root_.GlobalTheory.Mem.SrcFunRead.srcFun_secC_read I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f P0 hf R0 hR0 k hk1 Bm g hg3 v hv
  set R := twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0 with hRdef
  have hR : MvPolynomial.map (I.rec7 l Z).what₂.embLL R = twSub (embT (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) P0 := by
    have h := map_twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0 (I.rec7 l Z).what₂.embLL
    have h' : MvPolynomial.map (I.rec7 l Z).what₂.embLL R = twSub (fun τ => ((I.rec7 l Z).what₂.embLL).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) Bm (shiftOf (lamTG (I.fm l u μ) i)) P0 :=
      h.trans (congrArg (twSub _ Bm _) hR0)
    have he : (fun τ => ((I.rec7 l Z).what₂.embLL).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) = embT (I.rec7 l Z) :=
      funext fun τ => RingHom.ext fun x => Formalism.L2.G.Cmp.tEL_emb _ τ x
    rw [he] at h'
    exact h'
  set c0 := ∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ) with hc0def
  have hc0 : ‖c0‖ = 1 := by
    rw [hc0def, norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, hg2 τ, _root_.one_zpow]
  have hRat' : MvPolynomial.map (I.rec7 l Z).what₂.embLL R ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i) := by
    rw [hR]; exact _root_.GlobalTheory.IntegralityCompare.twSub_mem_ratSpan _ _ Bm _ P0 hP0
  have hν : nuT (I.rec7 l Z) u i = fun τ r => (((I.fm l u μ).lam i τ).natW r) + k τ :=
    funext fun τ => funext fun r => hk τ r
  refine (_root_.GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem (embT (I.rec7 l Z)) Bm _ _ P0 _ eY f hf).trans ?_
  rw [← hR]
  refine (_root_.GlobalTheory.IntSpanCmp.intSpan_iff_delW _ Pl w _ R hRat').trans ?_
  rw [hsrc, hν]
  refine Iff.trans ?_ (_root_.GlobalTheory.WeylTensorSubst.subst_mem_iff _ _ _ _ g c0 (fun y => (∏ τ, (y τ).det ^ k τ) * polFun (MvPolynomial.map (Pl.iL w) R) y) hc0 hg1 hg2).symm
  exact (_root_.GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff _ _ _ _ k _).symm

end GlobalTheory.IntegralityCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem T_notMem_qv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  classical
  intro B X I hI _ u a P
  have hP : P.1 ∈ uSG (B.primes X).vGs I.SQ := Finset.mem_union.2 (Or.inr (I.mem_SQ.2 ⟨a, P.2⟩))
  exact GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 hP

end GlobalTheory.Mem.Col2.ChEx
end

