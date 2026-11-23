module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRankLevelMemIntegralGLAtTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLevInt

theorem mem_GLint_of_topLev : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (z : X.K), TopLev Ch sel mu cst j P g z → g ∈ GLint X.E (R.N j) P.1 := by
  intro X Pr R Ch sel S mu cst j P hP g z hT
  obtain ⟨g', hg', hpr, hat, -⟩ := hT
  unfold rowLevTop at hg'
  rw [if_neg hP] at hg'
  have hst : g' ∈ stabL X.E _ (stdAt X.E _ P.1) := (Subgroup.mem_inf.1 hg').1
  show ∀ x, g x ∈ stdAt X.E (R.N j) P.1 ↔ x ∈ stdAt X.E (R.N j) P.1
  intro x
  have h1 : prXpG X.E (R.N j) (g x) = g' (prXpG X.E (R.N j) x) := LinearMap.congr_fun hpr x
  have h2 : atNL X.E (R.N j) (R.N j - 1) (g x) = atNL X.E (R.N j) (R.N j - 1) x := LinearMap.congr_fun hat x
  have h3 := hst (prXpG X.E (R.N j) x)
  rw [ciMem_stdAt, ciMem_stdAt] at h3 ⊢
  rw [xt_split j (g x), xt_split j x, h1, h2, h3]

end GlobalTheory.TopLevInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainStabilisersEqStandardBaseLevelPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pdv

theorem stabStd_eq_stabSet {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun γ => (fun v => γ.1 v) '' ((I.stp u a i).rep c).1.2 = ((I.stp u a i).rep c).1.2) := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    have hs : _ = _ := s.2
    refine ⟨s.1, congrArg (fun p => p.1.1) hs, congrArg (fun p => p.1.2) hs, ?_⟩
    refine Prod.ext ?_ rfl
    exact GlobalTheory.KerJ.ufGL_val s.1.1
  · rintro ⟨b, hb, hq, rfl⟩
    refine ⟨⟨b, Subtype.ext (Prod.ext hb hq)⟩, ?_⟩
    refine Prod.ext ?_ rfl
    exact (GlobalTheory.KerJ.ufGL_val b.1).symm

theorem rep_coset_empty {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m)
    (c : (I.stp u a i).Cl) : ((I.stp u a i).rep c).1.2 = ∅ := by
  have key : ∀ y : Ys B.fields (B.R.N i), y = Ys.triv _ _ → ∀ s N, s ∈ y.ys N → s = ∅ := by
    rintro y rfl s N hs
    exact hs
  exact key _ (by unfold ysAt; exact if_neg hi) _ _ ((I.stp u a i).rep c).2

theorem stabStd_eq_stabSet_triv {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun _ => True) := by
  rw [stabStd_eq_stabSet, rep_coset_empty I u a i hi c]
  congr 1
  funext γ
  simp

theorem stab_pin : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → ∀ u a, GlobalTheory.KerJ.StabPin t u a (GlobalTheory.Pdv.stabStd I l Z u a) := by
  intro B X I hI hP l Z L hT Gi Gl K Y cX ex t hN hK hR u a
  change B.Word at u
  change I.ι at a
  obtain ⟨cc, cc_rec, cc_ok, δ', δ_ok, B', χ, χ_ok, idl, idl_ok, χ_rec, cD, X', seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S', word,
    T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf,
    kf_un, served⟩ := t
  obtain ⟨hX, hseam, hPr, hCh, hsel, hS, hword, htup, hcst, hidx, hm2, -, -, -, -⟩ := hK
  subst hX
  obtain rfl := eq_of_heq hseam
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hCh
  obtain rfl := eq_of_heq hsel
  subst hS
  obtain rfl := eq_of_heq hword
  obtain rfl := eq_of_heq htup
  obtain rfl := eq_of_heq hcst
  obtain rfl := eq_of_heq hidx
  subst hm2
  obtain ⟨r, hr, hrs⟩ := hR u a
  obtain rfl := eq_of_heq hr
  unfold GlobalTheory.KerJ.StabPin
  dsimp only
  have hm : B.R.m = B.R.m - 2 + 2 := (hI.idx_ok a).hm
  have h1 : B.R.m - 2 + 1 + 1 = B.R.m := by omega
  obtain ⟨hXo, hPro, -⟩ := base_fields_primes_ok B X
  have hG : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levG j (b.get h) := by
    intro j b h
    unfold levGAt
    rw [← Idx.some_get b h]
    rfl
  have hQ : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levQ j (b.get h) := by
    intro j b h
    unfold levQAt
    rw [← Idx.some_get b h]
    rfl
  have hGt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twLt I.Ch B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levGAt
    rw [hb]
    exact (topLev_levG_m _ _ _ _ _).trans (_root_.GlobalTheory.levGTop_rPsymF_eq_twLt B.fields (B.primes X) B.R I.Ch hXo hPro hI.ch_ok)
  have hQt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twTt (R := B.R) I.sel (I.tup a) B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levQAt
    rw [hb]
    refine (topLev_levQ_m _ _ _ _ _).trans ?_
    have hd : topDep B.R (I.cst a).M = 4 * B.R.m := by
      have := (hN a).2.1
      unfold topDep
      exact max_eq_left (by omega)
    rw [hd]
    exact GlobalTheory.T.level_quotient_eq_twisted_top B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) hXo hPro hI.sel_ok (fun i => hI.g_mem i)
      (fun v => hI.T_mem v)
  have hTop : ∀ j (hj : j = B.R.m) (c : ((I.rec7 l Z).chTw u a).cls j),
      stabStd I l Z u a j c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (twLt I.Ch j)
        (twTt (R := B.R) I.sel (I.tup a) j) ((I.stp u a j).rep c).1.1 (fun _ => True) := by
    intro j hj c
    subst hj
    rw [stabStd_eq_stabSet_triv I l Z u a _ (by omega) c, hGt, hQt]
  refine ⟨fun i _ c => ((I.stp u a i).rep c).1.1, fun i hi c => c.1.get (by omega),
    fun c => ((I.stp u a (B.R.m - 2 + 1)).rep c).1.2, fun c => ((I.stp u a (B.R.m - 2 + 1 + 1)).rep c).1.1,
    fun i _ c => hrs.1 i c, fun c => PtAt.mem_ybSet _ h1, ?_, ?_, ⟨fun c' => hrs.1 _ c', ?_⟩, ?_, ?_, fun c => hTop _ h1 c⟩
  · intro i hi c c' x
    rw [hrs.2 i (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 _ _ x) = _
    rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm
      (Idx.some_get c'.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) c.1 c'.1 _ _ x) = _
    rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2 + 1) c.1 c'.1 _ _ x) = _
    rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) h1,
      GlobalTheory.T.lastColumnStepDatum_eq_twistTopDatum B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) u (B.R.m - 2) h1]
    rfl
  · intro i _ hi c
    rw [stabStd_eq_stabSet_triv I l Z u a i (by omega) c, hG i c.1 (by omega), hQ i c.1 (by omega)]
    rfl
  · intro b c
    obtain ⟨b0, hb0⟩ := (hI.idx_ok a).last_uniq
    have hcb : c.1.get (by omega) = b := (hb0 _).trans (hb0 b).symm
    rw [stabStd_eq_stabSet, hG _ c.1 (by omega), hQ _ c.1 (by omega), hcb]
    rfl

end GlobalTheory.Pdv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnOrthonormalCoordsEqGiven
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem crd_eq_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi)) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) (A : AdData t u a (charts I l Z u a bad Ch chOf eY Kc)), I.StdKer l Z t → (∀ i hi, I.IdY l Z u a i hi (eY i hi)) → AdPins A dt → ∀ i hi, A.crd i hi = 1 := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t u a bad Ch chOf eY Kc dt A hK hY hA i hi
  obtain ⟨τ⟩ : Nonempty (I.rec7 l Z).what₂.Tau := ⟨(I.rec7 l Z).eTau.symm 1⟩
  let f : Formalism.L2.Forms.Fr (I.rec7 l Z) i hi := ⟨fun _ => 1, fun _ => by simp⟩
  set y := (eY i hi).symm f with hy
  have hYy : (eY i hi y).1 = y.1 := hY i hi y
  have hf : (eY i hi y) = f := by rw [hy, Equiv.apply_symm_apply]
  have h1 := hA.frm i hi y τ
  have h2 := hK.O.frm u a i y
  have hc : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (A.crd i hi).1 τ = 1 := by
    have e1 : ((charts I l Z u a bad Ch chOf eY Kc i hi).eY y).1 τ = 1 := by
      show ((eY i hi y).1) τ = 1
      rw [hf]
    rw [e1, mul_one, h2, ← hYy, hf] at h1
    exact h1.symm
  apply Units.ext
  refine Matrix.ext fun p q => ?_
  have := congrFun (congrFun hc p) q
  simp only [Formalism.L2.Forms.atInf, Matrix.map_apply] at this
  rw [Units.val_one]
  apply (Formalism.L2.Forms.embT (I.rec7 l Z) τ).injective
  rw [this]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.TwU.AtTrue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnTupleKernelsRational
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem tuple_kernels_rational : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Tw : TwForms (I.rec7 l Z)), ColIn.JetsIn I → Tw = I.tw l l0 Z →
    ∀ (u : B.Word) (a : I.ι) j, j < B.R.m → (Tw.fm u a).KRat j := by
  intro B X I h _ l Z l0 Tw hJ hTw u a j hj
  subst hTw
  exact ((KerRat.kernels_rational I l Z h hJ
    (Or.inr (GlobalTheory.Core.Ht2.family_laws I h (base_fields_primes_ok B X).1 l Z))).2.2 l0 u a).1 j hj

end GlobalTheory.TwU.AtTrue
end

