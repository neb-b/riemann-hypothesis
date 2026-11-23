module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0768
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovAtBaseRoot
section
namespace GlobalTheory.AdTh.CoverRoot

section Core

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdTh.CoverVal

theorem rdU_move {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U)
    {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) (k : U.Comp) {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom)
    {γ : GL (Fin r) E} (hγ : γ ∈ (U.X k).Γ) {b : Frame (U.X k).Ψ r} (hb : b ∈ Bor (U.X k).Ψ r) :
    rdU U f k (rmul (lact γ x) b) = rdU U f k x := by
  have hs := hU.2.2.2.2.1 0 0 ⟨fun τ _ _ _ => le_rfl, Even.zero⟩ f hf k
  rw [show laU U 0 0 k = 0 from GlobalTheory.Reg.IdemCusp.laU_zero (Formalism.L2.PjFree.Unf.ofPj U) k] at hs
  rw [hs.2.1 _ (dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)) b hb, hs.2.2 γ hγ x hx, GlobalTheory.Reg.IdemCusp.chi_zero _ hγ]
  simp [bchar]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}


set_option maxHeartbeats 1000000 in
theorem covAt_mem (hR : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (c0 : ℂ) (h0 : GlobalTheory.PtId.CovAt O c0) :
    c0 ∈ (inC O.c').range ∧ ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1 := by
  obtain ⟨c1, hm, hc⟩ := hO.cxi
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc ()
  obtain ⟨hlev, hA, -⟩ := hO.cov ()
  have hs0 : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hX₀, hon₀, -, hp₀, hrk, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    hs0 (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ ()).c₂ ((inC O.c').comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ ()).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ ()).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  obtain ⟨hroot, -⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  have hxi : ∀ x, R.xi A.μ0 x = 1 :=
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0)
  have hf : (O.dδ ()).cδ ∈ sec (O.dδ ()).Xo₂ (O.dδ ()).c₂ 0 0 := hlev.2.2.2.2.2.2.2.1
  have hv : ∀ h, rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c1 := fun h => by
    obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 h
    obtain ⟨x, hx⟩ := hroot (γ' * h)
    have hv := hval h γ' ⟨hγ', h2, h3⟩
    rw [(hO.tuple ()).xi _ _ hx, hxi, Circle.coe_one, _root_.mul_one] at hv
    exact hv
  have key : ∀ h, (O.dict₂ () h).2 ∈ ((O.U₂ ()).X (O.dict₂ () h).1).dom ∧
      rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c0 := fun h => by
    obtain ⟨hon, γ, ⟨hγ, hl, hfr⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ ()) hσ hU h1 hA R.θ (Wc D i)
      (rank_Wc i) (O.dict₂ ()) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt h
    obtain ⟨-, hsd, hmark, -⟩ := uw_lattice _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (O.U₂ ())) hσ hU' h1 Wt (O.dict₂ () h).1
    obtain ⟨Dc, hDc, -⟩ := exists_dic _ _ _ _ (O.dδ ()).c₂ _ _ Wt.g 0 ((O.U₂ ()).X (O.dict₂ () h).1) 0 Wt.e hσ hU.1
      (hU.2.1 _).1 (hU.2.1 _).2 hsd ⟨fun _ => antitone_const, Even.zero⟩
    have hper := Dc.per_eq
    have hty := Dc.ty_eq
    rw [hDc] at hper hty
    obtain ⟨hd', hu', -⟩ := hx_of_isONFr _ _ _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ hon
    have hA' := uw_anFib _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (O.U₂ ())) hσ hU' h1 Wt (O.dict₂ () h).1 Dc.bas Dc.idx
      Dc.sympl hper hty ⟨_, hd'⟩ hu'
    obtain ⟨x, hx⟩ := hroot (γ * h)
    have h3 := h0 () _ Wt.g Dc.bas Dc.idx Wt.e (γ * h) x (Wt.mark (O.dict₂ () h).1) (hmod _) (hU.2.1 _).1 Dc.sympl
      ⟨hper, hty⟩ hl hx hmark hma
    rw [← hfr, hxi, Circle.coe_one, _root_.mul_one] at h3
    obtain ⟨A', hA'', -⟩ := hA'
    exact ⟨hd', (dif_pos hd').trans (h3 _ A' hA'')⟩
  obtain rfl : c0 = c1 := (key 1).2.symm.trans (hv 1)
  refine ⟨?_, hm⟩
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT.laws _ (inR i) O.s0 (hs0 ▸ T.toCore.good_σ₀) (Wc D i) O.hV
    (rank_Wc i)
  have hpq := hrk ▸ h1
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.FlatLine.const_value_mem_range _ _ _ _ _ _ _ _ (O.U₂ ()) hσ hU hpq _ hf c0 fun k x hx => by
    obtain ⟨h, γ, hγ, b, hb, e⟩ := GlobalTheory.CoverIndep.dict_onto (Wc D i) (rank_Wc i) (O.U₂ ()) (O.dict₂ ()) (iotaW T i) e' F' ik φ
      th _ hσ hA hpq hU hW hD hio hth hx₀ (fun h => (key h).1) k x hx
    have h4 := hv h
    rw [e] at h4
    exact (rdU_move (O.U₂ ()) hU hf k hx hγ hb).symm.trans h4
  exact ⟨_, ha⟩

end Core

section Top

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem covAt_base_root : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ c0 : ℂ, GlobalTheory.PtId.CovAt (O i) c0 → c0 ∈ D.what₂.embLL.range ∧ ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O _ hC i hOP c0 h0
  obtain ⟨⟨a, rfl⟩, hm⟩ := covAt_mem hC ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩ (O i) hOP.2 c0 h0
  refine ⟨?_, hm⟩
  obtain ⟨b, hb⟩ := hOP.1.le a.2
  exact ⟨b, hb⟩

end Top

end GlobalTheory.AdTh.CoverRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberReferenceTuple
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

variable {D : D7}

theorem om_sum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
    (s : Finset ι) (F : ι → VC D a d → ℂ) (hF : ∀ i ∈ s, F i ∈ TT D (tor0 D ⊤ δ) a d) :
    W.Om g g' (∑ i ∈ s, F i) = ∑ i ∈ s, W.Om g g' (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : VC D a d → ℂ) ∈ TT D (tor0 D ⊤ δ) a d := (GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).zero_mem
    have := W.smul g g' 0 0 h0
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      W.add g g' _ (hF x (Finset.mem_insert_self _ _)) _
        ((GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).sum_mem fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem exists_bottom_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χβ : HeckeU D (botBig D i j)), (∀ x, χβ.f x = (betaH G i j)⁻¹.1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P.a = botBig D i j ∧ P.d = botBig D i j + botSmall D i j ∧ HasChars P (betaH G i j)⁻¹ (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P (condE G.pl) 0 ∧ IsBlockLevel P (condE G.pl) (botBig D i j) := by
  intro D T L sc μ₀ hL G hb δ t0 hc ht i j χβ hβ χν hν hn
  have hd : Even (botBig D i j + botSmall D i j) := by
    obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
    exact ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  have had : botBig D i j ≤ botBig D i j + botSmall D i j := Nat.le_add_right _ _
  obtain ⟨e0, vac, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht _ _ (hd.mul_left (botBig D i j))
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 vac.1 h0 χβ χν
  have hm : condE G.pl ≠ ⊥ := condE_ne_bot _
  have hcop := GlobalTheory.FunObj.StdDatum.condE_isCoprime_conj G.pl
  have hnu : ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → W.chV'.f u = 1 := by
    rw [hW2]; exact GlobalTheory.FunObj.SqNum.heckeU_nuInv_eq_one_of_cong hL G i j χν hν
  obtain ⟨hi0, -⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j)
  obtain ⟨R, hR1, hR2'⟩ := GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) (congLev_le _ _) hi0
  have hR2 : ∀ k ∈ intG D (botBig D i j), ∃! r, r ∈ R ∧ CongOne D (condE G.pl) (r⁻¹ * k) := by
    intro k hk
    obtain ⟨r, ⟨hr, hrk⟩, hu⟩ := hR2' k hk
    refine ⟨r, ⟨hr, ((GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hrk).2⟩, fun r' ⟨hr', h'⟩ => hu r' ⟨hr', (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).2
      ⟨mul_mem (inv_mem (hR1 r' hr')) hk, h'⟩⟩⟩
  have hcv := GlobalTheory.FunObj.CosetTT.cosetV_mem_TT D δ hc (condE G.pl) hm 0 _ _ e0 vac.1
  have hfix : ∀ k ∈ intG D (botBig D i j), W.Om k 1 (stdSum W (condE G.pl) 0 R) = stdSum W (condE G.pl) 0 R := by
    intro k hk
    unfold stdSum
    rw [om_sum W k 1 R _ fun r _ => W.maps _ _ _ hcv]
    have e1 : ∀ r, W.Om k 1 (W.Om r 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) = W.Om (k * r) 1 (cosetV D δ (condE G.pl) 0 _ _ e0) := by
      intro r
      have := W.mul k r 1 1 _ hcv
      rw [mul_one] at this
      exact this.symm
    simp_rw [e1]
    refine GlobalTheory.sum_transversal_left_translate_invariant (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) R
      (fun g => W.Om g 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) hR1 hR2' (fun r _ c hc' => ?_) k hk
    have := W.mul r c 1 1 _ hcv
    rw [mul_one] at this
    obtain ⟨hc1, hc2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hc'
    rw [this, _root_.GlobalTheory.FunObj.FixKey.om_cosetV_of_congOne D δ t0 hc e0 vac W (condE G.pl) hm hcop hnu 0 (by omega) c hc1 hc2]
  have hle : congLev D (condE G.pl) (botBig D i j + botSmall D i j) ≤
      blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hk
    refine (GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ _).2 ⟨hk1, fun a b hb ha => ?_⟩
    have hab : a ≠ b := fun e => by rw [e] at ha; omega
    have := hk2 a b
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hab, sub_zero] at this
  obtain ⟨hj0, hj1⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j + botSmall D i j)
  have hQ : 0 < levQ G.pl := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]; exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hm)
  let n : D.what₂.Tau → ℕ := fun τ => ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2).toNat
  have hwt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by
    intro τ
    rw [hW4, hW2, one_mul]
    obtain ⟨r, hr⟩ := χν.par τ
    have h1 := hn τ
    have h2 : ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2) = r := by omega
    simp only [n, h2]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hpres : Pres D ⊤ δ (levQ G.pl) e0 (stdSum W (condE G.pl) 0 R) := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact _root_.GlobalTheory.FunObj.StdDatum.pres_stdSum D δ t0 hc e0 vac had W _ hm hcop hb hnu R hR1 hR2 hfix
  have hidx_ne : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≠ 0 := fun h =>
    hj0 (Subgroup.relIndex_eq_zero_of_le_left hle h)
  have hidx_le : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≤ levQ G.pl ^ ((botBig D i j + botSmall D i j) ^ 2 + 4) := by
    refine (Subgroup.relIndex_le_of_le_left hle hj0).trans (hj1.trans ?_)
    rw [GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact Nat.pow_le_pow_right hQ (by omega)
  have heig := _root_.GlobalTheory.FunObj.StdDatum.CapelliMinorMembership.stdSum_eig D δ t0 hc e0 vac had W _ hm hcop hnu R hR1 hR2 hfix
  let P : Pair D ⊤ δ t0 (levQ G.pl) :=
    { crv := hc
      pt0 := ht
      a := botBig D i j
      d := botBig D i j + botSmall D i j
      a_le := had
      d_even := hd
      e0 := e0
      vac := vac
      W := W
      n := n
      wt := hwt
      F := stdSum W (condE G.pl) 0 R
      pres := hpres
      fix := hfix
      J := blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)
      J_le := blockLev_le _ _ _
      idx_ne := hidx_ne
      idx_le := hidx_le
      eig := heig }
  refine ⟨P, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩, fun h => GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ h⟩
  · show W.chV.f x ^ W.ep = _
    rw [hW1, hW3, zpow_one, hβ]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW2, hW4, zpow_one, hν]

end GlobalTheory.FunObj.StdDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.BetaInvIntegral

theorem betaH_inv_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  intro D T hF j hj n Λ σ p hp hU hT hTp
  have hβ : betaH (Dw := T.Q.Dw j) T.Q.c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  obtain ⟨M, hM, hint⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hp
    (betaH (Dw := T.Q.Dw j) T.Q.c Λ)⁻¹ (fun w hw => by
      obtain ⟨k, hk, h1, h2⟩ := hTp
      have hA : ReciprocityTheory.ChartRestriction.G.PullbackSections.AdaptAt Λ w :=
        ⟨k, GlobalTheory.ShortUnits.not_mem_of_coprime' w hk.symm hw, h1, h2⟩
      have hv := GlobalTheory.ShortUnits.vLa_betaH T hF j hj Λ w hU hT hA
      have hne : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) ≠ 0 := by simpa using hβ
      have h1' : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 1 := by
        rw [← WithZero.exp_log hne]
        simp only [vLa, neg_eq_zero] at hv
        rw [hv]; rfl
      rw [map_inv₀, h1', inv_one])
  refine ⟨M, hM, ?_⟩
  have := map_isIntegral_int σ hint
  simpa [map_mul, map_inv₀, map_natCast] using this

end GlobalTheory.BetaInvIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPoint
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.DetIdealPrime

theorem exists_ideal_coprime : ∀ (D : D7) (V : HSp D), HSpace.gram V = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ), IsIdemSum e P → SuppAt e V h → IsDetAt e V h y → ∀ (b : ℕ), (∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) → ∀ (Λ : GenLat D.host.E V.rank), (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat V (fin V h)) → ∀ p : ℕ, p.Prime → Λ.TrivAt p → ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ ((c y : Circle) : ℂ) = ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ) := by
  intro D V hg hL h e P y he hs hy b hb c ψ hc hu hr Λ hΛ p hp hT
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e P y he hs hy b hb c ψ hc hu hr
  refine ⟨cc, c0, c2, ?_, c4⟩
  refine GlobalTheory.NormCoprime.coprime_absNorm_of_sup p hp c0 ?_
  obtain ⟨k, hk, -, hk2⟩ := hT
  have hdet : ((k : D.host.E) ^ V.rank) ∈ Submodule.span (𝓞 D.host.E) (detSet (Bridge.hLat V (fin V h))) := by
    refine Submodule.subset_span ⟨fun i => (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E), fun i => ?_, ?_⟩
    · have hstd : (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
        rw [Formalism.L2.Pj.stdLat, Submodule.mem_pi]
        intro j _
        by_cases hj : j = i
        · subst hj; simpa using (Submodule.one_le.1 le_rfl : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E))
        · simp [Pi.single_apply, hj]
      have h1 := hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 D.host.E)) hstd)
      have h2 : ((k : 𝓞 D.host.E) • (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E)) =
          (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E) := by
        rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) k, algebraMap_smul]
      rw [h2] at h1
      have h3 := (hΛ _).1 h1
      convert h3 using 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · have : (Matrix.of fun i j => ((k : D.host.E) • (Pi.single j 1 : Fin V.rank → D.host.E)) i) =
          (k : D.host.E) • (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) := by
        ext i j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hcM : cc ≤ M := le_trans le_sup_left hle
  have hpM : ((p : ℕ) : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hkM : ((k : ℕ) : 𝓞 D.host.E) ∉ M := by
    intro hkM
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hk
    have e1 := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at e1
    refine hM.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e1]
    exact M.add_mem (M.mul_mem_left _ hkM) (M.mul_mem_left _ hpM)
  have hkn : ((k : ℕ) : 𝓞 D.host.E) ^ V.rank ∉ M := fun h0 => hkM (hM.isPrime.mem_of_pow_mem _ h0)
  have hc'M : cc.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ M := by
    intro x hx
    have hm : (k : D.host.E) ^ V.rank * (x : D.host.E) ∈ idlE cc := by
      rw [← c3]
      exact Submodule.mul_mem_mul hdet ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hm
    have hz' : z = ((k : ℕ) : 𝓞 D.host.E) ^ V.rank * x := by
      apply RingOfIntegers.ext
      rw [show (z : D.host.E) = Algebra.linearMap (𝓞 D.host.E) D.host.E z from rfl, hzeq]
      push_cast
      rfl
    rw [hz'] at hz
    exact ((hM.isPrime.mem_or_mem (hcM hz)).resolve_left hkn)
  exact hM.ne_top (top_le_iff.1 (c1 ▸ sup_le hcM hc'M))

end GlobalTheory.DetIdealPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalFieldDataStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_localField_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v),
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (ψL : AddChar (w.adicCompletion E) ℂ),
      IsConjAt σ h σL ∧ Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
      (∀ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z → ψL z = 1) ∧
      (∃ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
      ∀ z, ψL ((z + σL z) / 2) = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (-1 * ptAt hw h z)) := by
  first | exact @GlobalTheory.InertPsi.exists_field_data | exact GlobalTheory.InertPsi.exists_field_data | (intros; apply GlobalTheory.InertPsi.exists_field_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceOrthonormalSelfDualFrameStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_orthonormal_selfDual_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ A : GL (Fin a') (w.adicCompletion E), IsFrameAt w G.V'.L A ∧
      (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ * G.V'.J.map (algebraMap E (w.adicCompletion E)) *
        (A : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := by
  first | exact @GlobalTheory.InertUnitFrame.exists_frame_one | exact GlobalTheory.InertUnitFrame.exists_frame_one | (intros; apply GlobalTheory.InertUnitFrame.exists_frame_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacePointSupportedAndSurjectiveStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlacePoint_supported_and_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  first | exact @GlobalTheory.InertCoord.kap_at_and_onto | exact GlobalTheory.InertCoord.kap_at_and_onto | (intros; apply GlobalTheory.InertCoord.kap_at_and_onto <;> assumption)
end

