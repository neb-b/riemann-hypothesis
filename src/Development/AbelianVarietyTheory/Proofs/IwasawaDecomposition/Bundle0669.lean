module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStep
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitNontrivialAt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameTypes

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame


def IsBlockUpperUnipotentMatrix {k : Type} [CommRing k] {n : ℕ} (r : ℕ) (x : GL (Fin n) k) : Prop :=
  ∀ i j : Fin n, (r ≤ i.val → j.val < r → x.val i j = 0) ∧ (i.val < r → j.val < i.val → x.val i j = 0) ∧
    (i.val < r → i = j → x.val i j = 1)

theorem blkUni_one {k : Type} [CommRing k] {n : ℕ} (r : ℕ) : IsBlockUpperUnipotentMatrix r (1 : GL (Fin n) k) := by
  intro i j
  refine ⟨fun h1 h2 => ?_, fun _ h2 => ?_, fun _ h2 => ?_⟩
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, h2, Matrix.one_apply_eq]

theorem IsBlockUpperUnipotentMatrix.blk2 {k : Type} [CommRing k] {n r : ℕ} {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) : x ∈ blockTri (blk2 r) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blk2 at hij
  refine (h i j).1 ?_ ?_ <;> split_ifs at hij <;> omega

theorem IsBlockUpperUnipotentMatrix.blkOf {k : Type} [CommRing k] {n r t : ℕ} (hn : n ≤ r + t) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    x ∈ blockTri (blkOf r t) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blkOf at hij
  have hi := i.2
  by_cases h1 : i.val < r
  · rw [if_pos h1] at hij; omega
  · rw [if_neg h1, Nat.div_eq_of_lt (show i.val - r < t by omega)] at hij
    refine (h i j).1 (by omega) ?_
    by_contra h2
    rw [if_neg h2] at hij
    exact absurd hij (not_lt.2 (Nat.succ_le_succ (Nat.zero_le _)))

theorem IsBlockUpperUnipotentMatrix.unip {k : Type} [CommRing k] {n r : ℕ} (hr : r ≤ n) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    upperLeftBlock hr x ∈ unip k r := by
  refine ⟨mem_blockTri.2 fun i j hij => ?_, fun i => ?_⟩
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.1 i.2 hij
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.2 i.2 rfl

variable {D : D7}

theorem isConjPl_of_under (s : SplitPlace D.host.E) {PP : PlE D.host} (hne : PP ≠ s.w)
    (h : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) PP = s.v) : Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w := by
  rcases Formalism.L2.eq_or_eq_conjPlE s.w PP ((congrArg HeightOneSpectrum.asIdeal h).trans s.w_under.symm) with e | e
  · exact absurd e hne
  · intro c hc
    rw [e, Formalism.L2.mem_conjPlE] at hc
    refine ⟨_, hc, ?_⟩
    rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.TypePlaces.star_eq_conj, GlobalTheory.SplitPlaceOver.host_conj_eq']

theorem mem_level {V : TH.HSp D} {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : Formalism.IndefR.principalLevelFrame.RowPsi V n} (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hrt : V.rank ≤ L.r + L.t)
    (hH : ∀ g : G0 L.Pg L.r, (∀ PP, g PP ∈ unip (kP PP.1) L.r) → g ∈ L.P.H)
    (s : SplitPlace D.host.E) (hsep : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w)
    {φ : Os s →+* kP s.w} {b : GL (Fin n) (kP s.w)} (hfr : FrameRed hn P β s φ b)
    {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n) (hT : TrivOutside {s.v} κ) {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) :
    (IsBlockUpperUnipotentMatrix L.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → P.ψ κ ∈ Formalism.IndefR.Links.levS V β L) ∧
    (Matrix.GeneralLinearGroup.map φ y = 1 →
      P.ψ κ ∈ Formalism.IndefR.Links.levS V β L ∧ Formalism.IndefR.Lev.levChi V β L (P.ψ κ) = 1) := by
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ s.w → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
    intro PP hPP hne
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    exact GlobalTheory.NonSplitLevel.projV_eq_one hP κ PP (hT _ fun e => hsep PP hPP (isConjPl_of_under s hne e))
  have hent : ∀ i j : Fin V.rank, (redFn β s.w (Formalism.IndefR.Lev.finE V (P.ψ κ))).val i j =
      (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val (Fin.cast hn i) (Fin.cast hn j) :=
    fun i j => hfr κ hU y hy (Fin.cast hn i) (Fin.cast hn j)
  refine ⟨fun hb => ?_, fun h1 => ?_⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → IsBlockUpperUnipotentMatrix L.r (redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ))) := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        intro i j
        rw [hent]
        have hb' := hb (Fin.cast hn i) (Fin.cast hn j)
        exact ⟨hb'.1, hb'.2.1, fun h1 h2 => hb'.2.2 h1 (congrArg _ h2)⟩
      · rw [hred PP hPP e]; exact blkUni_one _
    exact ⟨P.into κ, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hS, fun PP h => (hall PP (Or.inl h)).blkOf hrt,
      fun PP h => (hall PP (Or.inr h)).blk2⟩, hH _ fun PP => (hall PP.1 (Or.inl PP.2)).unip L.hr⟩⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        refine Units.ext (Matrix.ext fun i j => ?_)
        rw [hent, h1, mul_one, mul_inv_cancel, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
        exact if_congr (Fin.cast_injective hn).eq_iff rfl rfl
      · exact hred PP hPP e
    refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hS hall⟩, ?_⟩
    unfold Formalism.IndefR.Lev.levChi
    rw [GlobalTheory.LevSplit.levFn_eq_one β L _ hall, Units.val_one]

section Read
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}


set_option maxHeartbeats 1000000 in
theorem exists_fn (ad : MtAd Y M) (μ : D.what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (k : Fin D.R.m)
    (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1))) :
    ∃ f : GAf D.host.E D.R.nV → ℂ, f ≠ 0 ∧
      (∀ κ (h : κ ∈ (M μ (k.1 + 1) (by omega) (by omega)).J) g,
        f (g * κ) = (((M μ (k.1 + 1) (by omega) (by omega)).χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ, (ad.PV k).ψ κ ∈ levS _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) →
        ∀ g, f (g * κ) = levChi _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) ((ad.PV k).ψ κ) * f g := by
  obtain ⟨x, hx⟩ := exists_ne (0 : D.what₂.Mt μ ((k : ℕ) + 1))
  have hr : (M μ (k.1 + 1) (by omega) (by omega)).real x ≠ 0 := fun e =>
    hx ((M μ (k.1 + 1) _ _).real_inj (e.trans (map_zero _).symm))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hr
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hg₀
  have hm : (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x ∈ NG.TypeSp (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).wt.ρ
      (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).J (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).χ :=
    (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real_range ▸ LinearMap.mem_range_self _ x
  refine ⟨fun g => l ((M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x g), fun e => hl (congrFun e g₀), fun κ h g => ?_, fun κ hJ g => ?_⟩
  · have e := congrFun (hm.2 ⟨κ, h⟩) g
    exact (congrArg l e).trans (map_smul l _ _)
  · have e1 := ad.read _ hμ k x (g * κ)
    have e2 := ad.read _ hμ k x g
    have e3 := (Y.IL.jMt _ hμ k x).2.2 _ hJ ((ad.PV k).ψ g)
    rw [← map_mul] at e3
    have e4 := e1.trans (e3.trans (congrArg _ e2.symm))
    rw [← map_smul] at e4
    exact (congrArg l ((ad.eW _ hμ k).injective e4)).trans (map_smul l _ _)


set_option maxHeartbeats 1000000 in
theorem types_of (ad : MtAd Y M) {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) {μ0 : T} (hlev : R.toRealDat.toLevCh.Is μ0) (hgl : R.toRealDat.grp_levels F.lv2)
    (i : D.nd.Loc) (μ : D.what₂.Tup) (k : Fin D.R.m) (hμ : μ = D.nd.mu i) (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1)))
    (s : SplitPlace D.host.E) (φ : Os s →+* kP s.w) (b : GL (Fin D.R.nV) (kP s.w)) (hs : s.w ∈ R.Pg)
    (hw : ∃ kk v, s.w = D.naut.plGw kk v) (hfr : FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.PV k) (R.βV k) s φ b) :
    ∃ (f : GAf D.host.E D.R.nV → ℂ) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
      (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
      (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
      f ≠ 0 ∧ NG.IsPsi0 s ψ₀ ∧ NG.LevelUni J χ s D.R.r ψ₀ ξ ∧ (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → ∀ y : GL (Fin D.R.nV) (Os s), IsCompOf s κ y →
        (IsBlockUpperUnipotentMatrix D.R.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
        (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g) := by
  have hu : Formalism.IndefR.RecTie.Used0 D μ := hμ ▸ Model.used_loc i
  rw [D.nd.mu_w i] at hμ
  subst hμ
  obtain ⟨kk, v, hv⟩ := hw
  obtain ⟨ψ₀, ξ, h1, -, h2⟩ := hin.uni (D.nd.w i) k kk v s hv
  obtain ⟨f, hf, hJ, hL⟩ := exists_fn ad _ hu k hnt
  obtain ⟨c, hc⟩ := hlev.βV k
  rw [one_pow] at hc
  obtain ⟨ψ0, -, hP0, -⟩ := hgl
  refine ⟨f, _, _, ψ₀, ξ, hf, h1, h2, hJ, fun κ hU hT y hy => ?_⟩
  have key := mem_level (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.std k) hc
    (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT (D.what₂.muTw (D.nd.w i))) (R.toRealDat.levR F.lv2 false))
    (le_of_eq (GlobalTheory.FrameBlockDiagonal.rankV D k))
    (fun g hg => by
      show g ∈ (R.toRealDat.levR F.lv2 false).H
      rw [hP0]
      exact fun PP _ => hg PP)
    s (fun PP hPP => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hlev _ hPP (Or.inl hs)) hfr hU hT hy
  refine ⟨fun hb => ⟨_, hL κ (key.1 hb)⟩, fun h1 g => ?_⟩
  rw [hL κ (key.2 h1).1 g, (key.2 h1).2, one_mul]

end Read


end GlobalTheory.FrameTypes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharWSeedStd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.StandardWeightCharacter


set_option maxHeartbeats 8000000 in
theorem charW_seed_std : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (C : Formalism.L2.Pj.CoreJ X.toD7) [Algebra C.Q.c.F X.toD7.what₂.LL] (R₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd), Inputs X.toD7 → IdemClass (D := X.toD7) (famR X I hX U Xg tr₀).A → (∀ R : RealDat X.toD7 (famR X I hX U Xg tr₀).A C.Q.c.F, R.Pre1 (face0 X I hX U Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.FullY → R.FullP → R.ExAt) → GeoExV (famR X I hX U Xg tr₀) C (face0 X I hX U Xg tr₀).lv2 → Formalism.L2.Host.ValLL X.toD7 R₀.C → C.pb = R₀.C.P.pb → R₀.toRealDat.Pre0 (face0 X I hX U Xg tr₀).lv2 → R₀.IsInert → R₀.IsTup → R₀.AllPlaces → Keep R₀.toRealDat (face0 X I hX U Xg tr₀).lv2 cG → ∃ (tr : TrI X.B px) (dict : _) (mu : _) (chiW : _) (x₀ : _) (cE : _) (R : RealDat3 X.toD7 (famR X I hX U Xg tr) C.Q.c.F) (cG' : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd), Pins R (face0 X I hX U Xg tr) cG' ∧ R.toRealDat.ExAt ∧ R.toRealDat.toLevCh = R₀.toRealDat.toLevCh ∧ HEq R.eG R₀.eG ∧ HEq cG' cG ∧ R.ψ = R₀.ψ ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧ (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr R.toRealDat) ∧ Nonempty (@GlobalTheory.RealGeo.GeoHalf X.toD7 _ _ _ _ _ (famR X I hX U Xg tr).A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE) (inferInstanceAs (Algebra C.Q.c.F X.toD7.what₂.LL)) R.toRealDat fun _ => 1) := by
  intro X px I hX U Xg tr₀ C _ R₀ cG hI hXi hEx hGeo hVal hpb p0 i0 t0 a0 k0
  classical
  obtain ⟨hL, hF⟩ := GlobalTheory.HeckeCharacterRestriction.liftsAt_and_seedFacts X.toD7 _ _ _ (famR X I hX U Xg tr₀).A C.Q.c.F (face0 X I hX U Xg tr₀).lv2
  obtain ⟨R1, p1, c1, t1, f1, g1, q1⟩ := analyticW_exists hI hXi hL hF
    (fun R => RealDat3.IsInert (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.IsTup (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.AllPlaces (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      R.toLevCh = R₀.toLevCh ∧ HEq R.eG R₀.eG ∧ R.ψ = R₀.ψ ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧
      (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr₀ R) ∧
      ∀ c : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) R (face0 X I hX U Xg tr₀).lv2 c)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 h => by
      rcases h with ⟨i, t, a, l, e, s, m, w, b, k⟩
      exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
        fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 h => by
      rcases h with ⟨i, t, a, l, e, s, m, w, b, k⟩
      exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
        fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩)
    (fun R a1 a2 a3 a4 a5 a6 h => by
      rcases h with ⟨i, t, a, l, e, s, m, w, b, k⟩
      exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
        fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩)
    R₀.toRealDat p0 ⟨⟨i0.tie, i0.onto, i0.hR, i0.hL, i0.SF⟩, ⟨t0.mu_off, t0.mu_used, t0.mu_ne, t0.mu_conj, t0.mu_on⟩, a0, rfl, HEq.rfl,
      rfl, rfl, rfl, id, fun c hc => by cases eq_of_heq hc; exact k0⟩
  have e1 : R1.ExAt := hEx R1 p1 c1 t1 f1 g1
  have l1 : R1.toLevCh = R₀.toLevCh := q1.2.2.2.1
  have hC : R1.C = R₀.C := congrArg (fun L => L.C) l1
  obtain ⟨cutoffDeriv, hcG1⟩ : ∃ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG := by
    rw [show R1.Pg = R₀.Pg from congrArg (fun L => L.Pg) l1]
    exact ⟨cG, HEq.rfl⟩
  have pc1 : GlobalTheory.RealGeo.PreChar R1 := ⟨p1.1.lev, p1.1.red_R, p1.1.red_L, p1.1.record, p1.1.fam, p1.2,
    RealDat.chain_of_weak c1 e1, RealDat.thP_of_weak t1 e1⟩
  have hV1 : Formalism.L2.Host.ValLL X.toD7 R1.C := by rw [hC]; exact hVal
  have hpb1 : C.pb = R1.C.P.pb := by rw [hC]; exact hpb
  obtain ⟨dict, mu, chiW, x₀, cE, nW, FW, hchi, ⟨geo⟩, hrat⟩ := hGeo R1 cutoffDeriv hV1 pc1 p1.1.levels hpb1 (q1.2.2.2.2.2.2.2.2.2 cutoffDeriv hcG1)
  let R2₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F := ⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨tr, htr⟩ : ∃ tr : TrI X.B px, (∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t') →
      R2₀.TrISem (face0 X I hX U Xg tr₀) tr ∧ SepWith (famR X I hX U Xg tr₀) tr := by
    by_cases h : ∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t'
    · obtain ⟨t', h'⟩ := h
      exact ⟨t', fun _ => h'⟩
    · exact ⟨tr₀, fun h' => absurd h' h⟩
  let R2 : RealDat3 X.toD7 (famR X I hX U Xg tr) C.Q.c.F := ⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := face0 X I hX U Xg tr) R2
  have q5 : RealDat3.IsInert (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.IsTup (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.AllPlaces (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).toLevCh = R₀.toLevCh ∧ HEq (R1.upd5 nW FW R1.mu R1.twPl R1.err0).eG R₀.eG ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).ψ = R₀.ψ ∧ (R1.upd5 nW FW R1.mu R1.twPl R1.err0).mu = R₀.mu ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).twPl = R₀.twPl ∧
      (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr₀ (R1.upd5 nW FW R1.mu R1.twPl R1.err0)) ∧
      ∀ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) (R1.upd5 nW FW R1.mu R1.twPl R1.err0) (face0 X I hX U Xg tr₀).lv2 c := by
    rcases q1 with ⟨i, t, a, l, e, s, m, w, b, k⟩
    exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
      fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩
  obtain ⟨i1, u1, a1, l6, e6, s6, m6, w6, b6, k6⟩ := q5
  have p6 := RealDat.preliminary_of_scalar_update (RealDat.preliminary_of_index_update p1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have f6 := RealDat.full_Y_of_scalar_update (RealDat.full_Y_of_index_update f1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have c6 := RealDat.weak_chain_of_scalar_update (RealDat.weak_chain_of_index_update c1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have t6 := RealDat.weak_theta_props_of_scalar_update (RealDat.weak_theta_props_of_index_update t1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have g6 := RealDat.full_P_of_scalar_update (RealDat.full_P_of_index_update g1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have hphs : (R2.updS kap lam).phase := by
    intro i
    refine ⟨show ‖(1 : ℂ)‖ = 1 from norm_one, fun _ x => ?_⟩
    obtain ⟨y, hy⟩ := hrat i x
    refine ⟨y, hy.trans ?_⟩
    show _ = Formalism.IndefR.Links.cj _ (1 : ℂ) • _
    rw [map_one]
    exact (one_smul ℂ _).symm
  have kv := k6 cutoffDeriv hcG1
  obtain ⟨g', -, -, -⟩ := GlobalTheory.RealGeo.geoHalf_upd X.toD7 _ _ _ (famR X I hX U Xg tr₀).A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
    (R1.upd5 nW FW R1.mu R1.twPl R1.err0) (fun _ => 1) kap R1.lam R1.err0 geo
  refine ⟨tr, dict, mu, chiW, x₀, cE, R2.updS kap lam, cutoffDeriv, ⟨⟨⟨p6.1.lev, ⟨p6.1.red_R, p6.1.red_L, p6.1.levels, p6.1.record, hchi⟩,
      p6.1.fam, p6.2, c6, t6⟩, ⟨⟨i1.tie.plI_inj, i1.tie.okI⟩, i1.onto, i1.hR, i1.hL, i1.SF⟩, f6.1, f6.2, g6, hs,
      ⟨u1.mu_off, u1.mu_used, u1.mu_ne, u1.mu_conj, u1.mu_on⟩, hphs, a1⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩,
    fun _ => rfl, fun h => htr h⟩, hEx _ p6 c6 t6 f6 g6, l6, e6, hcG1, s6, m6, w6, fun hb => b6 hb, ⟨g'⟩⟩

end GlobalTheory.StandardWeightCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorPrimesInLowSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem GlobalTheory.LamTie.cond0_primes_lowAll : ∀ (D : D7) (Z : GlobalTheory.LamTie.LamDat D), Z.Ok → Z.q0 = AbsolutelyIrreducibleSpan.q0 D → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → ∃ p ∈ lowAll D, P ∈ placesOver D.host.E p := by
  intro D Z hZ hq P hP
  have hPr : Prime (GlobalTheory.ToricDenom.below P).asIdeal := (GlobalTheory.ToricDenom.below P).prime

  have key : ∀ n : ℕ, ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) →
      ((n : 𝓞 D.host.E) ∈ P.asIdeal) := by
    intro n hn
    have h1 : algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal := hn
    simpa using h1
  have key' : ∀ n : ℕ, ((n : 𝓞 D.host.E) ∈ P.asIdeal) →
      ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) := by
    intro n hn
    show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal
    simpa using hn
  unfold GlobalTheory.LamTie.cond0 at hP
  rcases hPr.dvd_or_dvd hP with h | h
  · have h2 := hPr.dvd_of_dvd_pow h
    rw [Ideal.dvd_span_singleton] at h2
    have h3 := key _ (by exact_mod_cast h2)
    push_cast at h3
    have hpr := P.isPrime
    rcases hpr.mem_or_mem h3 with h4 | h4
    · rcases hpr.mem_or_mem h4 with h5 | h5
      · rcases hpr.mem_or_mem h5 with h6 | h6
        · exact ⟨D.host.g 0, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
        · exact ⟨D.host.g 1, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
      · exact ⟨D.host.pde, by simp [GlobalTheory.HeightCounting.lowAll], h5⟩
    · exact ⟨D.host.pde', by simp [GlobalTheory.HeightCounting.lowAll], h4⟩
  · have hle : (GlobalTheory.ToricDenom.below Z.w0).asIdeal ≤ (GlobalTheory.ToricDenom.below P).asIdeal :=
      Ideal.le_of_dvd h
    have heq : (GlobalTheory.ToricDenom.below Z.w0).asIdeal = (GlobalTheory.ToricDenom.below P).asIdeal :=
      ((GlobalTheory.ToricDenom.below Z.w0).isMaximal).eq_of_le (GlobalTheory.ToricDenom.below P).isPrime.ne_top hle
    have hw : ((Z.q0 : ℕ) : 𝓞 D.host.E) ∈ Z.w0.asIdeal := hZ.places.referencePlaceOverPrime
    have hb : ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below Z.w0).asIdeal := by
      show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ Z.w0.asIdeal
      simpa using hw
    rw [heq] at hb
    refine ⟨Z.q0, ?_, key _ hb⟩
    rw [hq]
    simp [GlobalTheory.HeightCounting.lowAll, lowPr]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def nTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) :
    NStage B w.C (P.q.W x.o.η x.o.hη) :=
  { x.o.N with ntw := N.tw, nexp := N.ex, nStage_trivialCharacter_coeff_eq := N.h0, nth := N.th, ntwbr := N.br, ntwbr_ind := N.hbr }

def oTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : P.q.Over := ⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩

theorem dof_oTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : (w.st (oTw x N).Z).toD7 = N.toD7 := rfl

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbeddingFixedFieldOfLeComplexImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_embedding_fixedField_of_le_complexImage : ∀ (s : Stages) (M : IntermediateField ℚ ℂ), M ≤ s.B.fixedCoefficientFieldInComplex → ∃ j : M →+* s.toD7.LL0, (embLL0 s.toD7).comp j = M.val.toRingHom := by
  intro s M hle
  let e := IntermediateField.equivMap s.B.LL0 s.B.embLL.toRatAlgHom
  refine ⟨(e.symm.toAlgHom.toRingHom).comp (IntermediateField.inclusion hle).toRingHom, ?_⟩
  ext x
  show s.B.embLL ((e.symm ⟨x.1, hle x.2⟩ : s.B.LL0) : _) = x.1
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x.1, hle x.2⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothRefinementPolyFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

theorem resolution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ Subordinate H.bar q φ' φ := by
  intro E _ _ _ H q φ lab hD hP hT hL hS
  suffices key : ∀ n : ℕ, ∀ φ lab : InvFun (𝓞 E), maxMult H.bar q φ = n → IsPolyFan H.bar q φ → IsTwInv H φ →
      IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧
        IsTwInv H φ' ∧ Subordinate H.bar q φ' φ by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (_root_.GlobalTheory.PolFan.maxMult_lt_top E H q φ hP).ne
    exact key n φ lab hn.symm hP hT hL hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ lab hn hP hT hL hS
    by_cases h2 : 2 ≤ maxMult H.bar q φ
    · obtain ⟨φ', lab', hP', hT', hL', hS', hsub, hlt⟩ :=
        _root_.GlobalTheory.PolFan.exists_round_lt_maxMult E H q φ lab hD hP hT hL hS (hn ▸ ENat.coe_lt_top n) h2
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (hlt.trans_le le_top).ne
      have hkn : k < n := by
        rw [← hk, hn] at hlt; exact_mod_cast hlt
      obtain ⟨φ'', h1, h2, h3, h4⟩ := ih k hkn φ' lab' hk.symm hP' hT' hL' hS'
      exact ⟨φ'', h1, h2, h3, h4.trans hsub⟩
    · have hle : maxMult H.bar q φ ≤ 1 := by
        rw [hn] at h2 ⊢
        have : ¬ 2 ≤ n := fun h => h2 (by exact_mod_cast h)
        exact_mod_cast (show n ≤ 1 by omega)
      obtain ⟨h1, h2⟩ := _root_.GlobalTheory.PolFan.smoothEnd E H q φ lab hD hP hS hle
      exact ⟨φ, h1, h2, hT, Subordinate.refl φ⟩

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStepStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicityLift_lastChainStep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.chain_ωX → R.chain_vX → R.chain_ptX → R.chain_ItX → ∃ io, ({ R with ioX := io } : RealDat D A Ks).chain_ioX := by
  first | exact @GlobalTheory.DefLift.exists_lift_last | exact GlobalTheory.DefLift.exists_lift_last | (intros; apply GlobalTheory.DefLift.exists_lift_last <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalSubfieldComplexFinitelyGenerate
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.finDimSubfield_finGen : ∀ (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ Lf : IntermediateField ℚ ℂ, (↑S : Set ℂ) ⊆ Lf → M ≤ Lf := by
  intro M hM
  classical
  let b := Module.finBasis ℚ M
  refine ⟨Finset.univ.image (fun i => ((b i : M) : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    have : IsIntegral ℚ (b i) := Algebra.IsIntegral.isIntegral _
    exact (this.map M.val).isAlgebraic
  · intro Lf hS x hx
    have hb : ∀ i, ((b i : M) : ℂ) ∈ Lf := fun i =>
      hS (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hx' : (⟨x, hx⟩ : M) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
    have : x = ((∑ i, (b.repr ⟨x, hx⟩ i) • b i : M) : ℂ) := by rw [← hx']
    rw [this, IntermediateField.coe_sum]
    simp only [IntermediateField.coe_smul]
    exact Lf.sum_mem fun i _ => Lf.smul_mem (hb i)
end

