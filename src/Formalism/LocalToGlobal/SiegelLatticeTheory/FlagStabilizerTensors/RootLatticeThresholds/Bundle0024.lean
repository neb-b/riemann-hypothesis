module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0013
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0039

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GammaFixedOfHypotheses
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.LoopTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1e

variable {D : D7} {X : HidaSetting D}

theorem gamma_one_eq_prod (Y : Full X) (u u' : D.what₂.Word) :
    (Y.tO u u').Gam1 = ∏ v, ((Fintype.card (GL (Fin D.R.k) (Y.TR.Fq v)) : ℝ) /
      (Formalism.L2.SG.GGMirabolic.cardU (Y.TR.Fq v) D.R.k : ℝ)) := by
  have h1 : Formalism.L2.SG.GGMirabolic.gamProd Y.TR.psi0 (1 : Iof Y.TR) =
      ((∏ v, ((Fintype.card (GL (Fin D.R.k) (Y.TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (Y.TR.Fq v) D.R.k : ℝ)) : ℝ) : ℂ) := by
    simp only [Formalism.L2.SG.GGMirabolic.gamProd, Pi.one_apply, Formalism.L2.SG.GGMirabolic.gam_one]
    push_cast
    rfl
  show (Formalism.L2.SG.GGMirabolic.gamProd Y.TR.psi0 (1 : Iof Y.TR)).re = _
  rw [h1, Complex.ofReal_re]

theorem card_gl_div_unipotent (K : Type) [Field K] [Fintype K] (k : ℕ) :
    (Fintype.card (GL (Fin k) K) : ℝ) / (Formalism.L2.SG.GGMirabolic.cardU K k : ℝ) =
      ∏ i ∈ Finset.Icc 1 k, ((Fintype.card K : ℝ) ^ i - 1) := by
  have hU : Formalism.L2.SG.GGMirabolic.cardU K k = Nat.card (Formalism.DoubleCosetMeasures.upUniG K k) := by
    unfold Formalism.L2.SG.GGMirabolic.cardU
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    show Formalism.L2.SG.GGMirabolic.IsUni k x ↔ Formalism.DoubleCosetMeasures.IsUpUni (x : Matrix (Fin k) (Fin k) K)
    constructor
    · intro h
      refine ⟨?_, h.1⟩
      intro i j hij
      exact h.2 i j hij
    · intro h
      refine ⟨h.2, ?_⟩
      intro i j hij
      exact h.1 hij
  have hG := Formalism.FourierDecayAlt.P.gamma_factor_product K k
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  have hpos : 0 < Nat.card (Formalism.DoubleCosetMeasures.upUniG K k) := Nat.card_pos
  rw [hU, ← Nat.card_eq_fintype_card, hG, Nat.cast_mul, mul_div_cancel_left₀ _ (by exact_mod_cast hpos.ne'),
    Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one]

theorem GamPin_of_split (Y : Full X) (h0 : Formalism.MainNotions.S.SplitsE D (D.host.g 0)) (h1 : Formalism.MainNotions.S.SplitsE D (D.host.g 1)) :
    GamPin Y := by
  intro u u'
  rw [gamma_one_eq_prod, Formalism.MainNotions.BridgeLemma.gaG_eq D h0 h1]
  simp_rw [card_gl_div_unipotent]
  rw [Formalism.L2.SG.Pf.SatGram.prod_two (fun v => Fintype.card (Y.TR.Fq v)) (D.host.g 0) (D.host.g 1) D.host.g_ne
    (fun v => Y.TR.card_q v) (fun n : ℕ => ∏ i ∈ Finset.Icc 1 D.R.k, ((n : ℝ) ^ i - 1)),
    Formalism.L2.SG.Pf.typed_count_holds X Y.TR 0, Formalism.L2.SG.Pf.typed_count_holds X Y.TR 1,
    Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F]

theorem GamPin_of_data (Y : Full X) {C0 : ℝ} (h : StandingNumericalData D C0) : GamPin Y :=
  GamPin_of_split Y h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1

theorem gammaFixed_of_hypotheses (Y : Full X) {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h : Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) : GamPin Y :=
  GamPin_of_data Y h.2.1

end ZsC1e

end Formalism.L2.SG.LoopTieOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KerSideCut
section
noncomputable section

open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.ProjRows Formalism.L2.SG.KerJoinS Formalism.IndefR.Cx Formalism.L2.Indef

namespace Formalism.L2.SG.KerSideCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Chain

theorem chainOpM_add' {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (f g : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (f + g) = Formalism.ThetaLiftIndependence.chainOpM w Km m f + Formalism.ThetaLiftIndependence.chainOpM w Km m g := by
  induction m with
  | zero => first | rfl | simp [Formalism.ThetaLiftIndependence.chainOpM]
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext t
    simp [Formalism.ThetaLiftIndependence.kerOpM, Finset.sum_add_distrib, smul_add, map_add (f := _)]

theorem chainOpM_smul' {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (c : Rg) (f : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f) = c • Formalism.ThetaLiftIndependence.chainOpM w Km m f := by
  induction m with
  | zero => first | rfl | simp [Formalism.ThetaLiftIndependence.chainOpM]
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext t
    simp [Formalism.ThetaLiftIndependence.kerOpM, Finset.smul_sum, map_smul, smul_smul, mul_comm]

def colL {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) :
    (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls R.m → C.Y R.m → ℂ) where
  toFun := C.col
  map_add' f g := chainOpM_add' (ι := C.cls) (M := fun j => C.Y j → ℂ) C.wt C.Kmap R.m f g
  map_smul' c f := chainOpM_smul' (ι := C.cls) (M := fun j => C.Y j → ℂ) C.wt C.Kmap R.m c f

def perColL (D : D7) (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] D.what₂.Amb D.what₂.mu0 →ₗ[ℂ] ℂ :=
  ((D.mem u).P.period ∘ₗ (D.mem u).P.lowerMap ∘ₗ (D.mem u).P.evz ∘ₗ colL (D.mem u).C ∘ₗ
    (D.mem u).A.Mram.subtype ∘ₗ (D.eMu u).toLinearMap).compl₂ (D.eMt u).symm.toLinearMap

theorem perColL_apply (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (F : D.what₂.Amb D.what₂.mu0) :
    perColL D u φ F = D.what₂.perCol u D.what₂.mu0 φ F := by
  rw [D.perCol_base_eq_PtilCol]
  simp only [perColL, LinearMap.compl₂_apply, LinearMap.comp_apply, PeriodMap.PtilCol, PeriodMap.Ptil]
  rfl

end Chain

section Read

variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₗ[ℂ] P.EE)

def GoodPartHasComplexCoordinates : Prop := D.what₂.V0 D.what₂.mu0 ≤ LinearMap.range cF

end Read

end Formalism.L2.SG.KerSideCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsFinal
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf

namespace Formalism.L2.SG.LoopsFinal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section admitted

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)

variable (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)

end admitted

section AtOne

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))
  (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A)

theorem jtPin_of (hA : AmpFibreConst Y) : JtPin hF hI (termTieOf W hI H A hV) := by
  intro u u' t s hs
  have h : ∃ s' : TT Y u u', s'.toTerm = tc hI t := ⟨s, hs⟩
  show hsNormSq (JtOf hI t) = ampL s ^ 2
  unfold JtOf
  rw [dite_eq_left h, ← Formalism.L2.SG.PackageTie.norm_hsEmb_sq]
  have e := hA u u' (tc hI t) ⟨h.choose, h.choose_spec⟩ ⟨s, hs⟩
  unfold ampL at e ⊢
  rw [e]

def FrameChangeAt : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)),
    (∀ a b, b < a → ξ a b = 0) → (∀ a, ξ a a = 1) →
      ∃ m ∈ NLam (lamOf W hI t) (fl'Of W hI t), ∀ b, m (frame (fl'Of W hI t) b) = frameAct (frame (fl'Of W hI t)) ξ b

theorem frameEqvInj_of (hFC : FrameChangeAt W hI) (u u' : D.what₂.Word) :
    FrameEqvInj (termTieOf W hI H A hV) (u' := u') (FlagOfWord W u) := by
  intro t t' hL hE
  obtain ⟨n, hn, ξ, hl, hd, hfr⟩ := hE
  obtain ⟨m, hm, hmf⟩ := hFC u u' t ξ hl hd
  refine term_injC W hI t t' hL ⟨n, hn, m, hm, fun b => ?_⟩
  have e1 : frame (fl'Of W hI t') b = frameAct (fun a => n (frame (fl'Of W hI t) a)) ξ b := congrFun hfr b
  rw [e1, hmf b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [frameAct, map_sum, map_smul]

end AtOne

section Ev

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
  (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (At x hx i))

end Ev

section Summ

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (sOf hF)}


end Summ

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (sOf (hF x hx i)))
  (W : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i))
  (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W x hx i) (hI x hx i))
  (A : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i))
  (hV : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W x hx i) (hI x hx i) (A x hx i))

def AtF : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i) :=
  fun x hx i => termTieOf (W x hx i) (hI x hx i) (H x hx i) (A x hx i) (hV x hx i)

variable (hFC : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FrameChangeAt (W x hx i) (hI x hx i))
  (B : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' C1)
  (M : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTermDat (Fm.D x i) (Fm.L x i) (AtF Fm X Y hF hI W H A hV x hx i) u u' C1 (B x hx i u u'))

variable (hAF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpFibreConst (Y x hx i))
  (hRF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.L2.SG.Pf.FibreCounting.RowFree (Y x hx i))
  (gam : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), GamPin (Y x hx i))

end Fam

section Closed

def NormTieC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    BridgeLemma₂.wordPairNormRelation (termTieOf W hI H A hV) u u'

def GramDeterminantCount : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    @Formalism.MainNotions.BridgeLemma.LatticeDeterminantFactorization D (termTieOf W hI H A hV) u u'

def EntryLatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    BridgeLemma₂.wordPairEntriesInLattice (termTieOf W hI H A hV) u u'

def FrameChangeC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X), FrameChangeAt W hI

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (sOf (hF x hx i)))
  (W : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i))
  (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W x hx i) (hI x hx i))
  (A : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i))
  (hV : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W x hx i) (hI x hx i) (A x hx i))

end Closed

end Formalism.L2.SG.LoopsFinal
end
end

