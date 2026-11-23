module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0613
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LawStep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceUnitaryPointMemHeckeClosure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCartanGen

open Formalism.UG

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

def dg : (Fin n → (v.adicCompletion F)ˣ) →* GL (Fin n) (v.adicCompletion F) :=
  (Units.map (Matrix.diagonalRingHom (Fin n) (v.adicCompletion F)).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

theorem dg_val (u : Fin n → (v.adicCompletion F)ˣ) :
    (dg u).1 = Matrix.diagonal fun i => (u i : v.adicCompletion F) := rfl

def heckeL (ϖ : v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F)) :=
  {x | ∃ k : ℕ, (∀ i j, x.1 i j ∈ Ov F v) ∧ (∀ i j, ϖ * (x⁻¹).1 i j ∈ Ov F v) ∧
    Valued.v x.1.det = Valued.v ϖ ^ k}

theorem single_mem {ϖ : v.adicCompletion F} (h0 : ϖ ≠ 0) (hϖO : ϖ ∈ Ov F v) (i : Fin n) :
    dg (Pi.mulSingle i (Units.mk0 ϖ h0)) ∈ heckeL (n := n) ϖ := by
  classical
  refine ⟨1, fun a b => ?_, fun a b => ?_, ?_⟩
  · rw [dg_val, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [Pi.mulSingle_apply]
      split_ifs
      · simpa using hϖO
      · simpa using one_mem (Ov F v)
    · exact zero_mem _
  · rw [← map_inv, dg_val, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [Pi.inv_apply, Pi.mulSingle_apply]
      split_ifs
      · simpa [h0] using one_mem (Ov F v)
      · simpa using hϖO
    · rw [mul_zero]; exact zero_mem _
  · rw [dg_val, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_pi_mulSingle']
    simp

theorem local_closure {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ Ov F v)
    (g : GL (Fin n) (v.adicCompletion F)) :
    g ∈ Submonoid.closure ((GLint (Fin n) (Ov F v) : Set (GL (Fin n) (v.adicCompletion F))) ∪ heckeL ϖ ∪
      {x | x⁻¹ ∈ heckeL ϖ}) := by
  classical
  have h0 : ϖ ≠ 0 := (GlobalTheory.SplitPlace.unif_facts hϖ).1
  set S := ((GLint (Fin n) (Ov F v) : Set (GL (Fin n) (v.adicCompletion F))) ∪ heckeL ϖ ∪
      {x | x⁻¹ ∈ heckeL ϖ}) with hS
  set M := (Submonoid.closure S).comap (dg (v := v) (n := n)) with hM
  have hz : ∀ i (z : ℤ), Pi.mulSingle i (Units.mk0 ϖ h0 ^ z) ∈ M := by
    intro i z
    have hmz := map_zpow (MonoidHom.mulSingle (fun _ : Fin n => (v.adicCompletion F)ˣ) i) (Units.mk0 ϖ h0) z
    simp only [MonoidHom.mulSingle_apply] at hmz
    rw [hmz]
    have m1 : Pi.mulSingle i (Units.mk0 ϖ h0) ∈ M :=
      Submonoid.subset_closure (Or.inl (Or.inr (single_mem h0 hϖO i)))
    have m2 : (Pi.mulSingle i (Units.mk0 ϖ h0))⁻¹ ∈ M := by
      refine Submonoid.subset_closure (Or.inr ?_)
      change (dg _)⁻¹ ∈ heckeL ϖ
      rw [map_inv, inv_inv]
      exact single_mem h0 hϖO i
    rcases z with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact pow_mem m1 m
    · rw [zpow_negSucc, ← inv_pow]; exact pow_mem m2 _
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ g
  have hu : (fun i => Units.mk0 ϖ h0 ^ a i) ∈ M := by
    rw [← Finset.univ_prod_mulSingle (fun i => Units.mk0 ϖ h0 ^ a i)]
    exact Submonoid.prod_mem M fun i _ => hz i (a i)
  have hg : g = k₁ * dg (fun i => Units.mk0 ϖ h0 ^ a i) * k₂ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, dg_val, e]
    congr 2
    simp [diagPow, Units.val_zpow_eq_zpow_val]
  rw [hg]
  exact mul_mem (mul_mem (Submonoid.subset_closure (Or.inl (Or.inl hk₁))) hu)
    (Submonoid.subset_closure (Or.inl (Or.inl hk₂)))

end Local

end GlobalTheory.SplitCartanGen

namespace GlobalTheory.SplitCartanGen

open Formalism.UG GlobalTheory.SplitPlace

theorem supp_mem_closure : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal →
    ϖ ∉ P.asIdeal ^ 2 → ∀ h ∈ GfC V, Formalism.L2.Theta.SuppAt e V h →
      h ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) := by
  intro D V P e ϖ he hP hP2 h _ hs
  classical
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1.1 h2 h3 h4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  obtain ⟨hex, hinj⟩ := comp_bij (V := V) (B := B) he.1 h1 h2
  have hK := fun g => K_iff (g := g) he.1 h2 h3 hB
  have hu := isUnif he h4 h5 ϖ hP hP2
  have hH := hecke_iff he.1 h1 h2 h3 h4 hB (unif_facts hu).1
  have hloc := local_closure hu (unif_facts hu).2 (comp V π B h)
  have s1 : Formalism.L2.Theta.SuppAt e V 1 := by
    rw [suppAt_iff, mt_one, sub_self, smul_zero]
  suffices key : ∀ a ∈ Submonoid.closure ((GLint (Fin V.rank) (Ov D.host.F v) : Set (GL (Fin V.rank) (Fv D.host.F v))) ∪
      heckeL (π (finPart D (incA D (ϖ : D.host.E)))) ∪ {x | x⁻¹ ∈ heckeL (π (finPart D (incA D (ϖ : D.host.E))))}),
      ∀ g, Formalism.L2.Theta.SuppAt e V g → comp V π B g = a → g ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) from key _ hloc h hs rfl
  intro a ha
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
    intro g hg hgx
    apply Submonoid.subset_closure
    rcases hx with (hx | ⟨k, hx⟩) | ⟨k, hx⟩
    · exact Or.inl (Or.inl ⟨(hK g hg).2 (hgx ▸ hx), hg⟩)
    · exact Or.inl (Or.inr ⟨k, (hH k g).2 ⟨hg, hgx ▸ hx⟩⟩)
    · refine Or.inr ⟨k, (hH k g⁻¹).2 ⟨suppAt_inv hg, ?_⟩⟩
      rw [map_inv, hgx]
      exact hx
  | one =>
    intro g hg hg1
    have : g = 1 := hinj _ _ hg s1 (by rw [hg1, map_one])
    rw [this]
    exact one_mem _
  | mul x y _ _ ihx ihy =>
    intro g hg hgxy
    obtain ⟨gx, sx, rfl⟩ := hex x
    obtain ⟨gy, sy, rfl⟩ := hex y
    have : g = gx * gy := hinj _ _ hg (suppAt_mul sx sy) (by rw [hgxy, map_mul])
    rw [this]
    exact mul_mem (ihx gx sx rfl) (ihy gy sy rfl)

end GlobalTheory.SplitCartanGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G}

abbrev pLine (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem pLine_gram : (pLine D).gram = antiDiagonalSignGramMatrix 1 (1 : D.host.E) := by
  refine Matrix.ext fun i j => ?_
  have e : ∀ a b : Fin 1, (Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram a b = 1 :=
    fun a b => by rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim a b]; simp [Examples₂.sgn]
  exact (e i j).trans (by simp [antiDiagonalSignGramMatrix]; exact ⟨Fin.val_eq_zero i, Fin.val_eq_zero j⟩)

def topOrth : OrthDec (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) (pLine D) where
  iA := frameMat _ _ G.sp.topDec.ι
  iB := G.sp.topDec.a
  isoA := frameMat_isom G.sp.topDec
  isoB := G.sp.topDec.gram.trans pLine_gram.symm
  orth := perp_sub' G.sp.topDec id
  rank_add := G.sp.topDec.rank

def topOrthAt {n : ℕ} (h : D.R.m = n) : OrthDec (G.V (.top n)) (G.V (.grid D.R.m D.R.m)) (pLine D) :=
  Eq.rec (motive := fun k _ => OrthDec (G.V (.top k)) (G.V (.grid D.R.m D.R.m)) (pLine D)) (topOrth G) h

def topEmb {n : ℕ} (h : D.R.m = n) : GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top n)) :=
  Eq.rec (motive := fun k _ => GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top k))) (stabilizerEmbedding G.sp.topDec) h

def lastTau : Matrix (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) (Fin (pLine D).rank) D.host.E := Matrix.of fun _ _ => -D.host.xi0

variable {G t}

def lastDat (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) :
    WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ :=
  GlobalTheory.FinPl.lastBi (besAt G hM j 0 hj vN).o (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau
    (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁))
    (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w))

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G}

theorem topOrth_emb (h : GA D (G.V (.grid D.R.m D.R.m))) : (topOrth G).emb (h, 1) = stabilizerEmbedding G.sp.topDec h :=
  (embRel_iff G.sp.topDec h _).1 ((topOrth G).embRel_left G.sp.topDec.ι rfl h)

variable {G t}

noncomputable def colPer (hM : M.Is t) : (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) →
    (chainFrom G Wl t hM σ j hj vN).Data → Fn G (.grid D.R.m D.R.m) → (GA D (G.V (.top j)) → ℂ) →
    GA D (G.V (.grid D.R.m j)) → (chainFrom G Wl t hM σ j hj vN).Var → ℂ
  | 0, j, hj, vN, Φ, F, φ, g, _ =>
    ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
      (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
      (lastDat Wl hM j hj vN g Φ.1 Φ.2) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
  | σ + 1, j, hj, vN, Φ, F, φ, g, h =>
    colPer hM σ (j + 1 + 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some Φ.2.2 F
      (GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (contr (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (G.V (.top (j + 1)))
          ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
          (flatBF (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega)) (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
            ((stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))).om
              (g, h.1) Φ.1))
          (flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (B := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega)))
            ((stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega))).om (h.1, h.2.1) Φ.2.1))))
      h.2.1 h.2.2

end GlobalTheory.RowChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopPairSourceCharProdLocalIdeles
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem chrS_top_prod_locIdele : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}, L.Is μ₀ →
    ∀ (j : ℕ), j + 1 < D.R.m → ∀ y : ∀ w : locPl G t, (Kw w.1)ˣ,
    ((G.chrS (.top t j) (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (y w) : ℂˣ) : ℂ) := by
  intro D T L sc G t μ₀ hL j hj y
  have hrank : (G.pS (.top t j)).rank = rankX D j :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).rank
  have hchr : G.chrS (.top t j) = L.mu t (j + 1) := by
    rw [GridData.chrS, hrank]
    simp [Formalism.IndefR.Lift.attChr, GridData.chr, Nat.not_odd_iff_even.2 (even_rankX D j)]
  have hE : ChrEq (L.mu t (j + 1)) (muBase L (j + 1) * L.xiH t) := by
    have h1 : muBase L (j + 1) = L.C.mu0 ⟨j, by omega⟩ := dif_pos (by omega)
    rw [h1]
    exact GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 ⟨j, by omega⟩) (hL.xi t)
  rw [hchr, map_prod]
  rw [show ∀ (s : Finset (locPl G t)) (f : locPl G t → Circle), ((∏ w ∈ s, f w : Circle) : ℂ) = ∏ w ∈ s, (f w : ℂ) from
    fun s f => map_prod Circle.coeHom f s]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact congrArg (fun f => ((f (y w) : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w.1)

end GlobalTheory.TopLevelInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedConjugateFixesStandardVacuumTopPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
noncomputable section

namespace GlobalTheory.TopLevelInv

section Unr

variable {D : D7}

theorem unrOff_mul' {e : AE D} {χ χ' : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ)
    (h' : Formalism.IndefR.Fin.UnrOff e χ') : Formalism.IndefR.Fin.UnrOff e (χ * χ') :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, one_mul]

theorem unrOff_inv' {e : AE D} {χ : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ) :
    Formalism.IndefR.Fin.UnrOff e χ⁻¹ :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

theorem pg_near_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    {PP : Pl D.host.E} (h : PP ∈ L.Pg) : ∃ w ∈ locPl G t, PP = w ∨ PP = GlobalTheory.IdemSupport.cP w := by
  classical
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  have hm := GlobalTheory.LevelRamif.typePrime_mem hk
  set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hv
  have hvk : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  have hS1 : v ∈ S1 D := by
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hvk
    · exact Or.inr (Or.inl hvk)
  have hS0 : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)
  refine ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hS0), ?_⟩
  exact GlobalTheory.IdemSupport.eq_or_eq_cP (by rw [G.pl.under_w hS0])

theorem conjPrime_conjPrime₂ (P : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO])

theorem unrOff_mu_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}
    (hL : L.Is μ₀) (j : Fin D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    Formalism.IndefR.Fin.UnrOff e (L.mu t ((j : ℕ) + 1)) ∧ Formalism.IndefR.Fin.UnrOff e L.eta := by
  classical
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ hL t j
  have hmu : Formalism.IndefR.Fin.UnrOff e (L.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.mu0 j) he fun PP' h1 h2 => by
      refine h4 PP' (fun h => ?_) fun PP h h' => ?_
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        rcases hw' with rfl | rfl
        · exact h1 hw
        · exact h2 w hw ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        have e1 := (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h'
        rcases hw' with rfl | rfl
        · exact h2 PP hw h'
        · rw [conjPrime_conjPrime₂] at e1
          exact h1 (e1 ▸ hw)
  have hxi : Formalism.IndefR.Fin.UnrOff e (L.xi t) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.xi t) he fun PP' h1 h2 => by
      by_contra hn
      rcases (hL.Q_ram t PP').1 hn with h | ⟨PP, h, h'⟩
      · exact h1 (Finset.mem_union_right _ h)
      · exact h2 PP (Finset.mem_union_right _ h) h'
  exact ⟨unrOff_mul' hmu hxi, GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e hL.eta he fun PP' _ _ => L.C.isEta.unr PP'⟩

end Unr


set_option maxHeartbeats 1000000 in
theorem vacFix_conjPt_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ e : AE D, IsIdemSum e (locPl G t) → ∀ ε : AF D.host.F, IsIdempotentElem ε →
    algebraMap (AF D.host.F) (AE D) ε = e + cA D e →
    W.om (.top t j) (1, resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) (S.Z.vac (.top t j)) =
      S.Z.vac (.top t j) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he ε hε halg
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hdS : DefNode D.R.m (.top j) := by show j ≤ D.R.m; omega
  have hdT : DefNode D.R.m (.top (j + 1)) := by show j + 1 ≤ D.R.m; omega
  have hS := S.N.selfDual (X := .top j) hdS
  have hT := S.N.selfDual (X := .top (j + 1)) hdT
  have hfS := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top j))) (G.Λ (.top j)) (S.βp j)
    (Lev.finE (G.V (.top j)) (S.N.u (.top j)).1) (S.βp_is j hdS) (S.N.u_lat _ hdS)
  have hfT := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top (j + 1)))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hdT) (S.N.u_lat _ hdT)
  have hrkS : (G.V (.top j)).rank = rankX D j := (G.isV (X := .top j) hdS fun _ e => by cases e).rank
  have hrkT : (G.V (.top (j + 1))).rank = rankX D (j + 1) := (G.isV (X := .top (j + 1)) hdT fun _ e => by cases e).rank
  have hrk : (G.V (.top j)).rank ≠ (G.V (.top (j + 1))).rank := by
    intro h
    rw [hrkS, hrkT] at h
    simp only [rankX, add_mul, one_mul] at h
    omega
  have hev : Even (G.V (.top j)).rank := hrkS ▸ even_rankX D j
  obtain ⟨hμ, hη⟩ := unrOff_mu_locPl G hL ⟨j, by omega⟩ he
  have hatt : ∀ n, Formalism.IndefR.Fin.UnrOff e (Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta n) := by
    intro n
    unfold Formalism.IndefR.Lift.attChr
    split_ifs
    · exact unrOff_mul' hμ (unrOff_inv' hη)
    · exact hμ
  have hn : ∃ (μ : Measure (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (𝓕 : Set (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))),
      IsCovolOne (ratL (G.pT (.top t j : Pair T)) (G.pS (.top t j : Pair T))) μ 𝓕 ∧
        nrm2 μ 𝓕 (S.Z.vac (.top t j)) = 1 := by
    obtain ⟨⟨p, hp⟩, hall⟩ := hv.2.norm
    exact ⟨p.1, p.2, hp, hall p hp⟩

  have hf := GlobalTheory.ExpansionInvariance.idem_conj_sum (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2
  have h2 := GlobalTheory.ExpansionInvariance.idem_compl hf
  have hcut : resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k) =
      GlobalTheory.ExpansionInvariance.cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) (conjPt S j k) := by
    apply Formalism.IndefR.Fin.LevelGroupLemmas.gaExt
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG _ hε', GlobalTheory.ExpansionInvariance.mt_cutPart h2.1 h2.2, map_sub, map_one, halg]
    unfold Formalism.IndefR.Fin.LevelGroupLemmas.resM
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hSt : Lev.finE (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) ∈
      St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) := by
    have hk2 : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) (fun w => topRank_eq G t w hj.le)
        (fun w => (S.term t Φ β w).pr _ j.succ_pos hj) := hk
    rw [hcut]
    exact GlobalTheory.OffPartLattice.finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1))
      (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (finG (G.V (.top (j + 1))) k) (conjPt S j k)
      (by simp only [conjPt, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; rfl) he (fun Q hQ => by
        have h3 := (Subgroup.mem_inf.1 hk2).2
        rw [Subgroup.mem_iInf] at h3
        have h4 := h3 Q
        rw [Subgroup.mem_iInf] at h4
        exact Subgroup.mem_comap.1 (h4 hQ))
  have hP : ∀ a b, (e + cA D e) * (mt (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) - 1) a b = 0 := by
    intro a b
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG_sub hε' _ a b, ← mul_assoc, map_sub, map_one, halg]
    have h0 : (e + cA D e) * (1 - (e + cA D e)) = 0 := by
      linear_combination (-1 : AE D) * hf.1
    rw [h0, zero_mul]
  exact Formalism.IndefR.Fin.LevelGroupLemmas.vacFixOff (Formalism.IndefR.Fin.splitLinF D) (Formalism.IndefR.Fin.placeModelAtF D)
    (Formalism.IndefR.Fin.splitOrInert D) W.ψ _ _ _ _ _ hW (GlobalTheory.InertAll.inertAllO D _ _ _ _ _ _ hW) hrk (Or.inl hev) _ _ hS hT _ _
    hfS hfT (locPl G t) e he (hatt _) (hatt _) _ hv.2.theta hv.2.lat hn 1 _ (one_mem _)
    (Formalism.IndefR.Fin.LevelGroupLemmas.resG_mem_GfC _ hε' (SetLike.coe_mem _)) (by rw [map_one]; exact one_mem _) hSt
    (fun a b => by rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', sub_self, Matrix.zero_apply, mul_zero]) hP

end GlobalTheory.TopLevelInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSelfDualLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_self_dual_lattices : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F F' : WO S T → ℂ,
    GlobalTheory.MovedAlg.IsAlgComb ψ S T v F → GlobalTheory.MovedAlg.IsAlgComb ψ S T v F' → IsAlgebraic ℚ (GlobalTheory.RawLift.thetaIP μ 𝓕 F F') := by
  first | exact @GlobalTheory.AlgPair.thetaIP_algComb | exact GlobalTheory.AlgPair.thetaIP_algComb | (intros; apply GlobalTheory.AlgPair.thetaIP_algComb <;> assumption)
end

