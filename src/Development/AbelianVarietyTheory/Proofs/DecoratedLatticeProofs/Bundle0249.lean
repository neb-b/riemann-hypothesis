module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdPlaces
section
noncomputable section

open Formalism.BasicNotions IsDedekindDomain NumberField Matrix Formalism.L2.DIV Formalism.IndefR.Lev GlobalTheory.StdFrames GlobalTheory.AdIsom
open scoped TensorProduct

namespace GlobalTheory.LevNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

@[reducible] def kField {E : Type} [Field E] [NumberField E] (Q : Pl E) : Field (kP Q) :=
  haveI := Q.isMaximal
  Ideal.Quotient.field Q.asIdeal

attribute [local instance] kField

def adPlaces (D : D7) : PlaceSys (EAf D) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Pl D.host.E) (fun Q => kP Q)
    (fun Q => resS D.host.F Q) where
  K Q := Q.adicCompletion D.host.E
  O Q := Q.adicCompletionIntegers D.host.E
  p Q := cpt Q
  e Q := idem Q
  surj Q x := by
    classical
    obtain ⟨z, hz⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
      (⟨Pi.single Q x, by
        refine Filter.mem_of_superset (Set.finite_singleton Q).compl_mem_cofinite fun Q' h => ?_
        show (Pi.single Q x : ∀ v : Pl D.host.E, v.adicCompletion D.host.E) Q' ∈ Q'.adicCompletionIntegers D.host.E
        rw [Pi.single_eq_of_ne h]
        exact zero_mem _⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    refine ⟨z, ?_⟩
    change toAd D z Q = _
    rw [hz]
    exact Pi.single_eq_same (M := fun v : Pl D.host.E => v.adicCompletion D.host.E) Q x
  e_self Q := ((isPlIdem_iff Q _).1 (isPlIdem_idem Q)).1
  e_ne Q := ((isPlIdem_iff Q _).1 (isPlIdem_idem Q)).2
  ext a h := cpt_ext fun Q => by rw [h Q, map_zero]
  int a := mem_OA a
  fin a := Filter.eventually_cofinite.1 (toAd D a).2
  r_surj Q y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, resS_oToS Q x⟩
  r_ker Q s := (resS_eq_zero_iff_cpt Q s).trans
    ((Valuation.isEquiv_valuation_valuationSubring Valued.v).lt_one_iff_lt_one)

end GlobalTheory.LevNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpQNotEqAmpG
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem ampQ_not_eq_ampG {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ Not L = ampG L := by
  funext d
  unfold ampQ ampG
  rw [Finset.sum_eq_single_of_mem ∅ (by simp) (fun A hA h => absurd (by simp at hA; exact hA.2) h)]
  simp

private theorem hasPt_of_isPt {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS)
    (h : PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ) : HasPt Y u u (Y.tO u u).genSet γ := by
  obtain ⟨c, n, t, ht, hv, -, hp, -⟩ := h
  rw [genT_ngSet] at ht
  exact ⟨t, ht, hv, hp⟩

theorem stepFam1_of : (∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) → Formalism.L2.SG.FamDefs.HTie → FamGen1 → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam → StepFam1 := by
  intro hG6 hH hF hG5 hW hG4 hE Cg cb Cw cT CT C0
  obtain ⟨CSt, hCSt, a4, b4, h4⟩ := hG4 Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH2⟩ := hH Cg cb Cw cT CT C0
  obtain ⟨a5, b5, h5⟩ := hG5 Cg cb Cw cT CT C0
  obtain ⟨aW, bW, hW2⟩ := hW Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE2⟩ := hE Cg cb Cw cT CT C0
  refine ⟨9, CSt, hCSt, max a4 (max aH (max a5 (max aW aE))), max b4 (max bH (max b5 (max bW bE))),
    fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨e1a, e1b, e1c, e1d, e1e⟩ := e1
  obtain ⟨e2a, e2b, e2c, e2d, e2e⟩ := e2
  have hQ := hF D X Y u hc.2.2
  obtain ⟨s, hs1, hs0, hsb, htie⟩ :=
    h4 C' Cl e1a e2a D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  refine ⟨s, hs1, hs0, hsb, fun γ hγ S => ?_⟩
  have hP := hasPt_of_isPt Y u _ _ _ γ hγ
  obtain ⟨Fm, hFT, hRel, hTerm, hDs, hrw⟩ := hE2 C' Cl e1e e2e D large₂ X Y u u hc _ _ _ _ hQ γ hP
  have hG5Fm := Formalism.L2.SG.FamDefs.orbitFamilyIdentity_at_volume hFT (h5 C' Cl e1c e2c D large₂ X Y u u hc _ _ _ _ hQ γ hP Fm hFT)
  obtain ⟨hWpos, hWle⟩ := hW2 C' Cl e1d e2d D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk
    _ _ _ _ hQ γ hP Fm hFT hRel hTerm hG5Fm
  refine ⟨Fm, Formalism.L2.SG.FamDefs.famOKS_of (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ S _ (fun L => ampG L) Fm hFT
    hRel hTerm hDs hrw (hG6 D (Formalism.L2.SG.FamDefs.four_rank_add_seven_le_k hc)) hG5Fm
    (hH2 C' Cl e1b e2b D large₂ X Y u u hc _ _ _ γ Fm hFT) hWpos hWle (fun x _ => ?_)⟩
  have h := htie _ _ _ _ hQ γ hP Fm hFT x.1 x.2
  rw [ampQ_not_eq_ampG] at h
  exact h

end GlobalTheory.Core.One
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaAdjointTauFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem doubleSum_eq_dotProduct_mapMatrix_mulVec {R K : Type*} [CommRing R] {m n : ℕ} (g : R → R) (f : K → R)
    (s : Fin m → R) (G : Matrix (Fin m) (Fin n) K) (v : Fin n → R) :
    (∑ i, ∑ j, g (s i) * f (G i j) * v j) = (fun i => g (s i)) ⬝ᵥ (G.map f *ᵥ v) := by
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem ringHom_conjTranspose_smul_dotProduct_adjoint {R : Type*} [CommRing R] {m n : ℕ} (σ : R →+* R) (c : R)
    (s : Fin m → R) (Y : Matrix (Fin n) (Fin m) R) (G : Matrix (Fin n) (Fin n) R)
    (a : Fin n → R) :
    (fun i => σ (s i)) ⬝ᵥ ((c • ((Y.map σ)ᵀ * G)) *ᵥ a)
      = c * ((fun k => σ ((Y *ᵥ s) k)) ⬝ᵥ (G *ᵥ a)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 2
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vecMul, mulVec, dotProduct, map_sum, map_mul, mul_comm]


set_option maxHeartbeats 2000000 in
theorem kappa_adj : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (x : WO S L') (a : Fin B.L.rank → AE D) (s : Fin S.rank → AE D), (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ a) j) = incA D (-D.host.xi0⁻¹) * ∑ i, ∑ j, cA D ((((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ s) i) * incA D (HSpace.gram B.L i j) * a j := by
  intro D ρ B L' ζ' l S x a s
  simp only [Link.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  have hG : gA S * giA S = 1 := by
    have h := Matrix.mul_nonsing_inv (HSpace.gram S) (gram_isUnit_det S)
    have h2 : (HSpace.gram S * (HSpace.gram S)⁻¹).map (incA D)
        = (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E).map (incA D) := by rw [h]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  rw [doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D) s, doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D)]
  rw [show (HSpace.gram S).map (incA D) = gA S from rfl,
    show (HSpace.gram B.L).map (incA D) = gA B.L from rfl]
  have hG' : ∀ N : Mx D S.rank B.L.rank, HMul.hMul (gA S) (HMul.hMul (giA S) N) = N := by
    intro N
    rw [← Matrix.mul_assoc, hG]
    exact Matrix.one_mul N
  rw [Matrix.mulVec_mulVec, Matrix.mul_smul, hG']
  exact ringHom_conjTranspose_smul_dotProduct_adjoint (cA D) _ s _ _ a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.CapelliLowest

end GlobalTheory.CapelliLowest

namespace GlobalTheory.CapelliLowest

theorem single_comm {N : ℕ} (a b c d : Fin N) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := h2), h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := h1), h1]
  · simp [Matrix.single_mul_single_of_ne (h := h1), Matrix.single_mul_single_of_ne (h := h2), h1, h2]

theorem lie_of_glRel {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (h : Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1))) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    Q X * Q Y - Q Y * Q X = Q (X * Y - Y * X) := by
  refine Matrix.induction_on' X ?_ ?_ ?_
  · simp
  · intro p q hp hq
    have e : (p + q) * Y - Y * (p + q) = (p * Y - Y * p) + (q * Y - Y * q) := by noncomm_ring
    rw [e, map_add (f := _), map_add (f := _), ← hp, ← hq]
    noncomm_ring
  · intro i j x
    refine Matrix.induction_on' Y ?_ ?_ ?_
    · simp
    · intro p q hp hq
      have e : Matrix.single i j x * (p + q) - (p + q) * Matrix.single i j x =
          (Matrix.single i j x * p - p * Matrix.single i j x) + (Matrix.single i j x * q - q * Matrix.single i j x) := by
        noncomm_ring
      rw [e, map_add (f := _), map_add (f := _), ← hp, ← hq]
      noncomm_ring
    · intro k l y
      have hx : Matrix.single i j x = x • Matrix.single i j (1 : ℂ) := by rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have hy : Matrix.single k l y = y • Matrix.single k l (1 : ℂ) := by rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have e : x • Matrix.single i j (1 : ℂ) * (y • Matrix.single k l 1) - y • Matrix.single k l (1 : ℂ) * (x • Matrix.single i j 1)
          = (x * y) • (Matrix.single i j (1 : ℂ) * Matrix.single k l 1 - Matrix.single k l 1 * Matrix.single i j 1) := by
        simp only [smul_mul_smul_comm, mul_comm y x, smul_sub]
      rw [hx, hy, e, single_comm, map_smul, map_smul, map_smul, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x,
        ← smul_sub, h i j k l]
      split_ifs <;> simp

theorem glRel_conj {A : Type} [Ring A] [Algebra ℂ A] (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (g : GL (Fin N) ℂ) (h : Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1))) :
    Formalism.REAL.GlRel (fun i j => Q (g.1 * Matrix.single i j 1 * (g⁻¹).1)) := by
  have HG : (g⁻¹).1 * g.1 = 1 := g.inv_mul
  have key : ∀ X Y : Matrix (Fin N) (Fin N) ℂ, (g.1 * X * (g⁻¹).1) * (g.1 * Y * (g⁻¹).1) = g.1 * (X * Y) * (g⁻¹).1 := by
    intro X Y
    rw [show g.1 * X * (g⁻¹).1 * (g.1 * Y * (g⁻¹).1) = g.1 * X * ((g⁻¹).1 * g.1) * Y * (g⁻¹).1 by simp only [mul_assoc],
      HG, mul_one]
    simp only [mul_assoc]
  intro a b c d
  simp only
  rw [lie_of_glRel Q h, key, key, ← sub_mul, ← mul_sub, single_comm]
  split_ifs <;> simp [mul_sub, sub_mul]

end GlobalTheory.CapelliLowest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionRepresentativeMemPreviousIndexSet
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.RepsAtTwist

theorem exists_rep_flat_ne : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0 := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL hP j c h b g' hg'
  have hm := hL.hm
  have hs := hA.steps
  obtain ⟨al, A₀, B₀, hne⟩ := hL.nonvan j (by omega) b P
  obtain ⟨g, hg, -⟩ := GlobalTheory.TwBridge.Model.isGL_existsUnique (k := k) ι j (c + 1 + 1) (by unfold cOf; omega) (L.h j al P)
  have hSum := GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA
  obtain ⟨A₁, B₁, hAB⟩ := hSum j c h (L.h j al P) (L.h (j + 1) b P) g g' hg hg'
    (hL.boundQ j al P hA.nmem) (hL.boundQ (j + 1) b P hA.nmem) (hL.depthQ' P hA.nmem)
  obtain ⟨e', he'⟩ : ∃ e : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e :=
    GlobalTheory.AtTypeExists.exists_ord.1 R.k R.t j
  obtain ⟨e, he⟩ : ∃ e : XIx (Fin R.k) (Fin R.t) (j + 1) ≃ Fin (R.N (j + 1)), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e :=
    GlobalTheory.AtTypeExists.exists_ord.1 R.k R.t (j + 1)
  obtain ⟨x, hx⟩ := Function.ne_iff.1 (hne (max A₀ A₁) (max B₀ B₁) (le_max_left _ _) (le_max_left _ _))
  have hF := hAB (max A₀ A₁) (max B₀ B₁) (le_max_right _ _) (le_max_right _ _) e' e he' he x
  have hsg : W.sg ≠ 0 := by
    intro h0
    have h2 := GlobalTheory.TwBridge.Model.sg_sq (h := hA) (hok := hc)
    rw [h0] at h2
    norm_num at h2
  refine ⟨al, g, hg, fun h0 => ?_⟩
  have h1 := congrFun h0 (GlobalTheory.SymBridge.toLoc ι e e' x)
  rw [hF, Pi.zero_apply] at h1
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ((map_ne_zero σ₀).2 hx) h1
  · unfold sgn; exact zpow_ne_zero _ hsg
  · unfold sgn; exact zpow_ne_zero _ hsg

end GlobalTheory.RepsAtTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionRepresentativesNormalFormModUnipotent
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge GlobalTheory.LatClass GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

noncomputable section
namespace GlobalTheory.TwNormalReps

theorem val_unif_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (hϖ _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)

theorem isGL_one {X : Fields} {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : X.E →+* k} {j c : ℕ} {g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k}
    (hg : IsGL ι (1 : AutY X R j) g) : g = 1 := by
  obtain ⟨e, -, he⟩ := hg
  apply Units.ext
  rw [he]
  ext i l
  simp [toLoc, Pi.single_apply, e.injective.eq_iff, Matrix.one_apply]

theorem exists_normal_rep : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → (∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0) → ∀ j c (h : j + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1)) k), IsGL ι (L.h j al P) g → ∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j c h (r * g) := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hcst hAt L G hL hIdx hstep
  haveI := hν.1
  have hϖ := val_unif_of W.unif
  have hb : ∀ j c h, latOf ((W.T s R).bas j c h) = latOf 1 := fun _ _ _ => rfl
  have H : (∀ j c h x, (W.T s R).Phi j c h x ≠ 0 → IntM x) ∧
      (∀ j c h x y, MaxM y → (W.T s R).Phi j c h (x + y) = (W.T s R).Phi j c h x) ∧
      ∀ j c h, ((W.T s R).lev j c h).J ≤ KO k _ :=
    GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s _ _ _ _ W.δ W.tame W.η _ _ (fun _ _ _ => rfl)
  obtain ⟨hs, hp, -⟩ := H
  intro j
  induction j with
  | zero =>
    intro c h al g hg
    rw [hL.zero_h] at hg
    obtain rfl := isGL_one hg
    exact ⟨1, one_mem _, by rw [one_mul]; exact normal_one hb c h⟩
  | succ j ih =>
    intro c h al g' hg'
    obtain ⟨al', g, hg, hf⟩ := hstep j c h al g' hg'
    obtain ⟨r, hr, e', z', he', hz', hl⟩ := ih (c + 1) (by omega) al' g hg
    rw [lat_bas hb, ← nfBasis_one] at hl
    obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c W.ψ ν _ _ g g' hf r hr)
    obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ W.cond he' hz'
      (hl ▸ om_supp (hs _ _ _) (r * g) g') (hl ▸ om_per hϖ (hp _ _ _) (r * g) g') h0
    exact ⟨r₂, hr₂, e, z, he, hz, by rw [lat_bas hb]; exact hl₂⟩

end GlobalTheory.TwNormalReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfLineMultipleMemIffIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ConjHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vecMul_jA_eq_zero (p : SplitPt D k) {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr = 0 := by
  have h0 : o.iAᴴ * HSpace.gram S₀ * o.iB = 0 := by
    have := congrArg Matrix.conjTranspose o.orth
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, gram_conjTranspose] using this
  have h1 : o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ) = 0 := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  funext l
  have h2 : ∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l =
      star ((o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ)) l) := by
    rw [Matrix.mulVec, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, star_mul', star_star, mul_comm]
  have h3 : ((fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr) l =
      (p.pr.comp (incA D)) (∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l) := by
    show ∑ i, (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) * (p.pr.comp (incA D)) (o.iA i l) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul]
  rw [h3, h2, h1, Pi.zero_apply, star_zero, map_zero]
  rfl

theorem sum_mul_star_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  have e1 : ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = vecB o ζ ⬝ᵥ star (HSpace.gram S₀ *ᵥ vecB o ζ) := rfl
  rw [e1, Matrix.star_mulVec, gram_conjTranspose, dotProduct_comm, ← Matrix.dotProduct_mulVec, vecB,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem sumFrame_dot (p : SplitPt D k) {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (hsum : IsSumFrame o ζ α α₀)
    (x' : n ⊕ Fin 1 → k) :
    (α₀.b *ᵥ x') ⬝ᵥ (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
      x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
  have e2 : ((o.jA.map p.pr * α.b) *ᵥ (x' ∘ Sum.inl)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, vecMul_jA_eq_zero]
    simp only [Matrix.zero_vecMul, zero_dotProduct]
  have e3 : ((replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) *ᵥ (x' ∘ Sum.inr)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
        x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
    rw [← sum_mul_star_eq]
    show ∑ i, (∑ j : Fin 1, (p.pr.comp (incA D)) (vecB o ζ i) * x' (Sum.inr j)) *
        (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) =
      x' (Sum.inr 0) * (p.pr.comp (incA D)) (∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    simp only [Fin.sum_univ_one, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum, Matrix.fromCols_mulVec, add_dotProduct, e2, e3]
  exact zero_add _

theorem pair_eq (p : SplitPt D k) (S₀ : HSp D) (z : Fin S₀.rank → D.host.E) (c : AE D) (x : Fin S₀.rank → k) :
    ∑ i, ∑ j, x i * p.pr (cA D (incA D (HSpace.gram S₀ i j))) * (p.pr (cA D c) * p.pr (incA D (star (z j))))
      = p.pr (cA D c) * (x ⬝ᵥ fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ z) i)))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Finset.mul_sum, Matrix.mulVec, star_sum, map_sum, FrameLat.cA_incA, star_mul', map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem conj_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => cA D p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr (cA D c) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k]) := by
  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hM hsum hlat c
  have hy : (fun r => cA D p.e * (c * incA D (vecB o ζ r))) =
      fun r => cA D (p.sec (p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))))) := by
    funext r
    have : p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))) = p.pr (cA D (c * incA D (vecB o ζ r))) := by
      simp only [map_mul, FrameLat.cA_incA]
    rw [this, p.sec_pr, map_mul, cA_cA]
  rw [hy, FrameLat.csec_mem_iff hM]
  constructor
  · intro H
    obtain ⟨x1, hx1l, hx1r⟩ : ∃ x1 : n ⊕ Fin 1 → k, x1 ∘ Sum.inl = 0 ∧ x1 (Sum.inr 0) = 1 :=
      ⟨Sum.elim 0 (fun _ => 1), Sum.elim_comp_inl _ _, rfl⟩
    have hx' : x1 ∈ lastKer Λ := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, hx1l, hx1r]
      exact ⟨zero_mem _, one_mem _⟩
    have hx := H (α₀.b *ᵥ x1) ((hlat _).1 hx')
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum, hx1r, one_mul] at hx
    exact hx
  · intro H x hx
    have hxx : x = α₀.b *ᵥ (α₀.b' *ᵥ x) := by rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
    rw [hxx] at hx ⊢
    have hl := ((GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer).1 ((hlat _).2 hx)).2
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum]
    convert mul_mem hl H using 1
    ring

end GlobalTheory.FinPl.ConjHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrimeStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime : ∀ (D : D7) (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ), (∀ x y, psiEf (x + y) = psiEf x * psiEf y) → (∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1) → (∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1) → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1 := by
  first | exact @GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one | exact GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one | (intros; apply GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one <;> assumption)
end

