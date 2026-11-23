module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DescentConstants
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField IsDedekindDomain Module GlobalTheory.AllWt GlobalTheory.CompHt Formalism.HN Formalism.HermitianLatticesTheory
open scoped ENNReal

section Coord

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]


open Classical in
def coordOf (N : (K →+* ℂ) → V → ℝ) :
    Σ n : ℕ, (V →ₗ[K] (Fin n → K)) × ((Fin n → K) →ₗ[K] V) × (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :=
  if h : HasGram N then ⟨h.some.1, h.some.2.1.1.equivFun, h.some.2.1.1.equivFun.symm, h.some.2.1.2⟩ else ⟨0, 0, 0, 1⟩

variable (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ)

def cDim : ℕ := (coordOf N).1

def toCo : V →ₗ[K] (Fin (cDim N) → K) := (coordOf N).2.1

def ofCo : (Fin (cDim N) → K) →ₗ[K] V := (coordOf N).2.2.1

def frameCo : InfinitePlace K → Matrix (Fin (cDim N)) (Fin (cDim N)) ℂ := (coordOf N).2.2.2

def mapCo (φ : V →ₗ[K] W) : (Fin (cDim N) → K) →ₗ[K] (Fin (cDim N') → K) := toCo N' ∘ₗ φ ∘ₗ ofCo N

variable {N N'}


omit [NumberField K] in
theorem exists_basis_co (h : HasGram N) : ∃ b : Basis (Fin (cDim N)) K V,
    IsGram b (frameCo N) N ∧ toCo N = b.equivFun ∧ ofCo N = b.equivFun.symm := by
  have key : ∀ s : Σ n : ℕ, (V →ₗ[K] (Fin n → K)) × ((Fin n → K) →ₗ[K] V) ×
      (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      s = ⟨h.some.1, h.some.2.1.1.equivFun, h.some.2.1.1.equivFun.symm, h.some.2.1.2⟩ →
      ∃ b : Basis (Fin s.1) K V, IsGram b s.2.2.2 N ∧ s.2.1 = b.equivFun ∧ s.2.2.1 = b.equivFun.symm := by
    rintro _ rfl
    exact ⟨_, h.some.2.2, rfl, rfl⟩
  exact key _ (dif_pos h)


omit [NumberField K] in
theorem cDim_eq (h : HasGram N) : cDim N = finrank K V := by
  obtain ⟨b, -⟩ := exists_basis_co h
  rw [finrank_eq_card_basis b, Fintype.card_fin]





variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]


variable (N) in
def latCo (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Fin (cDim N) → K) := L.map ((toCo N).restrictScalars (𝓞 K))








variable [StarRing K]

end Coord

section Copies

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] (ι : Type) [Fintype ι]

def piNorm (N : (K →+* ℂ) → V → ℝ) (σ : K →+* ℂ) (F : ι → V) : ℝ := Real.sqrt (∑ i, N σ (F i) ^ 2)

theorem hasGram_piNorm {N : (K →+* ℂ) → V → ℝ} (h : HasGram N) : HasGram (piNorm ι N) := by
  classical
  obtain ⟨n, ⟨b, X⟩, hb⟩ := h
  refine IsGram.hasGram (b := (Pi.basis fun _ : ι => b).reindex
    ((Equiv.sigmaEquivProd ι (Fin n)).trans (Equiv.prodComm _ _)))
    (X := fun v => Matrix.blockDiagonal fun _ : ι => X v) fun v => ⟨?_, fun F => ?_⟩
  · rw [Matrix.det_blockDiagonal]
    exact IsUnit.prod_iff.2 fun _ _ => (hb v).1
  · have hi : (Matrix.blockDiagonal fun _ : ι => X v)⁻¹ = Matrix.blockDiagonal fun _ : ι => (X v)⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.blockDiagonal_mul]
      simp only [Matrix.nonsing_inv_mul _ (hb v).1]
      exact Matrix.blockDiagonal_one
    simp only [piNorm, ← (hb v).2, normAt, cnorm, fcoord, hi]
    congr 1
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    have e : ∀ k, vecAt ((Pi.basis fun _ : ι => b).reindex
        ((Equiv.sigmaEquivProd ι (Fin n)).trans (Equiv.prodComm _ _))) v F k = vecAt b v (F k.2) k.1 := fun k => by
      simp only [vecAt, Basis.repr_reindex_apply]; rfl
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, e]

variable [Module (𝓞 K) V]

def piLat (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) (ι → V) := Submodule.pi Set.univ fun _ => L

end Copies

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
  Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def compMean (g : Comp Xo c → ℝ) : ℝ := (∑ᶠ Z, g Z) / (Nat.card (Comp Xo c) : ℝ)

section Short

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def cStarSet (G : WTZ E) : Set ℝ :=
  {t | ∃ (n : ℕ) (w : Fin n → cuspW Xo c U G) (abelian₂ : ℝ), CompShortGen U x V dict G w abelian₂ ∧ t = cStar n abelian₂}

def cStarInf (G : WTZ E) : ℝ := sInf (cStarSet U x V dict G)

variable {U x V dict} {G : WTZ E}

end Short

section Ref

variable {T : CDVR} {io : c.F →+* T.Fr}

def HasPhi (y : IntFr Xo c T io) (φ : ℝ) : Prop :=
  letI := io.toAlgebra
  ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t y.1.x)
    (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (P : PELUnif (maximalIdeal T.V) G) (ϖ : T.V)
    (Q : P.D.toPre.X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB (IsCMField.complexConj E : E → E) P.D.toPre.X),
    Irreducible ϖ ∧ QForm.IsQ P.D.toPre ϖ Q ∧ (∀ a, 0 ≤ Q a) ∧
      (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) ∧ φ = Formalism.MainNotions.ModuliIntegralCharts.phiC _ β

theorem HasPhi.nonneg {y : IntFr Xo c T io} {φ : ℝ} (h : HasPhi y φ) : 0 ≤ φ := by
  obtain ⟨G, t', -, -, P, ϖ, Q, β, -, -, h0, hβ, rfl⟩ := h
  refine Real.sInf_nonneg ?_
  rintro _ ⟨lf, -, hl, rfl⟩
  by_cases hb : β = 0
  · rw [hb, map_zero]
  · exact (hl β (fun a => by rw [hβ]; exact mul_nonneg zero_le_two (by exact_mod_cast h0 a)) hb).le

theorem exists_hasPhi (y : IntFr Xo c T io) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr))
    (m1 : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (P : PELUnif (maximalIdeal T.V) G) : ∃ φ, HasPhi y φ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨Q, β, hQ, h0, -, hβ, -⟩ := GlobalTheory.ValForm.main E H T.V G P ϖ hϖ (IsCMField.complexConj E : E → E) fun _ => rfl
  exact ⟨_, G, t', m1, m2, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def depthAt_vp (G : WTZ E) (p : ℕ) (y : IntFr Xo c T io) : EReal :=
  depth_vw U G fun f => nval T.V (vV T.V (p : T.Fr)).toNat (evI y f)

def refExp_vp (cst : ℝ) (G : WTZ E) (p : ℕ) : EReal :=
  ⨆ (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la.1 T.V io e) (y : IntFr Xo c T io)
    (_ : y.IsAlg) (φ : ℝ) (_ : HasPhi y φ), depthAt_vp U G p y - ((cst * φ / (vV T.V (p : T.Fr) : ℝ) : ℝ) : EReal)

theorem refExp_vp_le_iff {cst : ℝ} {G : WTZ E} {p : ℕ} {a : EReal} : refExp_vp U cst G p ≤ a ↔
    ∀ (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
      y.IsAlg → ∀ φ : ℝ, HasPhi y φ →
        depthAt_vp U G p y ≤ a + ((cst * φ / (vV T.V (p : T.Fr) : ℝ) : ℝ) : EReal) := by
  simp only [refExp_vp, iSup_le_iff, EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]

def refSum (cst : ℝ) (G : WTZ E) : ℝ≥0∞ :=
  ∑' p : Nat.Primes, (refExp_vp U cst G p).toENNReal * ENNReal.ofReal (Real.log (p : ℕ))

end Ref

end GlobalTheory.SlopeRec
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

def zetaLogDeriv {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : ℝ :=
  (logDeriv (fun s => riemannZeta s * DirichletCharacter.LFunction χ s) 0).re

def maxLift (D : D7) (g : ℕ → ℝ) : ℝ :=
  (Icc 1 D.R.m).sup' ⟨1, mem_Icc.2 ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩⟩ g

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

def pageOf : SlopeBoundParameters where
  Pl := D.what₂.Tau
  fPl := inferInstance
  x := L.sc.x
  eps := L.sc.eps
  rd := D.host.rdE
  v := D.host.v
  dN := D.host.d
  dimNeZero := ⟨D.host.hyp.2.1.ne_zero⟩
  χ := chiK D
  Z := haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩; zetaLogDeriv (chiK D)
  logOmK := eulerConstantTerm D.host.d
  logOm := L.logOm
  f := D.R.f
  m := D.R.m
  k := D.R.k
  S := L.Sc
  η := L.etaSz
  R := (D.R.r : ℝ) / 2
  PPp := maxLift D fun j => (numAt Q j).PPp
  PPpp := maxLift D fun j => (numAt Q j).PPpp
  PP := Q.PP
  PPT := Real.sqrt (ppTsq Q)
  Zpg := zBase L
  nV := D.R.nV
  Nr := D.R.r
  g12 := (D.host.g 0 : ℝ) * D.host.g 1

section Weights


variable (D) in
def uMinus (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uAn D j τ i - (cTw D j : ℤ) * deW D j i


variable (D) in
def kapMinus (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := kap D j τ i - (cTw D j : ℤ) * deW D j i


variable (D) in
def twW (j : ℕ) (_ : D.what₂.Tau) (i : ℕ) : ℤ := (cTw D j : ℤ) * deW D j i

def remW (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ :=
  aW D j τ i - aW D j τ (D.R.k - 2) - ((tN Q + placeRankTwoOne.dimY D + 1 : ℕ) : ℤ) * uOne Q j τ i

def uTwo (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uOne Q j τ i + remW Q j τ i

def uCan (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := canW D j i + uTwo Q j τ i + (placeRankTwoOne.dimY D : ℤ) * uOne Q j τ i

def uTop (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uCan Q j τ i + (tN Q : ℤ) * uOne Q j τ i

end Weights

section Numbers

def nOneW (j : ℕ) : ℝ := ∑ τ, nrm D (uOne Q j τ)

def nPrW (j : ℕ) : ℝ := ∑ τ, nrm D (uPr Q j τ)

def supPrW (j : ℕ) : ℕ := univ.sup fun τ : D.what₂.Tau => (range D.R.r).sup fun i => (uPr Q j τ i).natAbs

def bZero (j : ℕ) : ℝ := 4 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (1 + (supPrW Q j : ℝ) / (LevelStarExponents.h0 L / (4 * tR Q)))


variable (D L) in
def badPrimes (B : ℝ) : Finset ℕ :=
  (range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ (2 * (discr D.host.E).natAbs * levDeep D L).primeFactors


variable (D) in
def diff_vp (p : ℕ) : ℝ := (padicValNat p (discr D.host.E).natAbs : ℝ) / (Module.finrank ℚ D.host.E : ℝ)

def aSum (j : ℕ) : ℝ :=
  ∑ p ∈ badPrimes D L (bZero Q j), (1 / ((p : ℝ) - 1) + 40 * diff_vp D p) * (nPrW Q j + (numAt Q j).Pa) * Real.log p

def cInf (j : ℕ) : ℝ := (nOneW Q j + 6 * (numAt Q j).Pinf) / 2

def cA (j : ℕ) : ℝ := 26 * (26 * dY D ^ 2 + 2 * zed Q j * tR Q)

def lZero (j : ℕ) : ℝ := (numAt Q j).PPp * (nKap D j / tR Q + 1) + (numAt Q j).al

def cJ (C2 : ℝ) (j : ℕ) : ℝ :=
  dY D * (numAt Q j).PPp * (nKap D j / tR Q + 1) + tR Q * ((numAt Q j).QJ + (numAt Q j).PPp) +
    (dY D + 3) * addY C2 (pageOf Q) / tR Q

def cG (j : ℕ) : ℝ := (dY D + 1) * ((numAt Q j).o + (numAt Q j).B7 + 1) / 2 + 1

def rOne (C2 : ℝ) (j : ℕ) : ℝ :=
  cJ Q C2 j + 26 * dY D ^ 2 * (lZero Q j + Real.log (tR Q)) + (tR Q + dY D + 1) * (numAt Q j).Bt +
    (tR Q + dY D ^ 2) * (cG Q j + 2)

def rTwo (j : ℕ) : ℝ :=
  tR Q * (Real.log 2 + lZero Q j + (numAt Q j).Bt / 2) + 2 * ((numAt Q j).PPp * nKap D j)

def lamKap (j : ℕ) : ℝ := (numAt Q j).G * (nKap D j - (D.R.f : ℝ) * D.R.r * D.R.nV / 2 + D.R.nV)


variable (D L) in
def measureMove : ℝ := 61 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L

end Numbers

section Transport

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt
open Formalism.L2.Pj hiding kap

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}


open Classical in
def toWt (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : Weight Dw :=
  fun τ i => ∑ t, if τ.1 = DV.tauEmb D t then v t i else 0

variable {Dw : Datum H}

theorem toWt_apply (v : D.what₂.Tau → ℕ → ℤ) {τ : Psi H} {t : D.what₂.Tau} (h : τ.1 = DV.tauEmb D t)
    (i : Fin (Dw.p + Dw.q)) : toWt Dw v τ i = v t i := by
  rw [toWt, sum_eq_single t (fun s _ hs => if_neg fun e => hs ?_) (by simp), if_pos h]
  exact GlobalTheory.WeightExponents.tauEmb_injective D (e.symm.trans h)

def psiOf {T : Par D} (h : T.PinHost) (t : D.what₂.Tau) : Psi T.H := ⟨DV.tauEmb D t, h.2.2.2 t⟩

theorem psiOf_bijective {T : Par D} (h : T.Pins) : Function.Bijective (psiOf h.1) := by
  have hj : InR D 1 := ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩
  refine ⟨fun s t e => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val e), fun τ => ?_⟩
  obtain ⟨t, ht⟩ := ((GlobalTheory.WeightExponents.weight_exponents D T h 1 hj
    (WeightAlgebra.wscalar D 1 0 Even.zero)).2.2.1 τ.1).1 τ.2
  exact ⟨t, Subtype.ext ht.symm⟩

theorem toWt_psiOf {T : Par D} (h : T.PinHost) {Dw : Datum T.H} (v : D.what₂.Tau → ℕ → ℤ) (t : D.what₂.Tau)
    (i : Fin (Dw.p + Dw.q)) : toWt Dw v (psiOf h t) i = v t i := toWt_apply v rfl i

variable {T : Par D} {j : ℕ}

theorem sig_eq (h : T.Pins) (hj : InR D j) :
    (T.Dw j).p = pp D j ∧ (T.Dw j).q = qq D j ∧ (T.Dw j).p + (T.Dw j).q = D.R.r := by
  obtain ⟨h1, h2, -⟩ := h.2.2.2 j hj
  refine ⟨h1, h2, ?_⟩
  have := D.R.m_add_three_le_k
  have := hj.1
  have := hj.2
  rw [h1, h2]
  simp only [Ranks.sigW, Ranks.r]; omega

theorem dimFlag_eq (h : T.Pins) (hj : InR D j) : dimFlag (T.Dw j) = placeRankTwoOne.dimY D := by
  rw [dimFlag, Formalism.DegreeFormula.dimFl, (sig_eq h hj).2.2, ← Fintype.card_of_bijective (psiOf_bijective h), D.what₂.card_Tau,
    placeRankTwoOne.dimY, Nat.choose_two_right]


variable (D) in
def thetaExp (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : WTZ D.host.E := wtOf Dw (toWt Dw v) ((D.R.nV / 2 : ℕ) : ℤ)


variable (D) in
def plainExp (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : WTZ D.host.E := wtOf Dw (toWt Dw v) 0

theorem thetaExp_kap_eq (h : T.Pins) (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : w.n = D.R.nV)
    (hw : Formalism.L2.Geo.wtOf w = DV.kapW D j) : thetaExp D (T.Dw j) (kap D j) = wtZ (wtA w) w.n := by
  obtain ⟨hp, hq, hr⟩ := sig_eq h hj
  obtain ⟨-, -, hΨ, hΨ', hA⟩ := GlobalTheory.WeightExponents.weight_exponents D T h j hj w
  have hp' : (T.Dw j).p = (D.R.sigW j).1 := hp
  have hq' : (T.Dw j).q = (D.R.sigW j).2 := hq
  refine Prod.ext (funext fun ⟨τ, i⟩ => ?_) ?_
  · show _ = ((wtA w (τ, i) : ℕ) : ℤ)
    by_cases hτ : InPsi T.H τ
    · obtain ⟨t, rfl⟩ := (hΨ τ).1 hτ
      rw [(hA t i).1, ext0]
      by_cases hi : i < (T.Dw j).p
      · refine (wtOf_big _ _ (psiOf h.1 t) i hi).trans ?_
        rw [toWt_psiOf, GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants.kap, dite_eq_left (by show i < _; omega), ← hw, dite_eq_left (by omega)]
        simp only [Formalism.L2.Geo.wtOf, Formalism.L2.Geo.wtOfN, hn]
        rw [dite_eq_left (by omega)]; ring
      · rw [dite_eq_right (by omega)]
        simp only [thetaExp, wtOf]
        unfold InPsi at hτ
        rw [dite_eq_left hτ, dite_eq_right hi]; rfl
    · obtain ⟨t, rfl⟩ := (hΨ' τ).1 hτ
      rw [(hA t i).2, ext0]
      by_cases hi : i < (T.Dw j).q
      · refine (wtOf_small _ _ (psiOf h.1 t) i hi).trans ?_
        rw [toWt_psiOf, GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants.kap, dite_eq_left (by show (T.Dw j).p + _ < _; omega), ← hw, dite_eq_left (by omega)]
        simp only [Formalism.L2.Geo.wtOf, Formalism.L2.Geo.wtOfN, hn]
        rw [dite_eq_right (by omega), dite_eq_left (by omega)]
        have e : ∀ (a : Fin (D.R.sigW j).2) (b : Fin (D.R.sigW j).2), (a : ℕ) + b + 1 = (D.R.sigW j).2 → Fin.rev a = b :=
          fun a b hab => Fin.ext (by rw [Fin.val_rev]; omega)
        rw [e _ ⟨i, by omega⟩ (by simp only; omega)]; ring
      · rw [dite_eq_right (by omega)]
        simp only [thetaExp, wtOf]
        unfold InPsi at hτ
        rw [dite_eq_right hτ]
        split_ifs <;> first | rfl | omega
  · obtain ⟨a, ha⟩ := w.n_even
    show 2 * ((D.R.nV / 2 : ℕ) : ℤ) = ((w.n : ℕ) : ℤ)
    omega

theorem thetaExp_kap_kapTop (h : T.Pins) (hK : DV.KapDef D) (i : Fin D.R.m) :
    thetaExp D (T.Dw ((i : ℕ) + 1)) (kap D ((i : ℕ) + 1)) =
      wtZ (wtA (Formalism.IndefR.FWT.kapTop D i)) (Formalism.IndefR.FWT.kapTop D i).n :=
  thetaExp_kap_eq h ⟨Nat.le_add_left _ _, i.2⟩ _ rfl (GlobalTheory.RecordWeightVec.wtOf_kapTop D hK i).2

end Transport

end GlobalTheory.SlopeRec
end
end

