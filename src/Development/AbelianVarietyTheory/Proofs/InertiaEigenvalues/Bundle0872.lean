module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0870
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatch
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseSizeBoundsAlongFamily
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Proof.baseSize_bounds_along_family

open Formalism.BasicNotions

theorem baseSize_bounds {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) :
    ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes L,
      2 * (L.sc.b / LevelStarExponents.lStar L) + (D.R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ L.sc.b := by
  intro W0 hW
  have hls : Formalism.MainNotions.TwistedPlaces.lStar L = LevelStarExponents.lStar L := rfl
  have hl0 : 0 < LevelStarExponents.lStar L := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_pos L
  have hgt : L.sc.b' < LevelStarExponents.lStar L := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_gt L P
  have hleb : LevelStarExponents.lStar L ≤ L.sc.b := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_le_b L
  have hw := Formalism.MainNotions.TwistedPlaces.w''_le_b' L
  have hb'0 := Formalism.MainNotions.TwistedPlaces.b'_pos L
  have hx := L.sc.one_lt_alt
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx.le
  have hfl0 : (0 : ℝ) ≤ ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (div_nonneg hb'0.le (by linarith))
  have hfl1 : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _

  have h3 : 3 * LevelStarExponents.lStar L ≤ L.sc.b := by
    have hp2 := Formalism.MainNotions.TwistedPlaces.lStar_part2 L
    rw [hls] at hp2
    have hk := Formalism.MainNotions.TwistedPlaces.m_le_k D
    have hm := Formalism.MainNotions.TwistedPlaces.m_ge_one D
    have hn := Formalism.MainNotions.TwistedPlaces.n_ge_one D
    have ht : (7 : ℝ) ≤ D.R.t := by
      have := Formalism.MainNotions.TwistedPlaces.t_ge D; have := Formalism.MainNotions.TwistedPlaces.k_le_r D; have := Formalism.MainNotions.TwistedPlaces.k_ge_five D; linarith
    have hS := L.Sc_pos
    have hLg := Formalism.MainNotions.TwistedPlaces.Lg_nonneg L
    have hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by nlinarith
    have hA : 3 * (D.R.m : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by
      have e1 : (3 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by nlinarith
      have e2 : (D.R.m : ℝ) * 3 ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L)) :=
        mul_le_mul hk e1 (by norm_num) (by linarith)
      linarith
    have : LevelStarExponents.lStar L * (3 * (D.R.m : ℝ)) ≤ D.R.m * L.sc.b :=
      le_trans (mul_le_mul_of_nonneg_left hA hl0.le) hp2
    nlinarith

  have hη := L.etaSz_pos
  have hm := Formalism.MainNotions.TwistedPlaces.m_ge_one D
  have hq : 0 ≤ L.sc.b / LevelStarExponents.lStar L := div_nonneg (by linarith) hl0.le
  have hlow : 2 * (L.sc.b / LevelStarExponents.lStar L) + (D.R.t : ℝ) / 2 + 3 ≤ L.sc.w'' D.R.n := by
    have h1 := P.h0_ge.1
    have h2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη.le hm
    have h3' := P.mteta
    have ht : (0 : ℝ) ≤ D.R.t := by positivity
    have h4 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
      have : (1 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by nlinarith
      nlinarith
    have h7 : 12 * L.sc.b / LevelStarExponents.lStar L = 12 * (L.sc.b / LevelStarExponents.lStar L) := by ring
    linarith
  rcases hW with rfl | rfl | ⟨t, rfl⟩
  · exact ⟨le_trans hlow (by linarith), le_rfl⟩
  · exact ⟨hlow, by linarith⟩
  · have h1 := L.bT_ge t
    have h2 := Formalism.MainNotions.TwistedPlaces.bT_le_two_mul_b' L P t
    exact ⟨by linarith, by linarith⟩

theorem main : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x), ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
    2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ (Fm.L x a).sc.b := by
  intro eps Fm x hx a W0 hW
  exact baseSize_bounds (Fm.L x a) (Fm.params x hx a) W0 hW

end GlobalTheory.Proof.baseSize_bounds_along_family
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellIdentityRankinSelbergTorusTranslateStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_identity_rankinSelberg_torus_translate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ) (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T)
      (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
        ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (l.1 w))) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ (x : ℝ), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
        ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) *
          GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) := by
  first | exact @GlobalTheory.CellPw.cell_identity | exact GlobalTheory.CellPw.cell_identity | (intros; apply GlobalTheory.CellPw.cell_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutationFullnessOfReads
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CommFullAll

section Act
variable {D : D7} (S : RatDat D.ntw)

def hLr (j : ℕ) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) :
    Module.End S.Ks (FmK S j) :=
  ((hL k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx

theorem hkFR_act (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) (hst : RhoStab S j) (hχ : ChiInLL0 S j)
    (hc : ∀ g x, hL k P ((S.A j).ρ g x) = (S.A j).ρ g (hL k P x)) (g : G0g D.nd) (z : Fm S i j b) :
    hkFR S i j b hL hs k P (actG S i j b hst hχ g z) = actG S i j b hst hχ g (hkFR S i j b hL hs k P z) := by
  have hcomm : hLr S j hL hs k P * rhoKG S j hst (S.eG.symm g) = rhoKG S j hst (S.eG.symm g) * hLr S j hL hs k P := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hc (S.eG.symm g) (show ↥(S.A j).WK from x).1
  have h2 := LinearMap.congr_fun (congrArg (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)) hcomm) z
  rw [map_mul, map_mul] at h2
  change Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) ((readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g)) z) =
    (readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g))
        (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) z)
  rw [map_smul]
  congr 1
end Act

section Real
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Cx Formalism.L2.Pj
variable {D : D7} (X : RealSide D) {S : RatDat D.ntw} (YS : NExpRealS X.R X.cG S) (H : NExpRealH X.R X.cG S YS)

end Real

section Iso

variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
  {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL Ks' WL' W' G'}

theorem iso_smul (Y : NX.FormsIso A A') (c : Ks) (w : WL) : Y.e (c • w) = Y.eK c • Y.e w := by
  rw [← algebraMap_smul LL c w, map_smul, ← Y.eK_LL, algebraMap_smul]

theorem iso_symm_smul (Y : NX.FormsIso A A') (c : Ks') (y : WL') : Y.e.symm (c • y) = Y.eK.symm c • Y.e.symm y := by
  apply Y.e.injective
  rw [iso_smul]
  simp

theorem iso_span (Y : NX.FormsIso A A') (h : Submodule.span Ks' (A'.MK : Set WL') = A'.WK) :
    Submodule.span Ks (A.MK : Set WL) = A.WK := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => by obtain ⟨h, -⟩ := hx; exact h
  · intro x hx
    have h1 : Y.e x ∈ Submodule.span Ks' (A'.MK : Set WL') := h ▸ (Y.wk x).1 hx
    have h2 : ∀ y ∈ Submodule.span Ks' (A'.MK : Set WL'),
        Y.e.symm y ∈ Submodule.span Ks (A.MK : Set WL) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ((Y.mkK _).2 (by simpa using hy))
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [iso_symm_smul]; exact Submodule.smul_mem _ _ ha
    simpa using h2 _ h1

end Iso

section Base
variable {D : D7} (S : RatDat D.ntw) (i : D.ntw.Tw) (j : ℕ) (b : Bool)

def mkF (y : S.WL j) (h : y ∈ (S.A j).WK) : FmK S j := ⟨y, h⟩

def rdF (c : S.Ks) : FractionRing (D.ntw.O i) := ιK S i b c

def rdK (a : KB S i b) : FractionRing (D.ntw.O i) := a

def oneT (x : FmK S j) : Fm S i j b := ((1 : KB S i b) ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j)

theorem oneT_zero : oneT S i j b 0 = 0 := TensorProduct.tmul_zero _ _

theorem oneT_add (x y : FmK S j) : oneT S i j b (x + y) = oneT S i j b x + oneT S i j b y :=
  TensorProduct.tmul_add _ _ _

theorem oneT_smul (c : S.Ks) (x : FmK S j) :
    oneT S i j b (c • x) = (rdF S i b c) • oneT S i j b x := by
  change (1 : KB S i b) ⊗ₜ[S.Ks] (c • x) = (ιK S i b c : KB S i b) • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  congr 1

theorem Bsup_span (hS : Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)) = (S.A j).WK) :
    Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i j b : Set (Fm S i j b)) = ⊤ := by
  let B := Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i j b : Set (Fm S i j b))
  have aux : ∀ y ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)), ∃ h : y ∈ (S.A j).WK,
      oneT S i j b (mkF S j y h) ∈ B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, h'⟩ := id hy
      exact ⟨h, Submodule.subset_span (Submodule.subset_span ⟨mkF S j y h, hy, rfl⟩)⟩
    | zero =>
      refine ⟨(S.A j).WK.zero_mem, ?_⟩
      have : oneT S i j b (mkF S j 0 (S.A j).WK.zero_mem) = 0 := oneT_zero S i j b
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      refine ⟨(S.A j).WK.add_mem h1 h3, ?_⟩
      have : oneT S i j b (mkF S j (x + y) ((S.A j).WK.add_mem h1 h3)) =
          oneT S i j b (mkF S j x h1) + oneT S i j b (mkF S j y h3) :=
        oneT_add S i j b (mkF S j x h1) (mkF S j y h3)
      rw [this]
      exact Submodule.add_mem _ h2 h4
    | smul c x _ hx =>
      obtain ⟨h1, h2⟩ := hx
      refine ⟨(S.A j).WK.smul_mem c h1, ?_⟩
      have : oneT S i j b (mkF S j (c • x) ((S.A j).WK.smul_mem c h1)) =
          (rdF S i b c) • oneT S i j b (mkF S j x h1) :=
        oneT_smul S i j b c (mkF S j x h1)
      rw [this]
      exact Submodule.smul_mem _ _ h2
  have hall : ∀ (a : KB S i b) (x : FmK S j),
      ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) ∈ B := by
    intro a x
    have hx : (show ↥(S.A j).WK from x).1 ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)) := by
      rw [hS]; exact (show ↥(S.A j).WK from x).2
    obtain ⟨h, h'⟩ := aux _ hx
    have e : ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) =
        (rdK S i b a) • oneT S i j b x := by
      change a ⊗ₜ[S.Ks] x = a • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ h'
  refine eq_top_iff.2 fun t _ => ?_
  change t ∈ B
  induction (show KB S i b ⊗[S.Ks] FmK S j from t) using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a x => exact hall a x
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Base

end GlobalTheory.CommFullAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteAllLifts
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.NX
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SupLaw

section Coset

open GlobalTheory.HeckeParts

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem offPrincipalLevel (hSb : R.fam_Sb) (i : Fin D.R.m) {P : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) (c : ℕ) :
    OffLevel (R.datWp i R.triv) (1 ^ c) P := by
  refine ⟨hso.1, ?_, fun PP hPP => ?_⟩
  · rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  · have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]

theorem cosetSum_comm (hL : R.toLevCh.Is A.μ0) (hSb : R.fam_Sb) (i : Fin D.R.m) {P P' : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)))
    (hso' : Bridge.SplitOff P' (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) {k k' : ℕ} {α α' : GA D (Wc D i)}
    {Rc Rc' : Finset (GA D (Wc D i))} (ha : IsHeckeAt (Wc D i) P k α) (ha' : IsHeckeAt (Wc D i) P' k' α')
    (hR : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc)
    (hR' : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α' Rc') {F : GA D (Wc D i) → ℂ}
    (hF : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F) :
    heckeLin (Wc D i) Rc (heckeLin (Wc D i) Rc' F) = heckeLin (Wc D i) Rc' (heckeLin (Wc D i) Rc F) := by
  obtain ⟨c, hβ⟩ := hL.βW i
  have hP := offPrincipalLevel hSb i hso c
  have hP' := offPrincipalLevel hSb i hso' c
  obtain ⟨e, ϖ, he, -, -, hα⟩ := ha
  obtain ⟨e', ϖ', he', -, -, hα'⟩ := ha'
  obtain ⟨⟨A₀, hA⟩, -⟩ := exists_locRep hβ hP he hα.2.1
  obtain ⟨⟨B₀, hB⟩, -⟩ := exists_locRep hβ hP' he' hα'.2.1
  have e1 : ∀ {F : GA D (Wc D i) → ℂ}, RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F →
      heckeLin (Wc D i) Rc F = heckeLin (Wc D i) A₀ F := fun hF =>
    (dcOp_eq_rInv hR hA.2 ⟨1, 1, by simp⟩ hF).1
  have e2 : ∀ {F : GA D (Wc D i) → ℂ}, RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F →
      heckeLin (Wc D i) Rc' F = heckeLin (Wc D i) B₀ F := fun hF =>
    (dcOp_eq_rInv hR' hB.2 ⟨1, 1, by simp⟩ hF).1
  have i1 : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) (heckeLin (Wc D i) A₀ F) := dcOp_rInv hA.2 hF
  have i2 : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) (heckeLin (Wc D i) B₀ F) := dcOp_rInv hB.2 hF
  rw [e2 hF, e1 hF, e1 i2, e2 i1]
  exact hA.comm hβ hP hB hF

end Coset

section Tied

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S)

theorem commute_of_read (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hSb : Rl.toRealDat.fam_Sb) (hW : Rl.toRealDat.models_HW)
    (i : Fin D.R.m) (hinj : Function.Injective ((Rl.FW i).j (sg0 D A3.A))) {P P' : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)))
    (hso' : Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) {k k' : ℕ} {α α' : GA D (Wc D i)}
    {Rc Rc' : Finset (GA D (Wc D i))} (ha : IsHeckeAt (Wc D i) P k α) (ha' : IsHeckeAt (Wc D i) P' k' α')
    (hR : Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α Rc)
    (hR' : Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' Rc')
    {t t' : Module.End D.what₂.LL (S.WL ((i : ℕ) + 1))} {c c' : ℂ}
    (ht : ∀ x, (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t x))) =
      c • heckeOn (Rl.MW i (sg0 D A3.A)) Rc ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e x))))
    (ht' : ∀ x, (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t' x))) =
      c' • heckeOn (Rl.MW i (sg0 D A3.A)) Rc' ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e x)))) :
    Commute t t' := by
  refine LinearMap.ext fun x => (Y.fi i).e.injective (hinj ((hW i _).1 ?_))
  change (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t (t' x)))) =
    (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t' (t x))))
  rw [ht, ht', ht', ht, map_smul, map_smul, smul_comm]
  refine congrArg (fun z : MMap (Rl.MW i (sg0 D A3.A)) => c' • c • z) ?_
  exact MultilinearMap.ext fun v => cosetSum_comm hL hSb i hso hso' ha ha' hR hR'
    (fun k hk h => GlobalTheory.HeckeSup.model_inv_cl hW i _ _ v k hk h)


set_option synthInstance.maxHeartbeats 400000 in
theorem baseChange_comm (i : D.ntw.Tw) (j : ℕ) (b : Bool) {f : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (hs : HeckeStabR S j f) (k k' : ℕ) (P P' : PlE D.host) (h : Commute (f k P) (f k' P')) :
    Commute (hkFR S i j b f hs k P) (hkFR S i j b f hs k' P') := by
  let r : ℕ → PlE D.host → Module.End S.Ks (FmK S j) := fun k P =>
    ((f k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx
  have hr : r k P * r k' P' = r k' P' * r k P := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h.eq x.1)
  unfold hkFR Commute SemiconjBy
  change (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k P)) * (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k' P')) =
    (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k' P')) * (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k P))
  rw [← map_mul, ← map_mul, hr]


set_option synthInstance.maxHeartbeats 400000 in
theorem hkComm_of_family (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j))
    (c : ∀ i : D.ntw.Tw, Bool → ℕ → PlE D.host → FractionRing (D.ntw.O i))
    (hEq : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
      Formalism.BasicNotions.IsSplitPl D.host P → k ≤ D.R.r →
      Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) = c i b k P • hkFR S i j b (f j) (hs j h1 h2) k P (Y.eF i j b h1 h2 x))
    (hc : ∀ (i : D.ntw.Tw) j, 1 ≤ j → j ≤ D.R.m → ∀ k P k' P', Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P → Formalism.MainNotions.IntegralHeckeForms.HkIdx i k' P' →
      Commute (f j k P) (f j k' P')) : HkComm D := by
  intro i _ j hj b k P k' P' hk hk'
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have hF := baseChange_comm S i j b (hs j h1 h2) k k' P P' (hc i j h1 h2 k P k' P' hk hk')
  refine LinearMap.ext fun x => (Y.eF i j b h1 h2).injective ?_
  change Y.eF i j b h1 h2 (D.nexp.hkF i j b k P (D.nexp.hkF i j b k' P' x)) =
    Y.eF i j b h1 h2 (D.nexp.hkF i j b k' P' (D.nexp.hkF i j b k P x))
  rw [hEq i j b h1 h2 k P _ hk.2.2.2 hk.2.2.1 hk.2.1, hEq i j b h1 h2 k' P' _ hk'.2.2.2 hk'.2.2.1 hk'.2.1,
    hEq i j b h1 h2 k' P' _ hk'.2.2.2 hk'.2.2.1 hk'.2.1, hEq i j b h1 h2 k P _ hk.2.2.2 hk.2.2.1 hk.2.1, map_smul, map_smul,
    smul_comm]
  exact congrArg (fun z => c i b k' P' • c i b k P • z) (LinearMap.congr_fun hF.eq (Y.eF i j b h1 h2 x))

theorem family_comm (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hF : Rl.toRealDat.IsFam) (hW : Rl.toRealDat.models_HW)
    (hinj : ∀ i, Function.Injective ((Rl.FW i).j (sg0 D A3.A))) (hC : GlobalTheory.ExportPin.Model.Covered Rl)
    (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hr : ∀ (i : D.ntw.Tw) (n : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P →
      ∀ (α : GA D (Wc D n)) (R : Finset (GA D (Wc D n))), IsHeckeAt (Wc D n) P k α →
        Bridge.IsDC (levG (Wc D n) (Rl.βW n) (Rl.datWp n Rl.triv)) α R → ∃ c : ℂ, ∀ x : S.WL ((n : ℕ) + 1),
          (Rl.HW n (sg0 D A3.A)).e ((Rl.FW n).j (sg0 D A3.A) ((Y.fi n).e (f ((n : ℕ) + 1) k P x))) =
            c • heckeOn (Rl.MW n (sg0 D A3.A)) R ((Rl.HW n (sg0 D A3.A)).e ((Rl.FW n).j (sg0 D A3.A) ((Y.fi n).e x))))
    (i : D.ntw.Tw) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (k' : ℕ) (P' : PlE D.host)
    (hk : Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P) (hk' : Formalism.MainNotions.IntegralHeckeForms.HkIdx i k' P') : Commute (f j k P) (f j k' P') := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  let m : Fin D.R.m := ⟨n, h2⟩
  have so := hC i P hk.2.2.2 hk.2.2.1
  have so' := hC i P' hk'.2.2.2 hk'.2.2.1
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hL hF m so hk.2.1
  obtain ⟨α', Rc', ha', hR'⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hL hF m so' hk'.2.1
  obtain ⟨c, hc⟩ := hr i m k P hk α Rc ha hR
  obtain ⟨c', hc'⟩ := hr i m k' P' hk' α' Rc' ha' hR'
  exact commute_of_read Rl cG S Y hL hF.Sb hW m (hinj m) so so' ha ha' hR hR' hc hc'



end Tied

end GlobalTheory.SupLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualOfLabels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjPlaceDual

theorem conjPl_symm (D : D7) {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hy, GlobalTheory.SplitPlaceOver.host_conj_eq', GlobalTheory.SplitPlaceOver.host_conj_eq', IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

end GlobalTheory.ConjPlaceDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatchStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → CountIdentity := by
  first | exact @GlobalTheory.CountId.countIdentity_of_unitMatch | exact GlobalTheory.CountId.countIdentity_of_unitMatch | (intros; apply GlobalTheory.CountId.countIdentity_of_unitMatch <;> assumption)
end

