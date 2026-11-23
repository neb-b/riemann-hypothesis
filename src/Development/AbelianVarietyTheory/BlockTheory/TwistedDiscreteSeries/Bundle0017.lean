module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundedCommutantVacua
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField
open GlobalTheory.Size (l2O)
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Defs

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W))

variable {V W}

variable (V W)

def IsVac (θ : InfFam D) (sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (sW τ)) f

end Defs

section Basic₂

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {θ : InfFam D}

theorem exists_isVac_ne_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) (sV τ)) (hW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) :
    ∃ f, IsVac ψ V W θ sV sW f ∧ f ≠ 0 := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ V W _ _ hV hW _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  have h := hf 1
  simp only [one_mul] at h
  exact ⟨f, ⟨h.1, h.2.2⟩, f0⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingRationalGroups
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T) : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (R.datVt i t)

def IsLiftV (i : Fin D.R.m) (t : T) (g : G) (κ : (levV R i t).Q) : Prop :=
  rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf (Vc D i)) : GL _ _)) = R.eG g

def IsAlgV (i : Fin D.R.m) (t : T) (c : G → ℂ) (κ : G → (levV R i t).Q) (x y : (R.HV i t).H) : Prop :=
  (R.HV i t).e y = ∑ g, c g • Bridge.g0Act (levV R i t).ch (κ g) ((R.HV i t).e x)

def algW (i : Fin D.R.m) (c : G → ℂ) : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (gaL (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG c)

theorem algW_eC (i : Fin D.R.m) :
    algW R i (RealDat.eC (A := A) (sg0 D A)) = postOn _ (R.eWf i (sg0 D A)) := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

abbrev Rep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

abbrev Chr (D : D7) : Type := (AE D)ˣ →* Circle

def prodSpan {X X₁ X₂ : Type} (e : X → X₁ × X₂) (P₁ : (X₁ → ℂ) → Prop) (P₂ : (X₂ → ℂ) → Prop) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ {g | ∃ f₁ f₂, P₁ f₁ ∧ P₂ f₂ ∧ g = fun w => f₁ (e w).1 * f₂ (e w).2}

def UnifLimit {X : Type} (M : Submodule ℂ (X → ℂ)) (f : X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g ∈ M, ∀ w, ‖f w - g w‖ ≤ ε

structure TensorSource (ψ : AddChar (AF D.host.F) ℂ) {S A B : HSp D} (d : OrthDec S A B) (T : HSp D) : Prop where

  box_theta : ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (d.boxS T fA fB)

  box_zero : ∀ fA fB, d.boxS T fA fB 0 = fA 0 * fB 0

  heis_box : ∀ fA fB,
    (∀ u, heisO ψ S T ((d.resS T).symm (u, 0)) (d.boxS T fA fB) = d.boxS T (heisO ψ A T u fA) fB) ∧
    ∀ v, heisO ψ S T ((d.resS T).symm (0, v)) (d.boxS T fA fB) = d.boxS T fA (heisO ψ B T v fB)

  slice_theta : ∀ f, IsThetaFunO ψ S T f →
    (∀ v, IsThetaFunO ψ A T fun u => f ((d.resS T).symm (u, v))) ∧
    ∀ u, IsThetaFunO ψ B T fun v => f ((d.resS T).symm (u, v))

  dense : ∀ f, IsThetaFunO ψ S T f → UnifLimit (prodSpan (d.resS T) (IsThetaFunO ψ A T) (IsThetaFunO ψ B T)) f

  om_box : ∀ (χA χB χT : Chr D) (omS : Rep S T) (omA : Rep A T) (omB : Rep B T),
    IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB →
    ∀ a b h fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB →
      omS (d.emb (a, b), h) (d.boxS T fA fB) = d.boxS T (omA (a, h) fA) (omB (b, h) fB)

  om_slice : ∀ (χA χB χT : Chr D) (omS : Rep S T) (omA : Rep A T) (omB : Rep B T),
    IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB →
    ∀ a b h f, IsThetaFunO ψ S T f → ∀ v,
      IsThetaFunO ψ A T (fun u' => omB (b, h) (fun v' => f ((d.resS T).symm (u', v'))) v) ∧
      ∀ u, omS (d.emb (a, b), h) f ((d.resS T).symm (u, v)) =
        omA (a, h) (fun u' => omB (b, h) (fun v' => f ((d.resS T).symm (u', v'))) v) u

structure TensorTarget (ψ : AddChar (AF D.host.F) ℂ) {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) : Prop where

  box_theta : ∀ fA fB, IsThetaFunO ψ S A fA → IsThetaFunO ψ S B fB → IsThetaFunO ψ S T (d.boxT S fA fB)

  box_zero : ∀ fA fB, d.boxT S fA fB 0 = fA 0 * fB 0

  heis_box : ∀ fA fB,
    (∀ u, heisO ψ S T ((d.resT S).symm (u, 0)) (d.boxT S fA fB) = d.boxT S (heisO ψ S A u fA) fB) ∧
    ∀ v, heisO ψ S T ((d.resT S).symm (0, v)) (d.boxT S fA fB) = d.boxT S fA (heisO ψ S B v fB)

  slice_theta : ∀ f, IsThetaFunO ψ S T f →
    (∀ v, IsThetaFunO ψ S A fun u => f ((d.resT S).symm (u, v))) ∧
    ∀ u, IsThetaFunO ψ S B fun v => f ((d.resT S).symm (u, v))

  dense : ∀ f, IsThetaFunO ψ S T f → UnifLimit (prodSpan (d.resT S) (IsThetaFunO ψ S A) (IsThetaFunO ψ S B)) f

  om_box : ∀ (χS χA χB : Chr D) (omT : Rep S T) (omA : Rep S A) (omB : Rep S B),
    IsWeilDatumO ψ S T χS (χA * χB) omT → IsWeilDatumO ψ S A χS χA omA → IsWeilDatumO ψ S B χS χB omB →
    ∀ g a b fA fB, IsThetaFunO ψ S A fA → IsThetaFunO ψ S B fB →
      omT (g, d.emb (a, b)) (d.boxT S fA fB) = d.boxT S (omA (g, a) fA) (omB (g, b) fB)

  om_slice : ∀ (χS χA χB : Chr D) (omT : Rep S T) (omA : Rep S A) (omB : Rep S B),
    IsWeilDatumO ψ S T χS (χA * χB) omT → IsWeilDatumO ψ S A χS χA omA → IsWeilDatumO ψ S B χS χB omB →
    ∀ g a b f, IsThetaFunO ψ S T f → ∀ v,
      IsThetaFunO ψ S A (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) ∧
      ∀ u, omT (g, d.emb (a, b)) f ((d.resT S).symm (u, v)) =
        omA (g, a) (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) u

def cj {X Y : Type} (e : Y → X) (f : X → ℂ) : Y → ℂ := fun y => starRingEnd ℂ (f (e y))

theorem cj_cj {X Y : Type} (e : Y → X) (e' : X → Y) (h : ∀ x, e (e' x) = x) (f : X → ℂ) : cj e' (cj e f) = f := by
  funext x; simp [cj, h]

def cjEnd {X Y : Type} (e : Y ≃ X) : Module.End ℂ (X → ℂ) →* Module.End ℂ (Y → ℂ) where
  toFun L :=
    { toFun := fun f => cj e (L (cj e.symm f))
      map_add' := fun f f' => by
        have : cj e.symm (f + f') = cj e.symm f + cj e.symm f' := by funext x; simp [cj]
        rw [this, map_add (f := _)]; funext y; simp [cj]
      map_smul' := fun c f => by
        have : cj e.symm (c • f) = starRingEnd ℂ c • cj e.symm f := by funext x; simp [cj]
        rw [this, map_smul]; funext y; simp [cj] }
  map_one' := LinearMap.ext fun f => cj_cj e.symm e e.symm_apply_apply f
  map_mul' L L' := LinearMap.ext fun f => by
    show cj e (L (L' (cj e.symm f))) = cj e (L (cj e.symm (cj e (L' (cj e.symm f)))))
    rw [cj_cj e e.symm e.apply_symm_apply]

theorem cjEnd_cj {X Y : Type} (e : Y ≃ X) (L : Module.End ℂ (X → ℂ)) (f : X → ℂ) : cjEnd e L (cj e f) = cj e (L f) := by
  show cj e (L (cj e.symm (cj e f))) = _
  rw [cj_cj e e.symm e.apply_symm_apply]

def conjTarget {S T : HSp D} (om : Rep S T) : Rep S (negSp T) :=
  (cjEnd (Equiv.refl (WO S T))).comp (om.comp ((MonoidHom.id _).prodMap (negGA T).symm.toMonoidHom))

def conjSource {S T : HSp D} (om : Rep S T) : Rep (negSp S) T :=
  (cjEnd (Equiv.refl (WO S T))).comp (om.comp ((negGA S).symm.toMonoidHom.prodMap (MonoidHom.id _)))

def dagger (S T : HSp D) (x : WO S T) : WO T S := giA S ⬝ (adj x ⬝ gA T)

theorem dagger_dagger (S T : HSp D) (x : WO S T) : dagger T S (dagger S T x) = x := by
  simp only [dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, giA_gA_cancel]

def daggerEquiv (S T : HSp D) : WO T S ≃ WO S T where
  toFun := dagger T S
  invFun := dagger S T
  left_inv := dagger_dagger T S
  right_inv := dagger_dagger S T

def conjAdjoint {S T : HSp D} (om : Rep S T) : Rep T S :=
  (cjEnd (daggerEquiv S T)).comp (om.comp (MulEquiv.prodComm : GA D T × GA D S ≃* GA D S × GA D T).toMonoidHom)

structure ConjAdjoint (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop where

  theta_neg : ∀ f : WO S T → ℂ, (IsThetaFunO ψ S (negSp T) (cj id f) ↔ IsThetaFunO ψ S T f) ∧
    (IsThetaFunO ψ (negSp S) T (cj id f) ↔ IsThetaFunO ψ S T f)

  heis_neg : ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (negSp T) w (cj id f) = cj id (heisO ψ S T w f) ∧
    heisO ψ (negSp S) T w (cj id f) = cj id (heisO ψ S T w f)

  conj_target : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ (conjTarget om) ∧
    ∀ om' : Rep S (negSp T), IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (g, negGA T h) (cj id f) = cj id (om (g, h) f)

  conj_source : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ (conjSource om) ∧
    ∀ om' : Rep (negSp S) T, IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (negGA S g, h) (cj id f) = cj id (om (g, h) f)

  sympl_dagger : ∀ x y : WO S T, symplO T S (dagger S T x) (dagger S T y) = -symplO S T x y

  act_dagger : ∀ g h (x : WO S T), dagger S T (actO S T g h x) = actO T S h g (dagger S T x)

  theta_dagger : ∀ f : WO S T → ℂ, IsThetaFunO ψ T S (cj (dagger T S) f) ↔ IsThetaFunO ψ S T f

  heis_dagger : ∀ (w : WO S T) (f : WO S T → ℂ),
    heisO ψ T S (dagger S T w) (cj (dagger T S) f) = cj (dagger T S) (heisO ψ S T w f)

  conj_adjoint : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ T S χT χS (conjAdjoint om) ∧
    ∀ om' : Rep T S, IsWeilDatumO ψ T S χT χS om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f)

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (Φ : FormsL LL Ks WL W G)

def ball (la : HeightOneSpectrum (𝓞 Ks)) : Set Φ.WK := {f | ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1}

def resW (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK) : Φ.WK →ₗ[Ks] Φ.WK :=
  (hL.restrictScalars Ks).restrict hW

def LiesOver (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') : Prop :=
  ∀ x : Ks, algebraMap Ks K' x ∈ O ↔ FinitePlace.mk la x ≤ 1

def latK (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[Ks] Φ.WK) :=
  Submodule.span O ((fun f : Φ.WK => (1 : K') ⊗ₜ[Ks] f) '' ball Φ la)

def latKIn (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K')
    (V : Submodule LL WL) : Submodule O (K' ⊗[Ks] Φ.WK) :=
  latK Φ la O ⊓ (((V.restrictScalars Ks).comap Φ.WK.subtype).baseChange K').restrictScalars O

def latL (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra LL K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[LL] WL) :=
  Submodule.span O ((fun f : Φ.WK => (1 : K') ⊗ₜ[LL] (f : WL)) '' ball Φ la)

def latLIn (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra LL K'] (O : ValuationSubring K')
    (V : Submodule LL WL) : Submodule O (K' ⊗[LL] WL) :=
  latL Φ la O ⊓ (V.baseChange K').restrictScalars O

structure Keeps (la : HeightOneSpectrum (𝓞 Ks)) (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK) : Prop where

  sup : ∀ f : Φ.WK, (∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) → ∀ y : Φ.Pt la, Φ.nrm la y ⟨hL f, hW f f.2⟩ ≤ 1

  rho : ∀ g : G, hL ∘ₗ Φ.ρ g = Φ.ρ g ∘ₗ hL

  eOp : ∀ eC : G → LL, hL ∘ₗ Φ.eOp eC = Φ.eOp eC ∘ₗ hL

  typeP : ∀ (J : Subgroup G) (lam : J →* LLˣ), ∀ x ∈ Φ.typeP J lam, hL x ∈ Φ.typeP J lam

  good : ∀ eC : G → LL, ∀ x ∈ Φ.good eC, hL x ∈ Φ.good eC

  overK : ∀ (K' : Type) [Field K'] [Algebra Ks K'] (O : ValuationSubring K'), LiesOver la O →
    (∀ x ∈ latK Φ la O, (resW Φ hL hW).baseChange K' x ∈ latK Φ la O) ∧
    ∀ (J : Subgroup G) (lam : J →* LLˣ),
      (∀ x ∈ latKIn Φ la O (Φ.typeP J lam), (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O (Φ.typeP J lam)) ∧
      ∀ eC : G → LL, ∀ x ∈ latKIn Φ la O (Φ.Wgood J lam eC),
        (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O (Φ.Wgood J lam eC)

  overL : ∀ (K' : Type) [Field K'] [Algebra LL K'] [Algebra Ks K'] [IsScalarTower Ks LL K'] (O : ValuationSubring K'),
    LiesOver la O →
    (∀ x ∈ latL Φ la O, hL.baseChange K' x ∈ latL Φ la O) ∧
    ∀ (J : Subgroup G) (lam : J →* LLˣ),
      (∀ x ∈ latLIn Φ la O (Φ.typeP J lam), hL.baseChange K' x ∈ latLIn Φ la O (Φ.typeP J lam)) ∧
      ∀ eC : G → LL, ∀ x ∈ latLIn Φ la O (Φ.Wgood J lam eC), hL.baseChange K' x ∈ latLIn Φ la O (Φ.Wgood J lam eC)

end Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def hkC {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : ℂ :=
  ((((R.C.mu0 i).val P : ℂˣ) : ℂ) ^ k)⁻¹ * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹

def IsHkData {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ k ≤ D.R.r ∧
    IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def OffChar {Ks : Type} [Field Ks] [NumberField Ks] (P : Formalism.L2.DIV.Pl D.host.E) (la : HeightOneSpectrum (𝓞 Ks)) : Prop :=
  ∀ p : ℕ, p.Prime → (p : 𝓞 D.host.E) ∈ P.asIdeal → (p : 𝓞 Ks) ∉ la.asIdeal

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def ConstPinned (i : Fin D.R.m) : Prop :=
  ∃ (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
    O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧
    O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph

theorem constPinned_of (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) (hp : OMPins T R κ v₀ O i)
    (hr : OneMapRow0 T R κ v₀ O i) (hc : CTie T R κ v₀ O i) : ConstPinned T R κ v₀ i :=
  ⟨O i, (hc hr).choose, hp.1, hp.2, (hc hr).choose_spec⟩

structure ReadAt0 (i : Fin D.R.m) : Prop where
  ex : ∀ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i, JEvAt T R κ v₀ i (sg0 D A) hV
  inj : Function.Injective ((R.FW i).j (sg0 D A))
  rho : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (actW R i (sg0 D A)) (R.FW i).chi (R.FW i).ρ
  const : ConstPinned T R κ v₀ i

theorem readAt0_of (hj : JEvExists T R κ v₀) (fw : FWTie T R κ v₀) (hu : R.LUnif) (i : Fin D.R.m)
    (hc : ConstPinned T R κ v₀ i) : ReadAt0 T R κ v₀ i := by
  refine ⟨fun hV => hj i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV,
    ?_, (hu i (sg0 D A)).2.2, hc⟩
  refine (injective_iff_map_eq_zero ((R.FW i).j (sg0 D A))).2 fun x hx => ?_
  by_contra h
  have h1 := (hu i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h)
  exact h1.ne_zero 0 hx

def HkSupAt (i : Fin D.R.m) : Prop :=
  ∀ (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))), IsHkData R i P k α Rc →
    ∀ (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)),
      HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) (hkC R i P k) hL →
      ∀ (hW : ∀ x ∈ (R.FW i).WK, hL x ∈ (R.FW i).WK) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OffChar P la →
        Keeps (R.FW i) la hL hW

end GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Ker (ipO)
open scoped TensorProduct ENNReal ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def hermAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  ((gramAt D V τ)⁻¹ * wᴴ * gramAt D W τ * z).trace

def symplAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hermAt V W τ z w).re


open Classical in
def commScalar (V W : HSp D) (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  if τ = τ' then -(2 * Real.pi * Complex.I) * (symplAt V W τ z w : ℂ) else 0

def Cocompact (V W : HSp D) : Prop := CompactSpace (WO V W ⧸ (ratL W V : AddSubgroup (WO V W)))

def SquareIntegrable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∀ f, IsThetaFunO ψ V W f →
    (∀ γ ∈ ratL W V, ∀ x : WO V W, ‖f (γ + x)‖ = ‖f x‖) ∧
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      MemLp f 2 (μ.restrict 𝓕)

def HeisUnitary (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  (∀ (u v : WO V W) (f : WO V W → ℂ),
    heisO ψ V W u (heisO ψ V W v f) = ψ (symplOH V W u v) • heisO ψ V W (u + v) f) ∧
  (∀ (u : WO V W) (f : WO V W → ℂ), heisO ψ V W (-u) (heisO ψ V W u f) = f) ∧
  (∀ u f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (heisO ψ V W u f)) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
    ∀ u f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      ipO μ 𝓕 (heisO ψ V W u f) (heisO ψ V W u f') = ipO μ 𝓕 f f') ∧
  ∀ γ ∈ ratL W V, ∀ f, IsThetaFunO ψ V W f → heisO ψ V W γ f 0 = f 0

def DerSkew (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ f, IsThetaFunO ψ V W f → ∀ x, HasDerivAt (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) f x)
      (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f x) 0) ∧
    (∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f)) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
        ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) f' =
          -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f')

def DerComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ s t : ℝ, ψ (symplO V W (lineAt θ τ z s) (lineAt θ τ' w t)) =
      Complex.exp (s * t * commScalar V W τ τ' z w)) ∧
    ∀ f, IsThetaFunO ψ V W f →
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w f) -
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
          commScalar V W τ τ' z w • f

def FinRealComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ u : WO V W, u.map (infPart D) = 0 →
    (∀ v : WO V W, v.map (finPart D) = 0 → ∀ f : WO V W → ℂ,
      heisO ψ V W u (heisO ψ V W v f) = heisO ψ V W v (heisO ψ V W u f)) ∧
    ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (f : WO V W → ℂ), IsThetaFunO ψ V W f →
      heisO ψ V W u (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (heisO ψ V W u f)

def ThetaSquareIntegrable (D : D7) : Prop :=
  ∀ V W : HSp D, Cocompact V W ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
      SquareIntegrable ψ V W ∧ HeisUnitary ψ V W ∧
        ∀ θ : InfFam D, IsInfFam θ → DerSkew ψ θ V W ∧ DerComm ψ θ V W ∧ FinRealComm ψ θ V W

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

end
end

