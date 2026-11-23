module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.SepPer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def eu {n : ℕ} (y : Fin n → ℂ) : ℝ := Real.sqrt (∑ i, ‖y i‖ ^ 2)

def hsn {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)

section Point

variable (θ : InfFam D) {V : HSp D}

abbrev cmp (τ : D.what₂.Tau) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ := infMat D.sp.cm.sig V.gram (θ τ) g

def nrm (A : Fr V) (x : GA D V) (τ : D.what₂.Tau) (y : Fin V.rank → D.host.E) : ℝ :=
  eu (A.fr τ *ᵥ (cmp θ τ x⁻¹ *ᵥ fun i => tauE D τ (y i)))

def latAt (Λ : Lat V) (x : GA D V) : Lat V :=
  Submodule.span (𝓞 D.host.E) {y | (Lev.finE V x⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
    Formalism.L2.Herm.hatL (F := D.host.F) Λ}

def Long (A : Fr V) (Λ : Lat V) (x : GA D V) (s : ℝ) : Prop :=
  ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ w ∈ 𝔪 • latAt Λ x, w ≠ 0 →
    s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, nrm θ A x τ w

def Lip (A : Fr V) (φ : GA D V → ℂ) (c : ℝ) : Prop :=
  ∀ x τ, ∀ X ∈ lieAt V τ, ∀ s : ℝ, ‖φ (x * oneP θ V τ X s) - φ x‖ ≤ c * |s| * hsn (A.fr τ * X * (A.fr τ)⁻¹)

variable {S : D.what₂.Tau → SPar} (M : DSModel V S)

def coefR (v a : ∀ τ, M.H τ) (g : GA D V) : ℂ := ∏ τ, ⟪v τ, M.rep τ (cmp θ τ g) (a τ)⟫_ℂ


open Classical in
def coef (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ) (g : GA D V) : ℂ :=
  if Lev.finE V g ∈ K then coefR θ M v a g else 0

def poin (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ) (c : GA D V) (a : ∀ τ, M.H τ) (g : GA D V) : ℂ :=
  ∑' γ : GQ V, coef θ M K v a (c * γ * g)

def DecayAt (τ : D.what₂.Tau) (v a : M.H τ) (N : ℕ) : Prop :=
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ‖⟪v, M.rep τ g a⟫_ℂ‖ * (1 + hsn g) ^ N ≤ C

def KDecay (v : ∀ τ, M.H τ) : Prop :=
  ∀ τ, v τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ∧ ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, DecayAt M τ (v τ) a (2 * V.rank ^ 2 + 1)

end Point

section Pack

variable (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1)

def zv : Fin V.rank → D.host.E := fun i => d.a i 0

def Adapted (A : Fr Y) (B : Fr V) : Prop :=
  ∀ τ (y : Fin Y.rank → ℂ) (a : ℂ),
    eu (B.fr τ *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A.fr τ *ᵥ y) ^ 2 + ‖a‖ ^ 2

variable {S S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S') (M : DSModel V S)

structure Pack where

  A : Fr Y

  B : Fr V

  v₀ : ∀ τ, M.H τ

  g₀ : GA D V

  w : M₀.Vec

variable {M₀ M}

def Pack.v (p : Pack M₀ M) : ∀ τ, M.H τ := fun τ => M.rep τ (cmp θ τ p.g₀) (p.v₀ τ)

structure Pack.Base (p : Pack M₀ M) : Prop where

  adapted : Adapted d p.A p.B

  real : p.g₀ ∈ GinfC V

  dec : ∀ τ, p.v₀ τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ∧ DecayAt M τ (p.v₀ τ) (p.v₀ τ) (2 * V.rank ^ 2 + 1)

  ne : ∀ τ, (p.w τ : M₀.H τ) ≠ 0

structure Pack.RealAt (p : Pack M₀ M) (Q : ℝ) (m : Measure (GinfC Y)) (c : ℂ) : Prop where

  ne : c ≠ 0

  act : ∀ b : ∀ τ, M₀.H τ, ∫ h : GinfC Y, coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h) * coefR θ M₀ b (fun τ => p.w τ) h ∂m =
    c * ∏ τ, ⟪b τ, (p.w τ : M₀.H τ)⟫_ℂ

  far : ∀ g : GA D V, Integrable (fun h : GinfC Y => coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d h)) m ∧
    (∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d h)‖ ∂m) * (∏ τ, nrm θ p.B g⁻¹ τ (zv d)) ^ (2 * V.rank + 5) ≤
      Real.exp Q * ‖c‖

  lip : ∀ τ, ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    ∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X s * h)) - coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h)‖ ∂m ≤
      Real.exp Q * ‖c‖ * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)

def Pack.Is (p : Pack M₀ M) (Q : ℝ) : Prop :=
  p.Base d ∧ ∀ m : Measure (GinfC Y), m.IsHaarMeasure → ∃ c, p.RealAt θ d Q m c

structure Pack.AdelicAt (p : Pack M₀ M) (Q : ℝ) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)) (ν : Measure (GA D Y)) (φ : GA D Y → ℂ)
    (c : ℂ) : Prop where

  ne : c ≠ 0

  one : ∀ x, ∫ h, coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h) * φ h ∂ν = c * φ x

  term : ∀ (x : GA D Y) (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z →
    Integrable (fun h => coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h)) ν ∧
    (∫ h, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h)‖ ∂ν) *
      (∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ z) ^ (2 * V.rank + 5) ≤ Real.exp Q * ‖c‖ ∧
    (z - zv d ∉ 𝔪 • latAt Λ (stabilizerEmbedding d x) →
      ∀ h, coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h) = 0)

end Pack

def rdisc (D : D7) : ℝ := |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.E)

def loss (D : D7) (C b : ℝ) : ℝ := C * Fintype.card D.what₂.Tau * ((D.R.r : ℝ) + 1) ^ 4 * Real.log b

def Pays (D : D7) (Q N : ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧
    Real.exp Q * ((D.R.r : ℝ) ^ 2 * Fintype.card D.what₂.Tau * (D.host.g 0 * D.host.g 1 : ℕ) * rdisc D * (2 * s) ^ ((1 : ℝ) / D.R.m)) ≤ 1 / 2 ∧
    2 * Real.exp (Q + (6 * ((D.R.r : ℝ) + 1) + 9) * Fintype.card D.what₂.Tau) ≤ s ^ Fintype.card D.what₂.Tau * Real.sqrt N ∧
    1 < s ^ Fintype.card D.what₂.Tau * Real.sqrt N

def PackEx : Prop := ∃ C : ℝ, 0 ≤ C ∧ Ev fun {D} _ _ {sc} {G} W _ => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), ∃ p : Pack M₀ MP, p.Is W.θ G.sp.dec0 (loss D C sc.b)

def DepthPays : Prop := ∀ C : ℝ, 0 ≤ C → Ev fun {D} _ _ {sc} {G} _ _ => Pays D (loss D C sc.b) (Ideal.absNorm G.modul)

theorem eu_zero {n : ℕ} : eu (0 : Fin n → ℂ) = 0 := by simp [eu]

end GlobalTheory.SepPer

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct nonZeroDivisors ComplexConjugate
open GlobalTheory.SepRows GlobalTheory.EvenOnto
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure ReLat (V : HSp D) where

  L0 : Submodule (𝓞 D.host.E) V.V
  lat : Submodule.IsLattice D.host.E L0
  unimod : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L0

@[reducible] def ReLat.sp {V : HSp D} (r : ReLat V) : HSp D := { V with L0 := r.L0, standardTuple_isLattice := r.lat, baseLattice_isUnimodular := r.unimod }

@[reducible] def ReLat.mod {V : HSp D} (r : ReLat V) {S : D.what₂.Tau → SPar} (M : DSModel V S) : DSModel r.sp S where
  H := M.H
  σ := M.σ
  lam := M.lam
  ε := M.ε
  fr := M.fr
  enum := M.enum
  ds := M.ds
  fr_unit := M.fr_unit
  fr_gram := M.fr_gram

def scaleLat {n : ℕ} (𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {y | ∃ a ∈ 𝔟, ∃ x ∈ Λ, y = a • x}

def exch (A B : HSp D) (f : WO A B → ℂ) : WO (negSp B) A → ℂ := fun x => f (adjO A B x)

def Exch {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D (negSp B) × GA D A →* Module.End ℂ (WO (negSp B) A → ℂ))
    (ω' : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ A B f → ∀ g h, ω (negGA B h, g) (exch A B f) = exch A B (ω' (g, h) f)

def ExchLaw (D : D7) : Prop := ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) →
  (∀ f, IsThetaFunO ψ A B f ↔ IsThetaFunO ψ (negSp B) A (exch A B f)) ∧
  (∀ x f, heisO ψ (negSp B) A x (exch A B f) = exch A B (heisO ψ A B (adjO A B x) f)) ∧
  (∀ x x' : WO (negSp B) A, symplO (negSp B) A x x' = symplO A B (adjO A B x) (adjO A B x')) ∧
  Function.Bijective (adjO A B) ∧
  (∀ m X, IsCovolOne (ratL B A) m X → ∃ m' X', IsCovolOne (ratL A (negSp B)) m' X' ∧
    ∀ f f' : WO A B → ℂ, ∫ w in X, f w * conj (f' w) ∂m = ∫ w in X', exch A B f w * conj (exch A B f' w) ∂m') ∧
  ∀ χS χT ω, IsWeilDatumO ψ (negSp B) A χS χT ω → ∃ ω', IsWeilDatumO ψ A B χT⁻¹ χS⁻¹ ω' ∧ Exch ψ ω ω'

def ReLatLaw (D : D7) : Prop :=
  (∀ (V : HSp D) Λ, IsSelfDualC V Λ → ∃ r : ReLat V, GlobalTheory.AdelicU.frameLat r.sp = Λ) ∧
  (∀ (V : HSp D) (r : ReLat V) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)),
    (MultT θ (r.mod M) J 1 : Submodule ℂ (SmT M →ₗ[ℂ] (GA D V → ℂ))) = MultT θ M J 1 ∧
    (KF (r.mod M) : Submodule ℂ (SmT M)) = KF M ∧ cart (r.mod M) = cart M ∧
    GlobalTheory.Cusp.wittIndex r.sp = GlobalTheory.Cusp.wittIndex V ∧ ∀ F : GA D V → ℂ, RapidDec r.sp F ↔ RapidDec V F) ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (r : ReLat A) (r' : ReLat B),
    (∀ f : WO A B → ℂ, IsThetaFunO ψ r.sp r'.sp f ↔ IsThetaFunO ψ A B f) ∧
    ∀ χS χT (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)),
      IsWeilDatumO ψ r.sp r'.sp χS χT ω ↔ IsWeilDatumO ψ A B χS χT ω

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

def gridCom : Com D where
  θ := W.θ
  ψ := W.ψ
  S := G.pl.S0
  n := nRk D
  t := sLen D - 1
  m := D.R.m
  χ := fun k => (G.ch.chi (D.R.m - k))⁻¹
  a := fun k τ => -(cen D sc.cGap τ (D.R.m - k) : ℚ)


variable (G) in
def IsCoreLat (i : ℕ) (r : ReLat (G.V (.core i))) : Prop :=
  GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i))


variable (G) in
@[reducible] def gridStage (v : CoreVol G) (i : ℕ) (r : ReLat (G.V (.core i)))
    (M : DSModel (G.V (.core i)) (Node.par D sc.cGap (.core i))) : PiLocalization₂ D where
  V := r.sp
  par := Node.par D sc.cGap (.core i)
  M := r.mod M
  J := lev G (.core i)
  ν := (v i).μ
  fd := (v i).𝓕


variable (G) in
def IsOntoMod (i : ℕ) (x₀ : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core (i + 1))).rank) D.host.E) : Prop :=
  x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)) ∧ ∃ y₀ ∈ homLat (G.Λ (.core i)) (G.Λ (.core (i + 1))),
    x₀ * y₀ - 1 ∈ G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i))

def CosLaw (i : ℕ) (x₀ : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core (i + 1))).rank) D.host.E)
    (Φ : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ) : Prop :=
  Dep W (.core i) Φ ∧ ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
    (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
    heisO W.ψ _ _ y Φ = W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) • Φ

def Below (v : CoreVol G) (k : ℕ) (F : Fn G (.core k)) : Set (Fn G (.core 0)) :=
  {F₀ | ∃ Ψ : ∀ i, Fn G (.core i), (∀ i, i ≤ k → RapidDec (G.V (.core i)) (Ψ i)) ∧
    (∀ i, i < k → ∃ f : Sch G (.coreDown i), Dep W (.core i) f ∧ Ψ i = dn W v i f (Ψ (i + 1))) ∧ Ψ 0 = F₀ ∧ Ψ k = F}

def ComOK : Prop := Gap fun {_} _ _ _ _ W _ => (gridCom W).Is

def StageOK : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i ≤ D.R.m → (∃ r, IsCoreLat G i r) ∧
  ∀ r, IsCoreLat G i r → ∀ v M, (gridStage G v i r M).Is (gridCom W) i

def ParOK : Prop := ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ i, i < D.R.m → ∀ τ,
  UpPair (sLen D - 1) (Node.par D 1 (.core i) τ) (Node.par D 1 (.core (i + 1)) τ) (-(cen D 1 τ (D.R.m - i) : ℚ))
    (-(cen D 1 τ (D.R.m - i) : ℚ))

def OntoModEx : Prop := All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∃ x₀, IsOntoMod G i x₀

def LatExch : Prop := All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' →
  ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (x : WO (G.pS (.core i)) (G.pT (.core i))),
    x ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (T := _) (.core i) : Set _) (G.latT (.core i) : Set _) P ↔
      adjO (G.V (.core i)) (G.V (.core (i + 1))) x ∈
        latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) P

def DatumEx : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' →
  ∀ (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'), ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)),
    ∃ f, IsVacVec W.ψ W.θ M M' f ∧
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff W.ψ r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp) (GlobalTheory.AdelicU.frameLat r'.sp) G.pl.S0 f ∧
      ∀ φ, CosLaw W i x₀ (exch (G.V (.core i)) (G.V (.core (i + 1))) (ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ M M' f φ))

def CosSupp : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ Φ, CosLaw W i x₀ Φ →
  ∀ m X, IsCovolOne (ratL (G.pT (.core i)) (G.pS (.core i))) m X → ∀ g : GA D (G.V (.core i)),
    (∀ v ∉ G.pl.S0, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram v g ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (G.Λ (.core i)) v) →
    (∫ w in X, W.om (.core i) (1, g) Φ w * conj (Φ w) ∂m) ≠ 0 → Lev.finE (G.V (.core i)) g ∈ G.levCong (.core i)

def PreOK : Prop := Gap fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ v M M',
  ∃ ω f, PreStep (gridCom W) i (gridStage G v i r M) (gridStage G v (i + 1) r' M') ω f ∧ Exch W.ψ (W.om (.core i)) ω ∧
    ∀ φ, Dep W (.core i) (exch (G.V (.core i)) (G.V (.core (i + 1))) (ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ))

def ChainEx : Prop := Gap fun {D} _ _ _ {G} W _ => ∀ v r₀ M₀, IsCoreLat G 0 r₀ → ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧
  ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k (gridStage G v k r M) Θ ∧
    ∀ y, ∀ x ∈ (gridStage G v 0 r₀ M₀).KF, PiLocalization₂.val (Θ y) x ∈
      Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (PiLocalization₂.val y w)}

def TopCols : Prop := All fun {D} _ _ {sc} {G} W _ =>
  ∀ M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)), ∀ y ∈ CoreForms G W.θ D.R.m M, ∀ w,
    ∃ c ∈ Cols G W.θ, ∃ ξ : Module.Dual ℂ (coefPlus G W.θ).W, y w = pairVec (coefPlus G W.θ) ξ c

end GlobalTheory.CoreOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PairEx : Prop := ∀ (D : D7) (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ),
  (∀ τ, GlobalTheory.PairLift.PairPar (S τ) (S' τ) (aS τ) (aT τ)) → ∀ (V W : HSp D) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω : GlobalTheory.Grid.WRep V W, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f →
        IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It

def parRow (D : D7) (C : ℝ) (i : ℕ) : D.what₂.Tau → SPar := fun τ => dualPar (Node.par D C (.grid i 0) τ)

def RowModels : Prop := Gap fun {D} _ _ {sc} {G} W _ => ∀ i, i ≤ D.R.m →
  ∃ MV : DSModel (G.V (.grid i 0)) (parRow D sc.cGap i), cart MV = W.cart (.grid i 0)

def RowStep : Prop := Gap fun {D} {T} _ {sc} {G} W M => ∀ i, i < D.R.m → ∀ (S S' : D.what₂.Tau → SPar)
  (MA : DSModel (G.V (.grid i 0)) S) (MB : DSModel (G.V (.grid (i + 1) 0)) S'), S = parRow D sc.cGap i → S' = parRow D sc.cGap (i + 1) →
    cart MA = W.cart (.grid i 0) → cart MB = W.cart (.grid (i + 1) 0) →
    ∃ It : PolF D (G.V (.grid i 0)).rank (G.V (.grid (i + 1) 0)).rank → SmT MA → SmT MB, ∀ F ∈ MultT W.θ MA ∅ 1, ∀ κ : G.CosAt i,
      ∃ F' ∈ MultT W.θ MB ∅ 1, ∀ P v,
        LiftConv W M (.right i 0 : Arrow T) (W.fock (.chi i 0) (W.cosVec i κ) P) (F v) ∧
          liftA W M (.right i 0 : Arrow T) (W.fock (.chi i 0) (W.cosVec i κ) P) (F v) = F' (It P v)

def RowTower : Prop := Gap fun {D} {T} _ {sc} {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ (n : ℕ) (h : n ≤ D.R.m), ∃ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid n 0)) S), S = parRow D sc.cGap n ∧
    cart MB = W.cart (.grid n 0) ∧ ∃ vec : G.RealVec → SmT M₀ → SmT MB, ∀ t ∈ MultT W.θ M₀ ∅ 1, ∀ Φ : G.Datum,
      ∃ F' ∈ MultT W.θ MB ∅ 1, ∀ ρ w,
        PathConv W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) (t w) ∧ part W M ρ Φ (t w) n h = F' (vec ρ w)

def CoefTensor : Prop := ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is →
  ∃ (Wt : D.what₂.Tau → Type) (_ : ∀ τ, AddCommGroup (Wt τ)) (_ : ∀ τ, Module ℂ (Wt τ)) (_ : ∀ τ, FiniteDimensional ℂ (Wt τ))
    (π : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (Wt τ)) (e : (⨂[ℂ] τ, Wt τ) ≃ₗ[ℂ] Module.Dual ℂ c.W),
    (∀ τ, GlobalTheory.RealBessel.IsContIrred (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (π τ)) ∧
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x y : ∀ τ, Wt τ, y τ = π τ g (x τ) → (∀ τ', τ' ≠ τ → y τ' = x τ') →
        e (PiTensorProduct.tprod ℂ y) = e (PiTensorProduct.tprod ℂ x) ∘ₗ c.ρ (atTau θ V τ g)⁻¹

section Sep

variable {D : D7} {V A : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {r : ℕ}
  (F : D.what₂.Tau → Matrix (Fin V.rank) (Fin A.rank) ℂ) (e : D.what₂.Tau → Matrix (Fin V.rank) (Fin r) ℂ)
  (χ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) {Wt : D.what₂.Tau → Type} [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)]
  (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → Module.End ℂ (Wt τ))


open Classical in
def SepBes (β : (∀ τ, Wt τ) → M.Vec → ℂ) : Prop :=
  ∀ τ x v, ∃ b ∈ GlobalTheory.RealBessel.besselForms (gramAt D V τ) (gramAt D A τ) (F τ) (e τ) (χ τ) (M.rep τ) (π τ) (M.sm τ),
    ∀ y u, β (Function.update x τ y) (Function.update v τ u) = b y u

end Sep

def TopFrame : Prop := All fun {D} _ _ _ {G} W _ => ∃ z : D.what₂.Tau → Fin (G.V (.grid D.R.m 0)).rank → ℂ, ∀ τ,
  GlobalTheory.RealBessel.IsFrame (gramAt D (G.V (.grid D.R.m 0)) τ) (gramAt D (G.V (.top 0)) τ)
               ((frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ)) (G.besTop.e.map (tauE D τ)) (z τ) ∧
    GlobalTheory.RealBessel.IsGeneric (gramAt D (G.V (.grid D.R.m 0)) τ) (G.besTop.e.map (tauE D τ)) (z τ)
      fun u => besChar W.ψ G.besTop (atTau W.θ _ τ u)

def TopSep : Prop := All fun {D} _ _ _ {G} W M => ∀ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid D.R.m 0)) S),
  ∀ F' ∈ MultT W.θ MB ∅ 1, ∀ Ψ ∈ Cols G W.θ,
    (∃ b : Module.Dual ℂ (coefPlus G W.θ).W →ₗ[ℂ] SmT MB →ₗ[ℂ] ℂ, ∀ ξ v, Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v) = b ξ v) ∧
    ∀ (Wt : D.what₂.Tau → Type) [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)]
      (π : ∀ τ, Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ → Module.End ℂ (Wt τ))
      (e : (⨂[ℂ] τ, Wt τ) ≃ₗ[ℂ] Module.Dual ℂ (coefPlus G W.θ).W),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.top 0)) τ), ∀ x y : ∀ τ, Wt τ, y τ = π τ g (x τ) → (∀ τ', τ' ≠ τ → y τ' = x τ') →
        e (PiTensorProduct.tprod ℂ y) = e (PiTensorProduct.tprod ℂ x) ∘ₗ (coefPlus G W.θ).ρ (atTau W.θ _ τ g)⁻¹) →
      SepBes MB (fun τ => (frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ))
        (fun τ => G.besTop.e.map (tauE D τ)) (fun τ u => besChar W.ψ G.besTop (atTau W.θ _ τ u)) π
        fun x v => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ x)) Ψ) (F' (PiTensorProduct.tprod ℂ v))

def RowConv : Prop := Gap fun {D} _ {L} _ {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ t ∈ Rows L W.θ M₀, ∀ w ρ ξ, ∀ Ψ ∈ Cols G W.θ, ∀ Φ, FConv W M ρ ξ Ψ Φ (t w)

def GoodRows : Prop := ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ t ∈ R.EEat R.triv,
    PiTensorProduct.lift t ∈ Rows R.toLevCh R.θ (R.MY 0)

theorem parRow_zero (D : D7) (C : ℝ) : parRow D C 0 = parB (Ptw D) 0 :=
  funext fun τ => congrArg dualPar (parV_zero D C (Nat.zero_le _) τ)

end GlobalTheory.SepRows

end
end

