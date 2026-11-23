module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.HermitianForms.TiedSym

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S
open scoped Topology TensorProduct ContDiff

namespace GlobalTheory.CuspGeo

section Inst

variable (I : AutInst)

def IntVec (u : Fin I.n → I.E) : Prop := ∀ i, IsIntegral ℤ (u i)

def vec (y : I.Ginf) (u : Fin I.n → I.E) : InfinitePlace I.F → Fin I.n → ℂ :=
  fun v => uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i))

def NoShort (y : I.Ginf) (t : ℝ) : Prop := ∀ u, IntVec I u → u ≠ 0 → t ≤ ‖vec I y u‖

def Close (u : I.Ginf) (δ : ℝ) : Prop := ∀ v i j, ‖(uMat (u v) - 1) i j‖ ≤ δ

def IsZBasis {N : ℕ} (e : Fin N → Fin I.n → I.E) : Prop :=
  LinearIndependent ℤ e ∧ ∀ u, IntVec I u ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e i

def IsRealCoord {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) : Prop :=
  ∀ x y, ρ x ⬝ᵥ ρ y = ∑ v, ∑ i, (star (x v i) * y v i).re

def gm {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ρ (vec I y (e j)) i

def trForm (x y : Fin I.n → I.E) : ℚ := Algebra.trace ℚ I.E (Formalism.UG.hform (starRingEnd I.E) I.J x y)

def BddType {N : ℕ} (R : ℝ) (e : Fin N → Fin I.n → I.E) : Prop :=
  (∀ k j, ∃ z : Fin N → ℤ, (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i ∧ ∀ i, |(z i : ℝ)| ≤ R) ∧
    ∀ i j, |(trForm I (e i) (e j) : ℝ)| ≤ R

def RedBasis : Prop :=
  ∃ (N : ℕ) (R C : ℝ), ∀ y : I.Ginf, ∃ e : Fin N → Fin I.n → I.E, IsZBasis I e ∧ BddType I R e ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 → NoShort I y t → ∀ j, ‖vec I y (e j)‖ * t ^ N ≤ C

def HtMin : Prop :=
  ∃ (b : ℕ) (C : ℝ) (K : Set I.Gf), IsCompact K ∧ ∀ (y : I.Ginf) (t : ℝ), 0 < t → t ≤ 1 → NoShort I y t →
    ∃ γ ∈ I.GFset, γ.2 ∈ K ∧ ∀ v i j, ‖uMat ((γ.1 * y) v) i j‖ * t ^ b ≤ C

def ShortCusp : Prop :=
  ∀ U ∈ 𝓝 (1 : I.Gf), ∃ s₀ η₀ C : ℝ, 0 < s₀ ∧ 0 < η₀ ∧ ∀ (y : I.Ginf) (η : ℝ), 0 < η → η ≤ η₀ →
    (∃ u, IntVec I u ∧ u ≠ 0 ∧ ‖vec I y u‖ ≤ s₀ * η ^ (I.n + 1)) →
    ∃ W, I.IsIsot W ∧ ∀ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA W →
      ∃ γ ∈ I.GFset, γ.2 ∈ U ∧ Close I (y⁻¹ * (γ.1 * m) * y) (C * η)

def NearInst : Prop :=
  ∀ Kp : Subgroup I.Gf, IsOpen (Kp : Set I.Gf) → ∃ (b : ℕ) (C δ₀ : ℝ) (K : Set I.Gf), 0 < δ₀ ∧ IsCompact K ∧
    ∀ x : I.GA, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∃ γ ∈ I.GFset, (γ * x).2 ∈ K ∧ ∀ v i j, ‖uMat ((γ * x).1 v) i j‖ * δ ^ b ≤ C) ∧
      (δ₀ ≤ δ ∨ ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset, ∃ u : I.Ginf, ∃ k ∈ Kp,
        m * x = γ * x * (u, k) ∧ Close I u (C * δ))

end Inst

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

def CloseR (u : GA D V) (δ : ℝ) : Prop :=
  u ∈ GinfC V ∧ ∀ τ i j, ‖(infMat D.sp.cm.sig V.gram (θ τ) u - 1) i j‖ ≤ δ

def Near : Prop :=
  ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ ∧
    ∀ g : GA D V, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ GlobalTheory.Grow.quotHeight V g * δ ^ b ≤ C ∧
      (δ₀ ≤ δ ∨ ∃ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ ∧ ∀ m ∈ NI V C₀,
        ∃ γ ∈ GQ V, ∃ u k : GA D V, CloseR θ V u (C * δ) ∧ k ∈ U ∧ k ∈ GfC V ∧ m * g = γ * g * u * k)

def SmoothW (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

end Rec

end GlobalTheory.CuspGeo

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

abbrev EF (D : D7) : Type := D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F

section Gen
variable (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

def finM (g : GA D V) : Matrix (Fin n) (Fin n) (EF D) :=
  ((mt V g).map (toEAf D)).reindex (finCongr hn) (finCongr hn)

def infM (g : GA D V) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  (compAt θ τ (mt V g)).reindex (finCongr hn) (finCongr hn)

variable {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) {cl : Type}
  (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def IsDec (x : Matrix (Fin n) (Fin n) (EF D)) (p : cl × GL (Fin n) D.host.E × S.U) : Prop :=
  p.2.1 ∈ UJ (sigD D : D.host.E →+* D.host.E) J ∧
    x = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) p.2.1 * (yc p.1).1 * p.2.2.1).1

def atFr {G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (φ : Frames G → ℂ) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  if h : ∀ τ, IsUnit (y τ).det then φ ⟨y, h⟩ else 0

def rdS (ψ : cl → Frames (gramC J (embT D)) → ℂ) (y : Frames (gramC J (embT D))) (g : GA D V) : ℂ :=
  if h : ∃ p, IsDec S yc (finM V hn g) p then
    ((S.chi h.choose.2.2 : ℂˣ) : ℂ) * atFr (ψ h.choose.1) fun τ =>
      atInf (embT D) ((h.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ
  else 0

end Gen

structure Chart (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) where

  cl : Type

  inc : cl → (D.mem u).C.cls i

  K : LevelChart D (D.mem u).A.T (badG D) i hi (fun c : cl => (D.mem u).C.stab i (inc c)) (fun c => clsCrd D u i hi (inc c))

  eY : (D.mem u).C.Y i ≃ Fr D i hi

variable {u : D.what₂.Word}

def Chart.rd {i : ℕ} {hi : i ≤ D.R.m} (Q : Chart D u i hi) (θ : InfFam D)
    (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) (y : (D.mem u).C.Y i) : GA D (D.sp.X i) → ℂ :=
  rdS θ (D.sp.X i) (rankN D i hi) Q.K.lev Q.K.y (fun c z => ψ (Q.inc c) (Q.eY.symm z)) (Q.eY y)

section Sym
variable {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)

def endChart (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0 ∨ i = D.R.m) : Chart D u i hi where
  cl := (D.mem u).C.cls i
  inc := id
  K := (F.cls i hi h).toChart
  eY := (F.val i hi h).eY

def midChart (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : Ch i) : Chart D u i (le_of_succ_m h2) where
  cl := {c // chOf i c = β}
  inc := Subtype.val
  K := F.ch i h1 h2 β
  eY := F.eYC i h1 h2

def chart (i : ℕ) (hi : i ≤ D.R.m) (β : Ch i) : Chart D u i hi :=
  if h : i = 0 ∨ i = D.R.m then endChart F i hi h else midChart F i (by omega) (by omega) β

def rd (θ : InfFam D) (i : ℕ) (hi : i ≤ D.R.m) (β : Ch i) (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)
    (y : (D.mem u).C.Y i) : GA D (D.sp.X i) → ℂ :=
  (chart F i hi β).rd θ ψ y

def OnChart (i : ℕ) (hi : i ≤ D.R.m) (β : Ch i) (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) : Prop :=
  ∀ c, c ∉ Set.range (chart F i hi β).inc → ψ c = 0

end Sym

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepsOnto
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.Core.Rk

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
structure Tower (D : D7) extends LevCh D Unit where

  θ : InfFam D

  ψ : AddChar (AF D.host.F) ℂ

  MY : ∀ j, DSModel (Yc D j) (parB (Ptw D) (min j D.R.m))

  MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)

  νY : ∀ j, Measure (GA D (Yc D j))
  fdY : ∀ j, Set (GA D (Yc D j))

  νX : Measure (GA D D.sp.X')
  fdX : Set (GA D D.sp.X')

  ωY : ∀ k, GA D (Yc D k) × GA D (Yc D (k + 1)) →* Module.End ℂ (WO (Yc D k) (Yc D (k + 1)) → ℂ)

  ωX : GA D (Yc D (D.R.m - 1)) × GA D D.sp.X' →* Module.End ℂ (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ)

  vac : ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vacX : WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ

  vY : ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vX : WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ

  ItY : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank →ₗ[ℂ] SmT (MY (k + 1)) →ₗ[ℂ] SmT (MY k)
  ItX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT MX →ₗ[ℂ] SmT (MY (D.R.m - 1))

  ioY : ∀ k, MultT θ (MY (k + 1)) (levS _ (βY (k + 1)) (toLevCh.datYt () (k + 1) toLevCh.triv))
      (levChi _ (βY (k + 1)) (toLevCh.datYt () (k + 1) toLevCh.triv)) →ₗ[ℂ]
    MultT θ (MY k) (levS _ (βY k) (toLevCh.datYt () k toLevCh.triv)) (levChi _ (βY k) (toLevCh.datYt () k toLevCh.triv))

  ioX : MultT θ MX (levS _ βX (toLevCh.datXt ())) (levChi _ βX (toLevCh.datXt ())) →ₗ[ℂ]
    MultT θ (MY (D.R.m - 1)) (levS _ (βY (D.R.m - 1)) (toLevCh.datYt () (D.R.m - 1) toLevCh.triv))
      (levChi _ (βY (D.R.m - 1)) (toLevCh.datYt () (D.R.m - 1) toLevCh.triv))

namespace Tower

variable {D : D7} (W : Tower D)

abbrev Lv : Type := LevelP W.Pg D.R.r ℂ

abbrev CP (P : W.Lv) (j : ℕ) : Submodule ℂ (SmT (W.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) :=
  MultT W.θ (W.MY j) (levS _ (W.βY j) (W.datYt () j P)) (levChi _ (W.βY j) (W.datYt () j P))

abbrev CC (j : ℕ) : Submodule ℂ (SmT (W.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) := W.CP W.triv j

def datXP (P : W.Lv) : LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X W.Pg (W.Q ()) P W.chi (W.xiR ()) Frm.B

abbrev CXP (P : W.Lv) : Submodule ℂ (SmT W.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) :=
  MultT W.θ W.MX (levS _ W.βX (W.datXP P)) (levChi _ W.βX (W.datXP P))

abbrev CX : Submodule ℂ (SmT W.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) :=
  MultT W.θ W.MX (levS _ W.βX (W.datXt ())) (levChi _ W.βX (W.datXt ()))

def thDn : W.CX →ₗ[ℂ] W.CC 0 := Lift.thetaDn W.CC W.ioY (D.R.m - 1) ∘ₗ W.ioX

def IsDn (T : SmT W.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) (T₀ : SmT (W.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) : Prop :=
  ∃ h : T ∈ W.CX, T₀ = (W.thDn ⟨T, h⟩ : W.CC 0)

end Tower

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word}

def HasMat (h : GA D D.sp.X')
    (y : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  h ∈ GfC D.sp.X' ∧ ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j = y.1 (finCongr (rankP D) i) (finCongr (rankP D) j)

def TopLev (K : ClsPTied u) (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (∀ h, h ∈ J ↔ ∃ κ : K.lev.U, HasMat h κ.1) ∧ ∀ h (κ : K.lev.U), HasMat h κ.1 → χ h = star ((K.lev.chi κ : ℂˣ) : ℂ)


open Classical in
structure IsJ (u : D.what₂.Word) {S : D.what₂.Tau → SPar} (M : DSModel D.sp.X' S) (j : SmT M →ₗ[ℂ] (FrP D → ℂ)) : Prop where
  inj : Function.Injective j
  range : LinearMap.range j = ValC (gramC (gramP D) (embT D)) (sgT u)
  eqv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
    ∀ y y' : FrP D, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr (rankP D)) (finCongr (rankP D)))) y' y →
      j (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = j (PiTensorProduct.tprod ℂ v) y'


end GlobalTheory.Core.Rk.Top

end
end

