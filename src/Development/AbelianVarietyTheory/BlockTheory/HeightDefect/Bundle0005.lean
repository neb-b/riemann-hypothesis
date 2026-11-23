module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def kFin {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  sSup {W | FiniteDimensional ℂ W ∧ IsKStableOn ε σ W}

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)

structure IsGKMap {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
    (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ)) : Prop where

  aut : ∀ v, IsAutFunSm θ V (T v)

  mapK : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P * g * P⁻¹ ∈ Formalism.REAL.Kset ε →
    ∀ v w : kFin ε σ, (w : H) = σ (P * g * P⁻¹) v → T w = rTr V (atTau θ V τ g) (T v)

  mapLie : ∀ X ∈ lieAt V τ, ∀ v w : kFin ε σ,
    HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • X) * P⁻¹) (v : H)) (w : H) 0 →
      T w = Rder θ V τ X (T v)

def finPartOfType (S : SPar) : Submodule ℂ (GA D V → ℂ) :=
  sSup {W | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
    (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    IsEnum S lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ IsDS ε lam σ ∧ IsUnit P ∧
      Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ ∧ IsGKMap θ V τ ε σ P T ∧ W = LinearMap.range T}

def HasTypeAt (S : SPar) (φ : GA D V → ℂ) : Prop :=
  ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ →
    ∃ ψ ∈ finPartOfType θ V τ S, ∀ x ∈ C, ‖φ x - ψ x‖ < δ

theorem HasTypeAt.of_mem {S : SPar} {φ : GA D V → ℂ} (h : φ ∈ finPartOfType θ V τ S) : HasTypeAt θ V τ S φ :=
  fun _ _ δ hδ => ⟨φ, h, fun x _ => by simpa using hδ⟩

def typeSub (S : SPar) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | HasTypeAt θ V τ S φ}
  zero_mem' := HasTypeAt.of_mem θ V τ (Submodule.zero_mem _)
  add_mem' := by
    intro a b ha hb C hC δ hδ
    obtain ⟨ψ, hψ, h1⟩ := ha C hC (δ / 2) (by linarith)
    obtain ⟨ψ', hψ', h2⟩ := hb C hC (δ / 2) (by linarith)
    refine ⟨ψ + ψ', Submodule.add_mem _ hψ hψ', fun x hx => ?_⟩
    have e : (a + b) x - (ψ + ψ') x = (a x - ψ x) + (b x - ψ' x) := by
      simp only [Pi.add_apply]; ring
    rw [e]
    have := norm_add_le (a x - ψ x) (b x - ψ' x)
    linarith [h1 x hx, h2 x hx]
  smul_mem' := by
    intro c a ha C hC δ hδ
    have hc : 0 < ‖c‖ + 1 := by positivity
    obtain ⟨ψ, hψ, h1⟩ := ha C hC (δ / (‖c‖ + 1)) (div_pos hδ hc)
    refine ⟨c • ψ, Submodule.smul_mem _ c hψ, fun x hx => ?_⟩
    have e : (c • a) x - (c • ψ) x = c * (a x - ψ x) := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e, norm_mul]
    have h2 := (lt_div_iff₀ hc).1 (h1 x hx)
    nlinarith [norm_nonneg c, norm_nonneg (a x - ψ x)]

end GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FockOrthogonalDecomposition
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsOrthDec (V : HSp D) (τ : D.what₂.Tau) (P N : Submodule D.host.E V.V) : Prop where
  compl : IsCompl P N
  orth : ∀ x ∈ P, ∀ y ∈ N, V.hT x y = 0
  pos : ∀ x ∈ P, x ≠ 0 → 0 < (tauE D τ (V.hT x x)).re
  neg : ∀ x ∈ N, x ≠ 0 → (tauE D τ (V.hT x x)).re < 0

def IsSignInv (V : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) : Prop :=
  ∃ P N : Submodule D.host.E V.V, IsOrthDec V τ P N ∧ (∀ x ∈ P, s x = x) ∧ ∀ x ∈ N, s x = -x

abbrev InvFam (V : HSp D) : Type := D.what₂.Tau → Module.End D.host.E V.V

def thAt (V : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (LinearMap.toMatrix V.frame V.frame s).map (tauE D τ)

def KAt (V : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) : Set (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  {g | g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ g * thAt V τ s = thAt V τ s * g}

abbrev InfFam (D : D7) : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

theorem infMat_one (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) :
    infMat D.sp.cm.sig V.gram θ (1 : GA D V) = 1 := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (1 : GA D V) = 1 := rfl
  simp only [infMat, this, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem infMat_mul (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

def Kinf (θ : InfFam D) (V : HSp D) (s : InvFam V) : Subgroup (GA D V) where
  carrier := {g | g ∈ GinfC V ∧ ∀ τ, Commute (infMat D.sp.cm.sig V.gram (θ τ) g) (thAt V τ (s τ))}
  one_mem' := ⟨one_mem _, fun τ => by rw [infMat_one]; exact Commute.one_left _⟩
  mul_mem' := fun {g h} hg hh => ⟨mul_mem hg.1 hh.1, fun τ => by
    rw [infMat_mul]; exact (hg.2 τ).mul_left (hh.2 τ)⟩
  inv_mem' := fun {g} hg => ⟨inv_mem hg.1, fun τ => by
    let u : (Matrix (Fin V.rank) (Fin V.rank) ℂ)ˣ :=
      ⟨infMat D.sp.cm.sig V.gram (θ τ) g, infMat D.sp.cm.sig V.gram (θ τ) g⁻¹,
        by rw [← infMat_mul, mul_inv_cancel, infMat_one], by rw [← infMat_mul, inv_mul_cancel, infMat_one]⟩
    exact Commute.units_inv_left (u := u) (hg.2 τ)⟩

abbrev WC (V W : HSp D) : Type := Matrix (Fin V.rank) (Fin W.rank) ℂ

def wAt (θ : InfFam D) (V W : HSp D) (τ : D.what₂.Tau) (x : WA V W) : WC V W :=
  x.map fun a => θ τ (infPart D a)

def actC (V W : HSp D) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (x : WC V W) : WC V W :=
  if V.rank ≤ W.rank then g.map (starRingEnd ℂ) * x * h.transpose
  else g * x * (h.map (starRingEnd ℂ)).transpose

def hC (V W : HSp D) (τ : D.what₂.Tau) (x y : WC V W) : ℂ :=
  if V.rank ≤ W.rank then
    ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * gramAt D V τ k i * gramAt D W τ j l * y k l
  else
    ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * gramAt D V τ i k * gramAt D W τ l j * y k l

def symplC (V W : HSp D) (τ : D.what₂.Tau) (x y : WC V W) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hC V W τ y x).re

def jAt (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V)
    (x : WC V W) : WC V W :=
  Complex.I • actC V W (thAt V τ s) (thAt W τ s') x

def IsRealLine (V W : HSp D) (L : ℝ →+ WA V W) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

def dHeis (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  fun w => deriv (fun t : ℝ => Heisenberg₂ ψ V W (L t) f w) 0

def IsJPair (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) (L L' : ℝ →+ WA V W) : Prop :=
  IsRealLine V W L ∧ IsRealLine V W L' ∧
    ∀ t τ, wAt θ V W τ (L' t) = jAt V W τ (s τ) (s' τ) (wAt θ V W τ (L t))

def cre (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L L' : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  dHeis ψ V W L f - Complex.I • dHeis ψ V W L' f

def ann (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L L' : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  dHeis ψ V W L f + Complex.I • dHeis ψ V W L' f

def IsVacuum (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W)
    (f : WA V W → ℂ) : Prop :=
  IsThetaFun ψ V W f ∧ ∀ L L', IsJPair θ V W s s' L L' → ann ψ V W L L' f = 0

inductive IsFockMon (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) :
    (WA V W → ℂ) → Prop
  | vac (f : WA V W → ℂ) : IsVacuum ψ θ V W s s' f → IsFockMon ψ θ V W s s' f
  | cre (L L' : ℝ →+ WA V W) (f : WA V W → ℂ) : IsJPair θ V W s s' L L' → IsFockMon ψ θ V W s s' f →
      IsFockMon ψ θ V W s s' (cre ψ V W L L' f)

def polFun (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) :
    Submodule ℂ (WA V W → ℂ) :=
  Submodule.span ℂ {f | IsFockMon ψ θ V W s s' f}

variable {X : ThetaX D} {T : ThetaTied D X}

end GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OmegaUpDownForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsSplitting (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) : Prop where
  heckeA : IsHeckeChar D χA
  heckeB : IsHeckeChar D χB
  resA : ResEta D χA A.rank
  resB : ResEta D χB B.rank

abbrev Rep (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) : Type := GA D A × GA D B →* Module.End ℂ (Theta ψ A B)

def kern {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} (om : Rep ψ A B) (f : Theta ψ A B) (g : GA D A) (h : GA D B) : ℂ :=
  thetaFun A B ((om (g, h) f : Theta ψ A B) : GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.WA A B → ℂ)

def IsQuotInt (V : HSp D) (c : ℝ) (φ : GA D V → ℂ) (z : ℂ) : Prop :=
  AllSome (fun m : Measure (GA D V) × Set (GA D V) => IsVolPair D V m.1 m.2) fun m =>
    IntegrableOn φ m.2 m.1 ∧ z = (c : ℂ) * ∫ g in m.2, φ g ∂m.1

structure Core {X : ThetaX D} (T : ThetaTied D X) where

  ψ : AddChar (AF D.host.F) ℂ

  ψ_std : IsStdChar D (-1) ψ

  eUp : ∀ A B : HSp D, A.rank ≤ B.rank → X.Sch A B ≃ₗ[ℂ] Theta ψ A B

  eDn : ∀ A B : HSp D, A.rank < B.rank → X.Sch B A ≃ₗ[ℂ] Theta ψ A B

  om : ∀ (A B : HSp D), A.rank ≤ B.rank → ∀ χA χB : X.Chr, IsSplitting A B (T.eChr χA) (T.eChr χB) → Rep ψ A B

  om_weil : ∀ A B hr χA χB hs, IsWeil ψ (T.eChr χA) (T.eChr χB) (om A B hr χA χB hs)

  thUp : ∀ (A B : HSp D) (hr : A.rank ≤ B.rank) (χA χB : X.Chr) (hs : IsSplitting A B (T.eChr χA) (T.eChr χB)),
    A.SigOK → ∀ (Φ : X.Sch A B) (φ : X.cusp A) (h : GA D B),
      IsQuotInt A (T.petC A) (fun g => kern (om A B hr χA χB hs) (eUp A B hr Φ) g h * T.ev A (φ : X.AF A) g)
        (T.ev B (X.th A B χA χB Φ φ) h)

  thDn : ∀ (A B : HSp D) (hr : A.rank < B.rank) (χA χB : X.Chr) (hs : IsSplitting A B (T.eChr χA) (T.eChr χB)),
    B.SigOK → ∀ (Φ : X.Sch B A) (G : X.cusp B) (g : GA D A),
      IsQuotInt B (T.petC B) (fun h => kern (om A B hr.le χA χB hs) (eDn A B hr Φ) g h * T.ev B (G : X.AF B) h)
        (T.ev A (X.th B A χB χA Φ G) g)

namespace Core

variable {X : ThetaX D} {T : ThetaTied D X} (C : Core T)

end Core

section
variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} {om : Rep ψ A B}

end

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ShiftMapsUpDown
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev AEf (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

def locPart (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom.comp (finPart D)

def gramFin (V : HSp D) : Matrix (Fin V.rank) (Fin V.rank) (AEf D) :=
  V.gram.map (inclR (F := D.host.F) (Af D.host.F))

def latFin (V : HSp D) : AddSubgroup (Fin V.rank → AEf D) := latHat D.host.F D.host.E (L0c D V)

def latFinAA (V : HSp D) : AddSubgroup (Fin V.rank → AEf D) :=
  latHat D.host.F D.host.E {y | ∃ a ∈ D.host.AA, ∃ x ∈ L0c D V, y = a • x}

def offS (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA V W) where
  carrier := {x | (∀ i j, infPart D (x i j) = 0) ∧ ∀ v ∈ S, ∀ i j, locPart D v (x i j) = 0}
  zero_mem' := ⟨fun i j => by simp, fun v _ i j => by simp⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨fun i j => ?_, fun v hv i j => ?_⟩
    · rw [Matrix.add_apply, RingHom.map_add (f := _), hx i j, hy i j, add_zero]
    · rw [Matrix.add_apply, RingHom.map_add (f := _), hx' v hv i j, hy' v hv i j, add_zero]
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨fun i j => ?_, fun v hv i j => ?_⟩
    · rw [Matrix.neg_apply, RingHom.map_neg, hx i j, neg_zero]
    · rw [Matrix.neg_apply, RingHom.map_neg, hx' v hv i j, neg_zero]

def mapUp (V W : HSp D) (x : WA V W) : Matrix (Fin W.rank) (Fin V.rank) (AEf D) :=
  HMul.hMul (x.map (finPart D)).transpose (gramFin V)

def mapDown (V W : HSp D) (x : WA V W) : Matrix (Fin V.rank) (Fin W.rank) (AEf D) :=
  HMul.hMul (x.map (finPart D)) (gramFin W)

theorem mapUp_add (V W : HSp D) (x y : WA V W) : mapUp V W (x + y) = mapUp V W x + mapUp V W y := by
  ext i j
  simp [mapUp, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]

theorem mapDown_add (V W : HSp D) (x y : WA V W) : mapDown V W (x + y) = mapDown V W x + mapDown V W y := by
  ext i j
  simp [mapDown, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]

theorem mapUp_neg (V W : HSp D) (x : WA V W) : mapUp V W (-x) = -mapUp V W x := by
  ext i j
  simp [mapUp, Matrix.mul_apply]

theorem mapDown_neg (V W : HSp D) (x : WA V W) : mapDown V W (-x) = -mapDown V W x := by
  ext i j
  simp [mapDown, Matrix.mul_apply]

theorem mapUp_zero (V W : HSp D) : mapUp V W 0 = 0 := by
  ext i j
  simp [mapUp, Matrix.mul_apply]

theorem mapDown_zero (V W : HSp D) : mapDown V W 0 = 0 := by
  ext i j
  simp [mapDown, Matrix.mul_apply]

def homInt (V W : HSp D) : AddSubgroup (WA V W) where
  carrier := {x | if V.rank ≤ W.rank then ∀ y ∈ latFin V, (mapUp V W x).mulVec y ∈ latFinAA W
    else ∀ y ∈ latFin W, (mapDown V W x).mulVec y ∈ latFinAA V}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, mapUp_zero, mapDown_zero, Matrix.zero_mulVec]
    split_ifs
    · exact fun _ _ => zero_mem _
    · exact fun _ _ => zero_mem _
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, mapUp_add, mapDown_add, Matrix.add_mulVec] at hx hy ⊢
    split_ifs at hx hy ⊢
    · exact fun z hz => add_mem (hx z hz) (hy z hz)
    · exact fun z hz => add_mem (hx z hz) (hy z hz)
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, mapUp_neg, mapDown_neg, Matrix.neg_mulVec] at hx ⊢
    split_ifs at hx ⊢
    · exact fun z hz => neg_mem (hx z hz)
    · exact fun z hz => neg_mem (hx z hz)

def homLat (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA V W) :=
  offS V W S ⊓ homInt V W

def UnramOutside (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (∀ v ∈ S, locPart D v (x : AE D) = 1) → χ x = 1

def vacSignOf (ψ : AddChar (AF D.host.F) ℂ) (θ : D.host.E) (V W : HSp D) (l : WA V W) : ℂ :=
  ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) *
    Algebra.trace (AF D.host.F) (AE D) (incA D (θ * D.host.xi0) * hHom V W l l))

def theta0 (D : D7) : D.host.E := (1 + D.host.sqrtMinusD) / 2

def vacSign (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (l : WA V W) : ℂ := vacSignOf ψ (theta0 D) V W l

variable {X : ThetaX D} {T : ThetaTied D X}

def IsVacuum (Wl : WeilTied D X T) (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (Φ : X.Sch V W) : Prop :=
  ∀ l ∈ homLat V W S, Heisenberg₂ Wl.ψ V W l (Wl.evS V W Φ) = vacSign Wl.ψ V W l • Wl.evS V W Φ

def HomLatSelfDual (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∀ x ∈ offS V W S, x ∈ homLat V W S ↔ ∀ l ∈ homLat V W S, ψ (sympl V W x l) = 1

def HyperspecialFixesVacuum (Wl : WeilTied D X T) : Prop :=
  ∀ (V W : HSp D) (χ χ' : X.Chr), V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), UnramOutside D S (T.eChr χ) → UnramOutside D S (T.eChr χ') →
      ∀ g ∈ KsphC V S, ∀ h ∈ KsphC W S, ∀ Φ : X.Sch V W, IsVacuum Wl V W S Φ → Wl.om V W χ χ' (g, h) Φ = Φ

end GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown

end
end

