module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
section
set_option autoImplicit false

noncomputable section

open WittVector Ideal CategoryTheory Opposite

namespace GlobalTheory.PDivLat

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]


variable (p O) in
def ghost (n : ℕ) (a : Ainf p O) : O :=
  fontaineTheta O p ((WittVector.frobenius : Ainf p O →+* Ainf p O)^[n] a)

set_option autoImplicit false in
open WittVector Ideal CategoryTheory Opposite in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.PDivLat.ghost_add (n : ℕ) (a b : _root_.GlobalTheory.Sandwich.Ainf p O) :
    _root_.GlobalTheory.PDivLat.ghost p O n (a + b) = _root_.GlobalTheory.PDivLat.ghost p O n a + _root_.GlobalTheory.PDivLat.ghost p O n b := by
  simp only [_root_.GlobalTheory.PDivLat.ghost, iterate_map_add, map_add (f := _)]

set_option autoImplicit false in
open WittVector Ideal CategoryTheory Opposite in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.PDivLat.ghost_mul (n : ℕ) (a b : _root_.GlobalTheory.Sandwich.Ainf p O) :
    _root_.GlobalTheory.PDivLat.ghost p O n (a * b) = _root_.GlobalTheory.PDivLat.ghost p O n a * _root_.GlobalTheory.PDivLat.ghost p O n b := by
  simp only [_root_.GlobalTheory.PDivLat.ghost, iterate_map_mul, map_mul]

set_option autoImplicit false in
open WittVector Ideal CategoryTheory Opposite in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.PDivLat.ghost_zero (n : ℕ) : _root_.GlobalTheory.PDivLat.ghost p O n 0 = 0 := by
  simp only [_root_.GlobalTheory.PDivLat.ghost, iterate_map_zero, map_zero]

theorem ghost_frobenius (n : ℕ) (a : Ainf p O) :
    ghost p O n (WittVector.frobenius a) = ghost p O (n + 1) a := rfl

abbrev TDual (G : PDivGroup p O) : Type := G.Tate →ₛₗ[ofPadic p O] Ainf p O

def latt (G : PDivGroup p O) : Submodule (Ainf p O) (TDual G) where
  carrier := {y | ∀ n, ∃ x : G.dual.Lie, ∀ t, ghost p O n (y t) = x (hodgeTate G t)}
  zero_mem' n := ⟨0, fun _ => ghost_zero n⟩
  add_mem' {y z} hy hz n := by
    obtain ⟨x, hx⟩ := hy n
    obtain ⟨x', hx'⟩ := hz n
    exact ⟨x + x', fun t => by rw [LinearMap.add_apply, ghost_add, hx, hx', LinearMap.add_apply]⟩
  smul_mem' a y hy n := by
    obtain ⟨x, hx⟩ := hy n
    exact ⟨ghost p O n a • x, fun t => by
      rw [LinearMap.smul_apply, smul_eq_mul, ghost_mul, hx, LinearMap.smul_apply, smul_eq_mul]⟩

def lattMap {G H : PDivGroup p O} (f : G ⟶ H) : latt H →ₗ[Ainf p O] latt G where
  toFun y := ⟨y.1.comp (tateMap G H O f), fun n => by
    obtain ⟨x, hx⟩ := y.2 n
    exact ⟨x ∘ₗ omegaDualMap G H f, fun t => by
      rw [LinearMap.comp_apply, hx, hodgeTate_tateMap, LinearMap.comp_apply]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


variable (p O) in
def lattFunctor : (PDivGroup p O)ᵒᵖ ⥤ ModuleCat.{0} (Ainf p O) where
  obj G := ModuleCat.of _ (latt G.unop)
  map f := ModuleCat.ofHom (lattMap f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

def HasDatum [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O) : Prop :=
  ∃ (D : Datum ε G.height ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]))
    (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin G.height → O) ⧸ D.Fil) ≃ₗ[O] G.Lie),
    (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin G.height → O)) ∧
      ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ = x (dlog G χ)

def IsConn (G : PDivGroup p O) : Prop := ∀ n, IsLocalRing (G.A n)

def IsConst (G : PDivGroup p O) : Prop :=
  ∀ n, Nonempty (G.A n ≃ₐ[O] (Fin (p ^ (n * G.height)) → O))

def IsSum (G G₁ G₂ : PDivGroup p O) : Prop :=
  ∃ (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G) (q₁ : G ⟶ G₁) (q₂ : G ⟶ G₂), i₁ ≫ q₁ = 𝟙 _ ∧ i₂ ≫ q₂ = 𝟙 _ ∧
    i₁ ≫ q₂ = 0 ∧ i₂ ≫ q₁ = 0 ∧ q₁ ≫ i₁ + q₂ ≫ i₂ = 𝟙 _

end GlobalTheory.PDivLat
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD)
open scoped Classical

namespace GlobalTheory.HilbFam

variable {F : Type} [Field F] [NumberField F]

abbrev Lat (F : Type) [Field F] [NumberField F] : Type := Submodule (𝓞 F) (Fin 2 → F)

def stdLat (F : Type) [Field F] [NumberField F] : Lat F :=
  Submodule.pi Set.univ fun _ ↦ (1 : Submodule (𝓞 F) F)

def HasLevel (N : ℕ) (L : Lat F) : Prop := (∀ x ∈ stdLat F, (N : 𝓞 F) • x ∈ L) ∧ L ≤ stdLat F

def mulMat (L : Lat F) (A : Matrix (Fin 2) (Fin 2) ℤ) : Lat F :=
  L.map ((Matrix.vecMulLinear (A.map (Int.cast : ℤ → F))).restrictScalars (𝓞 F))

def twist (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) : Lat F :=
  mulMat L (α.map (ZMod.cast : ZMod N → ℤ)) ⊔ mulMat (stdLat F) ((N : ℤ) • 1)

def split (𝔞 𝔟 : Frac F) (x : F) : Lat F where
  carrier := {v | v 0 ∈ (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ∧ v 1 - v 0 * x ∈ latM 𝔞}
  add_mem' := fun {v w} hv hw ↦ ⟨Submodule.add_mem _ hv.1 hw.1, by
    have : (v + w) 1 - (v + w) 0 * x = (v 1 - v 0 * x) + (w 1 - w 0 * x) := by simp only [Pi.add_apply]; ring
    rw [this]; exact Submodule.add_mem (latM 𝔞 : Submodule (𝓞 F) F) hv.2 hw.2⟩
  zero_mem' := ⟨Submodule.zero_mem _, by
    have : (0 : Fin 2 → F) 1 - (0 : Fin 2 → F) 0 * x = 0 := by simp
    rw [this]; exact Submodule.zero_mem (latM 𝔞 : Submodule (𝓞 F) F)⟩
  smul_mem' := fun c v hv ↦ ⟨Submodule.smul_mem _ c hv.1, by
    have : (c • v) 1 - (c • v) 0 * x = c • (v 1 - v 0 * x) := by simp only [Pi.smul_apply, smul_sub, smul_mul_assoc]
    rw [this]; exact Submodule.smul_mem (latM 𝔞 : Submodule (𝓞 F) F) c hv.2⟩

def cls (L : Lat F) : Set (Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F))) := {q | q.out ∈ L ∧ q.out ≠ 0}

def coord (b a : Emb F → ℂ) (x : Fin 2 → F) (i : Emb F) : ℂ := (i (x 0) : ℂ) * b i + (i (x 1) : ℂ) * a i

def gTerm (k : ℕ) (σ : ℂ) (b a : Emb F → ℂ) (x : Fin 2 → F) : ℂ :=
  (∏ i, coord b a x i)⁻¹ ^ k * ((‖∏ i, coord b a x i‖ : ℝ) : ℂ) ^ (-2 * σ)

def IsGVal (k : ℕ) (L : Lat F) (b a : Emb F → ℂ) (G : ℂ) : Prop :=
  (k ≠ 2 → HasSum (fun q : cls L ↦ gTerm k 0 b a q.1.out) G) ∧
  (k = 2 → ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {σ : ℂ | -1 / 2 < σ.re} ∧
    (∀ σ : ℂ, 0 < σ.re → HasSum (fun q : cls L ↦ gTerm 2 σ b a q.1.out) (H σ)) ∧ G = H 0)

def gval (k : ℕ) (L : Lat F) (b a : Emb F → ℂ) : ℂ := if h : ∃ G, IsGVal k L b a G then h.choose else 0

def word {I : Type} [Fintype I] (κ : I → ℕ) : List I := Finset.univ.toList.flatMap fun i ↦ List.replicate (κ i) i

def jet (k : ℕ) (L : Lat F) (κ : Emb F → ℕ) (τ c t : ℂ) : ℂ :=
  iterD (word κ) (fun z ↦ (cK F k : ℂ) * gval k L (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0

def wt (k : ℕ) (κ : Emb F → ℕ) : ℕ := k * Module.finrank ℚ F + 2 * ∑ i, κ i

def hfun (k : ℕ) (L : Lat F) (κ : Emb F → ℕ) (Ch : ℍ → ℂ) (τ : ℍ) : ℂ :=
  jet k L κ τ ((2 * Real.pi * Complex.I) ^ 2 * Ch τ) (-(2 * Real.pi * Complex.I)) / (2 * Real.pi * Complex.I) ^ wt k κ

def rco (k n m : ℕ) : ℤ := (-1) ^ (n - m) * (n.choose m : ℤ) * ((k + m).ascFactorial (n - m) : ℤ)

def lag (k n : ℕ) (c y : ℂ) : ℂ := ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * c ^ (n - m) * y ^ m

def IsCoef (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) : Prop :=
  a 0 = a₀ ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧
  (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ∧ ∀ i : Emb F, 0 < i ξ) ∧
  ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w)
    ((cK F k : ℂ) * gval k (split 𝔞 𝔟 0) w 1 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k)

def eTr (y : F) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F y : ℚ) : ℂ))

def ecoef (N : ℕ) (a : F → ℂ) (x : F) (μ : Emb F → ℕ) (n : ℕ) : ℂ :=
  ∑ᶠ ξ ∈ {ξ : F | (N : ℚ) * Algebra.trace ℚ F ξ = n}, a ξ * eTr (ξ * x) * ∏ i : Emb F, (i ξ : ℂ) ^ μ i

def hser (k N : ℕ) (𝔞 : Frac F) (a : F → ℂ) (x : F) (κ : Emb F → ℕ) (c : ℕ → ℂ) : PowerSeries ℂ :=
  ((omegaFactor 𝔞 : ℂ) ^ k) • ∑ μ ∈ Finset.Iic κ, ((∏ i, rco k (κ i) (μ i) * (-1) ^ μ i : ℤ) : ℂ) •
    (PowerSeries.mk c ^ (∑ i, (κ i - μ i)) * PowerSeries.mk (ecoef N a x μ))

def ZetaVals (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  ∀ C, ∃ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z ∧ Z (1 - (k : ℂ)) = (z C : ℂ)

end GlobalTheory.HilbFam
end
end

