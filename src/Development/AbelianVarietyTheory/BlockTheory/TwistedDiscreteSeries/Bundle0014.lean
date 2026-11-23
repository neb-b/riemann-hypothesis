module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LabelSettingScalars
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ


open Classical in
def badPl (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def rowPart (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : EigSys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) Sb c ⊓ R.EEat R.triv

def IsLValue (t : T) (B : GlobalTheory.LFun.Fam D.host.E) (j : ℕ) (l : ℝ) : Prop :=
  GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))))
               (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (R.toLevCh.mu t j))⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧
    0 < l ∧ GlobalTheory.LFun.LSD D (badPl R t) B (R.toLevCh.mu t j) ((1 + (D.R.t : ℂ)) / 2) = (l : ℂ)

def IsIP (t : T) (k : ℕ) (u u' : MMap (R.MY k)) (a : ℂ) : Prop :=
  IsMultIP (R.MY k) (R.νY t k) (R.fdY t k) u u' a

def IsUp (t : T) (k : ℕ) (u : MMap (R.MY k)) (x : MMap (R.MY (k + 1))) : Prop :=
  PiTensorProduct.lift x ∈ R.CC t (k + 1) ∧ ∀ y : R.CC t (k + 1), ∃ a : ℂ,
    IsIP R t (k + 1) x (PiTensorProduct.lift.symm y.1) a ∧ IsIP R t k u (PiTensorProduct.lift.symm (R.ioY t k y).1) a

def topStep (t : T) (y : (R.HX t).H) : MMap (R.MY (D.R.m - 1)) :=
  PiTensorProduct.lift.symm (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1

def IsUpTop (t : T) (u : MMap (R.MY (D.R.m - 1))) (x : (R.HX t).H) : Prop :=
  ∀ y : (R.HX t).H, IsIP R t (D.R.m - 1) u (topStep R t y) ⟪x, y⟫_ℂ

def reached (t : T) (c : EigSys D) (k : ℕ) : Set (MMap (R.MY k)) :=
  Nat.rec (motive := fun k => Set (MMap (R.MY k))) (rowPart R (badPl R t) c : Set (MMap (R.MY 0)))
    (fun k P => {x | ∃ u ∈ P, IsUp R t k u x}) k

theorem reached_zero (t : T) (c : EigSys D) : reached R t c 0 = (rowPart R (badPl R t) c : Set (MMap (R.MY 0))) := rfl

theorem reached_succ (t : T) (c : EigSys D) (k : ℕ) :
    reached R t c (k + 1) = {x | ∃ u ∈ reached R t c k, IsUp R t k u x} := rfl

def StepScalar (t : T) (c : EigSys D) (k : ℕ) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c k, ∃ x, IsUp R t k u x) ∧
  ∀ u₁ ∈ reached R t c k, ∀ u₂ ∈ reached R t c k, ∀ x₁ x₂, IsUp R t k u₁ x₁ → IsUp R t k u₂ x₂ →
    ∃ a : ℂ, IsIP R t k u₁ u₂ a ∧ IsIP R t (k + 1) x₁ x₂ ((Λ : ℂ) * a)

def TopScalar (t : T) (c : EigSys D) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c (D.R.m - 1), ∃ x, IsUpTop R t u x) ∧
  ∀ u₁ ∈ reached R t c (D.R.m - 1), ∀ u₂ ∈ reached R t c (D.R.m - 1), ∀ x₁ x₂, IsUpTop R t u₁ x₁ → IsUpTop R t u₂ x₂ →
    ∃ a : ℂ, IsIP R t (D.R.m - 1) u₁ u₂ a ∧ ⟪x₁, x₂⟫_ℂ = (Λ : ℂ) * a

def ScalarsWith (κ : ℕ → ℝ) : Prop :=
  ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ →
    (∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B) ∧
    ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
      (∀ k, k + 1 < D.R.m → ∃ l, IsLValue R t B (k + 1) l ∧ StepScalar R t c k (κ (k + 1) * l)) ∧
      ∃ l, IsLValue R t B D.R.m l ∧ TopScalar R t c (κ D.R.m * l)

def Scalars : Prop := ∃ κ : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < κ j) ∧ ScalarsWith R κ

theorem rowPart_mono {Sb Sb' : Finset (HeightOneSpectrum (𝓞 D.host.F))} (h : Sb ⊆ Sb') (c : EigSys D) :
    rowPart R Sb c ≤ rowPart R Sb' c := by
  refine inf_le_inf_right _ fun u hu => ?_
  rw [partDual, mem_partFull] at hu ⊢
  refine ⟨hu.1, fun P d Rp hR => hu.2 P d Rp ?_⟩
  obtain ⟨e, f, ϖ, α, h1, h2⟩ := hR
  exact ⟨e, f, ϖ, α, fun v hv => h1 v (h hv), h2⟩

theorem IsLValue.unique {R : RealDat D A Ks} {t : T} {B : GlobalTheory.LFun.Fam D.host.E} {j : ℕ} {l l' : ℝ}
    (h : IsLValue R t B j l) (h' : IsLValue R t B j l') : l = l' := by
  exact_mod_cast h.2.2.symm.trans h'.2.2

end GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def signCard (S : SPar) (b : Bool) : ℕ := (S.filter fun x => x.2 = b).card

def SigLowered (S : D.what₂.Tau → SPar) (i : ℕ) (V' : HSp D) : Prop :=
  ∀ τ, ∃ p' q' : ℕ, p' + i = signCard (S τ) true ∧ q' + i = signCard (S τ) false ∧
    Formalism.UG.HasSignature (gramAt D V' τ) p' q'

def LowVanish (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (f' : WO V' W → ℂ),
      IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) = 0

theorem signCard_dualPar (S : SPar) (b : Bool) : signCard (dualPar S) b = signCard S b := by
  unfold signCard dualPar
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro x y h
  simp only [Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.1 h.2

end GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def sgn (e : Bool) : ℂ := if e then 1 else -1

def idx {n : ℕ} (ε : Fin n → Bool) : ℚ := ∑ a, if ε a then (1 : ℚ) else -1

def wtS {b : ℕ} (ε' : Fin b → Bool) (aT : ℚ) (e : Bool) : ℚ := (if e then -(idx ε' / 2) else idx ε' / 2) - aT

def wtT {a : ℕ} (ε : Fin a → Bool) (aS : ℚ) (e : Bool) : ℚ := (if e then idx ε / 2 else -(idx ε / 2)) + aS

def signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (g.submatrix (Subtype.val : {a // ε a = e} → Fin n) (Subtype.val : {a // ε a = e} → Fin n)).det

def elt {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)

section Fock

variable {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def raiO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j))
    else -(MvPolynomial.pderiv (τ, i, j)).toLinearMap)

def lowO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (τ, i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j)))

def fockS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (raiO τ ε ε' i j * lowO τ ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def fockT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (raiO τ ε ε' i j * lowO τ ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def subst (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) : PolF D b a →ₐ[ℂ] PolF D b a := by
  classical
  exact MvPolynomial.aeval fun v : FVar D b a =>
    if v.1 = τ then
      ∑ l, ∑ m, (if ε' v.2.1 = ε v.2.2 then k l v.2.1 * g m v.2.2 else star (k l v.2.1 * g m v.2.2)) •
        MvPolynomial.X (τ, l, m)
    else MvPolynomial.X v

end Fock

section Clauses

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
  (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
  (τ : D.what₂.Tau) (aS aT : ℚ)

def TorusVac : Prop :=
  ∀ (t : Fin V.rank → ℝ) (t' : Fin W.rank → ℝ),
    ω (elt θ M τ (diagonal fun j => Complex.exp (Complex.I * t j)),
        elt θ M' τ (diagonal fun i => Complex.exp (Complex.I * t' i))) f =
      Complex.exp (Complex.I * (∑ j, (wtS (M'.ε τ) aT (M.ε τ j) : ℂ) * t j +
        ∑ i, (wtT (M.ε τ) aS (M'.ε τ i) : ℂ) * t' i)) • f

def CompactFock : Prop :=
  ∃ x y : Bool → ℤ, (∀ j, (x (M.ε τ j) : ℚ) = wtS (M'.ε τ) aT (M.ε τ j)) ∧
    (∀ i, (y (M'.ε τ i) : ℚ) = wtT (M.ε τ) aS (M'.ε τ i)) ∧
    ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ P : PolF D W.rank V.rank,
      ω (elt θ M τ h, elt θ M' τ k) (ptOf ψ θ M M' f P) =
        (signBlockDeterminant (M.ε τ) true h ^ x true * signBlockDeterminant (M.ε τ) false h ^ x false *
          (signBlockDeterminant (M'.ε τ) true k ^ y true * signBlockDeterminant (M'.ε τ) false k ^ y false)) •
          ptOf ψ θ M M' f (subst τ (M.ε τ) (M'.ε τ) (h.map (starRingEnd ℂ)) k P)

def LieFock : Prop :=
  (∀ X ∈ lieAt V τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P -
        ((aT : ℂ) * X.trace) • P) z) 0) ∧
  ∀ Y ∈ lieAt W τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P +
        ((aS : ℂ) * Y.trace) • P) z) 0

end Clauses

def VacChar (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacVec ψ θ M M' f →
      TorusVac θ M M' ω f τ aS aT ∧ CompactFock ψ θ M M' ω f τ aS aT ∧ LieFock ψ θ M M' ω f τ aS aT

end GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Filter GlobalTheory.LFun

section Defs

variable {K : Type} [Field K] [NumberField K]

def liftFam (c : Fam K) (m x : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) : Fam K :=
  twist c (x * m⁻¹) + segFam x t

def IsZetaCont (T : Set (HeightOneSpectrum (𝓞 K))) (Z : ℂ → ℂ) : Prop :=
  MeromorphicOn Z Set.univ ∧ ∀ s : ℂ, 1 < s.re → Z s = zetaOff T s

def HasSimplePole (Λ : ℂ → ℂ) (s₀ : ℂ) : Prop :=
  MeromorphicAt Λ s₀ ∧ meromorphicOrderAt Λ s₀ = ((-1 : ℤ) : WithTop ℤ) ∧
    ∃ ρ : ℂ, ρ ≠ 0 ∧ Tendsto (fun s => (s - s₀) * Λ s) (𝓝[≠] s₀) (𝓝 ρ)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rhs (S : Set (HeightOneSpectrum (𝓞 F))) (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ)
    (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)

def Hyp (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) : Prop :=
  S.Finite ∧ r + 5 ≤ t ∧
    ∀ w ∉ above E S, (c w).card = r ∧
      (∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧
      ‖(m w : ℂ)‖ = 1 ∧ ‖(x w : ℂ)‖ = 1 ∧ P w = liftFam c m x t w

def Concl (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) :
    Prop :=
  (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re →
    Converges (above E S) (twist P x⁻¹) s ∧
      (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧
      LSTw S P x s = rhs S c m t (zetaOff (above E S)) s) ∧
  ((∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧
    DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re}) ∧
  (∃ Z, IsZetaCont (above E S) Z) ∧
  ∀ Z, IsZetaCont (above E S) Z →
    MeromorphicOn (rhs S c m t Z) {s | ((r : ℝ) + 1) / 2 < s.re} ∧
      ((r : ℝ) + 1) / 2 < ((1 + (t : ℂ)) / 2).re ∧
      (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → rhs S c m t Z s = LSTw S P x s) ∧
      HasSimplePole (rhs S c m t Z) ((1 + (t : ℂ)) / 2)

def SimplePole : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ),
    Hyp S r t c P m x → Concl S r t c P m x

section Rep

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU

end Rep

theorem twist_liftFam (c : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ) :
    twist (liftFam c m x t) x⁻¹ = twist c m⁻¹ + segFam 1 t := by
  rw [liftFam, twist_add, twist_twist, twist_segFam, inv_mul_cancel_left, inv_mul_cancel]

end GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

open Matrix Formalism.UG ValuativeRel
open scoped TensorProduct
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsUWeilPair)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.LFun (HasSatU)

def str (q : ℂˣ) (n : ℤ) : Multiset ℂˣ := (Multiset.range n.toNat).map fun j : ℕ => q ^ (2 * (j : ℤ) - (n - 1))

section Valued

variable (E : Type) [Field E] [Valued E (WithZero (Multiplicative ℤ))]

def nu (z : Circle) : Eˣ →* Circle :=
  (zpowersHom Circle z⁻¹).comp ((WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
    (Units.map (Valued.v : Valuation E (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom))

def chi (n : ℕ) : Eˣ →* Circle := nu E (Circle.exp Real.pi ^ n)

variable {E}

variable {n : ℕ}

def IsSelfDualLat (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤ ∧
    ∀ x, x ∈ L ↔ ∀ y ∈ L, x ⬝ᵥ S *ᵥ (fun i => c (y i)) ∈ intL E

def IsHypFrame (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) (P : GL (Fin n) E) :
    Prop :=
  (∀ y : Fin n → E, P.1 *ᵥ y ∈ L ↔ ∀ i, y i ∈ intL E) ∧
    ∃ u : E, Valued.v u = 1 ∧ P.1ᵀ * S * P.1.map c = u • antiJ E n

end Valued

section Local

variable {F : Type} [Field F] {E : Type} [Field E] [Valued E (WithZero (Multiplicative ℤ))] [Algebra F E]
  (c : E →ₐ[F] E) {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

end Local

section Res

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]


variable {F} in
def IsUnramAdd (ϖ : F) (ψ : AddChar F ℂ) : Prop :=
  (∀ x ∈ 𝒪[F], ψ x = 1) ∧ ∃ x ∈ 𝒪[F], ψ (ϖ⁻¹ * x) ≠ 1

end Res

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

def TrivialBound (q n : ℕ) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∀ i, ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)

def SatakeBoundInert : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
      IsIrrSmooth π → IsUnitarisable π → HasSatU ϖ q π α → TrivialBound q n α

theorem bound_eq (q n : ℕ) : ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) = (q : ℝ) ^ ((n : ℝ) - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1
  push_cast
  ring

def trivParam (q n : ℕ) (hq : q ≠ 0) : Fin (n / 2) → ℂˣ :=
  fun i => Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem trivial_hyp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    IsIrrSmooth (charRep (1 : GU σ n →* ℂˣ)) ∧ IsUnitarisable (charRep (1 : GU σ n →* ℂˣ)) ∧
      HasSatU ϖ q (charRep (1 : GU σ n →* ℂˣ)) (trivParam q n hq) := by
  have hc : ∀ b : GU σ n, chiDeltaU q (fun i => (trivParam q n hq i : ℂ)) b = 1 := fun b => by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs with h
    · simp only [trivParam, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero (q : ℂ) using 2
      ring
    · rfl
  refine ⟨⟨fun z => by simp, charRep_irreducible _⟩, charRep_unitarisable _ (by simp), ?_, fun x _ h0 => ?_⟩
  · exact (Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 (by simp), one_ne_zero⟩
  · refine IsSatVecU.of_map hU (ρ' := rightReg ℂ _ ℂ) (LinearMap.pi fun _ => LinearMap.id)
      (fun g y => by funext z; simp [rightReg, LinearMap.funLeft]) (fun a b e => congrFun e 1)
      (isSatVecU_of_isSphericalU hU (fun b g k _ _ => by simp [hc]) fun e => h0 (congrFun e 1))

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

end
end

