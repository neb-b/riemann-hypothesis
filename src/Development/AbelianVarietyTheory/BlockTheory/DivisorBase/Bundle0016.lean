module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalRingCardinality.Bundle0006
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalRingCardinality.DataRRMetric
public import Formalism.LogFactorialIndices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



def absPow (half : Bool) (P : Pl D.host.E) (k : D.host.E) : ℂ :=
  cond half ((Real.sqrt (NumberField.FinitePlace.mk P k) : ℝ) : ℂ) 1

def conjRes (s : ℂ →+* ℂ) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => (Units.map s.toMonoidHom).comp (χ PP)



variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



set_option genInjectivity false in
set_option genSizeOfSpec false in
structure LiftInput (R : RealDat D A Ks) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) where

  mu : (AE D)ˣ →* Circle

  eta : (AE D)ˣ →* Circle

  om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)

  BV : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ

  BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ

  vac : WO (Vc D i) (Wc D i) → ℂ

  vec : WO (Vc D i) (Wc D i) → ℂ

  coef : CoefA (Vc D i)

  io : LowT (R.MW i σ) →ₗ[ℂ] coef.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank

  ν : Measure (GA D (Vc D i))

  fd : Set (GA D (Vc D i))

namespace LiftInput

variable {R : RealDat D A Ks} {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (X : LiftInput R i σ)

variable {t : T} {s : ℂ →+* ℂ} {P : LevelP R.Pg D.R.r ℂ}

end LiftInput

theorem labE_base (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem lab_base (ρ : D.what₂.Tau) : lab D.what₂.embLL ρ = ρ := by
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (labE_base ρ)⟩
  unfold lab
  rw [dite_eq_left h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rw [labE_base] at hs
  rcases hs with hs | hs
  · have h1 : D.host.sigmaOf (D.eTau τ).1 = D.host.sigmaOf (D.eTau ρ).1 :=
      AlgEquiv.ext fun x => D.host.φ₀.injective (DFunLike.congr_fun hs x)
    apply D.eTau.injective
    apply Subtype.ext
    exact (by unfold Host.sigmaOf at h1; exact (EquivLike.injective _) h1)
  · exfalso
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem isONBasis_onb {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (p : ℕ)
    (h : ∀ a, M.ε τ a = decide ((a : ℕ) < p)) : IsONBasis (gramAt D V τ) (cart M τ) (onb M τ) p := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hJ : (Matrix.diagonal fun a => (((if M.ε τ a = true then 1 else -1 : ℝ)) : ℂ)) = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    split_ifs <;> simp
  refine ⟨fun a => if M.ε τ a = true then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : (a : ℕ) < p
    · left; simp [h a, ha]
    · right; simp [h a, ha, Nat.le_of_not_lt ha]
  · rw [hJ, ← M.fr_gram τ, onb]
    have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    calc ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹
        = (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  · rw [hJ, cart, onb, Matrix.mul_assoc, h1, Matrix.mul_one]

end GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisedDualSystem
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev IsDedekindDomain NumberField Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ


open Classical in
def badF (R : RealDat D A Ks) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  R.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

variable {X : DivX D}

end GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ResInjAt {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m), ∀ U ∈ R.Wall i (sg0 D A),
    (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, U (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) = 0) → U = 0

def ResInj : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.models_inf → ResInjAt R

theorem ResInj.of_char (h : ResInj) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F) : ResInjAt R :=
  h D G Pl0 T A Ks R hR.models.inf

end GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RowsOfLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

section Abstract

variable {G K V : Type} [Group G] [Fintype G] [Field K] [AddCommGroup V] [Module ℂ V]


end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowsOfLevel (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (x : R.HE.H),
    R.HE.e x ∈ R.EEat (R.levR F b) ↔
      ∀ g : (F.lvl b).P, R.gE (g : G) x = D.what₂.embLL (((F.lvl b).ψ g : D.what₂.LLˣ) : D.what₂.LL) • x

end GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ThetaKernelFiring
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernel (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i))
    (φ : WO (Vc D i) (Wc D i) → ℂ) : ℂ :=
  thetaKO (R.ωP i t) h g φ

def FiresAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : (R.HV i t).H) : Prop :=
  (∀ (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)),
    IntegrableOn (fun h => kernel R i t g h (R.ptP i t (R.ioP i e (R.extV i t x h)))) (R.fdV i t) (R.νV i t)) ∧
  ∃ Θ ∈ R.Wall i (sg0 D A), ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
    Θ (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Lift.thetaPInt (R.νV i t) (R.fdV i t) (kernel R i t) (R.ptP i t) (R.ioP i) (R.extV i t x) (PiTensorProduct.tprod ℂ v)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def twVal {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (w : ℝ) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) : ℂ :=
  ((χ.locK P k : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-((w : ℂ) * ((Formalism.L2.Host.ordF P k : ℤ) : ℂ)))

def IsGalConj {E : Type} [Field E] [NumberField E] (s : ℂ ≃+* ℂ) (w : ℝ) (χ χ' : Formalism.L2.Host.HChar E) : Prop :=
  ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ), twVal χ' w P k = s (twVal χ w P k)

theorem isGalConj_refl {E : Type} [Field E] [NumberField E] (w : ℝ) (χ : Formalism.L2.Host.HChar E) :
    IsGalConj (RingEquiv.refl ℂ) w χ χ := fun _ _ => rfl


variable (D) in
def IsEmbOverK (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) : Prop :=
  (∀ a, σ a = s (D.what₂.embLL a)) ∧ ∀ x : D.host.E, x ∈ D.host.K → σ (D.embE x) = D.what₂.embLL (D.embE x)

theorem isEmbOverK_base : IsEmbOverK D D.what₂.embLL (RingEquiv.refl ℂ) := ⟨fun _ => rfl, fun _ _ => rfl⟩

def hookOf (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens (((List.range n).map a).insertionSort (· ≥ ·)) List.sortedGE_insertionSort)


variable (D) in
abbrev pW (i : Fin D.R.m) (ρ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D ρ)).1


variable (D) in
abbrev qW (i : Fin D.R.m) (ρ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D ρ)).2


variable (D) in
def aPlAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ → ℕ := aPl D i (pW D i ρ) (lab σ ρ)


variable (D) in
def aMiAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ → ℕ := aMi D i (pW D i ρ) (qW D i ρ) (lab σ ρ)


variable (D) in
def mainTerm (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log ((hookOf (pW D i ρ) (aPlAt D i σ ρ) : ℝ) * (hookOf (qW D i ρ) (aMiAt D i σ ρ) : ℝ))


variable (D) in
def Lp (b : ℝ) : ℝ := Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ))


variable (D) in
def Sizes (i : Fin D.R.m) (b : ℝ) : Prop :=
  (∀ τ : D.what₂.Tau, 0 < (((D.hc τ).e i : ℚ) : ℝ) ∧ (((D.hc τ).e i : ℚ) : ℝ) ≤ 2 * b ∧
    (∀ l, 0 ≤ (((D.hc τ).v l : ℚ) : ℝ) ∧ (((D.hc τ).v l : ℚ) : ℝ) ≤ b) ∧
    ∀ l, |(((D.hc τ).b l : ℚ) : ℝ) - (((D.hc τ).e i : ℚ) : ℝ)| ≤ b) ∧
  ∀ l, ((D.R.k : ℝ) * b) ^ 8 ≤ (D.host.g l : ℝ)


variable (D) in
def deltaAtEmb (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : PolF D (Wc D i).rank (Vc D i).rank :=
  Formalism.IndefR.Datum.delta (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ)

def IsLocalLevel {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) : Prop :=
  ∃ Hl cl, P = LevelP.ofLocal Hl cl

def datV (i : Fin D.R.m) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : LevDat D.host.E ℂ (Vc D i).rank where
  r := D.R.r
  hr := r_le_V i
  t := D.R.t
  s := 1
  Pg := Pg
  Q := Q
  P := P
  cg := fun _ => m
  xq := m

def grpOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) : Subgroup (Bridge.Gf V) :=
  (Lev.toAfE V (lev D.sp.cm V.gram β L)).comap (finHom V).range.subtype

def chrOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) : grpOf V β L →* ℂˣ :=
  (Lev.levCharAfE V β L).comp ((finHom V).range.subtype.subgroupComap _)


open Classical in
def IsLevelVec (ψ : AddChar (AF D.host.F) ℂ) (θ : Datum.InfFam D) (S T : HSp D)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (f₀ f : Datum.WO S T → ℂ) : Prop :=
  Datum.IsVacO ψ θ S T (fun _ => 1) sT ΛS ΛT f₀ ∧ ∃ e : AE D, Datum.IsIdemSum e (LT.Pg ∪ Q) ∧
    Datum.IsThetaAt ψ (Datum.symplO S T) (Datum.heisO ψ S T) (cA D e) (Datum.latO S T ΛS ΛT fun _ => True) 1 f₀
      (fun x => if Datum.IsHalf (cA D e) x ∧ Datum.IsIntM (Datum.frMapAdj S T βS βT x) then
        Datum.omegaG LT m (fun PP => Datum.redM PP (Datum.frMapAdj S T βS βT x)) *
          Datum.omegaQ Q T.rank m (-1) (fun PP => Datum.redM PP (Datum.frMapAdj S T βS βT x))
        else 0) f

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


open Classical in
def finS (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) := (R.Pg ∪ R.Q t).image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def PrimeToHost (t : T) : Prop :=
  ∀ PP : Pl D.host.E, PP ∈ R.Pg ∨ PP ∈ R.Q t →
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def IsConjChars (i : Fin D.R.m) (t : T) (s : ℂ ≃+* ℂ) (cμ cη : (AE D)ˣ →* Circle)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∃ μ' η' : Formalism.L2.Host.HChar D.host.E,
    IsGalConj s 0 (R.C.mu0 i * R.xiH t) μ' ∧ IsGalConj s (1 / 2) R.C.eta η' ∧ ChrEq cμ μ' ∧ ChrEq cη η' ∧
      ∀ PP : Pl D.host.E, PP ∈ R.Pg ∨ PP ∈ R.Q t → IsRes μ' PP (m PP)

def ptAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (f : Datum.WO (Vc D i) (Wc D i) → ℂ) : PolF D (Wc D i).rank (Vc D i).rank → (Datum.WO (Vc D i) (Wc D i) → ℂ) :=
  Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f

def IsLift (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (pt : PolF D (Wc D i).rank (Vc D i).rank → (Datum.WO (Vc D i) (Wc D i) → ℂ)) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))) (HV : HMod (Bridge.Gf (Vc D i) → c.W))
    (th : HV.H →ₗ[ℂ] (R.HW i σ).H) : Prop :=
  ∀ (x : HV.H) (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)),
    IntegrableOn (fun h => Datum.thetaKO ω h g (pt (io (PiTensorProduct.tprod ℂ v) (c.ext (HV.e x) h)))) 𝓕 ν ∧
      (R.HW i σ).e (th x) (fun ρ => v ρ) g =
        Lift.thetaPInt ν 𝓕 (fun g h f => Datum.thetaKO ω h g f) pt io (c.ext (HV.e x)) (PiTensorProduct.tprod ℂ v) g

def typePart (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (t : T) (P : LevelP R.Pg D.R.r ℂ)
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (R.HW i σ).H :=
  (partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) c).comap
    (R.HW i σ).e

def adjLev {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) : Y →ₗ[ℂ] X :=
  ((Nat.card P.H : ℂ))⁻¹ • LinearMap.adjoint th

end GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

end
end

