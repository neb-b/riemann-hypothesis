module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMulFinrankSubgroupEigenspaceOfTraceVanishes
section
noncomputable section

namespace GlobalTheory.DefFree

theorem isProj_eig_average {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (P : Subgroup G) [Fintype P] (χ : P →* ℂˣ) :
    LinearMap.IsProj (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ))
      ((Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • (ρ g : M →ₗ[ℂ] M)) := by
  classical
  have hcard : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have happ : ∀ x : M, ((Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • (ρ g : M →ₗ[ℂ] M)) x
      = (Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  ·
    rw [happ, mem_eig]
    intro h
    have hsum : ρ h (∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x)
        = ((χ h : ℂˣ) : ℂ) • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
      have hc : ((χ h : ℂˣ) : ℂ) * (((χ (h * g))⁻¹ : ℂˣ) : ℂ) = (((χ g)⁻¹ : ℂˣ) : ℂ) := by
        rw [← Units.val_mul, map_mul, mul_inv, mul_inv_cancel_left]
      show ρ h ((((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x)
        = ((χ h : ℂˣ) : ℂ) • ((((χ (h * g))⁻¹ : ℂˣ) : ℂ) • ρ ((h * g : P) : G) x)
      rw [smul_smul, hc, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    show ρ h (_ • _) = ((χ h : ℂˣ) : ℂ) • (_ • _)
    rw [map_smul, hsum, smul_comm]
  ·
    have hx' : ∀ g : P, ρ g x = ((χ g : ℂˣ) : ℂ) • x := fun g => (mem_eig.mp hx) g
    have hterm : ∀ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x = x := fun g => by
      rw [hx' g, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [happ]
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem card_mul_finrank_eig (G M : Type) [Group G] [Finite G] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P →* ℂˣ)
    (h : ∀ g ∈ P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) :
    Nat.card P * Module.finrank ℂ (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) = Module.finrank ℂ M := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  have htr := (isProj_eig_average ρ P χ).trace
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum, smul_eq_mul] at htr
  simp only [map_smul, smul_eq_mul] at htr

  rw [Finset.sum_eq_single (1 : P) (fun g _ hg => by
      rw [h g g.2 (fun h1 => hg (Subtype.ext h1)), mul_zero])
    (fun h1 => absurd (Finset.mem_univ _) h1)] at htr
  rw [map_one, inv_one, Units.val_one, one_mul, OneMemClass.coe_one, map_one,
    LinearMap.trace_one] at htr
  have hcard : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Nat.card_eq_fintype_card]
  have key : (Fintype.card P : ℂ) * (Module.finrank ℂ (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) : ℂ)
      = (Module.finrank ℂ M : ℂ) := by
    rw [← htr, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  exact_mod_cast key

end GlobalTheory.DefFree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR.Links Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharRealise

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def toCx3One (R : RealDat3 D A3 Ks) (F : Face3 D A3) : CxData A3.fam3.amb3 where
  FC t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HX t).H
  jR t := Tw.semi _ R.toRealDat.emb0 (R.jX t)
  EE := Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H
  Θ t := Tw.map _ (R.Th t)
  EEp p := Tw.sub _ (R.EEp3 p)
  EEl b := Tw.sub _ ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)).comap R.HE.e)
  FLC i t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HV i t).H
  jL i t := Tw.semi _ R.toRealDat.emb0 (R.jV i t)
  W i := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H
  θ' i t := Tw.map _ (R.thG i t)
  Wp i p := Tw.sub _ (R.Wp3 i p)
  dW b i := Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)
  WC b i v := Tw (twAt D.what₂.embLL v) (R.toRealDat.WS F.lv2 b i (sgAt D.what₂.embLL v))
  bW b i _ k := Tw.mk _ ⟨R.toRealDat.bC F.lv2 b i _ k, Submodule.subset_span ⟨k, rfl⟩⟩
  eW b i := Tw.map _ (((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).subtype)
  M b i := (R.FW i).Mcoord (F.lv2.lvl b).P (F.lv2.lvl b).ψ⁻¹ (fun g => (idemOf A3.A.X).coeff g) (R.toRealDat.bL F.lv2 b i)
  nP := RealDat.nP F.lv2
  μ := R.mu
  Tw := R.twPl
  κ _ := R.kap
  lam := R.lam3
  err0 := R.err0

theorem toCx3_eq_one (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hph : ∀ i, R.phs i = 1) : R.toCx3 F = toCx3One R F := by
  unfold RealDat3.toCx3 toCx3One
  congr 1
  funext i t
  simp only [hph, one_smul]

end GlobalTheory.CharRealise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev LPol (b a : ℕ) : Type := MvPolynomial (Fin b × Fin a) ℂ

section Local

variable {a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool)

def rai (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (i, j))
    else -(MvPolynomial.pderiv (i, j)).toLinearMap)

def low (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (i, j)))

def locS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (rai ε ε' i j * low ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def locT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (rai ε ε' i j * low ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def IsPolyIso {p q r s : ℕ} (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b) (κ : LPol b a ≃ₗ[ℂ] Pol p q r s) : Prop :=
  (∀ (Z : Mat p q) (P : LPol b a), κ (locS ε ε' (Matrix.reindex e e Z) P) = fockAct1 p q r s Z (κ P)) ∧
    ∀ (Z : Mat r s) (P : LPol b a), κ (locT ε ε' (Matrix.reindex e' e' Z) P) = fockAct2 p q r s Z (κ P)

end Local

structure IsCoverIt {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) : Prop where
  bdd : ∀ P, ∃ c : ℝ, ∀ y, ‖B P y‖ ≤ c * ‖y‖
  kfin : ∀ P y, B P y ∈ Set.range R₁.ι
  ne : ∀ y, y ≠ 0 → ∃ P, B P y ≠ 0
  src : ∀ Z ∈ upq p q, ∀ P y,
    HasDerivAt (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) (B (fockAct1 p q r s Z P) y) 0
  tgt : ∀ Z ∈ upq r s, ∀ P y,
    HasDerivAt (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) (-B (fockAct2 p q r s Z P) y) 0

variable {D : D7}

def glue {a b : ℕ} (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ τ, MvPolynomial.rename (fun s => (τ, s)) (P τ)


open Classical in
def GlueLaw (D : D7) (a b : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ ∧
    ∀ (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (P : D.what₂.Tau → LPol b a),
      (∀ X, fockS τ ε ε' X (glue P) = glue (Function.update P τ (locS ε ε' X (P τ)))) ∧
        ∀ Y, fockT τ ε ε' Y (glue P) = glue (Function.update P τ (locT ε ε' Y (P τ)))

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure LocIt (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ) : Prop where
  sm : ∀ P y, A P y ∈ M.sm τ
  ne : ∃ P, ∃ y ∈ M'.sm τ, A P y ≠ 0
  adj : ∀ P w, ∃ w', ∀ y, ⟪w, A P y⟫_ℂ = ⟪w', y⟫_ℂ
  src : ∀ X ∈ lieAt V τ, ∀ P y, HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (A P y))
    (A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P) y) 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ P y, HasDerivAt (fun t : ℝ => A P (M'.rep τ (NormedSpace.exp (t • Y)) y))
    (-A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y) 0

def srcOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tgtOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure GlobIt (aS aT : D.what₂.Tau → ℚ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) : Prop where
  incl : ∀ φ v, inclT M (It φ v) = I φ (inclT M' v)
  ne : It ≠ 0
  adj : ∀ φ w, ellT M w ∘ₗ I φ ∈ Submodule.span ℂ (Set.range (ellT M'))
  src : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (I φ x)))
      (ellT M w (I (srcOp M M' τ (aT τ) X φ) x)) 0
  tgt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (I φ (actT M' τ (NormedSpace.exp (t • Y)) x)))
      (-ellT M w (I (tgtOp M M' τ (aS τ) Y φ) x)) 0

structure TensorLaw : Prop where
  sep : ∀ x : ⨂[ℂ] τ, M.H τ, (∀ w, ellT M w x = 0) → x = 0
  inj : Function.Injective (inclT M)
  one : ∀ τ, actT M τ 1 = LinearMap.id
  mul : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    actT M τ (g * g') = actT M τ g ∘ₗ actT M τ g'
  adj : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, ∃ w', ellT M w ∘ₗ actT M τ g = ellT M w'

def ChosenSeries (X : ProvA) : Prop :=
  ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam

end GlobalTheory.Chain.RealIt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.FinZeta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KerGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {r : ℕ} (N : ℕ) (z : ℂˣ)
    (φ : GL (Fin r) (w.adicCompletion E) → ℂ) : Prop :=
  ∀ ϖ, IsUnifV E w ϖ → ∀ (d : Fin r → ℤ) (t : GL (Fin r) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
    ∀ k₁ ∈ KGL w (n := r), ∀ k₂ ∈ KGL w (n := r),
      φ (k₁ * t * k₂) = (z : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-((N : ℂ) / 2) * ((∑ i, |d i| : ℤ) : ℂ))

def KerU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ} (ϖ : L) (q N : ℕ) (z : ℂˣ)
    (φ : GU σ r → ℂ) : Prop :=
  ∀ (d : Fin r → ℤ) (t : GU σ r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ r, ∀ k₂ ∈ KU σ r,
    φ (k₁ * t * k₂) = ((z : ℂ) * ((q : ℂ) ^ N)⁻¹) ^ (∑ i, max (d i) 0)

variable {D : D7}

abbrev Gv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := GLoc D.sp.cm.sig V.gram v

abbrev Kv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Gv V v) := stabLoc D.sp.cm.sig V.gram (frameLat V) v

abbrev embV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Gv V v →* GA D V := emb D.sp.cm.sig V.gram v

abbrev projV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GA D V →* Gv V v := proj D.sp.cm.sig V.gram v

def IsLocKer (V : HSp D) (N : ℕ) (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Gv V v → ℂ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
    (IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e → KerGL w N (z w) (φ ∘ e.symm)) ∧
    (IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) →
      IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e → KerU ϖ (qV D.host.F v) N (z w) (φ ∘ e.symm))

def VacFin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T (frameLat S) (frameLat T) fun u => u = v) f

def bddAut (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | Continuous f ∧ (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) ∧ ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, 0, fun _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨h1, h2, C, h3⟩ ⟨h1', h2', C', h3'⟩
    exact ⟨h1.add h1', fun γ hγ g => by simp [h2 γ hγ, h2' γ hγ], C + C',
      fun g => (norm_add_le _ _).trans (add_le_add (h3 g) (h3' g))⟩
  smul_mem' := by
    rintro c f ⟨h1, h2, C, h3⟩
    exact ⟨h1.const_smul c, fun γ hγ g => by simp [h2 γ hγ], ‖c‖ * C,
      fun g => (norm_smul c (f g)).le.trans (mul_le_mul_of_nonneg_left (h3 g) (norm_nonneg _))⟩

def bddRep (V : HSp D) : Representation ℂ (GA D V) (bddAut V) :=
  GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ) (bddAut V) (by
    rintro g f ⟨h1, h2, C, h3⟩
    haveI : IsTopologicalGroup (GA D V) := isTopologicalGroup_HA _ _ _
    exact ⟨h1.comp (continuous_mul_const g), fun γ hγ x => by
      show f (γ * x * g) = f (x * g)
      rw [mul_assoc, h2 γ hγ], C, fun x => h3 _⟩)

theorem coe_bddRep (V : HSp D) (g : GA D V) (f : bddAut V) : (bddRep V g f : GA D V → ℂ) = rTr V g f := rfl


open Classical in
def levDatum (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank)
    (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) : WO S T → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaG LT m (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank m (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
    else 0

open Classical in
theorem isLevelVec_iff {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {LT : LevDat D.host.E ℂ T.rank} {Q : Finset (Pl D.host.E)}
    {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec ψ θ S T sT ΛS ΛT βS βT LT Q m f₀ f ↔
      IsVacO ψ θ S T (fun _ => 1) sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (LT.Pg ∪ Q) ∧
        IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ (levDatum S T βS βT LT Q m e) f :=
  Iff.rfl

end GlobalTheory.FinZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksProperties
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv.TwoBlockDet

def lowEquiv {n r : ℕ} (hr : r ≤ n) : Fin r ≃ {a : Fin n // a.val < r} where
  toFun i := ⟨Fin.castLE hr i, i.2⟩
  invFun a := ⟨a.1.val, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_eq_mul {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) κ) (h : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g := by
  apply Units.ext
  rw [Units.val_mul, diag_block_det_val 1 h, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    upper_block_val_submatrix hr h, Matrix.twoBlockTriangular_det (g : Matrix (Fin n) (Fin n) κ) (fun a : Fin n => a.val < r)
      (fun i hi j hj => h (by simp [blk2, hi, hj]))]
  congr 1
  · rw [← Matrix.det_submatrix_equiv_self (lowEquiv hr)]
    rfl
  · rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight
      (show ∀ a : Fin n, blk2 r a = 1 ↔ ¬ a.val < r from fun a => by unfold blk2; split_ifs with h <;> simp [h]))]
    rfl

theorem blockPartitionOf_eq_twoBlock (r t : ℕ) : (blkOf r t : Fin (r + t) → ℕ) = blk2 r := by
  funext a
  unfold blkOf blk2
  split_ifs with h
  · rfl
  · have := a.2
    rw [Nat.div_eq_of_lt (by omega)]

theorem firstDiagBlock_full_rank_eq_self {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have h : g ∈ blockTri (blk2 n) := fun i j hij => by simp [blk2] at hij
  apply Units.ext
  rw [upper_block_val_submatrix hr h]
  rfl

theorem det_blocks : ∀ (κ : Type) [CommRing κ] (n r t : ℕ) (hr : r ≤ n) (g : GL (Fin n) κ), (g ∈ blockTri (blk2 r) → Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g) ∧ (n = r + t → g ∈ blockTri (blkOf r t) → dBlk (blkOf r t) 1 g = dBlk (blk2 r) 1 g) ∧ (n = r → Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) = Matrix.GeneralLinearGroup.det g) := by
  intro κ _ n r t hr g
  refine ⟨det_eq_mul hr g, fun e _ => ?_, fun e => ?_⟩
  · subst e
    rw [blockPartitionOf_eq_twoBlock]
  · subst e
    rw [firstDiagBlock_full_rank_eq_self]

end GlobalTheory.VecInv.TwoBlockDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfFiniteOrderUnipotentReductionLargePrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipRed

theorem bc_val {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (g : GL (Fin n) A) :
    (Formalism.UG.bc f g : GL (Fin n) B).val = f.mapMatrix g.val := rfl

theorem eq_one_of_reduction_eq_one {E R k : Type} [Field E] [CommRing R] [CommRing k]
    [Nontrivial k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) {n m : ℕ} (hm : IsUnit (m : k))
    (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S) (hu : u ^ m = 1)
    (hxy : Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x) (hy : Formalism.UG.bc φ y = 1) : u = 1 := by
  have hU : u.val ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have h1 : (u.val - 1) * ∑ j ∈ Finset.range m, u.val ^ j = 0 := by
    rw [mul_geom_sum, hU, sub_self]
  have hj : ∀ j : ℕ, S.subtype.mapMatrix (y.val ^ j)
      = (x⁻¹).val * ι.mapMatrix (u.val ^ j) * x.val := by
    intro j
    have h : Formalism.UG.bc S.subtype (y ^ j) = x⁻¹ * Formalism.UG.bc ι (u ^ j) * x := by
      rw [map_pow, map_pow, hxy]
      simpa using conj_pow (a := x⁻¹) (b := Formalism.UG.bc ι u) (i := j)
    have h' := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, bc_val, bc_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val] at h'
    exact h'
  have hsum : S.subtype.mapMatrix (∑ j ∈ Finset.range m, y.val ^ j)
      = (x⁻¹).val * ι.mapMatrix (∑ j ∈ Finset.range m, u.val ^ j) * x.val := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hj j
  have hY : φ.mapMatrix y.val = 1 := by
    rw [← bc_val, hy, Units.val_one]
  have hk : φ.mapMatrix (∑ j ∈ Finset.range m, y.val ^ j) = (m : k) • 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_pow, hY, one_pow, Finset.sum_const, Finset.card_range]
    rw [Nat.cast_smul_eq_nsmul]
  have hd : (∑ j ∈ Finset.range m, u.val ^ j).det ≠ 0 := by
    intro h0
    have h2 : S.subtype (∑ j ∈ Finset.range m, y.val ^ j).det = 0 := by
      rw [RingHom.map_det, hsum, Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, h0, map_zero,
        mul_zero, zero_mul]
    have h3 : (∑ j ∈ Finset.range m, y.val ^ j).det = 0 := Subtype.ext h2
    have h4 := RingHom.map_det φ (∑ j ∈ Finset.range m, y.val ^ j)
    rw [h3, map_zero, hk, Matrix.det_smul, Matrix.det_one, mul_one] at h4
    exact (hm.pow _).ne_zero h4.symm
  have hunit : IsUnit (∑ j ∈ Finset.range m, u.val ^ j) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hd)
  have h5 : u.val - 1 = 0 := (hunit.mul_left_eq_zero).1 h1
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h5)

theorem eq_one_of_unipotent_reduction :
    ∀ (E R k : Type) [Field E] [NumberField E] [CommRing R] [CommRing k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) (p n : ℕ), p.Prime → CharP k p → Module.finrank ℚ E * n + 1 < p → ∀ (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S), IsOfFinOrder u → Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x → IsNilpotent ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) → u = 1 := by
  intro E R k _ _ _ _ S ι φ p n hp hchar hlt u x y hu hxy hnil
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Units.ext (Subsingleton.elim _ _)
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one (R := k) hp.ne_one
  obtain ⟨a, ha⟩ := hnil
  have hpa : (Formalism.UG.bc φ y) ^ (p ^ a) = 1 := by
    apply Units.ext
    have h1 : ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) ^ (p ^ a) = 0 :=
      pow_eq_zero_of_le (Nat.lt_pow_self hp.one_lt).le ha
    rw [sub_pow_char_pow_of_commute p a (Commute.one_right _), one_pow, sub_eq_zero] at h1
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu.orderOf_pos.ne' p hp.ne_one
  apply GlobalTheory.BadShare.gl_eq_one_of_pow_prime_pow E n p hp hlt u (a + b)
  refine eq_one_of_reduction_eq_one S ι φ (m := m) ((CharP.isUnit_natCast_iff hp).2 hm)
    _ x (y ^ p ^ (a + b)) ?_ ?_ ?_
  · rw [← pow_mul, pow_add, mul_assoc, ← hbm, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, map_pow, hxy]
    simpa using conj_pow (a := x⁻¹) (b := Formalism.UG.bc ι u) (i := p ^ (a + b))
  · rw [map_pow, pow_add, pow_mul, hpa, one_pow]

end GlobalTheory.UnipRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOneStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_detCharacter_of_irreducible_rank_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Type) [Fintype c] [DecidableEq c] [Subsingleton c] (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL c k) V), IsSmooth σ → σ.IsIrreducible → ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ Nonempty (σ.Equiv (detRep c ψ)) := by
  first | exact @GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep | exact GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep | (intros; apply GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep <;> assumption)
end

