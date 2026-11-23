module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.VolBr

structure IsBallFam {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G) : Prop where

  subset : ∀ r, B r ⊆ Λ

  zero_mem : ∀ r, 0 ≤ r → (0 : G) ∈ B r

  sub_mem : ∀ r r' x y, x ∈ B r → y ∈ B r' → x - y ∈ B (r + r')

  nsmul_iff : ∀ (n : ℕ) (r : ℝ) (x : G), 0 < n → x ∈ Λ → (n • x ∈ B (n * r) ↔ x ∈ B r)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

structure Pair (p : X ⟶ Sp k) where

  L : HermLB p

  A : HermLB p

  r : L.B.ι → X.functionFieldˣ

  r' : A.B.ι → X.functionFieldˣ

  hr : IsRatSec L.B r

  hr' : IsRatSec A.B r'

theorem exists_pair (L A : HermLB p) : ∃ P : Pair p, P.L = L ∧ P.A = A := by
  obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  exact ⟨⟨L, A, r, r', hr, hr'⟩, rfl, rfl⟩

namespace Pair

variable (P : Pair p)

def loc (a b : ℤ) (f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) : X.functionField :=
  f * (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b

def H (a b : ℤ) : AddSubgroup X.functionField where
  carrier := {f | ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → RegAt x (P.loc a b f i j)}
  zero_mem' x i j _ _ := ⟨0, by simp [loc]⟩
  add_mem' {f g} hf hg x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    obtain ⟨v, hv⟩ := hg x i j hi hj
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]; simp only [loc]; ring⟩
  neg_mem' {f} hf x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    exact ⟨-u, by rw [map_neg, hu]; simp only [loc]; ring⟩

def nu (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : ℝ :=
  ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
    Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)

def Bl (a b : ℤ) (R : ℝ) : Set X.functionField :=
  {f | f ∈ P.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ R}

def lc (a b : ℤ) (R : ℝ) : ℝ := Real.log ((P.Bl a b R).ncard : ℝ)

def Rep (a b : ℤ) (M : HermLB p) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c i j, x ∈ M.B.U c → x ∈ P.L.B.U i → x ∈ P.A.B.U j →
      UnitAt x ((ρ c : X.functionField) / P.loc a b 1 i j)) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c i j, y ∈ ptsIn p σ (M.B.U c) → y ∈ ptsIn p σ (P.L.B.U i) →
      y ∈ ptsIn p σ (P.A.B.U j) →
      Real.log ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 i j) y‖ - (M.φ σ).φ c y / 2 =
        -(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2

structure Good (D : ℕ) (b : ℕ) (s t : X.functionField) : Prop where

  ample : IsAmpleLB P.A.B

  nef : P.A.IsNef D

  pos : 0 < b

  s_mem : s ∈ P.Bl 0 1 1

  s_ne : s ≠ 0

  t_mem : t ∈ P.Bl (-1) b 1

  t_ne : t ≠ 0

  reg : ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ g : X.functionField, RegAt x g →
    RegAt x (g * P.loc (-1) b t i j / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j)

end Pair

namespace IntExample

open GlobalTheory.Points GlobalTheory.CechPic

theorem ratVal_nat {σ : k →+* ℂ} (y : CxPts p σ) (n : ℕ) : ratVal (n : X.functionField) y = n := by
  have h : genericPoint X ∈ (⊤ : X.Opens) := trivial
  have e : (n : X.functionField) = fnOf ⊤ h (n : Γ(X, ⊤)) := (map_natCast _ n).symm
  rw [e, ratVal_fnOf mem_ptsIn_top h, ev_eq mem_ptsIn_top, map_natCast]

end IntExample

end GlobalTheory.VolBr
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGenReads
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.CcModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem realM_mt {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (h : GA D W) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hth : IsInfEmb τ th) :
    realM θ (Formalism.L2.Theta.mt W h) τ = archM W th h := by
  have e : θ hτ.choose = th :=
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ _ _ (by have := hθ hτ.choose; rwa [← hτ.choose_spec] at this) hth
  rw [realM, dite_eq_left hτ, compAt, e]
  rfl

theorem exists_atComp {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hΨ : ∀ k, ∀ τ ∈ (U.X k).Ψ, ∃ ρ, τ = tauE D ρ)
    (hth : ∀ k τ, IsInfEmb τ.1 (th k τ)) (hD : DictLat U W hr dict ι e F ik φ th x₀) (h : GA D W) :
    ∃ γ, AtComp θ W hr U.X dict x₀ h γ := by
  obtain ⟨γ, hγ, h1, -, h3⟩ := hD.2 h
  refine ⟨γ, hγ, ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [h1, latR, Submodule.map_coe]
    rfl
  · funext τ
    have := h3 τ
    rw [← realM_mt hθ W (γ * h) τ.1 (hΨ _ _ τ.2) _ (hth _ τ)] at this
    exact this

variable {θ : InfFam D} {V W : HSp D} {r : ℕ} {hr : W.rank = r} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r}
    {dict : GA D W → Σ k, Frame (U.X k).Ψ r} {mu : GA D W → ℂ} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cc cc' : U.Comp → ℂ}

end

end GlobalTheory.AdTh.CcModel
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArithBase GlobalTheory.CechPic

namespace GlobalTheory.ArInt.Model

variable {L M : HermLB (𝟙 (Sp ℤ))} {s t : ℝ}


open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem lin_pow_eq_eval_sum_multinomial {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ) (r : ι → ℝ) :
    Ψ (_root_.GlobalTheory.ArInt.lin r ^ m) =
      MvPolynomial.eval r (∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial Finset.univ k : ℝ) *
            Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1))) := by
  unfold _root_.GlobalTheory.ArInt.lin
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∏ i, (MvPolynomial.C (r i) * MvPolynomial.X i) ^ k i =
      MvPolynomial.C (∏ i, r i ^ k i) *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [mul_pow, Finset.prod_mul_distrib, map_prod]
  rw [hk, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← mul_assoc, ← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ), ← map_mul,
    ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
  simp
  ring

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero {ι : Type} [Fintype ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ)
    (hΨ : ∀ n : ι → ℤ, Ψ (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ m) = 0)
    {P : MvPolynomial ι ℝ} (hP : P.IsHomogeneous m) : Ψ P = 0 := by
  classical
  set Q : MvPolynomial ι ℝ := ∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) *
        Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1)) with hQdef
  have hQ : Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    choose n hn using fun i => hx i (Set.mem_univ i)
    have hxn : x = fun i => (n i : ℝ) := funext fun i => (hn i).symm
    rw [map_zero, hxn, hQdef, ← lin_pow_eq_eval_sum_multinomial, hΨ]
  have hmon : ∀ d : ι →₀ ℕ, (Finsupp.weight 1) d = m →
      Ψ (MvPolynomial.monomial d 1) = 0 := by
    intro d hd
    have hmem : ⇑d ∈ (Finset.univ : Finset ι).piAntidiag m := by
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp
    have hc := congrArg (AddMonoidAlgebra.coeff · d) hQ
    rw [hQdef, MvPolynomial.coeff_sum, Finset.sum_eq_single (⇑d)] at hc
    · rw [Finsupp.equivFunOnFinite_symm_coe, MvPolynomial.coeff_monomial, if_pos rfl,
        MvPolynomial.coeff_zero] at hc
      have hne : (Nat.multinomial Finset.univ ⇑d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.multinomial_pos _ _).ne'
      exact (mul_eq_zero.mp hc).resolve_left hne
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro heq
      apply hb
      rw [← heq]
      simp
    · intro h
      exact absurd hmem h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hP (MvPolynomial.mem_support_iff.mp hd)
  have hsm : MvPolynomial.monomial d (AddMonoidAlgebra.coeff P d) =
      AddMonoidAlgebra.coeff P d • MvPolynomial.monomial d (1 : ℝ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, hmon d hw, smul_zero]


open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
theorem _root_.GlobalTheory.ArInt.Model.isArFun_unique {k : Type} [CommRing k] {X : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {D E : ℕ} (hX : _root_.GlobalTheory.IsArithVar p E)
    {ι : Type} [Fintype ι] {L : ι → _root_.GlobalTheory.HermLB p}
    {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : _root_.GlobalTheory.ArInt.IsArFun L D Φ)
    (h' : _root_.GlobalTheory.ArInt.IsArFun L D Φ') :
    Φ = Φ' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hpow : ∀ n : ι → ℤ,
      (Φ - Φ') (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ (D + 1)) = 0 := by
    intro n
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact _root_.GlobalTheory.HermLB.IsSelfInter.unique hX
      (h1 n) (h1' n)
  have hhom : ∀ (P : MvPolynomial ι ℝ) (d : ℕ), P.IsHomogeneous d → Φ P = Φ' P := by
    intro P d hP
    by_cases hd : d = D + 1
    · subst hd
      exact sub_eq_zero.mp (eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero (Φ - Φ') (D + 1) hpow hP)
    · rw [h2 P d hd hP, h2' P d hd hP]
  refine LinearMap.ext fun P => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPolynomial.sum_homogeneousComponent P, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    hhom _ j (MvPolynomial.homogeneousComponent_isHomogeneous j P)

end GlobalTheory.ArInt.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
section
noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace GlobalTheory.GamMul

section Blocks

variable {R : Type} [CommRing R]


open Classical in
def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : GL (Fin n) R := if h : IsUnit M then h.unit else 1

end Blocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (p q : ℕ) (c : kˣ) : Set (Matrix (Fin p) (Fin q) k) := {X | ∀ i j, valuation k (X i j) ≤ valuation k (c : k)}

end GlobalTheory.GamMul

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IwahoriRegularSeparable
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.Block5c

def TypeCusp : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0)

end GlobalTheory.Block5c
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev DatFn (D : D7) (i : Fin D.R.m) : Type :=
  (∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) → ℂ

abbrev IsWeilTw (χ : (AE D)ˣ →* Circle) (ω : WeilRep D i) : Prop :=
  IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω


open Classical in
def VecOf (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i) ∧
    ∃ e : AE D, IsIdemSum e (R.Pg ∪ Q) ∧
      IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e)
        (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i)
        (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
          Ω (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) φ


open Classical in
def PhiOf (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (N : Submodule (𝓞 D.host.E) La)
    (φ : (Fin (Vc D i).rank → La ⧸ N) → ℂ) : Prop :=
  ∃ e : AE D, IsIdemSum e (R.Pg ∪ Q) ∧ ∀ x : Fin (Vc D i).rank → La,
    IsIntM (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)) ∧
    φ (fun b => Submodule.Quotient.mk (x b)) =
      Ω (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)))

def ReadsOnly {i : Fin D.R.m} (S : Finset (Pl D.host.E)) (Ω : DatFn D i) : Prop :=
  ∀ y y', (∀ PP ∈ S, y PP = y' PP) → Ω y = Ω y'


open Classical in
def omegaFree (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) : DatFn D i := fun y =>
  (if ∀ PP ∈ R.Pg, y PP = y₀ PP then 1 else 0) *
    if h : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y PP)).det then ∏ PP ∈ Q.attach, (((ξR PP.1 (h PP.1 PP.2).unit)⁻¹ : ℂˣ) : ℂ) else 0

structure KerDat (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ) : Prop where
  chr : ChrEq χ ξ
  fin : ∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n
  triv : ξ.TrivOn D.host.F
  tame : ∀ v, ξ.TameAt v
  pl : IsTwistPlaces D.host.g Q
  off : ∀ PP ∈ Q, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  ram : ∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, IsConjPl PP' PP
  res : ∀ PP ∈ Q, IsRes ξ PP (ξR PP)
  weil : IsWeilTw R i χ ω
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg Q ξR (R.vacP i) φ

variable {R i}

theorem KerDat.isKernel {ξ χ ξR Q ω φ} (h : KerDat R i ξ χ ξR Q ω φ) : IsKernel R i ξ Q ω φ :=
  ⟨χ, ξR, h.chr, h.res, h.weil, h.vec⟩

theorem KerDat.vecOf {ξ χ ξR Q ω φ} (h : KerDat R i ξ χ ξR Q ω φ) :
    VecOf R i Q (fun y => omegaK R.Pg y * omegaQ Q (Wc D i).rank ξR (-1) y) φ := h.vec

theorem kerDat_tuple (hL : R.toLevCh.Is A.μ0) (hP : R.IsThP) (t : T0) :
    KerDat R i (R.xiH t) (R.xi t) (R.xiR t) (R.Q t) (R.ωP i t) (R.vP i t) :=
  ⟨hL.xi t, hL.xi_fin t, hL.xi_triv t, hL.xi_tame t, hL.Q_pl t, fun PP h => (hL.Q_off t PP h).1, hL.Q_ram t, hL.xiR t,
    hP.ωP i t, hP.vP i t⟩

end GlobalTheory.OnCmp

end
end

