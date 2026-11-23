module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

def IsQCart [IsLocallyNoetherian X] (D : X → ℚ) : Prop :=
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m

def QNum [IsLocallyNoetherian X] (p : X ⟶ Sp k) (N : LB X) (b : ℚ) (D : X → ℚ) : Prop :=
  letI := algebraΓOfHom p
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m ∧
    ∀ C : Closeds X, IsCompleteCurve k C →
      (interNumRed k C ![toLB D₀] : ℚ) / m = b * interNumRed k C ![N]


omit [IsIntegral X] in
def Off (B : X → ℚ) (z : X) : Prop := ∀ w, w ⤳ z → B w = 0

def CentreAt {p : X ⟶ Sp k} (E : DivOver p) (z : X) : Prop :=
  E.Through z ∧ ∀ f : X.functionFieldˣ, RegAt z (f : X.functionField) → E.ord f = 0 →
    RegAt z ((f⁻¹ : X.functionFieldˣ) : X.functionField)

def IsNkltCentre (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (z : X) : Prop :=
  ∃ (E : DivOver p) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ),
    η ≠ 0 ∧ 0 < m ∧ IsLogEqn p Γ η z m g ∧ CentreAt E z ∧ discrep E η m g ≤ -1

def LcCut (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (x : X) (j : ℕ) : Prop :=
  LcAt p n Γ x ∧ ¬ KltAt p n Γ x ∧
    ∀ z, z ⤳ x → ¬ KltAt p n Γ z → topologicalKrullDim (closure ({z} : Set X)) ≤ j

theorem QNum.isQCart [IsLocallyNoetherian X] {p : X ⟶ Sp k} {N : LB X} {b : ℚ} {D : X → ℚ}
    (h : QNum p N b D) : IsQCart D := by
  obtain ⟨m, D₀, hm, he, hD, -⟩ := h
  exact ⟨m, D₀, hm, he, hD⟩

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
section
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def PolyOnK (ε : Fin n → Bool) (f : Mat n → ℂ) : Prop := ∃ P : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, f k = ev k P

def trK {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : Mat n → (W →L[ℂ] W)) (k : Mat n) : ℂ :=
  LinearMap.trace ℂ W (T k : W →ₗ[ℂ] W)

def IsKIrr (ε : Fin n → Bool) (γ : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (T : Mat n → (W →L[ℂ] W)) : Prop :=
  Nontrivial W ∧ Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T ∧ Formalism.MainNotions.S.IsKTypeOf ε T γ ⊤

abbrev dD (ε : Fin n → Bool) {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    Module.End ℂ (TensorProduct ℂ M (Fock n)) := dOp ε (eT E) cpT + dOp' ε (eT E) cmT

abbrev tor (θ : Fin n → ℝ) : Fin n → ℂ := fun a => Complex.exp (θ a * Complex.I)

def BlockForm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ (M : ℕ) (Q : Poly n), Q ∈ blockAlg ε ∧
    ∀ k ∈ Formalism.REAL.Kset ε, ev k P = ev k (detbP n ^ M * Q)

def CoefPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    ∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ

def TrPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) → PolyOnK ε fun k => conj (trK T k)

def AvgMap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)) (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]
    (S : Mat n → (Z →L[ℂ] Z)) (Γ : Z →ₗ[ℂ] Z), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S →
    ∫ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) ∂(muK ε) ≠ 0 →
    ∃ Φ : W →ₗ[ℂ] Z, Φ ≠ 0 ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = S k (Φ v)

def SchurOne : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    ∫ k : KG ε, conj (trK T (toMK k)) * trK T (toMK k) ∂(muK ε) = 1

def SumTypes : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S →
    Formalism.MainNotions.S.IsKStableOn ε σ S → S ≤ sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'}

def PolyAvg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
      IsURepOn (UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧
        (∀ P : Poly n, P.totalDegree ≤ d → ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ S) ∧
        ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A

def DatumEquiv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StdGap ε lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
    IsURepOn (UJset ε) σ → Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) (lowK ε lam) V → V ≠ ⊥ →
    (∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
    ∃ U : H ≃ₗᵢ[ℂ] X, ∀ g ∈ UJset ε, ∀ x, U (σ g x) = D g (U x)

def MatRep : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)),
    IsUnitaryRep π → IsTopIrreducible π → ∃ σ : Mat n → (U →L[ℂ] U), IsURepOn (UJset ε) σ ∧
      Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ ∧ ∀ g : UJ ε, σ (toM g) = π g

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
section
set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.ChartGlue GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory.GoodTop

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

abbrev EndValuedForm11Coeffs (n : ℕ) (r : Type) : Type := Fin n → Fin n → Matrix r r ℂ

def mixTop (K : Fin n → EndValuedForm11Coeffs n r) : ℂ :=
  (n.factorial : ℂ)⁻¹ * ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
      (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det

def intersection_update_fsHerm_neg_one {α : Type} (K₁ L K₀ : α) (j : Fin n) : Fin n → α :=
  fun i => if i < j then K₁ else if i = j then L else K₀

def curvAt (G : V n → Matrix r r ℂ) (v : V n) : EndValuedForm11Coeffs n r :=
  fun a b => curv G v (coordVec a) (coordVec b)

def cutForm (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : EndValuedForm11Coeffs n r :=
  fun a b => dbar (fun x => (ρ x : ℂ)) v (coordVec b) • (conn G₁ v (coordVec a) - conn G₀ v (coordVec a))

def corrC (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : ℂ :=
  ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)

def corrTop (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : ℝ := (Real.pi ^ n)⁻¹ * (corrC ρ G₀ G₁ v).re

def offHyp (S : Finset (Fin n)) (U : Set (V n)) : Set (V n) := {v | v ∈ U ∧ ∀ a ∈ S, v a ≠ 0}

section Glue

variable {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {κ : Type}

def HasInt (e : κ → OpenPartialHomeomorph Y (V n)) (d : κ → Y → ℝ) (S : Set Y) (t : ℝ) : Prop :=
  (∀ ε : ℤˣ, glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d i y)) S ≠ ⊤) ∧
    (glueMeas e fun i y => ENNReal.ofReal (((1 : ℤˣ) : ℤ) * d i y)).real S -
      (glueMeas e fun i y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * d i y)).real S = t

structure IsTopForm (e : κ → OpenPartialHomeomorph Y (V n)) (d : κ → Y → ℝ) (S : Set Y) : Prop where
  trans : ∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → d i y = ‖transDet (e i) (e j) y‖ ^ 2 * d j y
  meas : ∀ i, AEMeasurable (fun v => d i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))

end Glue

section Var

open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle

variable {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {m : ℕ}

def topDens (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ)
    (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ) : ℝ :=
  chernTop (MvPolynomial.X ((), X.dim)) (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)

def corrDens (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (H₀ H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) (ρ : CxPts X.str σ → ℝ)
    (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ) : ℝ :=
  corrTop (fun v => ρ (c.e.symm v)) (fun v => H₀ (E.nonempty (under y)).choose (c.e.symm v) ())
    (fun v => H (E.nonempty (under y)).choose (c.e.symm v) ()) (c.e y)

structure GoodPatch (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ)
    (e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)) (S : Finset (Fin X.dim)) (A : Mat (fun _ : Unit => m) X.Fn)
    (W : Set (CxPts X.str σ)) (c : ℝ) : Prop where
  holo : IsHoloChart e
  isOpen : IsOpen W
  sub : W ⊆ e.source
  frame : ∀ z ∈ W, A ∈ E.S (under z)
  small : ∀ z ∈ W, ∀ a ∈ S, ‖e z a‖ ≤ 1 / 2
  mem : ∀ z ∈ W, z ∈ ptsIn X.str σ O ↔ ∀ a ∈ S, e z a ≠ 0
  form : ∀ z ∈ W, z ∈ ptsIn X.str σ O → ∀ a i j,
    ‖conn (fun v => H A (e.symm v) ()) (e z) (coordVec a) i j‖ * poinWt S (e z) a ≤ c
  dbar : ∀ z ∈ W, z ∈ ptsIn X.str σ O → ∀ a b i j,
    ‖curv (fun v => H A (e.symm v) ()) (e z) (coordVec a) (coordVec b) i j‖ * (poinWt S (e z) a * poinWt S (e z) b) ≤ c

theorem hasChernIntegral_iff (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) (t : ℝ) :
    HasChernIntegral E O H (MvPolynomial.X ((), X.dim)) t ↔
      HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) t := Iff.rfl

end Var

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDataOfPositivity
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory

namespace GlobalTheory.HilbertSamuel.Model

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem mulW_mem_global (j : ℕ) (u : Fin G.N → F) {f : G.Sec j} (hf : f ∈ G.global j) :
    G.mulW j u f ∈ G.global (j + 1) := by
  obtain ⟨f, rfl⟩ := hf
  refine ⟨(oneChart (isLB_tens G.K.isLB G.isLBA) G.isLB (Nat.cast_succ j).symm).mul
    (H0.ofSec G.str ⊤ (G.comb u)) f, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec, G.ofSec_comb]
  simp [Geo.mulW, Fintype.linearCombination_apply]

variable {T : ℕ} (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β)





end GlobalTheory.HilbertSamuel.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsLocCompIffEquiv
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def SoleTerm {ι : Type} (C : ι → ℂ) (p q : ι → Prop) : Prop :=
  ∃ i, C i ≠ 0 ∧ p i ∧ ∀ i', C i' ≠ 0 → q i' → i' = i

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isLocComp_iff_equiv {ρc : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : ρc.IsLocComp w σ)
    (τ : SmIrr (GLw n w)) : ρc.IsLocComp w τ ↔ Nonempty (τ.ρ.Equiv σ.ρ) :=
  ⟨fun h' => GlobalTheory.CuspRep.LocUniq.isLocComp_unique ρc w τ σ h' h,
    fun ⟨e⟩ => h.congr ((CuspSub.setoid E n).iseqv.refl ρc) ⟨e.symm⟩⟩

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWLit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]


variable (F κ) in
def IsTamagawa [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F)) : Prop :=
  μ.IsAddHaarMeasure ∧ ∃ 𝓕 : Set (κ → AF F), μ 𝓕 = 1 ∧
    IsAddFundamentalDomain (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range 𝓕 μ

end GlobalTheory.SWLit

end
end

