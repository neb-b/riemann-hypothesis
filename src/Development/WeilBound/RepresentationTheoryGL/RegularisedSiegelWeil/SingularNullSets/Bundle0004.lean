module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.CutSupp
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem cutSupp (θ : InfFam D) (hθ : IsInfFam θ) {a b : ℕ} (K : Set (Mx D a b)) (hK : IsCompact K)
    (Φ : Mx D a b → ℂ) (hbox : ∀ x, Φ x ≠ 0 → GlobalTheory.Unf.InBox K x) (c : (D.what₂.Tau → Fin a → Fin b → ℂ) → ℂ)
    (hc : HasCompactSupport c) : HasCompactSupport (fun x => c (fun τ i j => compAt θ τ x i j) * Φ x) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : D.what₂.Tau → Fin a → Fin b → ℂ)
  obtain ⟨hcl, hcont, -, hcpt⟩ := (_root_.GlobalTheory.Unf.maj_measurable_rat D θ hθ).1 a b K hK
  set R' : ℝ := ∑ _τ : D.what₂.Tau, ∑ _i : Fin a, ∑ _j : Fin b, R with hR'
  refine HasCompactSupport.intro' (hcpt R') (hcl.inter (isClosed_le hcont continuous_const)) fun x hx => ?_
  by_contra hne
  have hc0 : c (fun τ i j => compAt θ τ x i j) ≠ 0 := left_ne_zero_of_mul hne
  have hΦ : Φ x ≠ 0 := right_ne_zero_of_mul hne
  have hmem : (fun τ i j => compAt θ τ x i j) ∈ Metric.closedBall (0 : D.what₂.Tau → Fin a → Fin b → ℂ) R :=
    hR (subset_tsupport _ hc0)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  apply hx
  refine ⟨hbox x hΦ, ?_⟩
  show GlobalTheory.Unf.realSize θ x ≤ R'
  unfold GlobalTheory.Unf.realSize
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 := norm_le_pi_norm (fun τ i j => compAt θ τ x i j) τ
  have h2 := norm_le_pi_norm (fun i j => compAt θ τ x i j) i
  have h3 := norm_le_pi_norm (fun j => compAt θ τ x i j) j
  exact h3.trans (h2.trans (h1.trans hmem))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.DomBound
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem domBound (θ : InfFam D) (hθ : IsInfFam θ) {a b : ℕ} (Φ : Mx D a b → ℂ) (hΦ : Φ ∈ schwartzA θ a b) :
    ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ) (M : ℝ), 0 ≤ M ∧
      ∀ x, ‖Φ x‖ ≤ M * ∑ i, ‖f i (fun τ i j => compAt θ τ x i j)‖ := by
  obtain ⟨-, k, f, g, hg, hb⟩ := _root_.GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ a b Φ hΦ
  choose C hC using fun i => ((hg i).1.continuous).bounded_above_of_compact_support (hg i).2
  refine ⟨k, f, ∑ i, max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun x => ?_⟩
  have h1 : ‖Φ x‖ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ := by
    have h := hb x
    simp only [enorm_eq_nnnorm, ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_le_coe] at h
    have h' : ((‖Φ x‖₊ : NNReal) : ℝ) ≤ ((∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) *
        g i (fun i' j => finPart D (x i' j))‖₊ : NNReal) : ℝ) := NNReal.coe_le_coe.mpr h
    simpa only [coe_nnnorm, NNReal.coe_sum] using h'
  refine h1.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, mul_comm (∑ i, max (C i) 0)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (hC i _).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (f := fun i => max (C i) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ i)))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.DyadicFin
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LGenK

theorem dyadic_fin (D : D7) : ∃ S₀ : Finset (Pl D), ∀ v : Pl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S₀ := by
  have h2 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  obtain hfin := Ideal.finite_factors h2
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact Ideal.dvd_span_singleton.mpr hv

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.EvGoodSmul
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7} {a b : ℕ}

def EvGood (Φ : Mx D a b → ℂ) : Prop :=
  ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e Φ

theorem good_zero (S : Finset (Pl D)) (e : AE D) : Good S e (0 : Mx D a b → ℂ) := by
  intro x
  split_ifs <;> rfl

theorem good_add {S : Finset (Pl D)} {e : AE D} {Φ Ψ : Mx D a b → ℂ} (hΦ : Good S e Φ) (hΨ : Good S e Ψ) :
    Good S e (Φ + Ψ) := by
  intro x
  simp only [Pi.add_apply]
  rw [hΦ x, hΨ x]
  split_ifs with h
  · rfl
  · simp

theorem good_smul {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (c : ℂ) (hΦ : Good S e Φ) :
    Good S e (c • Φ) := by
  intro x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hΦ x]
  split_ifs with h
  · rfl
  · simp

theorem evGood_zero : EvGood (0 : Mx D a b → ℂ) :=
  ⟨∅, fun S _ e _ => good_zero S e⟩

theorem evGood_add {Φ Ψ : Mx D a b → ℂ} (hΦ : EvGood Φ) (hΨ : EvGood Ψ) : EvGood (Φ + Ψ) := by
  classical
  obtain ⟨S₁, h₁⟩ := hΦ
  obtain ⟨S₂, h₂⟩ := hΨ
  exact ⟨S₁ ∪ S₂, fun S hS e he =>
    good_add (h₁ S (Finset.union_subset_left hS) e he) (h₂ S (Finset.union_subset_right hS) e he)⟩

theorem evGood_smul {Φ : Mx D a b → ℂ} (c : ℂ) (hΦ : EvGood Φ) : EvGood (c • Φ) := by
  obtain ⟨S₀, h⟩ := hΦ
  exact ⟨S₀, fun S hS e he => good_smul c (h S hS e he)⟩

theorem evGood_span {s : Set (Mx D a b → ℂ)} (hs : ∀ φ ∈ s, EvGood φ) :
    ∀ Φ ∈ Submodule.span ℂ s, EvGood Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact evGood_zero
  | add x y _ _ hx hy => exact evGood_add hx hy
  | smul c x _ hx => exact evGood_smul c hx

theorem ev_span {θ : InfFam D} (s : Set (Mx D a b → ℂ)) (hs : schwartzA θ a b = Submodule.span ℂ s)
    (h : ∀ φ ∈ s, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e φ) :
    ∀ Φ ∈ schwartzA θ a b, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e Φ := by
  intro Φ hΦ
  rw [hs] at hΦ
  exact evGood_span h Φ hΦ

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.IsUnitOfComp
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

def crd (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) (k : Fin (Module.finrank F E)) : R :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr x k

theorem crd_tmul (R : Type) [CommRing R] [Algebra F R] (r : R) (e : E) (k : Fin (Module.finrank F E)) :
    crd R (r ⊗ₜ[F] e) k = r * algebraMap F R ((Module.finBasis F E).repr e k) := by
  unfold crd
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Finsupp.mapRange_apply, smul_eq_mul]

theorem crd_add (R : Type) [CommRing R] [Algebra F R] (x y : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    crd R (x + y) k = crd R x k + crd R y k := by
  simp [crd]

theorem crd_neg (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    crd R (-x) k = -crd R x k := by
  simp [crd]

theorem crd_zero (R : Type) [CommRing R] [Algebra F R] (k : Fin (Module.finrank F E)) :
    crd R (0 : R ⊗[F] E) k = 0 := by
  simp [crd]

theorem crd_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    crd R' (Algebra.TensorProduct.map f (AlgHom.id F E) x) k = f (crd R x k) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, crd_zero, crd_zero, map_zero]
  | tmul r e =>
    rw [Algebra.TensorProduct.map_tmul, crd_tmul, crd_tmul, map_mul, AlgHom.commutes]
    rfl
  | add x y hx hy => rw [map_add (f := _), crd_add, crd_add, hx, hy, map_add (f := _)]

theorem crd_ext (R : Type) [CommRing R] [Algebra F R] {x y : R ⊗[F] E}
    (h : ∀ k, crd R x k = crd R y k) : x = y :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr.injective (Finsupp.ext h)

theorem sum_crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) :
    ∑ k, crd R y k ⊗ₜ[F] (Module.finBasis F E) k = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis R (Module.finBasis F E)).sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

end Coord

variable {D : D7}

theorem cv_eq (v : Pl D) (x : AE D) :
    cv D v x = Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) x := rfl

theorem infPart_eq (x : AE D) :
    infPart D x = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x := rfl

theorem ext_comp {D : D7} {x y : AE D} (hf : ∀ v, cv D v x = cv D v y) (hi : infPart D x = infPart D y) : x = y := by
  refine crd_ext (AF D.host.F) fun k => ?_
  have hf' : ∀ v : Pl D, evFin D.host.F v (crd (AF D.host.F) x k) = evFin D.host.F v (crd (AF D.host.F) y k) := by
    intro v
    have := congrArg (fun z => crd (Fv D.host.F v) z k) (hf v)
    simpa only [cv_eq, crd_map] using this
  have hi' : fstA D.host.F (crd (AF D.host.F) x k) = fstA D.host.F (crd (AF D.host.F) y k) := by
    have := congrArg (fun z => crd (Ainf D.host.F) z k) hi
    simpa only [infPart_eq, crd_map] using this
  exact Prod.ext hi' (Subtype.ext (funext hf'))

theorem cv_cA {D : D7} (v : Pl D) (x : AE D) : cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem infPart_cA {D : D7} (x : AE D) : infPart D (cA D x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem crd_int_ev (k : Fin (Module.finrank D.host.F D.host.E)) :
    ∀ᶠ v in Filter.cofinite, ∀ y ∈ intLoc D.host.F D.host.E (v : Pl D),
      crd (Fv D.host.F v) y k ∈ (v : Pl D).adicCompletionIntegers D.host.F := by
  classical
  set b := Module.finBasis D.host.F D.host.E
  set B := NumberField.RingOfIntegers.basis D.host.E
  have hev : ∀ᶠ v in Filter.cofinite, ∀ j,
      algebraMap D.host.F (Fv D.host.F v) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) k) ∈
        (v : Pl D).adicCompletionIntegers D.host.F := by
    rw [Filter.eventually_all]; intro j
    exact (algebraMap D.host.F (Af D.host.F) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) k)).2
  filter_upwards [hev] with v hv
  intro y hy
  refine intLoc_induction (p := fun y => crd (Fv D.host.F v) y k ∈ (v : Pl D).adicCompletionIntegers D.host.F)
    ?_ ?_ ?_ ?_ hy
  · intro a ha o
    rw [crd_tmul]
    refine mul_mem ha ?_
    have ho : (o : D.host.E) = ∑ j, (B.repr o j) • ((B j : 𝓞 D.host.E) : D.host.E) := by
      conv_lhs => rw [← B.sum_repr o]
      push_cast
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ho, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (hv j) _
  · rw [crd_zero]; exact zero_mem _
  · intro y z hy hz; rw [crd_add]; exact add_mem hy hz
  · intro y hy; rw [crd_neg]; exact neg_mem hy

theorem glue_one (D : D7) (f : ∀ v : Pl D, Fv D.host.F v ⊗[D.host.F] D.host.E)
    (hf : ∀ v, f v ∈ intLoc D.host.F D.host.E v) :
    ∃ x : AE D, (∀ v, cv D v x = f v) ∧ infPart D x = 0 := by
  classical
  let c : Fin (Module.finrank D.host.F D.host.E) → (v : Pl D) → Fv D.host.F v := fun k v => crd (Fv D.host.F v) (f v) k
  have hc : ∀ k, ∀ᶠ v in Filter.cofinite, c k v ∈ (v : Pl D).adicCompletionIntegers D.host.F := by
    intro k
    filter_upwards [crd_int_ev (D := D) k] with v hv
    exact hv _ (hf v)
  let C : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F := fun k => RestrictedProduct.mk (c k) (hc k)
  refine ⟨∑ k, pairA D.host.F 0 (C k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E) k, fun v => ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [← sum_crd (Fv D.host.F v) (f v)]
    rfl
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    rw [TensorProduct.zero_tmul]

theorem glue_mat (D : D7) {m p : ℕ} (b : ∀ v : Pl D, Matrix (Fin m) (Fin p) (Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hb : ∀ v i j, b v i j ∈ intLoc D.host.F D.host.E v) :
    ∃ x : Mx D m p, (∀ v i j, cv D v (x i j) = b v i j) ∧ ∀ i j, infPart D (x i j) = 0 := by
  choose g hg using fun i j => glue_one D (fun v => b v i j) (fun v => hb v i j)
  exact ⟨Matrix.of fun i j => g i j, fun v i j => (hg i j).1 v, fun i j => (hg i j).2⟩

theorem isUnit_of_comp (D : D7) (y : AE D) (hf : ∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v y * z = 1)
    (hi : infPart D y = 1) : IsUnit y := by
  choose z hz hzy using hf
  obtain ⟨s, hs, hs0⟩ := glue_one D z hz
  set e : AE D := pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E) with he
  have hev : ∀ v, cv D v e = 0 := by
    intro v
    show (evFin D.host.F v (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    have : evFin D.host.F v (pairA D.host.F 1 0) = 0 := rfl
    rw [this, TensorProduct.zero_tmul]
  have hei : infPart D e = 1 := rfl
  have h1 : y * (s + e) = 1 := by
    refine ext_comp (fun v => ?_) ?_
    · rw [map_mul, map_add (f := _), hs, hev, add_zero, hzy, map_one]
    · rw [map_mul, map_add (f := _), hs0, hei, zero_add, hi, mul_one, map_one]
  exact ⟨⟨y, s + e, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem haar_map_eq {G G' : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G']
    [SecondCountableTopology G'] [T2Space G'] [MeasurableSpace G'] [BorelSpace G'] (Θ : G ≃ₜ+ G')
    (μ : Measure G) [μ.IsAddHaarMeasure] (μ' : Measure G') [μ'.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ μ.map Θ = c • μ' := by
  haveI : (μ.map Θ).IsAddHaarMeasure := Θ.isAddHaarMeasure_map μ
  exact ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, Measure.isAddLeftInvariant_eq_smul _ _⟩

def fixS {X : Type} [AddCommGroup X] (p : X →+ X) : AddSubgroup X where
  carrier := {x | p x = x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add (f := _), ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [map_neg, ha]

theorem decomp {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (p : X →+ X) (hp : Continuous p)
    (hpp : ∀ x, p (p x) = p x) (μ : Measure X) [μ.IsAddHaarMeasure] (νH : Measure (fixS p)) [νH.IsAddHaarMeasure]
    (νY : Measure p.ker) [νY.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : X → ℂ,
      (Integrable f μ ↔ Integrable (fun z : fixS p × p.ker => f (z.1.1 + z.2.1)) (νH.prod νY)) ∧
      ∫ x, f x ∂μ = (c : ℂ) * ∫ z : fixS p × p.ker, f (z.1.1 + z.2.1) ∂(νH.prod νY) := by
  have hH : IsClosed (fixS p : Set X) := isClosed_eq hp continuous_id
  have hY : IsClosed (p.ker : Set X) := isClosed_singleton.preimage hp
  haveI : LocallyCompactSpace (fixS p) := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace p.ker := hY.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (fixS p) :=
    TopologicalSpace.Subtype.secondCountableTopology (fixS p : Set X)
  haveI : SecondCountableTopology p.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (p.ker : Set X)
  haveI : BorelSpace (fixS p) := inferInstance
  haveI : BorelSpace p.ker := inferInstance
  haveI : BorelSpace (fixS p × p.ker) := Prod.borelSpace
  let Θ : (fixS p × p.ker) ≃ₜ+ X :=
    { toFun := fun z => z.1.1 + z.2.1
      invFun := fun x => (⟨p x, hpp x⟩, ⟨x - p x, by rw [AddMonoidHom.mem_ker, map_sub, hpp, sub_self]⟩)
      left_inv := by
        rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        have ha' : p a = a := ha
        have hb' : p b = 0 := hb
        ext <;> simp [ha', hb']
      right_inv := fun x => by simp
      map_add' := fun z w => by
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add]
        abel
      continuous_toFun := by fun_prop
      continuous_invFun := by
        refine Continuous.prodMk (hp.subtype_mk _) ((continuous_id.sub hp).subtype_mk _) }
  obtain ⟨c, hc, hmap⟩ := haar_map_eq Θ (νH.prod νY) μ
  have hemb : MeasurableEmbedding Θ := Θ.toHomeomorph.measurableEmbedding
  have hμ : μ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) • (νH.prod νY).map Θ := by
    rw [hmap, ← ENNReal.smul_def, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  refine ⟨c⁻¹, inv_pos.2 hc, fun f => ⟨?_, ?_⟩⟩
  · rw [hμ, integrable_smul_measure (by simpa using hc.ne') ENNReal.coe_ne_top, hemb.integrable_map_iff]
    rfl
  · rw [hμ, integral_smul_measure, hemb.integral_map]
    simp only [ENNReal.coe_toReal, Complex.real_smul, NNReal.coe_inv, Complex.ofReal_inv]
    push_cast
    rfl

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

