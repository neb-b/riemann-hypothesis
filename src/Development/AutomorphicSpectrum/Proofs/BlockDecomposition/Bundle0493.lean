module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirSignatureMemCenter
section
noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.CasFamily

theorem sum_squares_eq {A : Type} [Ring A] [Algebra ℂ A] {a : ℕ} (X Y : Fin a → Fin a → A) :
    ∑ i, ∑ j, ((X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
        ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i))) =
      (8 : ℂ) • (Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
        Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j))) := by
  have h1 : ∀ i j, (X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
      ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i)) =
      (2 : ℂ) • (X i j * X j i) + (2 : ℂ) • (X j i * X i j) -
        ((2 : ℂ) • (Y i j * Y j i) + (2 : ℂ) • (Y j i * Y i j)) := by
    intro i j
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    match_scalars <;> ring
  have h2 : ∀ i j, ((1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i - Complex.I • Y j i)) +
      ((1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i + Complex.I • Y j i)) =
      (1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i) := by
    intro i j
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub, smul_smul]
    match_scalars <;> ring_nf <;> simp <;> norm_num
  have hX : ∑ i, ∑ j, X j i * X i j = ∑ i, ∑ j, X i j * X j i := Finset.sum_comm
  have hY : ∑ i, ∑ j, Y j i * Y i j = ∑ i, ∑ j, Y i j * Y j i := Finset.sum_comm
  have hc : Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
      Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) =
      ∑ i, ∑ j, ((1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i)) := by
    simp only [Formalism.REAL.Cas, ← Finset.sum_add_distrib, h2]
  rw [hc]
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, hX, hY]
  match_scalars <;> norm_num

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def sgl (i j : Fin a) : Cinf E →ₗ[ℝ] Lie E a :=
  (Matrix.singleLinearMap ℝ i j : Cinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))

def eW (w : InfinitePlace E) : Cinf E := atEmb w.embedding 1

def fW (w : InfinitePlace E) : Cinf E := atEmb w.embedding Complex.I

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
open Classical in
theorem atEmb_embedding_apply (w v : InfinitePlace E) (z : ℂ) :
    atEmb w.embedding z v = if v = w then z else 0 := by
  unfold atEmb
  rw [InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem star_atEmb (w : InfinitePlace E) (z : ℂ) :
    star (atEmb w.embedding z) = atEmb w.embedding (starRingEnd ℂ z) := by
  classical
  funext v
  rw [Pi.star_apply, atEmb_embedding_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem star_eW (w : InfinitePlace E) : star (eW w) = eW w := by
  simp [eW, star_atEmb]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem star_fW (w : InfinitePlace E) : star (fW w) = -fW w := by
  classical
  funext v
  simp only [fW, star_atEmb, Pi.neg_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [_root_.NumberField.IsTotallyComplex E] in
theorem sum_atEmb (x : Cinf E) : x = ∑ w, ((x w).re • eW w + (x w).im • fW w) := by
  classical
  have e : ∀ w, (x w).re • eW w + (x w).im • fW w = atEmb w.embedding (x w) := fun w =>
    (atEmb_eq _ _).symm
  simp only [e]
  funext v
  simp [Finset.sum_apply, atEmb_embedding_apply]

def famZ : InfinitePlace E × Fin a × Fin a × Bool × Bool → Lie E a
  | (w, i, j, false, false) => sgl i j (eW w) + sgl j i (eW w)
  | (w, i, j, false, true) => sgl i j (eW w) - sgl j i (eW w)
  | (w, i, j, true, false) => sgl i j (fW w) - sgl j i (fW w)
  | (w, i, j, true, true) => sgl i j (fW w) + sgl j i (fW w)

theorem span_famZ : Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) = ⊤ := by
  set S := Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) with hS
  have hz : ∀ k, famZ (E := E) (a := a) k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hE : ∀ w i j, sgl (E := E) (a := a) i j (eW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (eW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, false, false) + famZ (w, i, j, false, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (eW w) + sgl j i (eW w)) + (sgl i j (eW w) - sgl j i (eW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hF : ∀ w i j, sgl (E := E) (a := a) i j (fW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (fW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, true, false) + famZ (w, i, j, true, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (fW w) - sgl j i (fW w)) + (sgl i j (fW w) + sgl j i (fW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hx : ∀ i j (x : Cinf E), sgl (a := a) i j x ∈ S := fun i j x => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_atEmb x, map_sum]
    refine S.sum_mem fun w _ => ?_
    rw [map_add (f := _), map_smul, map_smul]
    exact S.add_mem (S.smul_mem _ (hE w i j)) (S.smul_mem _ (hF w i j))
  refine eq_top_iff.2 fun L _ => ?_
  have e : L = ∑ i, ∑ j, sgl i j (L i j) := Matrix.matrix_eq_sum_single (Matrix.of L)
  rw [e]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hx i j _

theorem conjTranspose_sgl (i j : Fin a) (x : Cinf E) :
    (Matrix.of (sgl i j x))ᴴ = Matrix.of (sgl j i (star x)) :=
  Matrix.conjTranspose_single i j x

theorem skew_famZ (k : InfinitePlace E × Fin a × Fin a × Bool × Bool) (hk : k.2.2.2.2 = true) :
    (Matrix.of (famZ k))ᴴ = -(Matrix.of (famZ k)) := by
  obtain ⟨w, i, j, b, c⟩ := k
  obtain rfl : c = true := hk
  cases b
  · change (Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))ᴴ =
      -(Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))
    rw [Matrix.conjTranspose_sub, conjTranspose_sgl, conjTranspose_sgl, star_eW, neg_sub]
  · change (Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))ᴴ =
      -(Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))
    have hn : ∀ i j : Fin a, Matrix.of (sgl i j (-fW w)) = -Matrix.of (sgl i j (fW w)) := fun i j => by
      rw [map_neg]; rfl
    rw [Matrix.conjTranspose_add, conjTranspose_sgl, conjTranspose_sgl, star_fW, hn, hn, neg_add, add_comm]

theorem Eop_embedding (w : InfinitePlace E) (i j : Fin a) :
    Eop w.embedding i j = (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w)) := rfl

theorem Eop_conjugate (w : InfinitePlace E) (i j : Fin a) :
    Eop (ComplexEmbedding.conjugate w.embedding) i j =
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w)) := by
  have h : atEmb w.embedding (-Complex.I) = -fW w := by
    rw [atEmb_eq]; simp [fW]
  rw [Eop, atEmb_conj, atEmb_conj, map_one, Complex.conj_I, h, map_neg, smul_neg, sub_neg_eq_add]
  rfl

theorem sum_famZ [DecidableEq (InfinitePlace E)] :
    ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ,
        lie E a (famZ k) * lie E a (famZ k) -
      ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true,
        lie E a (famZ k) * lie E a (famZ k) =
    ∑ w : InfinitePlace E, (8 : ℂ) • (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
      Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  have e : ∀ f : InfinitePlace E × Fin a × Fin a × Bool × Bool → Module.End ℂ (Sm E a),
      ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ, f k -
        ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true, f k =
      ∑ k, if k.2.2.2.2 = true then -f k else f k := fun f => by
    rw [Finset.compl_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k.2.2.2.2 = true <;> simp [h]
  rw [e]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h := sum_squares_eq (fun i j : Fin a => lieS E a i j (eW w)) (fun i j => lieS E a i j (fW w))
  have c1 : Formalism.REAL.Cas (Eop (a := a) w.embedding) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w))) := rfl
  have c2 : Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding)) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w))) :=
    congrArg _ (funext fun i => funext fun j => Eop_conjugate w i j)
  rw [c1, c2, ← h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have f1 : lie E a (famZ (w, i, j, false, false)) = lieS E a i j (eW w) + lieS E a j i (eW w) := map_add _ _ _
  have f2 : lie E a (famZ (w, i, j, false, true)) = lieS E a i j (eW w) - lieS E a j i (eW w) := map_sub _ _ _
  have f3 : lie E a (famZ (w, i, j, true, false)) = lieS E a i j (fW w) - lieS E a j i (fW w) := map_sub _ _ _
  have f4 : lie E a (famZ (w, i, j, true, true)) = lieS E a i j (fW w) + lieS E a j i (fW w) := map_add _ _ _
  simp only [if_true, Bool.false_eq_true, if_false, f1, f2, f3, f4]
  abel

theorem exists_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Z : ι → GlobalTheory.CuspRep.Lie E a) (K : Finset ι), Submodule.span ℝ (Set.range Z) = ⊤ ∧ (∀ κ ∈ K, (Matrix.of (Z κ))ᴴ = -(Matrix.of (Z κ))) ∧ (∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ)) ∈ Zalg E a := by
  intro E _ _ _ a
  have : DecidableEq (InfinitePlace E) := Classical.decEq _
  refine ⟨InfinitePlace E × Fin a × Fin a × Bool × Bool, inferInstance, inferInstance, famZ,
    Finset.univ.filter fun k => k.2.2.2.2 = true, span_famZ, fun κ hκ => skew_famZ κ (Finset.mem_filter.1 hκ).2, ?_⟩
  rw [sum_famZ]
  exact Subalgebra.sum_mem _ fun w _ => Subalgebra.smul_mem _
    (Subalgebra.add_mem _ (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _) (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _)) _

end GlobalTheory.CompanionTheory.CasFamily
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponential
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.Clozel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def scalarCurve (s : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (s : ℂ))

theorem scalarCurve_zero : scalarCurve E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 :=
    Units.ext (funext fun _ => by simp [expU])
  rw [scalarCurve, h, map_one]

theorem hasDerivAt_scalarCurve :
    HasDerivAt (fun s => toL (scalarCurve E a s).val) (oneL E a) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro w
  by_cases h : i = j
  · subst h
    have e : (fun s : ℝ => toL (scalarCurve E a s).val i i w) = fun s : ℝ => Complex.exp (s : ℂ) := by
      funext s
      simp [scalarCurve, toL, expU, Matrix.scalar_apply]
    have d : HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ)) 1 0 := by
      simpa using (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    have o : oneL E a i i w = 1 := by simp [oneL, toL]
    rw [e, o]
    exact d
  · have e : (fun s : ℝ => toL (scalarCurve E a s).val i j w) = fun _ : ℝ => 0 := by
      funext s
      simp [scalarCurve, toL, Matrix.scalar_apply, h]
    have o : oneL E a i j w = 0 := by simp [oneL, toL, h]
    rw [e, o]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem eigen_along_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ),
    lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a),
      φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  intro E _ _ _ a φ c hφ t g
  set f : ℝ → ℂ := fun u => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) with hf
  have hd : ∀ u, HasDerivAt f (c * f u) u := by
    intro u
    have h1 := hasDerivAt_curve φ (g * GlobalTheory.UnitaryBC.splitCentre E a u) (scalarCurve E a) (oneL E a)
      scalarCurve_zero hasDerivAt_scalarCurve
    have h2 : lieD (oneL E a) φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) = c * f u := by
      have := congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) hφ
      simpa [hf] using this
    rw [h2] at h1
    have h3 : HasDerivAt (fun x : ℝ => φ.1 ((g * GlobalTheory.UnitaryBC.splitCentre E a u) * infGL E a (scalarCurve E a (x - u))))
        (c * f u) u := by
      have h0 : u - u = (0 : ℝ) := sub_self u
      exact HasDerivAt.comp_sub_const u u (by rw [h0]; exact h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have e : GlobalTheory.UnitaryBC.splitCentre E a x =
        GlobalTheory.UnitaryBC.splitCentre E a u * infGL E a (scalarCurve E a (x - u)) := by
      have := GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add (E := E) (a := a) u (x - u)
      rw [add_sub_cancel] at this
      exact this
    simp only [hf, e, mul_assoc]
  have hP : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-c * v) * f v)
      (Complex.exp (-c * u) * (-c) * f u + Complex.exp (-c * u) * (c * f u)) u := by
    intro u
    have h0 : HasDerivAt (fun v : ℝ => -c * (v : ℂ)) (-c) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-c)
    exact h0.cexp.mul (hd u)
  have hconst : ∀ u : ℝ, Complex.exp (-c * u) * f u = Complex.exp (-c * (0 : ℝ)) * f 0 := by
    refine fun u => is_const_of_deriv_eq_zero (f := fun v : ℝ => Complex.exp (-c * v) * f v)
      (fun x => (hP x).differentiableAt) (fun x => ?_) u 0
    rw [(hP x).deriv]
    ring
  have h0 : f 0 = φ.1 g := by
    simp [hf, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  have ht := hconst t
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0] at ht
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm]
  change f t = _
  rw [← ht, ← mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory.CompanionTheory.Clozel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAlongOneParameterPath
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7}

theorem trace_incA_algebraMap_mul (D : D7) (β : D.host.F) (z : AE D) :
    Algebra.trace (AF D.host.F) (AE D) (incA D (algebraMap D.host.F D.host.E β) * z) =
      algebraMap D.host.F (AF D.host.F) β * Algebra.trace (AF D.host.F) (AE D) z := by
  have h : incA D (algebraMap D.host.F D.host.E β) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) β) := by
    show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E β) =
      (algebraMap D.host.F (AF D.host.F) β) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem theta_half_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {α β : D.host.F} (hβ : β + β = α) (s : ℝ) (t : AE D) (ρ : D.what₂.Tau) :
    θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t))) =
      ((1 / 2 * s : ℝ) : ℂ) * θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t)) := by
  have hi : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hσ.inf ρ).1 e
  have hs : θ ρ (infPart D (rs σ s)) = (s : ℂ) := hσ.comp _ ρ
  have hb : tauE D ρ (algebraMap D.host.F D.host.E α) =
      tauE D ρ (algebraMap D.host.F D.host.E β) + tauE D ρ (algebraMap D.host.F D.host.E β) := by
    rw [← map_add (f := _), ← map_add (f := _), hβ]
  rw [map_mul (infPart D), map_mul (θ ρ), hi, map_mul (infPart D), map_mul (θ ρ), hs,
    map_mul (infPart D), map_mul (θ ρ), hi, hb]
  push_cast
  ring

theorem psi_halfTr_rs : ∀ (D : D7) (ψ ψ₀ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ₀ (-1) → ∀ α : D.host.F,
    (∀ x, ψ x = ψ₀ (algebraMap D.host.F (AF D.host.F) α * x)) → ∀ (θ : InfFam D)
    (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (t : AE D) (s : ℝ),
    ψ (halfTr (rs σ s * t)) = Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)) := by
  intro D ψ ψ₀ h₀ α hψ θ σ hσ t s
  obtain ⟨β, hβ', hβ⟩ : ∃ β : D.host.F, β = α * (1 / 2) ∧ β + β = α := ⟨_, rfl, by ring⟩
  set z' : AE D := incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t) with hz'
  have hR : algebraMap D.host.F (AF D.host.F) α * halfTr (rs σ s * t) =
      Algebra.trace (AF D.host.F) (AE D) z' := by
    rw [hz', trace_incA_algebraMap_mul, hβ', map_mul, mul_assoc]
    rfl
  have hfin : finPart D z' = 0 := by
    have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [hz', map_mul (finPart D), map_mul (finPart D) (rs σ s), h0, zero_mul, mul_zero]
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set R := Algebra.trace (AF D.host.F) (AE D) z' with hRdef
  have h1 : ψ₀ R = psiInf D.host.F ψ₀ (fstA D.host.F R) := by
    unfold psiInf
    rw [← hT]
  have h2 := h₀.2.2 θ hσ.inf (fstA D.host.F R)
  have h3 : ∀ ρ, θ ρ (fstA D.host.F R ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((s * (θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re : ℝ) : ℂ) := by
    intro ρ
    rw [hRdef, GlobalTheory.PhaseReal.theta_trace θ hσ.inf ρ z', hz', theta_half_rs hσ hβ, Complex.re_ofReal_mul]
    congr 1
    ring
  rw [hψ, hR, h1, h2]
  congr 1
  simp only [h3]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum]
  unfold lam
  push_cast
  ring

end GlobalTheory.CompanionTheory.WSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTracePairingEqInnerPsi
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Phase

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

theorem repr_tmap (f : R →ₐ[F] S) {ι : Type} (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem trace_tmap [Module.Finite F E] (f : R →ₐ[F] S) (z : R ⊗[F] E) :
    f (Algebra.trace R (R ⊗[F] E) z) =
      Algebra.trace S (S ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis S b)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← repr_tmap, map_mul]
  simp only [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]

theorem tmap_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ z) =
      sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tmap_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR]

theorem tmap_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    (gramR R σ J X).map (Algebra.TensorProduct.map f (AlgHom.id F E)) =
      gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  ext a c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, gramR, hR, Formalism.UG.hform, JR, map_sum, map_mul, tmap_sigR, tmap_inclR]

theorem tmap_phase [Module.Finite F E] (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (X : Fin n → Fin M → R ⊗[F] E) :
    f (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (Matrix.trace (B * gramR R σ J X))) =
      algebraMap F S (1 / 2) * Algebra.trace S (S ⊗[F] E)
        (Matrix.trace (B.map (Algebra.TensorProduct.map f (AlgHom.id F E)) *
          gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)))) := by
  rw [map_mul, AlgHom.commutes, trace_tmap, ← tmap_gramR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

end Gen

theorem adelic_phase_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
  (b : HermR (AF F) σ n) (X : Fin n → Fin M → AF F ⊗[F] E),
  ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) =
    psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        gramR (Ainf F) σ J (projInf X)))) *
    psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gramR (Af F) σ J (projFin X)))) := by
  intro F E _ _ _ _ _ σ _ M J n ψ b X
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 := tmap_phase (fstA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have h2 := tmap_phase (sndA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have key : ∀ T : AF F, ψ T = psiInf F ψ (fstA F T) * psiFin F ψ (sndA F T) := by
    intro T
    simp only [psiInf, psiFin]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    exact (Prod.fst_add_snd T).symm
  rw [key, h1, h2]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Integ.Phase
end
end

