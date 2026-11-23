module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFiniteDirect
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PGenericLinearTrdeg
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0033

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructure
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RvRingPf

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem repr_one_tmul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr ((1 : Fv F v) ⊗ₜ[F] e) k =
      algebraMap F (Fv F v) (bs.repr e k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem struct_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i j k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  exact Finset.mem_image.2 ⟨(i, j, k), Finset.mem_univ _, rfl⟩

theorem one_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (k : Fin d) :
    algebraMap F (Fv F v) (bs.repr 1 k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩

theorem sig_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image.2 ⟨(i, k), Finset.mem_univ _, rfl⟩

theorem repr_mul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (x * y) k =
      ∑ i, ∑ j, ((Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        (Algebra.TensorProduct.basis (Fv F v) bs).repr y j) *
          algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : x * y = ∑ i, ∑ j, (bK.repr x i * bK.repr y j) • ((1 : Fv F v) ⊗ₜ[F] (bs i * bs j)) := by
    conv_lhs => rw [← bK.sum_repr x, ← bK.sum_repr y]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, hbK, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

theorem repr_sig (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (sigR (Fv F v) σ x) k =
      ∑ i, (Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : sigR (Fv F v) σ x = ∑ i, bK.repr x i • ((1 : Fv F v) ⊗ₜ[F] σ (bs i)) := by
    conv_lhs => rw [← bK.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbK, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp [sigR]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

def ringOf {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) : Subring (Fv F v ⊗[F] E) where
  carrier := Rv bs v
  mul_mem' := by
    intro x y hx hy k
    rw [repr_mul]
    exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (struct_int h i j k)
  one_mem' := by
    intro k
    rw [Algebra.TensorProduct.one_def, repr_one_tmul]
    exact one_int h k
  add_mem' := by
    intro x y hx hy k
    rw [map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx k) (hy k)
  zero_mem' := by
    intro k
    rw [map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx k
    rw [map_neg, Finsupp.neg_apply]
    exact neg_mem (hx k)

theorem sigR_mem {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (x : Fv F v ⊗[F] E) (hx : x ∈ ringOf h) :
    sigR (Fv F v) σ x ∈ ringOf h := by
  intro k
  rw [repr_sig]
  exact sum_mem fun i _ => mul_mem (hx i) (sig_int h i k)

theorem rvRing : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  intro F E _ _ _ _ _ σ d bs v h
  exact ⟨ringOf h, (sigR (Fv F v) σ).restrict (ringOf h) (ringOf h) (sigR_mem h), rfl, fun x => rfl⟩

end GlobalTheory.CompanionTheory.RvRingPf

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBounded
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

private theorem exists_isCompact_sub_incA_mem (D : D7) :
    ∃ C : Set (AE D), IsCompact C ∧ ∀ z : AE D, ∃ x : D.host.E, z - incA D x ∈ C := by
  classical
  obtain ⟨K0, hK0, hK0'⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F
  let b := Module.finBasis D.host.F D.host.E
  let bA := Algebra.TensorProduct.basis (AF D.host.F) b
  let e : AE D ≃ₗ[AF D.host.F] (Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := bA.equivFun
  have he : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap
      (e.symm : (Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) →ₗ[AF D.host.F] AE D)
  have h1 : ∀ x : Fin (Module.finrank D.host.F D.host.E) → D.host.F,
      e.symm (fun i => algebraMap D.host.F (AF D.host.F) (x i)) = incA D (∑ i, x i • b i) := by
    intro x
    rw [show incA D (∑ i, x i • b i) = (1 : AF D.host.F) ⊗ₜ[D.host.F] (∑ i, x i • b i) from rfl,
      TensorProduct.tmul_sum]
    simp only [e, Module.Basis.equivFun_symm_apply, bA, Algebra.TensorProduct.basis_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algebraMap_smul, TensorProduct.tmul_smul]
  refine ⟨e.symm '' Set.univ.pi (fun _ => K0), (isCompact_univ_pi fun _ => hK0).image he, ?_⟩
  intro z
  choose x hx using fun i => hK0' (e z i)
  refine ⟨∑ i, x i • b i, fun i => e z i - algebraMap D.host.F (AF D.host.F) (x i), fun i _ => hx i, ?_⟩
  have hv : (fun i => e z i - algebraMap D.host.F (AF D.host.F) (x i)) =
      e z - fun i => algebraMap D.host.F (AF D.host.F) (x i) := rfl
  rw [hv, map_sub, LinearEquiv.symm_apply_apply, h1]

theorem schwartzA_continuous_and_tsum_enorm_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n →
    Continuous φ ∧ ∃ B : ℝ≥0, ∀ w : Mx D m n, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖φ (rat ξ + w)‖ₑ ≤ B := by
  intro D θ hθ m n φ hφ
  have hSB := GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ hφ
  obtain ⟨hcont, K, hK, hKb⟩ := _root_.GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n φ hSB
  refine ⟨hcont, ?_⟩
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Unf.MajLoc.summable_bound D θ hθ m n
  obtain ⟨C, hC, hCz⟩ := exists_isCompact_sub_incA_mem D
  choose xf hxf using hCz
  let Q : Set (Mx D m n) := {w | ∀ i j, w i j ∈ C}
  have hQ : IsCompact Q := by
    have h := isCompact_univ_pi (fun (_ : Fin m) => isCompact_univ_pi (fun (_ : Fin n) => hC))
    have hQeq : Q = (Set.univ.pi fun (_ : Fin m) => Set.univ.pi fun (_ : Fin n) => C) := by
      ext w
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [hQeq]
    exact h
  obtain ⟨b, hbs, hb⟩ := hN K Q hK hQ
  obtain ⟨c, hc⟩ := hKb N
  set c' : ℝ := max c 0 with hc'
  refine ⟨Real.toNNReal (c' * ∑' ξ, b ξ), fun w => ?_⟩
  let ξ0 : Matrix (Fin m) (Fin n) D.host.E := Matrix.of fun i j => xf (w i j)
  let x0 : Mx D m n := w - rat ξ0
  have hx0 : x0 ∈ Q := fun i j => hxf (w i j)
  have hb0 : ∀ ξ, 0 ≤ b ξ := fun ξ => (GlobalTheory.Unf.maj_nonneg θ K N _).trans (hb x0 hx0 ξ)
  have hrat : ∀ ξ, rat ξ + w = x0 + rat (ξ + ξ0) := by
    intro ξ
    ext i j
    simp only [x0, rat, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, map_add (f := _)]
    abel
  have hpt : ∀ ξ, ‖φ (rat ξ + w)‖ₑ ≤ ENNReal.ofReal (c' * b (ξ + ξ0)) := by
    intro ξ
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [hrat ξ]
    calc ‖φ (x0 + rat (ξ + ξ0))‖ ≤ c * GlobalTheory.Unf.maj θ K N (x0 + rat (ξ + ξ0)) := hc _
      _ ≤ c' * GlobalTheory.Unf.maj θ K N (x0 + rat (ξ + ξ0)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (GlobalTheory.Unf.maj_nonneg _ _ _ _)
      _ ≤ c' * b (ξ + ξ0) := mul_le_mul_of_nonneg_left (hb x0 hx0 _) (le_max_right _ _)
  calc ∑' ξ, ‖φ (rat ξ + w)‖ₑ ≤ ∑' ξ, ENNReal.ofReal (c' * b (ξ + ξ0)) := ENNReal.tsum_le_tsum hpt
    _ = ∑' η, ENNReal.ofReal (c' * b η) :=
      (Equiv.addRight ξ0).tsum_eq (fun η => ENNReal.ofReal (c' * b η))
    _ = ENNReal.ofReal (∑' η, c' * b η) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun η => mul_nonneg (le_max_right _ _) (hb0 η)) (hbs.mul_left c')).symm
    _ = ((Real.toNNReal (c' * ∑' ξ, b ξ) : ℝ≥0) : ℝ≥0∞) := by
      rw [tsum_mul_left]
      rfl

end GlobalTheory.CompanionTheory.EisUnfold
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwiner
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegQuotTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parIndMap_surjective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {V W : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (Levi k m) V}
    {ρ' : Representation ℂ (Levi k m) W} (f : ρ.IntertwiningMap ρ') (hρ : IsSmooth ρ)
    (hf : Function.Surjective f) : Function.Surjective (parIndMap e f) := by
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let σ₀ : Representation ℂ (parab k e) V := (twist ρ (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
    hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont)
    (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
  intro x _
  refine Submodule.subset_span ⟨(), -x, ?_⟩
  show x = (0 : _) - -x
  simp

theorem prod₂_map_surjective {r t : ℕ} {U U' W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (hσ : IsSmooth σ) (hρ : IsSmooth ρ) (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ' ρ'), Function.Surjective F := by
  have hσ' : IsSmooth σ' := (IsSubquotient.of_surjective f hf).isSmooth hσ
  have hc : Continuous fun h : Levi k (Two (Fin r) (Fin t)) => (h false, h true) :=
    (continuous_apply false).prodMk (continuous_apply true)
  have h1 : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) := LinearMap.rTensor_surjective W hf
  have h2 : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight σ' g) := LinearMap.lTensor_surjective U' hg
  have h1' : Function.Surjective (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := h1
  have h2' : Function.Surjective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ' g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := h2
  have s1 := parIndMap_surjective (two (stdSum (rfl : r + t = r + t))) _
    (isSmooth_comp (isSmooth_extTensor hσ hρ) _ hc) h1'
  have s2 := parIndMap_surjective (two (stdSum (rfl : r + t = r + t))) _
    (isSmooth_comp (isSmooth_extTensor hσ' hρ) _ hc) h2'
  exact ⟨(parIndMap (two (stdSum (rfl : r + t = r + t))) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ' g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)).comp (parIndMap (two (stdSum (rfl : r + t = r + t)))
      (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)), s2.comp s1⟩

theorem nonempty_prodIrr_equiv_of_cast {c c' N : ℕ} (h : c = c') (x : Fin c → IrrGL (k := k)) (x' : Fin c' → IrrGL (k := k))
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) :
    Nonempty ((prodIrr x hd).Equiv (prodIrr x' hd')) := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  exact ⟨.refl _⟩

theorem append_term (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len)
    (hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len)
    (i : Fin ((segLow Δ a h0).len + (segHigh Δ a h1).len)) :
    Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i = Δ.term (Fin.cast hlen i) := by
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    rfl
  | right j =>
    rw [Fin.append_right]
    show (Δ.first.nu ((a : ℕ) : ℂ)).nu ((j : ℕ) : ℂ) = Δ.first.nu (((segLow Δ a h0).len + (j : ℕ) : ℕ) : ℂ)
    rw [IrrGL.nu_nu]
    show _ = Δ.first.nu ((a + (j : ℕ) : ℕ) : ℂ)
    push_cast
    rfl

theorem hasFiniteLength_prodIrr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem nontrivial_prodIrr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : Nontrivial (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) :=
  GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp _ (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x)
    (isSmooth_piTensor fun a => (x a).2.rep.smooth)

theorem exists_surjective_of_equiv {G A B C D : Type} [Group G] [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] {α : Representation ℂ G A}
    {β : Representation ℂ G B} {γ : Representation ℂ G C} {δ : Representation ℂ G D} (E : Nonempty (β.Equiv α))
    (F : ∃ f : β.IntertwiningMap γ, Function.Surjective f) (H : Nonempty (γ.Equiv δ)) :
    ∃ f : α.IntertwiningMap δ, Function.Surjective f := by
  obtain ⟨E⟩ := E
  obtain ⟨F, hF⟩ := F
  obtain ⟨H⟩ := H
  exact ⟨H.toIntertwiningMap.comp (F.comp E.symm.toIntertwiningMap),
    H.toLinearEquiv.surjective.comp (hF.comp E.symm.toLinearEquiv.surjective)⟩

theorem exists_surjective_of_prod₂_equiv {r t : ℕ} {U U' W W' A D : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup A]
    [Module ℂ A] [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} {α : Representation ℂ (GL (Fin (r + t)) k) A}
    {δ : Representation ℂ (GL (Fin (r + t)) k) D} (hσ : IsSmooth σ) (hρ : IsSmooth ρ) (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) (hg : Function.Surjective g)
    (E : Nonempty ((prod₂ σ ρ).Equiv α)) (H : Nonempty ((prod₂ σ' ρ').Equiv δ)) :
    ∃ F : α.IntertwiningMap δ, Function.Surjective F :=
  exists_surjective_of_equiv E (prod₂_map_surjective hσ hρ f g hf hg) H

theorem exists_surjective_append {p q : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (u v : IrrGL (k := k))
    (hx : ∑ a, (x a).1 = u.1) (hy : ∑ a, (y a).1 = v.1) (h : ∑ a, (Fin.append x y a).1 = u.1 + v.1)
    (hd : ∑ i, (![u, v] i).1 = u.1 + v.1)
    (fu : (prodIrr x hx).IntertwiningMap u.rep) (hfu : Function.Surjective fu)
    (fv : (prodIrr y hy).IntertwiningMap v.rep) (hfv : Function.Surjective fv) :
    ∃ F : (prodIrr (Fin.append x y) h).IntertwiningMap (prodIrr ![u, v] hd), Function.Surjective F :=
  exists_surjective_of_prod₂_equiv (isSmooth_prodIrr x hx) (isSmooth_prodIrr y hy) fu fv hfu hfv
    (GlobalTheory.T.product_irreducible_append_equiv k p q u.1 v.1 x y hx hy h) (nonempty_prod₂_equiv_prodIrr_pair u v hd)

theorem quotient_of_quotient {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V) (Q : Representation ℂ G X)
    (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (hf : ∃ f : P.IntertwiningMap Q, Function.Surjective f)
    (hQ : Nontrivial X) : ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  obtain ⟨f, hf⟩ := hf
  exact _root_.GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient σ P Q hc hfl f hf hQ

theorem quottwo : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL (k := k))
    (hu : IsLSeg (segLow Δ a h0) u.rep) (hv : IsLSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N),
    ∃ f : (prodIrr ![u, v] hd).IntertwiningMap π, Function.Surjective f := by
  intro k _ _ _ _ hA Δ N V _ _ π hπ a h0 h1 u v hu hv hd
  have hN : u.1 + v.1 = N := hd.symm ▸ (Fin.sum_univ_two (fun i => (![u, v] i).1)).symm
  subst hN
  obtain ⟨hx, -, fu, hfu, -⟩ := hu
  obtain ⟨hy, -, fv, hfv, -⟩ := hv
  obtain ⟨hΔ, hc⟩ := hπ
  have hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len := by
    show a + (Δ.len - a) = Δ.len
    omega
  have hsum : ∑ i, (Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i).1 = u.1 + v.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact congrArg₂ (· + ·) hx hy
  exact quotient_of_quotient π _ _ hc (hasFiniteLength_prodIrr hA _ hΔ)
    (exists_surjective_of_equiv (nonempty_prodIrr_equiv_of_cast hlen _ Δ.term (append_term Δ a h0 h1 hlen) hsum hΔ)
      (exists_surjective_append _ _ u v hx hy hsum hd fu hfu fv hfv) ⟨.refl _⟩) (nontrivial_prodIrr hA _ hd)

end GlobalTheory.CompanionTheory.SegQuotTwo

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.SegreChart

theorem Chart.incIdealDim : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealDim.proof
    (GroundTheory.Heights₂.Heights.IncidenceGeneric.proof GroundTheory.Heights₂.Heights.FGNullstellensatz.proof)
    GroundTheory.Heights₂.Heights.GenericLinearTrdeg.proof GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof

theorem Chart.incIdealPrime : GroundTheory.Heights₂.Heights.IncIdealPrime.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealPrime.proof
    (GroundTheory.Heights₂.Heights.IncidenceGeneric.proof GroundTheory.Heights₂.Heights.FGNullstellensatz.proof)

theorem Chart.coneDimOfChowForm : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof Chart.incIdealDim Chart.incIdealPrime

theorem Chart.GoodChartDim : GroundTheory.Heights₂.Heights.GoodChartDim.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartDim.proof GroundTheory.Heights₂.Heights.ConeVanishingHomog.proof GroundTheory.Heights₂.Heights.ConeSliceIdeal.proof GroundTheory.Heights₂.Heights.ChartDehomogPrime.proof

theorem Chart.GoodChartModel : GroundTheory.Heights₂.Heights.GoodChartModel.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartModel.proof GroundTheory.Heights₂.Heights.GoodChartZeroSet.proof Chart.GoodChartDim

theorem Chart.PtsGenericCount : GroundTheory.Heights₂.Heights.PtsGenericCount.Statement :=
  @GroundTheory.Heights₂.Heights.PtsGenericCount.proof Chart.GoodChartModel GroundTheory.Heights₂.Heights.ComponentsGenericCount.proof GroundTheory.Heights₂.Heights.SheetLift.proof

theorem Chart.PtsSheetSimpleNull : GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.proof Chart.PtsGenericCount

theorem Chart.PtsSheetOnlyNull : GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.proof GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof

theorem Chart.PtsPosPartProjIndep : GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.proof Chart.PtsSheetSimpleNull Chart.PtsSheetOnlyNull GroundTheory.Heights₂.Heights.PtsPosPartLocal.proof GroundTheory.Heights₂.Heights.PtsPosDensMeasurable.proof

theorem Chart.PtsSegreChartFibreSum : GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof

theorem Chart.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem Chart.ConeSliceSheetParam : GroundTheory.Heights₂.Heights.ConeSliceSheetParam.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSliceSheetParam.proof Chart.DiscriminantSheetCover

theorem Chart.AreaFormulaInjSet : GroundTheory.Heights₂.Heights.AreaFormulaInjSet.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInjSet.proof GroundTheory.Heights₂.Heights.AreaFormulaLocal.proof

theorem Chart.AreaFormulaInj : GroundTheory.Heights₂.Heights.AreaFormulaInj.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInj.proof Chart.AreaFormulaInjSet

theorem Chart.ConeMapAreaOne : GroundTheory.Heights₂.Heights.ConeMapAreaOne.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapAreaOne.proof Chart.AreaFormulaInj

theorem Chart.ConeMapArea : GroundTheory.Heights₂.Heights.ConeMapArea.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapArea.proof Chart.ConeMapAreaOne

theorem Chart.ConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.proof Chart.ConeSliceSheetParam Chart.ConeMapArea

theorem Chart.SliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.SliceMassFinite.proof' Chart.ConeSheetGramLintegral GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite Chart.coneDimOfChowForm

theorem Chart.SegreChartAbsIntegrable : GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.proof Chart.SliceMassFinite GroundTheory.Heights₂.Heights.SegreChartSheetCompare.proof

theorem Chart.PtsSemiPosMassFinite : GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.proof Chart.PtsPosPartProjIndep Chart.PtsSegreChartFibreSum Chart.SegreChartAbsIntegrable

theorem Chart.PtsPosDensIntegrable : GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.proof Chart.PtsSemiPosMassFinite

theorem Chart.PtsIntegralProjIndep : GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.proof Chart.PtsPosDensIntegrable Chart.PtsPosPartProjIndep

theorem Chart.PtsIntegralSegreChartProj : GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof Chart.SegreChartAbsIntegrable Chart.PtsSegreChartFibreSum

theorem Chart.SegreChartIntegral : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartIntegral.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SegreCoordGoodProj Chart.PtsIntegralProjIndep Chart.PtsIntegralSegreChartProj

end GlobalTheory.CompanionTheory.Ar.SegreChart
end

