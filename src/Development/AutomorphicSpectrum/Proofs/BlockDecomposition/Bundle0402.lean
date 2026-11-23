module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsThetaLePowOfColProd
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColProd

theorem tsum_pow_fin {α : Type*} (f : α → ℝ≥0∞) (n : ℕ) :
    ∑' g : Fin n → α, ∏ j, f (g j) = (∑' v, f v) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n + 1) => α))]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod (f := fun a (g : Fin n → α) => f a * ∏ i, f (g i))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih, pow_succ']

theorem absTheta_le_pow_of_colProd : ∀ (D : D7) (V : HSp D) {n : ℕ} (φ : Mx D V.rank n → ℂ) (ρ : Mx D V.rank 1 → ℝ≥0∞) (C : ℝ≥0∞) (y : GA D V), (∀ x : Mx D V.rank n, ‖φ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ ≤ C * ∏ j : Fin n, ρ (fun i (_ : Fin 1) => x i j)) → ∀ a : GA D V, absTheta V φ (a * y) ≤ C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ρ (invPt V a ξ)) ^ n := by
  intro D V n φ ρ C y hφ a
  have hstep : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      ‖φ (invPt V (a * y) ξ)‖ₑ ≤ C * ∏ j : Fin n, ρ (invPt V a (fun i (_ : Fin 1) => ξ i j)) := by
    intro ξ
    have h1 : invPt V (a * y) ξ =
        (HMul.hMul (mt V y⁻¹) (invPt V a ξ) : Matrix (Fin V.rank) (Fin n) (AE D)) := by
      simp only [invPt, mul_inv_rev, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.mul_assoc]
    rw [h1]
    refine (hφ (invPt V a ξ)).trans (le_of_eq ?_)
    congr 1
  let e : (Fin n → Matrix (Fin V.rank) (Fin 1) D.host.E) ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun g i j => g j i 0
      invFun := fun ξ j i _ => ξ i j
      left_inv := fun g => by
        funext j i u
        show g j i 0 = g j i u
        rw [Fin.fin_one_eq_zero u]
      right_inv := fun ξ => by rfl }
  calc absTheta V φ (a * y)
      = ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖φ (invPt V (a * y) ξ)‖ₑ := by rfl
    _ ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          C * ∏ j : Fin n, ρ (invPt V a (fun i (_ : Fin 1) => ξ i j)) := ENNReal.tsum_le_tsum hstep
    _ = C * ∑' g : Fin n → Matrix (Fin V.rank) (Fin 1) D.host.E, ∏ j : Fin n, ρ (invPt V a (g j)) := by
        rw [ENNReal.tsum_mul_left, ← Equiv.tsum_eq e]
        congr 1
        refine tsum_congr (fun g => Finset.prod_congr rfl (fun j _ => ?_))
        congr 2
        funext i u
        show g j i 0 = g j i u
        rw [Fin.fin_one_eq_zero u]
    _ = C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ρ (invPt V a ξ)) ^ n := by
        rw [tsum_pow_fin (fun v => ρ (invPt V a v)) n]

end GlobalTheory.CompanionTheory.ColProd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectorsStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_spanned_by_weight_vectors : ∀ {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A), (∀ k, φ (e (k, k)) t = rhoVec n k • t) → ∀ x : U n, φ x t = 0 → x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | exact GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRationalEmbeddingMap
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem archMat_projArch_ratEmb (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) (w : InfinitePlace F) (τ : EmbOver E w) :
    archMat σ J τ (projArch σ J w (ratEmb σ J γ)) = γ.1.1.map τ.1 := by
  rw [GlobalTheory.Orb.archMat_apply, projArch_ratEmb]
  ext i j
  change infEmb τ ((1 : w.Completion) ⊗ₜ[F] (γ.1.1 i j)) = τ.1 (γ.1.1 i j)
  rw [infEmb_tmul, map_one, one_mul]

end GlobalTheory.CompanionTheory.CFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicNormFiniteNonzero
section
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc

theorem sqMass_ne_top_and_ne_zero :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
      (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
      ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → φ ≠ 0 →
        (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ ⊤ ∧ (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ 0 := by
  intro E _ _ _ N _ _ μ _ F hF φ hA hS hne
  exact ⟨(GlobalTheory.CompanionTheory.SqIntFD.sqIntAt E N μ F hF φ hA hS).ne,
    (GlobalTheory.CompanionTheory.PosNormFD.posNorm E N μ F hF φ hA hS hne).ne'⟩

end GlobalTheory.CompanionTheory.FinDisc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolicLocal
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (extH tensNU tensNU_tmul)

namespace GlobalTheory.CompanionTheory.KFin

section Step

variable {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
  [CommRing R'] [Algebra F R'] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)

theorem tensNU_mul_inclR (u : R ⊗[F] E) (e : E) :
    tensNU j hj u * inclR (F := F) R' e = tensNU j hj (u * inclR (F := F) R e) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]
  | tmul a e' => simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem map_tensNU_mul_inclR {a b c : Type} [Fintype b] (A : Matrix a b (R ⊗[F] E)) (X : Matrix b c E) :
    A.map (tensNU j hj) * X.map (inclR (F := F) R') = (A * X.map (inclR (F := F) R)).map (tensNU j hj) := by
  ext r s
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, tensNU_mul_inclR, map_sum]

theorem inclR_mul_map_tensNU {a b c : Type} [Fintype b] (X : Matrix a b E) (A : Matrix b c (R ⊗[F] E)) :
    X.map (inclR (F := F) R') * A.map (tensNU j hj) = (X.map (inclR (F := F) R) * A).map (tensNU j hj) := by
  ext r s
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, mul_comm (inclR (F := F) R' _), mul_comm (inclR (F := F) R _),
    tensNU_mul_inclR, map_sum]

theorem mat_extH_eq_add (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J) :
    (HA.mat R' σ J (extH σ J j hj g)).1 = 1 + ((HA.mat R σ J g).1 - 1).map (tensNU j hj) := by
  ext r s
  rw [GlobalTheory.AutFunCompare.mat_extH]
  by_cases h : r = s
  · subst h
    simp [map_sub]
    ring
  · simp [Matrix.one_apply, h]

theorem extH_stab (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J)
    (X : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (hB : B.BlockTriangular id)
    (h : (HA.mat R σ J g).1 * X.map (inclR (F := F) R) = X.map (inclR (F := F) R) * B) :
    ∃ B' : Matrix (Fin r) (Fin r) (R' ⊗[F] E), B'.BlockTriangular id ∧
      (HA.mat R' σ J (extH σ J j hj g)).1 * X.map (inclR (F := F) R') = X.map (inclR (F := F) R') * B' := by
  refine ⟨1 + (B - 1).map (tensNU j hj), ?_, ?_⟩
  · intro a b hab
    have hne : a ≠ b := fun e => by subst e; exact lt_irrefl _ hab
    have h0 : B a b = 0 := hB hab
    simp [Matrix.one_apply, hne, h0]
  · rw [mat_extH_eq_add, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, map_tensNU_mul_inclR,
      inclR_mul_map_tensNU, Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]

end Step

theorem emb_mem_minPar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (v : HeightOneSpectrum (𝓞 F)) (p : GLoc σ J v) (B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E))
    (hB : B.BlockTriangular id)
    (h : (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B) :
    emb σ J v p ∈ minPar σ J X := by
  obtain ⟨B₁, hB₁, h₁⟩ := extH_stab (singleFin v) (singleFin_mul v) σ J p X B hB h
  obtain ⟨B₂, hB₂, h₂⟩ := extH_stab (R' := AF F) (LinearMap.inr F (Ainf F) (Af F))
    (fun _ _ => Prod.ext (mul_zero _).symm rfl) σ J _ X B₁ hB₁ h₁
  exact ⟨B₂, hB₂, h₂⟩

end GlobalTheory.CompanionTheory.KFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedIntegralMatricesFinite
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem matrices_bounded_denominator_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsTotallyReal F → ∀ {ι : Type} [Finite ι] (d : ℕ) (B : ℝ), 0 < d → {N : Matrix ι ι E | (∀ u v, IsIntegral ℤ ((d : E) * N u v)) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : ι), ‖τ.1 (N u v)‖ ≤ B}.Finite := by
  intro F E _ _ _ _ _ hF ι _ d B hd
  haveI := hF
  have hS : {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ) * B}.Finite :=
    Embeddings.finite_of_norm_le E ℂ _
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hT := hS.preimage (f := fun e : E => (d : E) * e)
    (fun a _ b _ h => mul_left_cancel₀ hd0 h)
  have hM := Set.Finite.pi' (fun _ : ι => Set.Finite.pi' (fun _ : ι => hT))
  refine hM.subset ?_
  rintro N ⟨h1, h2⟩ u v
  refine ⟨h1 u v, fun φ => ?_⟩
  have hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F E)) :=
    IsTotallyReal.complexEmbedding_isReal _
  have hb := h2 (InfinitePlace.mk (φ.comp (algebraMap F E)))
    ⟨φ, (InfinitePlace.embedding_mk_eq_of_isReal hr).symm⟩ u v
  rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d)

end GlobalTheory.CompanionTheory.CFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirEqOfSingularWeightVectorStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_eq_of_singular_weight_vector : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n), IsAdW μ x → (∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) → x ∉ Jp n → casC (fun k => rhoVec n k + (μ k : ℂ)) = casC (rhoVec n) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq | exact GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq | (intros; apply GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstProperty
section
noncomputable section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem hecke_dominant_mul_abstract (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    PositivityTheory.SphericalProduct.A1 G := by
  intro D V _ _ π hπ t t' ht _ U U' hU hU' v f hf
  obtain ⟨r, hr, x, hx, hcos⟩ := _root_.GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom G D t' ‹_›
  have hform := _root_.GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average G D.J D.isOpen_J D.isCompact_J V π hπ (t' : G) U' hU' r x hr
    (fun i => (hx i).1) hcos v
  have hfx : ∀ (x : G), x ∈ D.J → ∀ w : V, f (π x w) = f w := fun x hxJ w =>
    LinearMap.congr_fun (hf x hxJ) w
  have hterm : ∀ i, f (π (t : G) (π (x i * (t' : G)) (v : V))) = f (π ((t : G) * t') (v : V)) := by
    intro i
    have hconj : (t : G) * x i * (t : G)⁻¹ ∈ D.J := (ht.1 (x i) (hx i)).1
    have hmul : (t : G) * (x i * (t' : G)) = ((t : G) * x i * (t : G)⁻¹) * ((t : G) * t') := by group
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]
    exact hfx _ hconj _
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hUU : ((((U * U') v : fixed π D.J)) : V) = ((U (U' v) : fixed π D.J) : V) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hUU, ← hU (U' v) f hf, hform, map_smul, map_smul, map_sum, map_sum, Finset.sum_congr rfl (fun i _ => hterm i)]
  simp [hr0]

end GlobalTheory.CompanionTheory.Casselman

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesLieAction
section
noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.ZalgCentral

theorem Zalg_mul_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)),
    z ∈ Zalg E a → ∀ X, z * lie E a X = lie E a X * z := by
  intro E _ _ _ a z hz X
  unfold Zalg at hz
  have hle : Algebra.adjoin ℂ {z : Module.End ℂ (Sm E a) | ∃ τ u, z = cap τ u} ≤
      Subalgebra.centralizer ℂ {lie E a X} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (commute_cap_lie τ u X).symm.eq
  have hc := (Subalgebra.mem_centralizer_iff ℂ).mp (hle hz) (lie E a X) (Set.mem_singleton _)
  exact hc.symm

end GlobalTheory.CompanionTheory.ZalgCentral
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterWeightMap
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

namespace GlobalTheory.CompanionTheory.CharInf

theorem chWMap : ChWMap := by
  intro E _ _ n lam P
  rfl

end GlobalTheory.CompanionTheory.CharInf
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationTransfer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory GlobalTheory.Points GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.ProjVar.Var

namespace GlobalTheory.CompanionTheory.ChernTransport

section Chart

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B B' : LB X} {φ : Weight p σ B} {ψ : Weight p σ B'}

theorem hess_eq_of_unit (c : AlgChart p σ D) (h : φ.IsCInf) {y : CxPts p σ} (hy : y ∈ c.e.source)
    {i : B.ι} {j : B'.ι} (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B'.U j))
    (a : Γ(X, B.U i ⊓ B'.U j)ˣ)
    (ha : ∀ z ∈ ptsIn p σ (B.U i ⊓ B'.U j),
      ψ.φ j z = φ.φ i z + Real.log (‖ev p σ _ a.val z‖ ^ 2)) :
    c.hess ψ j y = c.hess φ i y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ B'.U j))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, hj⟩)
  have hg := c.holo _ a.val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ B'.U j),
      (ev p σ _ a.val ∘ c.e.symm) v ≠ 0 := fun v hv => ev_ne_zero hv.2 a.isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h i) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun w => ((Real.log (‖(ev p σ _ a.val ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext s t
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 s t
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ha _ hv.2, one_mul]
  rfl

theorem chartMeas_congr_source {n : ℕ} {T : Type} [TopologicalSpace T] [MeasurableSpace T]
    (e : OpenPartialHomeomorph T (V n)) {ρ ρ' : T → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  have hae : (ρ ∘ e.symm) =ᵐ[volume.restrict e.target] (ρ' ∘ e.symm) :=
    (ae_restrict_iff' e.open_target.measurableSet).2
      (Filter.Eventually.of_forall fun v hv => h _ (e.map_target hv))
  show Measure.map e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) =
    Measure.map e.symm ((volume.restrict e.target).withDensity (ρ' ∘ e.symm))
  rw [withDensity_congr_ae hae]

theorem chernPart_eq_of_chernDens (h : ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source,
    c.chernDens ψ y = c.chernDens φ y) (ε : ℤˣ) : ψ.chernPart D ε = φ.chernPart D ε := by
  show (⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens ψ y)) =
    ⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens φ y)
  exact iSup_congr fun c => chartMeas_congr_source _ fun y hy => by rw [h c y hy]

end Chart

variable {Y : Var ℂ} {Δ : Y.Dv} {L L' : LB Y.X} {r : L.ι → Y.Fnˣ} {r' : L'.ι → Y.Fnˣ}

theorem exists_unit_tv (hp : Presents Δ L r) (hp' : Presents Δ L' r') (i : L.ι) (j : L'.ι) :
    ∃ a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ, ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
      tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z := by
  obtain ⟨a, ha⟩ := exists_unit_fnOf_eq (U := L.U i ⊓ L'.U j)
    (f := (r' j : Y.Fn) / (r i : Y.Fn))
    fun x hx => (hp.isEqn i x hx.1).iff_unitAt.1 (hp'.isEqn j x hx.2)
  refine ⟨a, fun z hz => ?_⟩
  have hb := mem_ptsIn_iff.1 hz
  rw [tv, ← ha (gen_mem hb), val_cx_fnOf hb]

theorem exists_transport (hp : Presents Δ L r) (hp' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (hφ : φ.IsCInf) :
    ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
      ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  have hs : mSmooth Y (RingHom.id ℂ) Δ (ofWeight Y (RingHom.id ℂ) Δ L r hp φ) :=
    (mSmooth_ofWeight_iff hp φ).2 ((Weight.isCInf_iff_isSmooth (Y.an _)).1 hφ)
  set m := ofWeight Y (RingHom.id ℂ) Δ L r hp φ with hm
  let ψ : Weight Y.str (RingHom.id ℂ) L' := m.toWeight hs.posSet_eq hp'
  have hψ : ψ.IsCInf := (Weight.isCInf_iff_isSmooth (Y.an _)).2 (hs.isSmooth_toWeight hp')
  have key : ∀ (i : L.ι) (j : L'.ι) (a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ),
      (∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z) →
      ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        ψ.φ j z = φ.φ i z + Real.log (‖ev Y.str (RingHom.id ℂ) _ a.val z‖ ^ 2) := by
    intro i j a ha z hz
    obtain ⟨hi, hj⟩ := mem_ptsIn_inf.1 hz
    have hw : m.wt (r i) z = φ.φ i z := by
      rw [Met.wt, hm, ofWeight_h hp φ hi, Real.log_exp, neg_neg]
    have := Met.wt_trans (hs.posSet_eq ▸ mem_univ z) (ptsIn_subset_eqnSet hp i hi)
      (ptsIn_subset_eqnSet hp' j hj)
    rw [hw, ha z hz] at this
    exact this
  have hd : ∀ (c : AlgChart Y.str (RingHom.id ℂ) Y.dim), ∀ y ∈ c.e.source,
      c.chernDens ψ y = c.chernDens φ y := by
    intro c y hy
    have hi := mem_pick φ.isLB y
    have hj := mem_pick ψ.isLB y
    obtain ⟨a, ha⟩ := exists_unit_tv hp hp' _ _
    rw [c.chernDens_eq hψ hy hj, c.chernDens_eq hφ hy hi,
      hess_eq_of_unit c hφ hy hi hj a (key _ _ a ha)]
  refine ⟨ψ, hψ, ?_⟩
  rw [Weight.chernInt, Weight.chernInt, chernPart_eq_of_chernDens hd, chernPart_eq_of_chernDens hd]

theorem transport : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ),
    Presents Δ L r → Presents Δ L' r' → ∀ φ : Weight Y.str (RingHom.id ℂ) L, φ.IsCInf →
      ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
        ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  intro Y Δ L L' r r' hp hp' φ hφ
  exact exists_transport hp hp' φ hφ

end GlobalTheory.CompanionTheory.ChernTransport
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousParabolicProj
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_gpProj_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) :=
  GlobalTheory.CompanionTheory.BZMir.continuous_gpProj

end GlobalTheory.CompanionTheory.LeibPhi
end

