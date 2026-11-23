module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0489
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationViaTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0171
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0272
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0491
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0503
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicTensorRationalApproximationStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_tensor_rational_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ε : ℝ), 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ b : AF F ⊗[F] E, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧ ∃ c : E, (q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c ∈ boxE F E ε := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet | exact GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicVectorIntegralProductStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_vector_integral_product : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} (A : (Fin k → Cinf E) → ℂ) (B : (Fin k → Af E) → ℂ), ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) = (∫ x, A x ∂nuInf E k) * ∫ f, B f ∂nuFin E k := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.Split.integral_split | exact GlobalTheory.CompanionTheory.CutOff.Split.integral_split | (intros; apply GlobalTheory.CompanionTheory.CutOff.Split.integral_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedQuotientVanishAboveDim
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.GrTop

variable {X : Scheme.{0}}

theorem iInf_basicOpen {V : X.Opens} {ι : Type} (f : ι → Γ(X, V)) (S : Finset ι) (hS : S.Nonempty) :
    (⨅ α ∈ S, X.basicOpen (f α)) = X.basicOpen (∏ α ∈ S, f α) := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [Finset.cons_eq_insert, Finset.iInf_insert, Finset.prod_insert (by simpa using ha), Scheme.basicOpen_mul, ih]

theorem exists_cover {O : Type} [CommRing O] (q : X ⟶ Spec (CommRingCat.of O)) (d : ℕ) [SmoothOfRelativeDimension d q]
    {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → Γ(X, V)), (⨆ α, X.basicOpen (f α)) = V ∧
      ∀ α, Nonempty (Coord q (X.basicOpen (f α)) d) := by
  classical
  have h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (q.appLE ⊤ V le_top).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have key : ∀ x : V, ∃ f : Γ(X, V), (x : X) ∈ X.basicOpen f ∧ Nonempty (Coord q (X.basicOpen f) d) := by
    intro x
    obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen (RingHom.IsStandardSmoothOfRelativeDimension d)
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso q hV h x.2
    obtain ⟨g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨f, hf, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he⟩
  choose f hf hc using key
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).2) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hf _⟩)
  refine ⟨t, inferInstance, fun a => f a.1, le_antisymm (iSup_le fun a => X.basicOpen_le _) ?_, fun a => hc a.1⟩
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht hx)
  obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

theorem twoVariableSeriesVanishesBelowDegree_one_shiftVariable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s r j : ℕ)
    (hsr : s ≤ r) : Subsingleton (HQ (KS q s {V}) (r : ℤ) ((r : ℤ) + 1) j) := by
  have hz : ∀ (T : (KS q s {V}).FullSubcategory)
      (x : (sq (sFil (KS q s {V}) (r : ℤ)) (sFil (KS q s {V}) ((r : ℤ) + 1))).obj T), x = 0 := by
    intro T x
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have hy2 : (show T.obj.B from y) ∈ T.obj.pdPow ((r : ℤ).toNat) := hy
    rw [Int.toNat_natCast] at hy2
    have hy' : (show T.obj.B from y) ∈ T.obj.pdPow s := T.obj.pdPow_anti hsr hy2
    rw [T.property.1.1, Ideal.mem_bot] at hy'
    subst hy'
    rfl
  refine ⟨fun a b => ?_⟩
  obtain ⟨z, hz1, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 a
  obtain ⟨z', hz1', rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 b
  have e : z = z' := funext fun σ => (hz _ _).trans (hz _ _).symm
  subst e
  rfl

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

theorem grTop (hG : KH.LocGr) (hP : KH.PolyTf) : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V →
    ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r → Subsingleton (HQ (KS q s {V}) r (r + 1) j) := by
  intro K _ _ X q d _ V hV s r j hr
  lift r to ℕ using (by omega)
  have hdr : d < r := by exact_mod_cast hr
  rcases le_or_gt s r with hsr | hsr
  · exact twoVariableSeriesVanishesBelowDegree_one_shiftVariable q V s r j hsr
  obtain ⟨ι, _, f, hcov, hc⟩ := exists_cover q d hV
  let U : ι → X.Opens := fun α => X.basicOpen (f α)
  have hloc : ∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU (sq (thFil (smFun X q) (r : ℤ))
      (thFil (smFun X q) ((r : ℤ) + 1))) (St (TF 1 s) {⨅ α ∈ S, U α}) j) := by
    intro S hS j
    obtain ⟨α, hα⟩ := id hS
    have haff : IsAffineOpen (⨅ α ∈ S, U α) := by
      change IsAffineOpen (⨅ α ∈ S, X.basicOpen (f α))
      rw [iInf_basicOpen f S hS]
      exact hV.basicOpen _
    obtain ⟨c', -⟩ := _root_.GlobalTheory.CompanionTheory.CoordRes.main (hc α).some (iInf₂_le α hα) haff
    exact GlobalTheory.CompanionTheory.KIso.loc_vanish q hG hP c' r s hdr (by omega) j
  have hglob := (GlobalTheory.T.stable_cover_cech_vanishing.1 (sq (thFil (smFun X q) (r : ℤ)) (thFil (smFun X q) ((r : ℤ) + 1))) (TF 1 s) U 0).2.1
    hloc j
  have h2 : KS q s (Set.range U) ≤ KS q s {V} := by
    rintro T ⟨hT, W, ⟨α, rfl⟩, hW⟩
    exact ⟨hT, V, rfl, fun x hx => X.basicOpen_le (f α) (hW hx)⟩
  have hc' : ∀ W ∈ ({V} : Set X.Opens), W ≤ sSup (Set.range U) := by
    intro W hW
    rw [Set.mem_singleton_iff.1 hW, sSup_range]
    exact hcov.ge
  have b := (_root_.GlobalTheory.CompanionTheory.NlZar.zariski_descent (TF 1 s : ObjectProperty (Thick (smFun X q))) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} h2 hc' j).1 (r : ℤ) ((r : ℤ) + 1)
  have : Subsingleton (HQ (KS q s (Set.range U)) (r : ℤ) ((r : ℤ) + 1) j) := hglob
  exact ⟨fun a c => b.1 (@Subsingleton.elim _ this _ _)⟩

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

theorem grTop_main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V → ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r →
    Subsingleton (HQ (KS q s {V}) r (r + 1) j) :=
  @grTop GlobalTheory.CompanionTheory.LocGrStep.loc_gr GlobalTheory.CompanionTheory.PolyTfCon.polyTf

end GlobalTheory.CompanionTheory.GrTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorAdelicLatticeCompactStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_adelic_lattice_compact : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ}, StdPsi ψ → ∀ (S : Finset (Pl E)), (∀ w, w ∉ S → Cond ψ w) → ∀ (L : Set (Af E)), (∀ w, w ∉ S → ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) → (∀ w ∈ S, ∃ N ∈ 𝓝 (0 : w.adicCompletion E), ∀ t ∈ N, sLoc E w t ∈ L) → ∃ C : Set (Af E), IsCompact C ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → z ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator | exact GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator | (intros; apply GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
section
set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_monic_aeval_add {M : Type*} [AddCommGroup M] [Module ℂ M] (Ω T : Module.End ℂ M)
    (hc : Commute Ω T) (W : Submodule ℂ M) [FiniteDimensional ℂ W] (hT : ∀ w ∈ W, T w ∈ W)
    (q : Polynomial ℂ) (hq : q.Monic) (hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0) {v : M} (hv : v ∈ W) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (Ω + T) P v = 0 := by
  classical
  let V : Submodule ℂ M := ⨆ m : Fin (q.natDegree + 1), W.map (Ω ^ (m : ℕ))
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_iSup _
  have hmem : ∀ (i : ℕ), i < q.natDegree + 1 → ∀ w ∈ W, (Ω ^ i) w ∈ V := fun i hi w hw =>
    Submodule.mem_iSup_of_mem (⟨i, hi⟩ : Fin (q.natDegree + 1)) ⟨w, hw, rfl⟩
  have hpow : ∀ (m : ℕ), ∀ w ∈ W, (Ω ^ m) w ∈ V := by
    intro m w hw
    have e : (Ω ^ m) w = Polynomial.aeval Ω (Polynomial.X ^ m %ₘ q) w := by
      have h1 := Polynomial.modByMonic_add_div (Polynomial.X ^ m : Polynomial ℂ) q
      have h2 : Polynomial.aeval Ω (q * (Polynomial.X ^ m /ₘ q)) w = 0 := by
        rw [mul_comm, map_mul, Module.End.mul_apply, hqW w hw, map_zero]
      have h3 := congrArg (fun p => Polynomial.aeval Ω p w) h1
      simp only [map_add (f := _), LinearMap.add_apply, h2, add_zero, map_pow, Polynomial.aeval_X] at h3
      exact h3.symm
    rw [e, Polynomial.aeval_eq_sum_range' (n := q.natDegree + 1)
      (Nat.lt_succ_of_le (Polynomial.natDegree_modByMonic_le _ hq)), LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i hi => by
      rw [LinearMap.smul_apply]
      exact V.smul_mem _ (hmem i (Finset.mem_range.1 hi) w hw)
  have hst : ∀ x ∈ V, (Ω + T) x ∈ V := by
    intro x hx
    have hle : V ≤ V.comap (Ω + T) := by
      refine iSup_le fun m => ?_
      rintro _ ⟨w, hw, rfl⟩
      have e : (Ω + T) ((Ω ^ (m : ℕ)) w) = (Ω ^ ((m : ℕ) + 1)) w + (Ω ^ (m : ℕ)) (T w) := by
        rw [LinearMap.add_apply, pow_succ', Module.End.mul_apply, ← Module.End.mul_apply T,
          ((hc.pow_left (m : ℕ)).eq).symm, Module.End.mul_apply]
      change (Ω + T) ((Ω ^ (m : ℕ)) w) ∈ V
      rw [e]
      exact V.add_mem (hpow _ w hw) (hpow _ _ (hT w hw))
    exact hle hx
  have hv' : v ∈ V := by simpa using hpow 0 v hv
  exact AutomorphicForm.exists_monic_aeval_apply_eq_zero (Ω + T) V hst hv'

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_aeval_lapOp_eq_zero (φ : Sm E a) (hA : IsAutForm φ) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (hskew : ∀ i, ε i = -1 → b i ∈ archSkew E a) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (lapOp (⇑b)) P φ = 0 := by
  classical
  set Ω := omegaOp (E := E) (a := a) (⇑b) ε with hΩ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hWdef
  haveI : FiniteDimensional ℂ W := hA.kfin
  have hZ : Ω ∈ Zalg E a := by
    rw [hΩ, GlobalTheory.T.omega_operator_eq_casimir_sum  E a d b ε hε horth]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun w _ => Subalgebra.add_mem _ ?_ ?_) _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
  set Vz := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hVz
  haveI : FiniteDimensional ℂ Vz := hA.zfin
  have hVs : ∀ w ∈ Vz, Ω w ∈ Vz := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Ω w ∈ Vz) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨z, hz, rfl⟩
      exact Submodule.subset_span ⟨Ω * z, Subalgebra.mul_mem _ hZ hz, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hφV : φ ∈ Vz := Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩
  obtain ⟨q, hqm, -, hq⟩ := AutomorphicForm.exists_monic_aeval_apply_eq_zero Ω Vz hVs hφV
  have hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Polynomial.aeval Ω q w = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      have hcomm : ∀ m, cptRep E a k (Ω m) = Ω (cptRep E a k m) := fun m =>
        (congrArg (fun T : Module.End ℂ (Sm E a) => T m)
          (GlobalTheory.T.omega_operator_commutes_infinite_gl E a d b ε hε horth (Unitary.toUnits k))).symm
      have := AutomorphicForm.map_aeval_apply_of_intertwine (cptRep E a k) hcomm q φ
      rw [hq, map_zero] at this
      exact this.symm
    · rw [map_zero]
    · intro x y _ _ hx hy; rw [map_add (f := _), hx, hy, add_zero]
    · intro c x _ hx; rw [map_smul, hx, smul_zero]
  have hlap : Commute Ω (lapOp (⇑b)) := by
    simp only [lapOp, Commute, SemiconjBy]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Ω * liB (b i) = liB (b i) * Ω := omegaOp_comm_liB b ε hε horth (b i)
    rw [← mul_assoc, h1, mul_assoc, h1, mul_assoc]
  have hTW : ∀ w ∈ W, (lapOp (⇑b) - Ω) w ∈ W := by
    intro w hw
    have e : (lapOp (E := E) (a := a) (⇑b) - Ω) w =
        ∑ i, ((1 : ℂ) - (ε i : ℂ)) • liB (b i) (liB (b i) w) := by
      simp only [hΩ, lapOp, omegaOp, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        Module.End.mul_apply]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      module
    rw [e]
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases hε i with h | h
    · simp [h]
    · refine W.smul_mem _ ?_
      have hs := mem_archSkew.1 (hskew i h)
      have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := hA.kfin
      exact _root_.GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span E a φ (b i) hs hfd _ (_root_.GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span E a φ (b i) hs hfd _ hw)
  have hφW : φ ∈ W := by
    refine Submodule.subset_span ⟨1, ?_⟩
    change cptRep E a 1 φ = φ
    rw [map_one]
    rfl
  have hc : Commute Ω (lapOp (⇑b) - Ω) := by
    refine LinearMap.ext fun x => ?_
    have h2 := LinearMap.congr_fun hlap.eq x
    simp only [Module.End.mul_apply] at h2 ⊢
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h2]
  have hsum : Ω + (lapOp (⇑b) - Ω) = lapOp (⇑b) := LinearMap.ext fun x => by simp
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_monic_aeval_add Ω (lapOp (⇑b) - Ω) hc W hTW q hqm hqW hφW
  refine ⟨P, hP1, hP2, ?_⟩
  rwa [hsum] at hP3

theorem sliceL_aeval_lapOp {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra)
    (P : Polynomial ℂ) (ψ : Sm E a) (g : AdelicGLn.AdelicGL E a) :
    sliceL g (smL E a (Polynomial.aeval (lapOp (⇑b)) P ψ)) =
      Polynomial.aeval ((isExpLieAlgebra E a).laplacian (F := ℂ) b) P (sliceL g (smL E a ψ)) := by
  refine AutomorphicForm.map_aeval_apply_of_intertwine ((sliceL g).comp (smL E a)) (fun m => ?_) P ψ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, smL_lapOp, map_sum, sliceL_uAction,
    IsExpLieAlgebra.laplacian, LinearMap.sum_apply, Module.End.mul_apply,
    IsExpLieAlgebra.rightUAction_ι]

theorem uJ_eq_conv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hs : φ.1 ∈ AutomorphicForm.archSmooth E a), IsAutForm φ → (∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (μ : MeasureTheory.Measure (AutomorphicForm.archGroup E a)) [μ.IsHaarMeasure]
    (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim E a)),
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : AdelicGLn.AdelicGL E a,
      ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) k J) (⟨φ.1, hs⟩ : ↥(AutomorphicForm.archSmooth E a)) :
        ↥(AutomorphicForm.archSmooth E a)) : AdelicGLn.AdelicGL E a → ℂ) g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂μ) := by
  intro E _ _ _ a φ hs hA _ _ μ _ k J
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := E) (n := a)
  obtain ⟨P, hm, hd, hP⟩ := exists_aeval_lapOp_eq_zero φ hA b ε hε horth hskew
  exact GlobalTheory.T.laplacian_monic_annihilator_measure E a (smL E a φ) d b P hm hd
    (fun g => by rw [← sliceL_aeval_lapOp, hP, map_zero, map_zero]) μ k J

end GlobalTheory.CompanionTheory.HCRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterInCoordinates
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem half_trace_eq (σ : E →ₐ[F] E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (z : Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = (Θ z w).re := by
  have h4 := h.2.2.2 z w
  have h5 : e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = 2 * (Θ z w).re := by
    have := congrArg Complex.re h4
    simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at this
    rw [this]; ring
  rw [map_mul, Pi.mul_apply, he, h5, map_div₀, map_one, map_ofNat]
  ring

def evC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) : Ainf F ⊗[F] E →+* ℂ :=
  (Pi.evalRingHom (fun _ : InfinitePlace F => ℂ) w).comp (Θ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ))

theorem evC_apply (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) (z : Ainf F ⊗[F] E) :
    evC Θ w z = Θ z w := rfl

theorem coord_gramR (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    matC Θ (gramR (Ainf F) σ J X) w = gramC (J.map (τ w)) (tupC Θ X w) := by
  ext a c
  change evC Θ w (Formalism.UG.hform (sigR (Ainf F) σ) (JR (Ainf F) J) (X a) (X c)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, gramC, tupC, evC_apply, h.2.1, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show inclR (Ainf F) (J i j) = (1 : Ainf F) ⊗ₜ[F] (J i j) from rfl, h.2.2.1]

theorem coord_trace_mul (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (B G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) :
    Θ (Matrix.trace (B * G)) w = Matrix.trace (matC Θ B w * matC Θ G w) := by
  change evC Θ w _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]
  rfl

theorem gramC_smul {n M : ℕ} (c : ℂ) (J : Matrix (Fin M) (Fin M) ℂ) (X : Fin n → Fin M → ℂ) :
    gramC (c • J) X = c • gramC J X := by
  ext a b
  simp only [gramC, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem psiInf_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∀ (a : F) (ψ : AddChar (AF F) ℂ),
  (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) →
  ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
    (X : Fin n → Fin M → Ainf F ⊗[F] E),
  psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (B * gramR (Ainf F) σ J X))) =
    Complex.exp (2 * Real.pi * Complex.I * ((phaseM (fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w))
      (fun w => matC Θ B w) (tupC Θ X) : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ σ ρ e τ Θ h he a ψ hψ M n J B X
  change ψ (pairA F _ 0) = _
  rw [hψ]
  congr 3
  rw [phaseM]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [half_trace_eq σ ρ e τ Θ h he, coord_trace_mul, coord_gramR σ e τ Θ h, gramC_smul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponentialStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_eigen_exponential : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ), lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a), φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | exact GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | (intros; apply GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterQuadraticTrace
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ChzConj

theorem chz_conj : ∀ (D : D7) (ρ p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (b : Mx D p p) (y : Mx D ρ p) (z₀ : hermA D ρ),
  z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) →
    chz ψ b₀ z₀ = ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) := by
  intro D ρ p ψ b₀ b y z₀ hz
  unfold chz pr
  rw [hz]
  congr 2
  change Matrix.trace (Matrix.map b₀.1 (incA D) * ((y * b) * adj y)) = Matrix.trace (b * (adj y * (Matrix.map b₀.1 (incA D) * y)))
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.ChzConj

end
end

